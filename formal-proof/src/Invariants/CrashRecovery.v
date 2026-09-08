(* CrashRecovery.v: power loss and startup recovery over the page-granular
   FTLState.

   Translation is page-granular here: [l2p_map s a p : option PhysAddr] sends
   each logical page (a, p) to its own physical page (block + page offset), so
   recovery must rebuild the mapping one *logical page* at a time from the
   reverse stamp (page_lpa : option (Addr * Page)) that each live page carries
   in its OOB, rather than one block at a time.

   ── The volatility split ──────────────────────────────────────────────

   Every field of [FTLState] is DRAM-resident (lost on power loss) or lives
   on flash / in vendor configuration (survives).  A field is persistent
   exactly when the only instructions that modify it are flash commands
   (read core/Operational.v):

     l2p_map                       PrimMapAddr, PrimRemap        VOLATILE
     block_tenant, block_namespace PrimMapAddr, PrimRemap, ...   VOLATILE
     free_block_list, free_block   allocation / erase           VOLATILE
     open_block, write_ptr,        the page-granular allocation
       block_open                  frontier (DRAM only)         VOLATILE
     page_state, page_role,        recorded on flash / OOB      PERSISTENT
       page_meta, wear_count
     addr_tenant, addr_namespace,  vendor configuration         PERSISTENT
       region_table, key_table

   The three frontier fields [open_block]/[write_ptr]/[block_open] are the
   per-tenant allocation frontier, which is DRAM-resident controller state: a
   power loss loses which block was open and how far its write pointer had
   advanced.  A real FTL does not persist this; it re-opens a block lazily on
   the first post-boot write.  So [crash] clears them and [recover] leaves
   them cleared -- after recovery no block is open.  The frontier clauses
   (Inv20, Inv21, Inv23, Inv25) then hold vacuously, and the free-pool clause
   (Inv24) by the same rebuild that restores the free list.

   ── What is proved here ───────────────────────────────────────────────

   [l2p_reconstruction_sound]      recovery never invents a mapping;
   [l2p_reconstruction_complete]   every logical page whose physical page is
                                   live is mapped exactly as before;
   [l2p_reconstruction_exact]      pointwise equality when every mapped page
                                   is live;
   [read_page_after_recovery]      every sector reads the same;
   [recover_preserves_invariant]   all 29 conjuncts survive crash+recover;
   [recover_preserves_spare_block_available]
                                   a device that could open a fresh block
                                   still can.                                *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   Section 1: the crash transition
   ══════════════════════════════════════════════════════════════════════ *)

Definition crash (s : FTLState) : FTLState :=
  mkFTLState
    (fun _ _ => None)          (* l2p_map          : DRAM mapping table   *)
    (page_state s)
    (page_role s)
    (addr_tenant s)
    (addr_namespace s)
    (fun _ => None)            (* block_tenant     : ACU ownership table  *)
    (fun _ => None)            (* block_namespace  : ACU ownership table  *)
    (page_meta s)
    (region_table s)
    []                         (* free_block_list  : DRAM allocator       *)
    (fun _ => false)           (* free_block       : DRAM allocator       *)
    (wear_count s)
    (key_table s)
    (fun _ _ => None)          (* open_block       : DRAM frontier        *)
    (fun _ _ => 0)             (* write_ptr        : DRAM frontier        *)
    (fun _ => false).          (* block_open       : DRAM frontier        *)

Lemma crash_idempotent : forall s, crash (crash s) = crash s.
Proof. intros s. reflexivity. Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 2: geometry
   ══════════════════════════════════════════════════════════════════════ *)

(* Nothing lives at a page index the block does not have. *)
Definition in_geometry (s : FTLState) : Prop :=
  forall b p,
    pages_per_block <= p ->
    page_state s b p = PS_Empty /\
    page_role s b p = None /\
    page_meta s b p = empty_page_meta.

Lemma in_geometry_valid_lt :
  forall s b p d,
    in_geometry s ->
    page_state s b p = PS_Valid d ->
    p < pages_per_block.
Proof.
  intros s b p d Hgeo Hps.
  destruct (le_lt_dec pages_per_block p) as [Hle | Hlt]; [| exact Hlt].
  destruct (Hgeo b p Hle) as [Hempty _]. rewrite Hempty in Hps. discriminate.
Qed.

Lemma in_geometry_nonempty_lt :
  forall s b p,
    in_geometry s ->
    page_state s b p <> PS_Empty ->
    p < pages_per_block.
Proof.
  intros s b p Hgeo Hne.
  destruct (le_lt_dec pages_per_block p) as [Hle | Hlt]; [| exact Hlt].
  destruct (Hgeo b p Hle) as [Hempty _]. contradiction.
Qed.

Lemma empty_state_in_geometry : in_geometry empty_state.
Proof. intros b p _. cbn. auto. Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 3: the start-up scan
   ══════════════════════════════════════════════════════════════════════ *)

Definition all_blocks : list Block := seq 0 total_blocks.

Lemma in_all_blocks : forall b, In b all_blocks <-> b < total_blocks.
Proof. intros b. unfold all_blocks. rewrite in_seq. lia. Qed.

Lemma in_all_pages : forall p, In p all_pages <-> p < pages_per_block.
Proof. intros p. unfold all_pages. rewrite in_seq. lia. Qed.

(* Every physical page (block, offset) in the device geometry. *)
Definition all_phys : list (Block * Page) :=
  flat_map (fun b => map (fun p => (b, p)) all_pages) all_blocks.

Lemma in_all_phys :
  forall b p, In (b, p) all_phys <-> b < total_blocks /\ p < pages_per_block.
Proof.
  intros b p. unfold all_phys. rewrite in_flat_map. split.
  - intros [b' [Hb Hin]]. apply in_map_iff in Hin.
    destruct Hin as [p' [Heq Hp]]. injection Heq as <- <-.
    split; [apply in_all_blocks; exact Hb | apply in_all_pages; exact Hp].
  - intros [Hb Hp]. exists b. split; [apply in_all_blocks; exact Hb |].
    apply in_map_iff. exists p. split; [reflexivity | apply in_all_pages; exact Hp].
Qed.

(* A page is live iff it holds data. *)
Definition live_pageb (s : FTLState) (b : Block) (p : Page) : bool :=
  match page_state s b p with PS_Valid _ => true | _ => false end.

(* A block is live iff one of its pages is. *)
Definition block_liveb (s : FTLState) (b : Block) : bool :=
  existsb (live_pageb s b) all_pages.

(* A live physical page stamped with logical page (a, q). *)
Definition stamped_phys (s : FTLState) (a q : nat) (bp : Block * Page) : bool :=
  match page_state s (fst bp) (snd bp),
        page_lpa (page_meta s (fst bp) (snd bp)) with
  | PS_Valid _, Some lp => andb (Nat.eqb (fst lp) a) (Nat.eqb (snd lp) q)
  | _, _ => false
  end.

(* The forward mapping, rebuilt one logical page at a time from the reverse
   stamps in the OOB. *)
Definition recover_l2p (s : FTLState) (a q : nat) : option PhysAddr :=
  match find (stamped_phys s a q) all_phys with
  | Some bp => Some (mkPhysAddr (fst bp) (snd bp))
  | None => None
  end.

(* The logical address a live block serves: the address stamped on its first
   live page.  Inv18 makes all live pages of a block share one tenant, so any
   representative gives the same ownership. *)
Definition block_lpa (s : FTLState) (b : Block) : option Addr :=
  match find (live_pageb s b) all_pages with
  | Some p =>
      match page_lpa (page_meta s b p) with
      | Some lp => Some (fst lp)
      | None => None
      end
  | None => None
  end.

Definition recover_block_tenant (s : FTLState) (b : Block) : option TenantId :=
  match block_lpa s b with Some a => addr_tenant s a | None => None end.

Definition recover_block_namespace (s : FTLState) (b : Block) : option NamespaceId :=
  match block_lpa s b with Some a => addr_namespace s a | None => None end.

Definition option_nat_eqb (x y : option nat) : bool :=
  match x, y with
  | None, None => true
  | Some m, Some n => Nat.eqb m n
  | _, _ => false
  end.

Definition option_lpa_eqb (x y : option LPA) : bool :=
  match x, y with
  | None, None => true
  | Some m, Some n => andb (Nat.eqb (fst m) (fst n)) (Nat.eqb (snd m) (snd n))
  | _, _ => false
  end.

Definition page_meta_eqb (m1 m2 : PageMeta) : bool :=
  Nat.eqb (page_owner_tenant m1) (page_owner_tenant m2) &&
  Nat.eqb (page_owner_namespace m1) (page_owner_namespace m2) &&
  option_nat_eqb (page_tag m1) (page_tag m2) &&
  option_lpa_eqb (page_lpa m1) (page_lpa m2).

Lemma option_nat_eqb_eq : forall x y, option_nat_eqb x y = true -> x = y.
Proof.
  intros [m|] [n|] H; cbn in H; try discriminate; [| reflexivity].
  apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

Lemma option_lpa_eqb_eq : forall x y, option_lpa_eqb x y = true -> x = y.
Proof.
  intros [[m1 m2]|] [[n1 n2]|] H; cbn in H; try discriminate; [| reflexivity].
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma page_meta_eqb_eq : forall m1 m2, page_meta_eqb m1 m2 = true -> m1 = m2.
Proof.
  intros [t1 n1 g1 l1] [t2 n2 g2 l2] H.
  unfold page_meta_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H Hl].
  apply andb_true_iff in H. destruct H as [H Hg].
  apply andb_true_iff in H. destruct H as [Ht Hn].
  apply Nat.eqb_eq in Ht. apply Nat.eqb_eq in Hn.
  apply option_nat_eqb_eq in Hg. apply option_lpa_eqb_eq in Hl.
  subst. reflexivity.
Qed.

(* An erased page: empty, with a clean OOB. *)
Definition erased_pageb (s : FTLState) (b : Block) (p : Page) : bool :=
  match page_state s b p with
  | PS_Empty => page_meta_eqb (page_meta s b p) empty_page_meta
  | _ => false
  end.

Definition block_erasedb (s : FTLState) (b : Block) : bool :=
  forallb (erased_pageb s b) all_pages.

(* Recovery erases a block that holds no live page and is not already
   erased.  A block already erased is listed as free without another erase. *)
Definition reclaimb (s : FTLState) (b : Block) : bool :=
  negb (block_liveb s b) && negb (block_erasedb s b).

Definition recover_free_list (s : FTLState) : list Block :=
  filter (fun b => negb (block_liveb s b)) all_blocks.

Definition recover_free_block (s : FTLState) (b : Block) : bool :=
  Nat.ltb b total_blocks && negb (block_liveb s b).

Definition recover (s : FTLState) : FTLState :=
  mkFTLState
    (recover_l2p s)
    (fun b p => if reclaimb s b then PS_Empty else page_state s b p)
    (fun b p => if reclaimb s b then None else page_role s b p)
    (addr_tenant s)
    (addr_namespace s)
    (recover_block_tenant s)
    (recover_block_namespace s)
    (fun b p => if reclaimb s b then empty_page_meta else page_meta s b p)
    (region_table s)
    (recover_free_list s)
    (recover_free_block s)
    (fun b => if reclaimb s b then S (wear_count s b) else wear_count s b)
    (key_table s)
    (fun _ _ => None)          (* open_block  : no block open after boot   *)
    (fun _ _ => 0)             (* write_ptr   : frontier cleared           *)
    (fun _ => false).          (* block_open  : nothing open               *)

(* [recover] reads persistent fields only. *)
Lemma recover_crash : forall s, recover (crash s) = recover s.
Proof. intros s. reflexivity. Qed.

Lemma flash_determines_recovery :
  forall s1 s2, crash s1 = crash s2 -> recover s1 = recover s2.
Proof.
  intros s1 s2 H.
  rewrite <- (recover_crash s1), <- (recover_crash s2), H. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 4: what the scan finds
   ══════════════════════════════════════════════════════════════════════ *)

Lemma live_pageb_true :
  forall s b p,
    live_pageb s b p = true <-> exists d, page_state s b p = PS_Valid d.
Proof.
  intros s b p. unfold live_pageb.
  destruct (page_state s b p) as [| | d] eqn:Hps; split; intros H;
    try discriminate; try (destruct H; discriminate).
  - exists d. reflexivity.
  - reflexivity.
Qed.

Lemma block_liveb_true :
  forall s b,
    block_liveb s b = true <->
    exists p d, p < pages_per_block /\ page_state s b p = PS_Valid d.
Proof.
  intros s b. unfold block_liveb. rewrite existsb_exists. split.
  - intros [p [Hin Hl]]. apply live_pageb_true in Hl. destruct Hl as [d Hps].
    exists p, d. split; [apply in_all_pages; exact Hin | exact Hps].
  - intros [p [d [Hp Hps]]]. exists p. split; [apply in_all_pages; exact Hp |].
    apply live_pageb_true. exists d. exact Hps.
Qed.

Lemma block_liveb_false :
  forall s b p d,
    block_liveb s b = false ->
    p < pages_per_block ->
    page_state s b p <> PS_Valid d.
Proof.
  intros s b p d Hdead Hp Hps.
  assert (Hlive : block_liveb s b = true).
  { apply block_liveb_true. exists p, d. auto. }
  congruence.
Qed.

Lemma block_liveb_of_valid :
  forall s b p d,
    p < pages_per_block ->
    page_state s b p = PS_Valid d ->
    block_liveb s b = true.
Proof.
  intros s b p d Hp Hps. apply block_liveb_true. exists p, d. auto.
Qed.

Lemma stamped_phys_true :
  forall s a q bp,
    stamped_phys s a q bp = true <->
    (exists d, page_state s (fst bp) (snd bp) = PS_Valid d) /\
    page_lpa (page_meta s (fst bp) (snd bp)) = Some (a, q).
Proof.
  intros s a q bp. unfold stamped_phys. split.
  - intros H.
    destruct (page_state s (fst bp) (snd bp)) as [| | d] eqn:Hps; try discriminate.
    destruct (page_lpa (page_meta s (fst bp) (snd bp))) as [[a' q']|] eqn:Hlpa;
      try discriminate.
    apply andb_true_iff in H. destruct H as [Ha Hq].
    apply Nat.eqb_eq in Ha. apply Nat.eqb_eq in Hq. cbn in Ha, Hq. subst.
    split; [exists d; reflexivity | reflexivity].
  - intros [[d Hps] Hlpa]. rewrite Hps, Hlpa. cbn. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma block_erasedb_true :
  forall s b,
    block_erasedb s b = true ->
    forall p,
      p < pages_per_block ->
      page_state s b p = PS_Empty /\ page_meta s b p = empty_page_meta.
Proof.
  intros s b H p Hp.
  unfold block_erasedb in H. rewrite forallb_forall in H.
  specialize (H p (proj2 (in_all_pages p) Hp)).
  unfold erased_pageb in H.
  destruct (page_state s b p); try discriminate.
  split; [reflexivity | apply page_meta_eqb_eq; exact H].
Qed.

Lemma reclaimb_true_dead :
  forall s b, reclaimb s b = true -> block_liveb s b = false.
Proof.
  intros s b H. unfold reclaimb in H. apply andb_true_iff in H.
  destruct H as [H _]. apply negb_true_iff in H. exact H.
Qed.

Lemma live_not_reclaimed :
  forall s b, block_liveb s b = true -> reclaimb s b = false.
Proof.
  intros s b H. unfold reclaimb. rewrite H. reflexivity.
Qed.

Lemma dead_not_reclaimed_erased :
  forall s b,
    reclaimb s b = false ->
    block_liveb s b = false ->
    block_erasedb s b = true.
Proof.
  intros s b Hr Hd. unfold reclaimb in Hr. rewrite Hd in Hr. cbn in Hr.
  apply negb_false_iff in Hr. exact Hr.
Qed.

(* Everything the scan learned about a recovered mapping entry. *)
Lemma recover_l2p_found :
  forall s a q pa,
    recover_l2p s a q = Some pa ->
    pa_block pa < total_blocks /\ pa_page pa < pages_per_block /\
    (exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d) /\
    page_lpa (page_meta s (pa_block pa) (pa_page pa)) = Some (a, q).
Proof.
  intros s a q pa H. unfold recover_l2p in H.
  destruct (find (stamped_phys s a q) all_phys) as [bp|] eqn:Hf; [| discriminate].
  injection H as <-. cbn.
  apply find_some in Hf. destruct Hf as [Hin Hst].
  destruct bp as [b p]. cbn in *.
  apply in_all_phys in Hin. destruct Hin as [Hb Hp].
  apply stamped_phys_true in Hst. cbn in Hst. destruct Hst as [Hval Hlpa].
  repeat split; assumption.
Qed.

Lemma recover_l2p_live :
  forall s a q pa, recover_l2p s a q = Some pa -> block_liveb s (pa_block pa) = true.
Proof.
  intros s a q pa H. apply recover_l2p_found in H.
  destruct H as [_ [Hp [[d Hps] _]]].
  eapply block_liveb_of_valid; eauto.
Qed.

Lemma recover_l2p_not_reclaimed :
  forall s a q pa, recover_l2p s a q = Some pa -> reclaimb s (pa_block pa) = false.
Proof.
  intros s a q pa H. apply live_not_reclaimed. eapply recover_l2p_live; eauto.
Qed.

Lemma in_recover_free_list :
  forall s b,
    In b (recover_free_list s) <-> b < total_blocks /\ block_liveb s b = false.
Proof.
  intros s b. unfold recover_free_list. rewrite filter_In, in_all_blocks.
  rewrite negb_true_iff. reflexivity.
Qed.

Lemma block_lpa_dead :
  forall s b, block_liveb s b = false -> block_lpa s b = None.
Proof.
  intros s b Hdead. unfold block_lpa.
  destruct (find (live_pageb s b) all_pages) as [p|] eqn:Hf; [| reflexivity].
  apply find_some in Hf. destruct Hf as [Hin Hl].
  exfalso. apply live_pageb_true in Hl. destruct Hl as [d Hps].
  apply in_all_pages in Hin.
  exact (block_liveb_false s b p d Hdead Hin Hps).
Qed.

Lemma recover_page_state_valid :
  forall s b p d,
    page_state (recover s) b p = PS_Valid d ->
    reclaimb s b = false /\ page_state s b p = PS_Valid d.
Proof.
  intros s b p d H. cbn in H.
  destruct (reclaimb s b); [discriminate | auto].
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 5: reconstruction of the mapping (Inv3/Inv4 at work)
   ══════════════════════════════════════════════════════════════════════ *)

(* Recovery never invents a mapping: a stamp is honoured by the mapping
   (Inv4). *)
Lemma recover_l2p_sound :
  forall s a q pa,
    ftl_invariant s ->
    recover_l2p s a q = Some pa ->
    l2p_map s a q = Some pa.
Proof.
  intros s a q pa Hinv Hrec.
  destruct Hinv as (_&_&_&_&_&_&HInv4&_).
  apply recover_l2p_found in Hrec. destruct Hrec as [_ [_ [[d Hps] Hlpa]]].
  pose proof (HInv4 a q (pa_block pa) (pa_page pa) d Hps Hlpa) as Hmap.
  destruct pa as [b p]. cbn in Hmap. exact Hmap.
Qed.

(* Every logical page whose physical page is live is mapped as before: the
   page is stamped with it (Inv3), and no other page carries that stamp
   (Inv4). *)
Lemma recover_l2p_complete :
  forall s a q pa d,
    ftl_invariant s ->
    l2p_map s a q = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    recover_l2p s a q = Some pa.
Proof.
  intros s a q pa d Hinv Hmap Hps.
  pose proof Hinv as Hinv0.
  destruct Hinv as (_&_&_&HInv1&_&HInv3&HInv4&_).
  pose proof (HInv3 a q pa d Hmap Hps) as Hlpa.
  pose proof (HInv1 a q pa Hmap) as [Hb [Hp _]].
  assert (Hwit : stamped_phys s a q (pa_block pa, pa_page pa) = true).
  { apply stamped_phys_true. cbn. split; [exists d; exact Hps | exact Hlpa]. }
  unfold recover_l2p.
  destruct (find (stamped_phys s a q) all_phys) as [bp|] eqn:Hf.
  - apply find_some in Hf. destruct Hf as [_ Hst].
    apply stamped_phys_true in Hst. destruct Hst as [[d' Hps'] Hlpa'].
    pose proof (HInv4 a q (fst bp) (snd bp) d' Hps' Hlpa') as Hmap'.
    rewrite Hmap in Hmap'. injection Hmap' as <-. reflexivity.
  - exfalso.
    pose proof (find_none _ _ Hf (pa_block pa, pa_page pa)
                  (proj2 (in_all_phys _ _) (conj Hb Hp))) as Hfalse.
    congruence.
Qed.

Theorem l2p_reconstruction_sound :
  forall s a q pa,
    ftl_invariant s ->
    l2p_map (recover (crash s)) a q = Some pa ->
    l2p_map s a q = Some pa.
Proof.
  intros s a q pa Hinv H. rewrite recover_crash in H. cbn in H.
  eapply recover_l2p_sound; eauto.
Qed.

Theorem l2p_reconstruction_complete :
  forall s a q pa d,
    ftl_invariant s ->
    l2p_map s a q = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    l2p_map (recover (crash s)) a q = Some pa.
Proof.
  intros s a q pa d Hinv Hmap Hps. rewrite recover_crash. cbn.
  eapply recover_l2p_complete; eauto.
Qed.

(* Pointwise equality of the two mappings, under the hypothesis that every
   mapped physical page is live.  The hypothesis cannot be dropped:
   [COpInvalidate] leaves the target stale while nothing on flash records the
   mapping. *)
Theorem l2p_reconstruction_exact :
  forall s,
    ftl_invariant s ->
    (forall a q pa,
       l2p_map s a q = Some pa ->
       exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d) ->
    forall a q, l2p_map (recover (crash s)) a q = l2p_map s a q.
Proof.
  intros s Hinv Hlive a q.
  destruct (l2p_map s a q) as [pa|] eqn:Hmap.
  - destruct (Hlive a q pa Hmap) as [d Hps].
    eapply l2p_reconstruction_complete; eauto.
  - destruct (l2p_map (recover (crash s)) a q) as [pa|] eqn:Hrec; [| reflexivity].
    apply l2p_reconstruction_sound in Hrec; [| exact Hinv]. congruence.
Qed.

(* The device reads the same after power loss and recovery, sector by
   sector. *)
Theorem read_page_after_recovery :
  forall s a p,
    ftl_invariant s ->
    in_geometry s ->
    read_page (recover (crash s)) a p = read_page s a p.
Proof.
  intros s a p Hinv Hgeo.
  rewrite recover_crash. unfold read_page.
  destruct (l2p_map s a p) as [pa|] eqn:Hmap.
  - destruct (page_state s (pa_block pa) (pa_page pa)) as [| | d] eqn:Hps.
    + (* empty target: whatever the recovery does, nothing readable appears *)
      destruct (l2p_map (recover s) a p) as [pa'|] eqn:Hrec; [| reflexivity].
      cbn in Hrec. pose proof (recover_l2p_sound s a p pa' Hinv Hrec) as Hmap'.
      rewrite Hmap in Hmap'. injection Hmap' as <-.
      cbn. destruct (reclaimb s (pa_block pa)); [reflexivity | rewrite Hps; reflexivity].
    + destruct (l2p_map (recover s) a p) as [pa'|] eqn:Hrec; [| reflexivity].
      cbn in Hrec. pose proof (recover_l2p_sound s a p pa' Hinv Hrec) as Hmap'.
      rewrite Hmap in Hmap'. injection Hmap' as <-.
      cbn. destruct (reclaimb s (pa_block pa)); [reflexivity | rewrite Hps; reflexivity].
    + assert (Hrec : l2p_map (recover s) a p = Some pa).
      { cbn. apply recover_l2p_complete with (d := d); assumption. }
      rewrite Hrec. cbn.
      assert (Hp : pa_page pa < pages_per_block)
        by (eapply in_geometry_valid_lt; eauto).
      rewrite (live_not_reclaimed s (pa_block pa)
                 (block_liveb_of_valid s (pa_block pa) (pa_page pa) d Hp Hps)).
      rewrite Hps. reflexivity.
  - destruct (l2p_map (recover s) a p) as [pa'|] eqn:Hrec; [| reflexivity].
    cbn in Hrec. pose proof (recover_l2p_sound s a p pa' Hinv Hrec) as Hmap'.
    congruence.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 6: block ownership after recovery
   ══════════════════════════════════════════════════════════════════════ *)

(* A live block's representative address exists and is mapped into the block:
   the first live page is stamped (Inv0 -> Inv3) and that stamp is honoured
   (Inv4). *)
Lemma block_lpa_mapped_owner :
  forall s a q pa,
    ftl_invariant s ->
    l2p_map s a q = Some pa ->
    recover_block_tenant s (pa_block pa) = addr_tenant s a /\
    recover_block_namespace s (pa_block pa) = addr_namespace s a.
Proof.
  intros s a q pa Hinv Hmap.
  pose proof Hinv as Hinv0.
  destruct Hinv as (_&_&HInv0&HInv1&_&HInv3&HInv4&_&_&_&_&_&_&_&_&_&_&_&_&_&HInv18&_&_&_&HInv22&_&_&_&_).
  (* The mapped physical page is live (Inv22 + Inv1). *)
  destruct (HInv22 a q pa Hmap) as [d0 Hval0].
  pose proof (HInv1 a q pa Hmap) as [Hb0 [Hp0 _]].
  assert (Hlive : block_liveb s (pa_block pa) = true)
    by (eapply block_liveb_of_valid; eauto).
  (* [block_lpa] finds some live page of the block. *)
  unfold recover_block_tenant, recover_block_namespace, block_lpa.
  destruct (find (live_pageb s (pa_block pa)) all_pages) as [p0|] eqn:Hf.
  2:{ exfalso. apply block_liveb_true in Hlive.
      destruct Hlive as [p [d [Hp Hps]]].
      pose proof (find_none _ _ Hf p (proj2 (in_all_pages p) Hp)) as Hfalse.
      unfold live_pageb in Hfalse. rewrite Hps in Hfalse. discriminate. }
  apply find_some in Hf. destruct Hf as [Hinp Hlp0].
  apply in_all_pages in Hinp.
  apply live_pageb_true in Hlp0. destruct Hlp0 as [d1 Hps1].
  (* That live page is mapped (Inv0) and stamped (Inv3). *)
  destruct (HInv0 (pa_block pa) p0 d1 Hps1) as [a0 [q0 Hmap0]].
  pose proof (HInv1 a0 q0 (mkPhysAddr (pa_block pa) p0) Hmap0) as [_ [_ [_ _]]].
  pose proof (HInv3 a0 q0 (mkPhysAddr (pa_block pa) p0) d1 Hmap0 Hps1) as Hstamp.
  cbn in Hstamp. rewrite Hstamp. cbn.
  (* Both a and a0 own [pa_block pa] (Inv18), so their owners agree. *)
  destruct (HInv18 a q pa Hmap) as [Hbt Hbn].
  destruct (HInv18 a0 q0 (mkPhysAddr (pa_block pa) p0) Hmap0) as [Hbt0 Hbn0].
  cbn in Hbt0, Hbn0.
  split.
  - rewrite <- Hbt0, Hbt. reflexivity.
  - rewrite <- Hbn0, Hbn. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 7: the invariant bundle survives crash and recovery
   ══════════════════════════════════════════════════════════════════════ *)

(* The mapping is page-indexed, so Inv1 bounds every physical page a mapping
   points at, and the reconstruction needs no [in_geometry] side condition. *)
Theorem recover_preserves_invariant :
  forall s,
    ftl_invariant s ->
    ftl_invariant (recover (crash s)).
Proof.
  intros s Hinv.
  rewrite recover_crash.
  pose proof Hinv as Hinv0.
  destruct Hinv as (W0&W1&I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15&I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26).
  apply make_ftl_invariant.
  - (* WF0 *) exact W0.
  - (* WF1 *) intros b p _ _. eexists. reflexivity.
  - (* Inv0: a live page's block is mapped *)
    intros b p d Hps.
    apply recover_page_state_valid in Hps. destruct Hps as [Hr Hps].
    destruct (I0 b p d Hps) as [a [q Hmap]].
    exists a, q. cbn.
    apply recover_l2p_complete with (d := d); [exact Hinv0 | exact Hmap | cbn; exact Hps].
  - (* Inv1: bounds *)
    intros a p pa Hmap. cbn in Hmap.
    apply I1. eapply recover_l2p_sound; eauto.
  - (* Inv2: injectivity *)
    intros a1 p1 a2 p2 pa Hm1 Hm2. cbn in Hm1, Hm2.
    apply recover_l2p_sound in Hm1; [| exact Hinv0].
    apply recover_l2p_sound in Hm2; [| exact Hinv0].
    exact (I2 a1 p1 a2 p2 pa Hm1 Hm2).
  - (* Inv3: forward stamp *)
    intros a p pa d Hmap Hps. cbn in Hmap, Hps.
    destruct (reclaimb s (pa_block pa)) eqn:Hr; [discriminate |].
    cbn. rewrite Hr.
    exact (I3 a p pa d (recover_l2p_sound s a p pa Hinv0 Hmap) Hps).
  - (* Inv4: reverse stamp *)
    intros a p b q d Hps Hlpa. cbn in Hps, Hlpa.
    destruct (reclaimb s b) eqn:Hr; [discriminate |].
    cbn.
    apply recover_l2p_complete with (d := d);
      [exact Hinv0 | exact (I4 a p b q d Hps Hlpa) | exact Hps].
  - (* Inv5: a mapped page's block is not free *)
    intros a p pa Hmap Hin. cbn in Hmap. cbn in Hin.
    apply in_recover_free_list in Hin. destruct Hin as [_ Hdead].
    pose proof (recover_l2p_live s a p pa Hmap) as Hlive.
    congruence.
  - (* Inv6: free blocks are erased *)
    intros b Hin p Hp. cbn in Hin.
    apply in_recover_free_list in Hin. destruct Hin as [Hb Hdead].
    cbn.
    destruct (reclaimb s b) eqn:Hr.
    + split; reflexivity.
    + apply block_erasedb_true; [| exact Hp].
      apply dead_not_reclaimed_erased; assumption.
  - (* Inv7: page owner agrees with address owner *)
    intros a p pa d t ns Hmap Hps Ht Hns. cbn in Hmap, Hps, Ht, Hns.
    destruct (reclaimb s (pa_block pa)) eqn:Hr; [discriminate |].
    cbn. rewrite Hr.
    exact (I7 a p pa d t ns (recover_l2p_sound s a p pa Hinv0 Hmap) Hps Ht Hns).
  - (* Inv8: free blocks are in range *)
    intros b Hin. cbn in Hin.
    apply in_recover_free_list in Hin. tauto.
  - (* Inv9: live pages carry a tag *)
    intros b p d Hps. cbn in Hps.
    destruct (reclaimb s b) eqn:Hr; [discriminate |].
    cbn. rewrite Hr.
    exact (I9 b p d Hps).
  - (* Inv10: every block is free, open, mapped, or garbage *)
    intros b Hb. cbn.
    destruct (block_liveb s b) eqn:Hlive.
    + right. right. left.
      apply block_liveb_true in Hlive. destruct Hlive as [p [d [Hp Hps]]].
      destruct (I0 b p d Hps) as [a [q Hmap]].
      exists a, q, (mkPhysAddr b p). split; [| reflexivity].
      apply recover_l2p_complete with (d := d); [exact Hinv0 | exact Hmap | cbn; exact Hps].
    + left. apply in_recover_free_list. auto.
  - (* Inv11: the free list has no duplicates *)
    cbn. apply NoDup_filter. apply seq_NoDup.
  - (* Inv12: a block with a metadata page is mapped or has a stale page *)
    intros b Hb [p Hrole]. cbn in Hrole.
    destruct (reclaimb s b) eqn:Hr; [discriminate |].
    destruct (I12 b Hb (ex_intro _ p Hrole)) as [[a [p' [pa [Hmap Hpb]]]] | [q Hstale]].
    + left.
      destruct (I22 a p' pa Hmap) as [d Hval].
      exists a, p', pa. split; [| exact Hpb].
      cbn. apply recover_l2p_complete with (d := d); assumption.
    + right. exists q. cbn. rewrite Hr. exact Hstale.
  - (* Inv13: valid pages are data pages *)
    intros b p d Hps. cbn in Hps.
    destruct (reclaimb s b) eqn:Hr; [discriminate |].
    cbn. rewrite Hr. exact (I13 b p d Hps).
  - (* Inv14: data pages are valid *)
    intros b p Hrole. cbn in Hrole.
    destruct (reclaimb s b) eqn:Hr; [discriminate |].
    cbn. rewrite Hr. exact (I14 b p Hrole).
  - (* Inv15: metadata pages are non-empty *)
    intros b p Hrole. cbn in Hrole.
    destruct (reclaimb s b) eqn:Hr; [discriminate |].
    cbn. rewrite Hr. exact (I15 b p Hrole).
  - (* Inv16: empty pages have no role *)
    intros b p Hps. cbn in Hps. cbn.
    destruct (reclaimb s b) eqn:Hr; [reflexivity |].
    exact (I16 b p Hps).
  - (* Inv17: free blocks carry no ownership *)
    intros b Hfree. cbn in Hfree.
    unfold recover_free_block in Hfree.
    apply andb_true_iff in Hfree. destruct Hfree as [_ Hdead].
    apply negb_true_iff in Hdead.
    cbn. unfold recover_block_tenant, recover_block_namespace.
    rewrite (block_lpa_dead s b Hdead). split; reflexivity.
  - (* Inv18: block ownership agrees with address ownership *)
    intros a p pa Hmap. cbn in Hmap. cbn.
    pose proof (recover_l2p_sound s a p pa Hinv0 Hmap) as Hmap0.
    exact (block_lpa_mapped_owner s a p pa Hinv0 Hmap0).
  - (* Inv19: region table entries are in range *)
    intros i r Hr. cbn in Hr. exact (I19 i r Hr).
  - (* Inv20: frontier well-formedness -- no block is open *)
    intros t ns b Hob. cbn in Hob. discriminate.
  - (* Inv21: erased above the frontier -- no block is open *)
    intros t ns b q Hob. cbn in Hob. discriminate.
  - (* Inv22: the forward map points only at live pages *)
    intros a p pa Hmap. cbn in Hmap.
    pose proof (recover_l2p_found s a p pa Hmap) as Hf.
    destruct Hf as [_ [_ [[d Hps] _]]].
    exists d. cbn.
    rewrite (recover_l2p_not_reclaimed s a p pa Hmap). exact Hps.
  - (* Inv23: block_open mirrors open_block -- nothing open *)
    intros b Hbo. cbn in Hbo. discriminate.
  - (* Inv24: the free bitmap and free list agree *)
    intros b.
    change (free_block (recover s) b) with (recover_free_block s b).
    change (free_block_list (recover s)) with (recover_free_list s).
    unfold recover_free_block.
    rewrite andb_true_iff, Nat.ltb_lt, negb_true_iff, in_recover_free_list.
    reflexivity.
  - (* Inv25: programmed below the frontier -- nothing open *)
    intros t ns b q Hob. cbn in Hob. discriminate.
  - (* Inv26: a mapped address carries vendor ownership *)
    intros a p pa Hmap. cbn in Hmap. cbn.
    exact (I26 a p pa (recover_l2p_sound s a p pa Hinv0 Hmap)).
Qed.

Theorem recover_preserves_in_geometry :
  forall s, in_geometry s -> in_geometry (recover (crash s)).
Proof.
  intros s Hgeo b p Hp. rewrite recover_crash. cbn.
  destruct (reclaimb s b).
  - auto.
  - exact (Hgeo b p Hp).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 8: allocation readiness survives
   ══════════════════════════════════════════════════════════════════════

   Page-granular allocation opens a fresh block only when the free list has a
   spare to keep in reserve for garbage collection ([open_fresh] needs
   [free_block_list = _ :: _ :: _]).  After recovery no block is open, so the
   first write must open a fresh one; [spare_block_available] is exactly that
   precondition. *)

Definition spare_block_available (s : FTLState) : Prop :=
  exists b1 b2 tl, free_block_list s = b1 :: b2 :: tl.

Lemma length_ge2_cons :
  forall (A : Type) (l : list A), 2 <= length l -> exists x y tl, l = x :: y :: tl.
Proof.
  intros A [| x [| y tl]] H; cbn in H; try lia.
  exists x, y, tl. reflexivity.
Qed.

Theorem recover_preserves_spare_block_available :
  forall s,
    ftl_invariant s ->
    spare_block_available s ->
    spare_block_available (recover (crash s)).
Proof.
  intros s Hinv [b1 [b2 [tl Hfl]]].
  pose proof Hinv as Hinv0.
  destruct Hinv as (_&_&_&_&_&_&_&_&HInv6&_&HInv8&_&_&HInv11&_).
  (* b1 and b2 are on the free list, hence in range, distinct, and dead. *)
  assert (Hin1 : In b1 (free_block_list s)) by (rewrite Hfl; left; reflexivity).
  assert (Hin2 : In b2 (free_block_list s)) by (rewrite Hfl; right; left; reflexivity).
  assert (Hdead : forall b, In b (free_block_list s) -> block_liveb s b = false).
  { intros b Hin. apply not_true_iff_false. intros Hlive.
    apply block_liveb_true in Hlive. destruct Hlive as [p [d [Hp Hps]]].
    destruct (HInv6 b Hin p Hp) as [Hempty _]. congruence. }
  assert (Hne : b1 <> b2).
  { unfold Inv11 in HInv11. rewrite Hfl in HInv11.
    inversion HInv11 as [| x l Hnotin Hnd]; subst.
    intros Hc. subst b2. apply Hnotin. left. reflexivity. }
  (* [b1;b2] is a duplicate-free sublist of the recovered free list. *)
  assert (Hincl : incl [b1; b2] (recover_free_list s)).
  { intros b Hb. cbn in Hb. apply in_recover_free_list.
    destruct Hb as [<- | [<- | []]].
    - split; [apply HInv8; exact Hin1 | apply Hdead; exact Hin1].
    - split; [apply HInv8; exact Hin2 | apply Hdead; exact Hin2]. }
  assert (Hnd2 : NoDup [b1; b2]).
  { constructor; [cbn; intros [Hc | []]; exact (Hne (eq_sym Hc)) | constructor; [cbn; auto | constructor]]. }
  pose proof (NoDup_incl_length Hnd2 Hincl) as Hlen.
  change (length [b1; b2]) with 2 in Hlen.
  rewrite recover_crash. unfold spare_block_available.
  change (free_block_list (recover s)) with (recover_free_list s).
  apply length_ge2_cons. exact Hlen.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 9: recovery depends on flash contents only, pointwise
   ══════════════════════════════════════════════════════════════════════

   [flash_determines_recovery] needs the two crashed states to be the same
   term.  The decomposition results deliver pointwise ([state_eqv]) agreement
   instead, so [CrashPoints] needs the pointwise version. *)

Definition flash_eqv (s1 s2 : FTLState) : Prop :=
  (forall b p, page_state s1 b p = page_state s2 b p) /\
  (forall b p, page_role s1 b p = page_role s2 b p) /\
  (forall a, addr_tenant s1 a = addr_tenant s2 a) /\
  (forall a, addr_namespace s1 a = addr_namespace s2 a) /\
  (forall b p, page_meta s1 b p = page_meta s2 b p) /\
  (forall i, region_table s1 i = region_table s2 i) /\
  (forall b, wear_count s1 b = wear_count s2 b) /\
  (forall k, key_table s1 k = key_table s2 k).

Lemma existsb_ext :
  forall (A : Type) (f g : A -> bool) (l : list A),
    (forall x, f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; cbn; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

Lemma forallb_ext :
  forall (A : Type) (f g : A -> bool) (l : list A),
    (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; cbn; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

Lemma find_ext :
  forall (A : Type) (f g : A -> bool) (l : list A),
    (forall x, f x = g x) -> find f l = find g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; cbn; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

Section FlashEqv.

Variables s1 s2 : FTLState.
Hypothesis Heqv : flash_eqv s1 s2.

Let Hps := proj1 Heqv.
Let Hrole := proj1 (proj2 Heqv).
Let Hat := proj1 (proj2 (proj2 Heqv)).
Let Han := proj1 (proj2 (proj2 (proj2 Heqv))).
Let Hmeta := proj1 (proj2 (proj2 (proj2 (proj2 Heqv)))).
Let Hwc := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Heqv)))))).

Lemma live_pageb_eqv : forall b p, live_pageb s1 b p = live_pageb s2 b p.
Proof. intros b p. unfold live_pageb. rewrite Hps. reflexivity. Qed.

Lemma block_liveb_eqv : forall b, block_liveb s1 b = block_liveb s2 b.
Proof. intros b. unfold block_liveb. apply existsb_ext. apply live_pageb_eqv. Qed.

Lemma stamped_phys_eqv :
  forall a q bp, stamped_phys s1 a q bp = stamped_phys s2 a q bp.
Proof. intros a q bp. unfold stamped_phys. rewrite Hps, Hmeta. reflexivity. Qed.

Lemma recover_l2p_eqv : forall a q, recover_l2p s1 a q = recover_l2p s2 a q.
Proof.
  intros a q. unfold recover_l2p.
  rewrite (find_ext _ _ _ _ (stamped_phys_eqv a q)). reflexivity.
Qed.

Lemma block_lpa_eqv : forall b, block_lpa s1 b = block_lpa s2 b.
Proof.
  intros b. unfold block_lpa.
  rewrite (find_ext _ _ _ _ (live_pageb_eqv b)).
  destruct (find (live_pageb s2 b) all_pages); [rewrite Hmeta |]; reflexivity.
Qed.

Lemma erased_pageb_eqv : forall b p, erased_pageb s1 b p = erased_pageb s2 b p.
Proof. intros b p. unfold erased_pageb. rewrite Hps, Hmeta. reflexivity. Qed.

Lemma block_erasedb_eqv : forall b, block_erasedb s1 b = block_erasedb s2 b.
Proof. intros b. unfold block_erasedb. apply forallb_ext. apply erased_pageb_eqv. Qed.

Lemma reclaimb_eqv : forall b, reclaimb s1 b = reclaimb s2 b.
Proof.
  intros b. unfold reclaimb. rewrite block_liveb_eqv, block_erasedb_eqv. reflexivity.
Qed.

Lemma recover_l2p_map_eqv :
  forall a q, l2p_map (recover s1) a q = l2p_map (recover s2) a q.
Proof. intros a q. cbn. apply recover_l2p_eqv. Qed.

Lemma recover_page_state_eqv :
  forall b p, page_state (recover s1) b p = page_state (recover s2) b p.
Proof.
  intros b p. cbn. rewrite reclaimb_eqv.
  destruct (reclaimb s2 b); [reflexivity | apply Hps].
Qed.

Lemma recover_page_role_eqv :
  forall b p, page_role (recover s1) b p = page_role (recover s2) b p.
Proof.
  intros b p. cbn. rewrite reclaimb_eqv.
  destruct (reclaimb s2 b); [reflexivity | apply Hrole].
Qed.

Lemma recover_page_meta_eqv :
  forall b p, page_meta (recover s1) b p = page_meta (recover s2) b p.
Proof.
  intros b p. cbn. rewrite reclaimb_eqv.
  destruct (reclaimb s2 b); [reflexivity | apply Hmeta].
Qed.

Lemma recover_block_tenant_eqv :
  forall b, block_tenant (recover s1) b = block_tenant (recover s2) b.
Proof.
  intros b. cbn. unfold recover_block_tenant. rewrite block_lpa_eqv.
  destruct (block_lpa s2 b); [apply Hat | reflexivity].
Qed.

Lemma recover_block_namespace_eqv :
  forall b, block_namespace (recover s1) b = block_namespace (recover s2) b.
Proof.
  intros b. cbn. unfold recover_block_namespace. rewrite block_lpa_eqv.
  destruct (block_lpa s2 b); [apply Han | reflexivity].
Qed.

Lemma recover_free_list_eqv :
  free_block_list (recover s1) = free_block_list (recover s2).
Proof.
  change (free_block_list (recover s1)) with (recover_free_list s1).
  change (free_block_list (recover s2)) with (recover_free_list s2).
  unfold recover_free_list. apply filter_ext.
  intros b. rewrite block_liveb_eqv. reflexivity.
Qed.

Lemma recover_free_block_eqv :
  forall b, free_block (recover s1) b = free_block (recover s2) b.
Proof.
  intros b.
  change (free_block (recover s1) b) with (recover_free_block s1 b).
  change (free_block (recover s2) b) with (recover_free_block s2 b).
  unfold recover_free_block. rewrite block_liveb_eqv. reflexivity.
Qed.

Lemma recover_wear_count_eqv :
  forall b, wear_count (recover s1) b = wear_count (recover s2) b.
Proof.
  intros b.
  change (wear_count (recover s1) b)
    with (if reclaimb s1 b then S (wear_count s1 b) else wear_count s1 b).
  change (wear_count (recover s2) b)
    with (if reclaimb s2 b then S (wear_count s2 b) else wear_count s2 b).
  rewrite reclaimb_eqv, Hwc. reflexivity.
Qed.

End FlashEqv.
