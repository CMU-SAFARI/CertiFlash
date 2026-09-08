(* DFTL.v: DFTL as a case study of the modular-verification interface,
   under page-granular translation.

   DFTL (Gupta, Kim and Urgaonkar, ASPLOS 2009) is a demand-paged FTL.  It
   keeps a working set of logical-to-physical entries in a small cached
   mapping table (CMT) held in controller DRAM, and the rest of the map on
   flash in *translation pages*.  A request whose entry is not cached must
   first fetch it from a translation page; a cached entry that has been
   updated is dirty and must be written back to its translation page before
   it can be evicted.

   The case study rests on the framework's translation granularity.
   Translation is [Addr -> Page -> option PhysAddr], so a CMT entry names a
   genuine logical page (a, p) and points at a genuine physical page, which
   is exactly the entry DFTL caches.

   Three commitments make the case study load-bearing rather than
   decorative:

   1. [user_to_model] is the first projection.  All 29 conjuncts of the
      framework invariant are stated over the real flash state, not over a
      DFTL-side copy of it.

   2. There is no shadow contents map.  [dftl_read] resolves a logical page
      through the CMT, or -- on a miss -- through the translation-page
      image, to a physical address, and then reads [page_state] of the real
      device.  Nothing is answered out of a private data plane.  This is
      what makes the isolation hypothesis non-trivial: to know what a read
      returns one must know both that the translation is honest and that
      the physical page still holds what was programmed into it.

   3. The auxiliary invariant [dftl_ok] is what keeps the two-level map
      honest: the CMT is bounded, every cached entry agrees with
      [l2p_map], every *clean* entry agrees with the translation-page
      image, and every uncached logical page is answered correctly by the
      translation-page image.  Together the last two say the composite
      [dftl_translate] *is* [l2p_map] -- which is the property a demand-paged
      FTL must maintain and which its eviction path can break.

   Nothing is admitted; no axiom, parameter, variable or hypothesis is
   introduced beyond the module type's own; no existing file is edited. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import core.CustomFTLInterface.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.
Require Import Invariants.Preservation.
Require Import Refinement.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 0 -- generic helpers
   ══════════════════════════════════════════════════════════════════════ *)

Lemma len_filter : forall (A : Type) (f : A -> bool) (l : list A),
  length (filter f l) <= length l.
Proof.
  intros A f l. induction l as [|x tl IH]; cbn; [lia|].
  destruct (f x); cbn; lia.
Qed.

Lemma len_map : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof. intros A B f l. induction l as [|x tl IH]; cbn; auto. Qed.

(* Equality of logical pages, in the [andb]-of-[Nat.eqb] shape the rest of
   the development uses for pointwise updates. *)
Definition lpa_eqb (a1 p1 a2 p2 : nat) : bool :=
  andb (Nat.eqb a1 a2) (Nat.eqb p1 p2).

Lemma lpa_eqb_refl : forall a p, lpa_eqb a p a p = true.
Proof. intros. unfold lpa_eqb. now rewrite !Nat.eqb_refl. Qed.

Lemma lpa_eqb_eq : forall a1 p1 a2 p2,
  lpa_eqb a1 p1 a2 p2 = true -> a1 = a2 /\ p1 = p2.
Proof.
  intros a1 p1 a2 p2 H. unfold lpa_eqb in H.
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2. split; assumption.
Qed.

Lemma lpa_eqb_neq : forall a1 p1 a2 p2,
  (a1 <> a2 \/ p1 <> p2) -> lpa_eqb a1 p1 a2 p2 = false.
Proof.
  intros a1 p1 a2 p2 H. unfold lpa_eqb.
  destruct (Nat.eqb a1 a2) eqn:E1; destruct (Nat.eqb p1 p2) eqn:E2; cbn; auto.
  apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2. destruct H; congruence.
Qed.

Definition phys_eqb (x y : PhysAddr) : bool :=
  lpa_eqb (pa_block x) (pa_page x) (pa_block y) (pa_page y).

Lemma phys_eqb_eq : forall x y, phys_eqb x y = true -> x = y.
Proof.
  intros [b1 p1] [b2 p2] H. unfold phys_eqb in H. cbn in H.
  apply lpa_eqb_eq in H as [H1 H2]. cbn in H1, H2. congruence.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the cached mapping table and the translation-page image
   ══════════════════════════════════════════════════════════════════════ *)

(* A CMT entry is exactly what DFTL caches: one logical page, the physical
   page it currently lives on, and a dirty bit recording whether the
   corresponding translation page has been brought up to date. *)
Record CMTEntry := mkCMTEntry {
  ce_addr  : Addr;
  ce_page  : Page;
  ce_ppa   : PhysAddr;
  ce_dirty : bool
}.

Definition CMT := list CMTEntry.

(* The CMT is a bounded DRAM structure; that bound is the whole reason DFTL
   exists.  Any positive capacity does; the proofs use only positivity. *)
Definition CMT_CAPACITY : nat := 8.

Lemma CMT_CAPACITY_pos : 0 < CMT_CAPACITY.
Proof. unfold CMT_CAPACITY. lia. Qed.

Fixpoint cmt_find (c : CMT) (a : Addr) (p : Page) : option CMTEntry :=
  match c with
  | [] => None
  | e :: tl => if lpa_eqb (ce_addr e) (ce_page e) a p then Some e else cmt_find tl a p
  end.

Definition cmt_lookup (c : CMT) (a : Addr) (p : Page) : option PhysAddr :=
  match cmt_find c a p with
  | Some e => Some (ce_ppa e)
  | None => None
  end.

Lemma cmt_find_in : forall c a p e, cmt_find c a p = Some e -> In e c.
Proof.
  induction c as [|x tl IH]; intros a p e H; cbn in H; [discriminate|].
  destruct (lpa_eqb (ce_addr x) (ce_page x) a p).
  - injection H as H. subst x. now left.
  - right. exact (IH a p e H).
Qed.

Lemma cmt_find_key : forall c a p e,
  cmt_find c a p = Some e -> ce_addr e = a /\ ce_page e = p.
Proof.
  induction c as [|x tl IH]; intros a p e H; cbn in H; [discriminate|].
  destruct (lpa_eqb (ce_addr x) (ce_page x) a p) eqn:E.
  - injection H as H. subst x. exact (lpa_eqb_eq _ _ _ _ E).
  - exact (IH a p e H).
Qed.

Lemma cmt_find_cons_hit : forall e tl,
  cmt_find (e :: tl) (ce_addr e) (ce_page e) = Some e.
Proof. intros e tl. cbn. now rewrite lpa_eqb_refl. Qed.

Lemma cmt_find_cons_miss : forall e tl a p,
  (ce_addr e <> a \/ ce_page e <> p) ->
  cmt_find (e :: tl) a p = cmt_find tl a p.
Proof. intros e tl a p H. cbn. now rewrite lpa_eqb_neq by exact H. Qed.

(* Dropping every entry for one logical page.  A write re-admits its page,
   so the stale copy must go; otherwise it would outlive the update and be
   found first after an eviction. *)
Definition cmt_remove (a : Addr) (p : Page) (c : CMT) : CMT :=
  filter (fun e => negb (lpa_eqb (ce_addr e) (ce_page e) a p)) c.

Lemma cmt_remove_in : forall a p c e, In e (cmt_remove a p c) -> In e c.
Proof.
  intros a p c e H. unfold cmt_remove in H. now apply filter_In in H as [H _].
Qed.

Lemma cmt_remove_key : forall a p c e,
  In e (cmt_remove a p c) -> (ce_addr e <> a \/ ce_page e <> p).
Proof.
  intros a p c e H. unfold cmt_remove in H. apply filter_In in H as [_ Hf].
  apply negb_true_iff in Hf.
  destruct (Nat.eq_dec (ce_addr e) a) as [Ha|Ha]; [|now left].
  destruct (Nat.eq_dec (ce_page e) p) as [Hp|Hp]; [|now right].
  rewrite Ha, Hp, lpa_eqb_refl in Hf. discriminate.
Qed.

Lemma cmt_remove_len : forall a p c, length (cmt_remove a p c) <= length c.
Proof. intros. apply len_filter. Qed.

Lemma cmt_find_remove_other : forall c a p a0 p0,
  (a0 <> a \/ p0 <> p) ->
  cmt_find (cmt_remove a p c) a0 p0 = cmt_find c a0 p0.
Proof.
  induction c as [|x tl IH]; intros a p a0 p0 Hne; [reflexivity|].
  cbn [cmt_remove filter].
  destruct (negb (lpa_eqb (ce_addr x) (ce_page x) a p)) eqn:Ex.
  - cbn [cmt_find]. destruct (lpa_eqb (ce_addr x) (ce_page x) a0 p0) eqn:E0.
    + reflexivity.
    + exact (IH a p a0 p0 Hne).
  - apply negb_false_iff in Ex. apply lpa_eqb_eq in Ex as [Ea Ep].
    cbn [cmt_find].
    rewrite lpa_eqb_neq by
      (rewrite Ea, Ep; destruct Hne as [H'|H']; [left|right]; congruence).
    exact (IH a p a0 p0 Hne).
Qed.

(* The image of the on-flash translation pages: the half of the map that is
   not resident in the CMT.  It is a map to *physical addresses*, not to
   data; every read still has to go to [page_state] afterwards. *)
Definition TransImage := Addr -> Page -> option PhysAddr.

Definition tp_set (g : TransImage) (a : Addr) (p : Page) (v : option PhysAddr)
  : TransImage :=
  fun x y => if lpa_eqb x y a p then v else g x y.

Lemma tp_set_here : forall g a p v, tp_set g a p v a p = v.
Proof. intros. unfold tp_set. now rewrite lpa_eqb_refl. Qed.

Lemma tp_set_other : forall g a p v x y,
  (x <> a \/ y <> p) -> tp_set g a p v x y = g x y.
Proof. intros. unfold tp_set. now rewrite lpa_eqb_neq by assumption. Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- the DFTL state, its translation path and its read path
   ══════════════════════════════════════════════════════════════════════ *)

Record DFTLState := mkDFTLState {
  ds_model  : FTLState;
  ds_cmt    : CMT;
  ds_tpages : TransImage
}.

(* Demand paging in one line: the CMT if it has the entry, the translation
   pages otherwise. *)
Definition dftl_translate (s : DFTLState) (a : Addr) (p : Page) : option PhysAddr :=
  match cmt_lookup (ds_cmt s) a p with
  | Some pa => Some pa
  | None => ds_tpages s a p
  end.

(* The read path.  Note what is *not* here: no contents map.  A read
   resolves to a physical page and then reads the device. *)
Definition dftl_read (s : DFTLState) (a : Addr) (p : Page) : option Data :=
  match dftl_translate s a p with
  | Some pa =>
      match page_state (ds_model s) (pa_block pa) (pa_page pa) with
      | PS_Valid d => Some d
      | _ => None
      end
  | None => None
  end.

(* ── the auxiliary invariant ──────────────────────────────────────── *)

Definition CMTBounded (s : DFTLState) : Prop :=
  length (ds_cmt s) <= CMT_CAPACITY.

Definition CMTSound (s : DFTLState) : Prop :=
  forall e, In e (ds_cmt s) ->
    l2p_map (ds_model s) (ce_addr e) (ce_page e) = Some (ce_ppa e).

Definition CMTCleanSynced (s : DFTLState) : Prop :=
  forall e, In e (ds_cmt s) -> ce_dirty e = false ->
    ds_tpages s (ce_addr e) (ce_page e) = Some (ce_ppa e).

Definition TransComplete (s : DFTLState) : Prop :=
  forall a p, cmt_lookup (ds_cmt s) a p = None ->
    ds_tpages s a p = l2p_map (ds_model s) a p.

Definition dftl_ok (s : DFTLState) : Prop :=
  CMTBounded s /\ CMTSound s /\ CMTCleanSynced s /\ TransComplete s.

(* The payoff of [dftl_ok]: the two-level map composes to the device's own
   forward map.  Everything else about DFTL's read path follows. *)
Lemma dftl_translate_exact : forall s a p,
  dftl_ok s -> dftl_translate s a p = l2p_map (ds_model s) a p.
Proof.
  intros s a p (_ & Hsound & _ & Hcomplete).
  unfold dftl_translate, cmt_lookup.
  destruct (cmt_find (ds_cmt s) a p) as [e|] eqn:Hf.
  - destruct (cmt_find_key _ _ _ _ Hf) as [Ha Hp].
    pose proof (Hsound e (cmt_find_in _ _ _ _ Hf)) as Hm.
    rewrite Ha, Hp in Hm. now rewrite Hm.
  - apply Hcomplete. unfold cmt_lookup. now rewrite Hf.
Qed.

Lemma dftl_read_is_read_page : forall s a p,
  dftl_ok s -> dftl_read s a p = read_page (ds_model s) a p.
Proof.
  intros s a p Hok. unfold dftl_read, read_page.
  now rewrite (dftl_translate_exact s a p Hok).
Qed.

(* Cached entries point at live pages.  This is *derived*, from soundness of
   the CMT together with the framework's Inv22, rather than assumed: an
   entry agreeing with [l2p_map] inherits the framework's guarantee that the
   forward map points only at programmed pages. *)
Lemma dftl_entries_live : forall s e,
  dftl_ok s -> ftl_invariant (ds_model s) -> In e (ds_cmt s) ->
  exists d, page_state (ds_model s)
              (pa_block (ce_ppa e)) (pa_page (ce_ppa e)) = PS_Valid d.
Proof.
  intros s e (_ & Hsound & _ & _) Hinv Hin.
  destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I24&_).
  exact (I24 _ _ _ (Hsound e Hin)).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- the four operations
   ══════════════════════════════════════════════════════════════════════ *)

(* Evicting the CMT's head entry.  A dirty entry has to be written back to
   its translation page first; a clean one is already there.  Getting this
   wrong is how a real demand-paged FTL loses a mapping, and it is exactly
   what [CMTCleanSynced] is there to rule out. *)
Definition cmt_writeback (e : CMTEntry) (g : TransImage) : TransImage :=
  if ce_dirty e
  then tp_set g (ce_addr e) (ce_page e) (Some (ce_ppa e))
  else g.

Definition dftl_evict (s : DFTLState) : DFTLState :=
  match ds_cmt s with
  | [] => s
  | e :: tl => mkDFTLState (ds_model s) tl (cmt_writeback e (ds_tpages s))
  end.

Definition cmt_evict_if_full (s : DFTLState) : DFTLState :=
  if Nat.leb CMT_CAPACITY (length (ds_cmt s)) then dftl_evict s else s.

(* Admitting a freshly written logical page: make room, drop any stale copy
   of the same entry, install the new one dirty (the translation page has
   not been rewritten). *)
Definition dftl_admit (s : DFTLState) (m : FTLState)
                      (a : Addr) (p : Page) (pa : PhysAddr) : DFTLState :=
  let s1 := cmt_evict_if_full s in
  mkDFTLState m (mkCMTEntry a p pa true :: cmt_remove a p (ds_cmt s1))
              (ds_tpages s1).

Definition dftl_write (s : DFTLState) (a : Addr) (p : Page) (d : Data)
  : DFTLState :=
  match step (ds_model s) (COpWrite a p d) with
  | Some m' =>
      match l2p_map m' a p with
      | Some pa => dftl_admit s m' a p pa
      | None => s
      end
  | None => s
  end.

(* Garbage collection moves live pages, so cached entries for the pages that
   moved are now stale.  DFTL rewrites the affected translation pages during
   reclaim; we model that by rebuilding the translation-page image from the
   post-GC map and keeping exactly those CMT entries that survived the move,
   now clean because the translation pages agree with them again. *)
Definition entry_agrees (m : FTLState) (e : CMTEntry) : bool :=
  match l2p_map m (ce_addr e) (ce_page e) with
  | Some pa => phys_eqb pa (ce_ppa e)
  | None => false
  end.

Definition cmt_resync (m : FTLState) (c : CMT) : CMT :=
  map (fun e => mkCMTEntry (ce_addr e) (ce_page e) (ce_ppa e) false)
      (filter (entry_agrees m) c).

Definition dftl_gc (s : DFTLState) : DFTLState :=
  match step (ds_model s) COpGC with
  | Some m' => mkDFTLState m' (cmt_resync m' (ds_cmt s)) (l2p_map m')
  | None => s
  end.

Definition dftl_wear_level (s : DFTLState) : DFTLState :=
  match step (ds_model s) COpWearLevel with
  | Some m' => mkDFTLState m' (cmt_resync m' (ds_cmt s)) (l2p_map m')
  | None => s
  end.

(* ── readiness ────────────────────────────────────────────────────── *)

(* The residual precondition a write needs beyond [admissible]: the device
   must actually be able to hand out a page.  [alloc_page] returns [None]
   when the frontier is exhausted and the free pool is down to its reserve,
   and no theorem can conjure a destination out of a full device. *)
Definition write_lands (m : FTLState) (a : Addr) (p : Page) : Prop :=
  match addr_tenant m a, addr_namespace m a with
  | Some t, Some ns =>
      alloc_page (match l2p_map m a p with
                  | Some old => invalidate_at m old
                  | None => m
                  end) t ns <> None
  | _, _ => False
  end.

Definition dftl_write_ready (s : DFTLState) (a : Addr) (p : Page) : Prop :=
  dftl_ok s /\ write_lands (ds_model s) a p.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- what a device-level write does to the map
   ══════════════════════════════════════════════════════════════════════ *)

Lemma alloc_page_same_fields : forall s t ns pa s1,
  alloc_page s t ns = Some (pa, s1) ->
  l2p_map s1 = l2p_map s /\ page_state s1 = page_state s.
Proof.
  intros s t ns pa s1 H. unfold alloc_page in H.
  destruct (open_block s t ns) as [b|] eqn:Hob.
  - destruct (Nat.ltb (write_ptr s t ns) pages_per_block).
    + injection H as Hpa Hs1. subst s1. split; reflexivity.
    + unfold open_fresh in H.
      destruct (free_block_list s) as [|x [|y r]]; try discriminate.
      injection H as Hpa Hs1. subst s1. split; reflexivity.
  - unfold open_fresh in H.
    destruct (free_block_list s) as [|x [|y r]]; try discriminate.
    injection H as Hpa Hs1. subst s1. split; reflexivity.
Qed.

(* A page-granular write touches the forward map at exactly one logical
   page: the mapping of every other logical page is left alone. *)
Lemma write_step_map : forall m a p d m',
  step m (COpWrite a p d) = Some m' ->
  (exists pa, l2p_map m' a p = Some pa /\
              page_state m' (pa_block pa) (pa_page pa) = PS_Valid d) /\
  (forall a0 p0, (a0 <> a \/ p0 <> p) -> l2p_map m' a0 p0 = l2p_map m a0 p0).
Proof.
  intros m a p d m' Hstep. cbn [step] in Hstep.
  match type of Hstep with
  | (if ?c then _ else _) = _ => destruct c eqn:Hguard
  end; [|discriminate].
  unfold exec_write in Hstep. cbv zeta in Hstep.
  destruct (addr_tenant m a) as [t|] eqn:Ht; [|discriminate].
  destruct (addr_namespace m a) as [ns|] eqn:Hns; [|discriminate].
  destruct (l2p_map m a p) as [old|] eqn:Hold.
  - destruct (alloc_page (invalidate_at m old) t ns) as [[pa s2]|] eqn:Halloc;
      [|discriminate].
    injection Hstep as Hs'. subst m'.
    destruct (alloc_page_same_fields _ _ _ _ _ Halloc) as [Hl2p _].
    split.
    + exists pa. split.
      * cbn [l2p_map program_page]. apply set_l2p_here.
      * cbn [page_state program_page]. apply set_ps_here.
    + intros a0 p0 Hne. cbn [l2p_map program_page].
      rewrite set_l2p_other by exact Hne. rewrite Hl2p. reflexivity.
  - destruct (alloc_page m t ns) as [[pa s2]|] eqn:Halloc; [|discriminate].
    injection Hstep as Hs'. subst m'.
    destruct (alloc_page_same_fields _ _ _ _ _ Halloc) as [Hl2p _].
    split.
    + exists pa. split.
      * cbn [l2p_map program_page]. apply set_l2p_here.
      * cbn [page_state program_page]. apply set_ps_here.
    + intros a0 p0 Hne. cbn [l2p_map program_page].
      rewrite set_l2p_other by exact Hne. rewrite Hl2p. reflexivity.
Qed.

(* Readiness is exactly what makes [step] succeed. *)
Lemma write_lands_step : forall m a p d,
  a < addr_space -> p < pages_per_block ->
  write_lands m a p ->
  exists m', step m (COpWrite a p d) = Some m'.
Proof.
  intros m a p d Ha Hp Hland. unfold write_lands in Hland.
  destruct (addr_tenant m a) as [t|] eqn:Ht; [|contradiction].
  destruct (addr_namespace m a) as [ns|] eqn:Hns; [|contradiction].
  cbn [step].
  rewrite (proj2 (Nat.ltb_lt a addr_space) Ha).
  rewrite (proj2 (Nat.ltb_lt p pages_per_block) Hp).
  rewrite Ht, Hns. cbn [andb].
  unfold exec_write. cbv zeta. rewrite Ht, Hns.
  destruct (l2p_map m a p) as [old|] eqn:Hold.
  - destruct (alloc_page (invalidate_at m old) t ns) as [[pa s2]|] eqn:Halloc.
    + eexists. reflexivity.
    + exfalso. congruence.
  - destruct (alloc_page m t ns) as [[pa s2]|] eqn:Halloc.
    + eexists. reflexivity.
    + exfalso. congruence.
Qed.

Lemma dftl_write_model : forall s a p d m',
  step (ds_model s) (COpWrite a p d) = Some m' ->
  ds_model (dftl_write s a p d) = m'.
Proof.
  intros s a p d m' Hstep.
  destruct (write_step_map _ _ _ _ _ Hstep) as [[pa [Hmap _]] _].
  unfold dftl_write. rewrite Hstep, Hmap. reflexivity.
Qed.

Lemma dftl_write_cmt : forall s a p d m' pa,
  step (ds_model s) (COpWrite a p d) = Some m' ->
  l2p_map m' a p = Some pa ->
  ds_cmt (dftl_write s a p d) =
    mkCMTEntry a p pa true :: cmt_remove a p (ds_cmt (cmt_evict_if_full s)).
Proof.
  intros s a p d m' pa Hstep Hmap.
  unfold dftl_write. rewrite Hstep, Hmap. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- [dftl_ok] is preserved by every operation
   ══════════════════════════════════════════════════════════════════════ *)

Lemma dftl_evict_model : forall s, ds_model (dftl_evict s) = ds_model s.
Proof. intros s. unfold dftl_evict. destruct (ds_cmt s); reflexivity. Qed.

Lemma cmt_evict_if_full_model : forall s,
  ds_model (cmt_evict_if_full s) = ds_model s.
Proof.
  intros s. unfold cmt_evict_if_full.
  destruct (Nat.leb CMT_CAPACITY (length (ds_cmt s)));
    [apply dftl_evict_model | reflexivity].
Qed.

Lemma dftl_ok_evict : forall s, dftl_ok s -> dftl_ok (dftl_evict s).
Proof.
  intros s (Hb & Hs & Hc & Ht). unfold dftl_evict.
  destruct (ds_cmt s) as [|e tl] eqn:Hcmt.
  - repeat split; assumption.
  - (* the head entry leaves the table, writing back if it was dirty *)
    assert (Hhead : In e (ds_cmt s)) by (rewrite Hcmt; now left).
    assert (Htail : forall x, In x tl -> In x (ds_cmt s))
      by (intros x Hx; rewrite Hcmt; now right).
    unfold dftl_ok, CMTBounded, CMTSound, CMTCleanSynced, TransComplete.
    cbn [ds_model ds_cmt ds_tpages].
    split; [unfold CMTBounded in Hb; rewrite Hcmt in Hb; cbn in Hb; lia|].
    split; [intros x Hx; exact (Hs x (Htail x Hx))|].
    (* the written-back value is the one the map already agrees with *)
    assert (Hval : ds_tpages s (ce_addr e) (ce_page e) = Some (ce_ppa e) \/
                   ce_dirty e = true).
    { destruct (ce_dirty e) eqn:Ed; [now right|]. left. exact (Hc e Hhead Ed). }
    assert (Hwb : forall x y, (x = ce_addr e /\ y = ce_page e) ->
                   cmt_writeback e (ds_tpages s) x y =
                     l2p_map (ds_model s) x y).
    { intros x y [Hx Hy]. subst x y. unfold cmt_writeback.
      destruct (ce_dirty e) eqn:Ed.
      - rewrite tp_set_here. symmetry. exact (Hs e Hhead).
      - destruct Hval as [Hv|Hv]; [|rewrite Hv in Ed; discriminate].
        rewrite Hv. symmetry. exact (Hs e Hhead). }
    assert (Hwb_other : forall x y, (x <> ce_addr e \/ y <> ce_page e) ->
                   cmt_writeback e (ds_tpages s) x y = ds_tpages s x y).
    { intros x y Hne. unfold cmt_writeback.
      destruct (ce_dirty e); [now rewrite tp_set_other by exact Hne|reflexivity]. }
    split.
    + intros x Hx Hclean.
      destruct (Nat.eq_dec (ce_addr x) (ce_addr e)) as [Ha|Ha];
        [destruct (Nat.eq_dec (ce_page x) (ce_page e)) as [Hp|Hp]|].
      * rewrite Hwb by (split; assumption). exact (Hs x (Htail x Hx)).
      * rewrite Hwb_other by (right; exact Hp). exact (Hc x (Htail x Hx) Hclean).
      * rewrite Hwb_other by (left; exact Ha). exact (Hc x (Htail x Hx) Hclean).
    + intros a0 p0 Hmiss.
      destruct (Nat.eq_dec a0 (ce_addr e)) as [Ha|Ha];
        [destruct (Nat.eq_dec p0 (ce_page e)) as [Hp|Hp]|].
      * rewrite Hwb by (split; assumption). reflexivity.
      * rewrite Hwb_other by (right; exact Hp). apply Ht.
        unfold cmt_lookup in Hmiss |- *. rewrite Hcmt.
        rewrite cmt_find_cons_miss by (right; congruence). exact Hmiss.
      * rewrite Hwb_other by (left; exact Ha). apply Ht.
        unfold cmt_lookup in Hmiss |- *. rewrite Hcmt.
        rewrite cmt_find_cons_miss by (left; congruence). exact Hmiss.
Qed.

Lemma dftl_ok_evict_if_full : forall s,
  dftl_ok s -> dftl_ok (cmt_evict_if_full s).
Proof.
  intros s Hok. unfold cmt_evict_if_full.
  destruct (Nat.leb CMT_CAPACITY (length (ds_cmt s)));
    [now apply dftl_ok_evict | exact Hok].
Qed.

Lemma evict_if_full_room : forall s,
  dftl_ok s -> length (ds_cmt (cmt_evict_if_full s)) < CMT_CAPACITY.
Proof.
  intros s (Hb & _ & _ & _). unfold CMTBounded in Hb.
  unfold cmt_evict_if_full.
  destruct (Nat.leb CMT_CAPACITY (length (ds_cmt s))) eqn:E.
  - apply Nat.leb_le in E.
    unfold dftl_evict. destruct (ds_cmt s) as [|e tl] eqn:Hcmt.
    + cbn in E. pose proof CMT_CAPACITY_pos. lia.
    + cbn [ds_cmt]. cbn [length] in Hb, E. lia.
  - apply Nat.leb_gt in E. exact E.
Qed.

Theorem dftl_ok_write : forall s a p d,
  dftl_ok s -> dftl_ok (dftl_write s a p d).
Proof.
  intros s a p d Hok.
  unfold dftl_write.
  destruct (step (ds_model s) (COpWrite a p d)) as [m'|] eqn:Hstep; [|exact Hok].
  destruct (l2p_map m' a p) as [pa|] eqn:Hmap; [|exact Hok].
  destruct (write_step_map _ _ _ _ _ Hstep) as [_ Hoff].
  set (s1 := cmt_evict_if_full s).
  pose proof (dftl_ok_evict_if_full s Hok) as Hok1.
  pose proof (evict_if_full_room s Hok) as Hroom.
  pose proof (cmt_evict_if_full_model s) as Hm1.
  destruct Hok1 as (Hb1 & Hs1 & Hc1 & Ht1).
  unfold dftl_admit, dftl_ok, CMTBounded, CMTSound, CMTCleanSynced, TransComplete.
  cbn [ds_model ds_cmt ds_tpages].
  split.
  { cbn [length]. pose proof (cmt_remove_len a p (ds_cmt s1)). unfold s1 in *. lia. }
  split.
  { intros e [He|He].
    - subst e. cbn [ce_addr ce_page ce_ppa]. exact Hmap.
    - pose proof (cmt_remove_key _ _ _ _ He) as Hne.
      rewrite (Hoff (ce_addr e) (ce_page e) Hne).
      rewrite <- Hm1. exact (Hs1 e (cmt_remove_in _ _ _ _ He)). }
  split.
  { intros e [He|He] Hclean.
    - subst e. cbn [ce_dirty] in Hclean. discriminate.
    - exact (Hc1 e (cmt_remove_in _ _ _ _ He) Hclean). }
  { intros a0 p0 Hmiss.
    unfold cmt_lookup in Hmiss.
    (* the freshly admitted entry is found first, so a miss means a
       different logical page *)
    assert (Hne : a0 <> a \/ p0 <> p).
    { destruct (Nat.eq_dec a0 a) as [Ha|Ha]; [|now left].
      destruct (Nat.eq_dec p0 p) as [Hp|Hp]; [|now right].
      subst a0 p0. cbn [cmt_find ce_addr ce_page] in Hmiss.
      rewrite lpa_eqb_refl in Hmiss. discriminate. }
    rewrite cmt_find_cons_miss in Hmiss by
      (cbn [ce_addr ce_page]; destruct Hne as [H'|H']; [left|right]; congruence).
    rewrite cmt_find_remove_other in Hmiss by exact Hne.
    rewrite (Hoff a0 p0 Hne), <- Hm1.
    apply Ht1. unfold cmt_lookup. now rewrite Hmiss. }
Qed.

(* The reclaim path re-establishes [dftl_ok] outright: the translation pages
   are rewritten from the post-reclaim map, and only entries that still
   agree with it are kept. *)
Lemma dftl_ok_resync : forall m c,
  dftl_ok (mkDFTLState m (cmt_resync m c) (l2p_map m)) \/ length c > CMT_CAPACITY.
Proof.
  intros m c.
  destruct (Nat.leb (length c) CMT_CAPACITY) eqn:Hlen;
    [apply Nat.leb_le in Hlen | apply Nat.leb_gt in Hlen; now right].
  left.
  assert (Hsound : forall e, In e (cmt_resync m c) ->
            l2p_map m (ce_addr e) (ce_page e) = Some (ce_ppa e)).
  { intros e He. unfold cmt_resync in He.
    apply in_map_iff in He as [e0 [Heq He0]]. subst e.
    apply filter_In in He0 as [_ Hag]. unfold entry_agrees in Hag.
    cbn [ce_addr ce_page ce_ppa].
    destruct (l2p_map m (ce_addr e0) (ce_page e0)) as [pa0|] eqn:Hm0;
      [|discriminate].
    apply phys_eqb_eq in Hag. now subst pa0. }
  unfold dftl_ok, CMTBounded, CMTSound, CMTCleanSynced, TransComplete.
  cbn [ds_model ds_cmt ds_tpages].
  split.
  { unfold cmt_resync. rewrite len_map.
    pose proof (len_filter _ (entry_agrees m) c). lia. }
  split; [exact Hsound|].
  split; [intros e He _; exact (Hsound e He)|].
  intros a0 p0 _. reflexivity.
Qed.

Theorem dftl_ok_gc : forall s, dftl_ok s -> dftl_ok (dftl_gc s).
Proof.
  intros s Hok. unfold dftl_gc.
  destruct (step (ds_model s) COpGC) as [m'|] eqn:Hstep; [|exact Hok].
  destruct (dftl_ok_resync m' (ds_cmt s)) as [H|H]; [exact H|].
  exfalso. destruct Hok as (Hb & _). unfold CMTBounded in Hb. lia.
Qed.

Theorem dftl_ok_wear_level : forall s, dftl_ok s -> dftl_ok (dftl_wear_level s).
Proof.
  intros s Hok. unfold dftl_wear_level.
  destruct (step (ds_model s) COpWearLevel) as [m'|] eqn:Hstep; [|exact Hok].
  destruct (dftl_ok_resync m' (ds_cmt s)) as [H|H]; [exact H|].
  exfalso. destruct Hok as (Hb & _). unfold CMTBounded in Hb. lia.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 6 -- the interface instance
   ══════════════════════════════════════════════════════════════════════ *)

Module DFTLConcreteFTL <: CUSTOM_FTL.

  Definition user_state := DFTLState.

  Definition user_read       := dftl_read.
  Definition user_write      := dftl_write.
  Definition user_gc         := dftl_gc.
  Definition user_wear_level := dftl_wear_level.

  (* The first projection.  Every clause the framework states is stated
     about the device, not about a DFTL-side copy of it. *)
  Definition user_to_model (s : DFTLState) : FTLState := ds_model s.

  Definition user_write_ready := dftl_write_ready.

  Definition admissible (s : user_state) (a : Addr) (p : Page) : Prop :=
    a < addr_space /\ p < pages_per_block /\
    (exists t, addr_tenant (user_to_model s) a = Some t) /\
    (exists ns, addr_namespace (user_to_model s) a = Some ns).

  Definition security_contract (m : FTLState) : Prop := ftl_invariant m.

  (* ════════════════════════════════════════════════════════════════
     Hyp1-Hyp3: preservation, delegated through the projection.

     Because [user_to_model] is the first projection, each of these is:
     compute what the DFTL operation did to [ds_model], observe that it is
     either untouched or the result of the corresponding [step], and hand
     the goal to the framework's own preservation theorem.
     ════════════════════════════════════════════════════════════════ *)

  Lemma invariants_preserved_on_write :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_write s a p d)).
  Proof.
    intros s a p d _ _ Hinv.
    unfold security_contract, user_to_model, user_write in *.
    unfold dftl_write.
    destruct (step (ds_model s) (COpWrite a p d)) as [m'|] eqn:Hstep;
      [|exact Hinv].
    destruct (l2p_map m' a p) as [pa|] eqn:Hmap; [|exact Hinv].
    cbn [ds_model dftl_admit].
    exact (step_preserves_invariant_closed _ _ _ Hinv Hstep).
  Qed.

  Lemma invariants_preserved_on_gc :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_gc s)).
  Proof.
    intros s Hinv.
    unfold security_contract, user_to_model, user_gc in *.
    unfold dftl_gc.
    destruct (step (ds_model s) COpGC) as [m'|] eqn:Hstep; [|exact Hinv].
    cbn [ds_model].
    exact (step_preserves_invariant_closed _ _ _ Hinv Hstep).
  Qed.

  Lemma invariants_preserved_on_wear_level :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_wear_level s)).
  Proof.
    intros s Hinv.
    unfold security_contract, user_to_model, user_wear_level in *.
    unfold dftl_wear_level.
    destruct (step (ds_model s) COpWearLevel) as [m'|] eqn:Hstep; [|exact Hinv].
    cbn [ds_model].
    exact (step_preserves_invariant_closed _ _ _ Hinv Hstep).
  Qed.

  (* ════════════════════════════════════════════════════════════════
     Hyp4: read-after-write.

     The read goes CMT -> physical address -> [page_state].  The entry the
     write just admitted is at the head of the CMT, so the lookup hits it;
     what it points at is the page the device programmed, and that page
     holds [d].  Nothing is read out of a DFTL-side data structure.
     ════════════════════════════════════════════════════════════════ *)

  Lemma read_after_write_correctness :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      user_read (user_write s a p d) a p = Some d.
  Proof.
    intros s a p d (Ha & Hp & _ & _) (Hok & Hland) Hinv.
    unfold user_read, user_write, dftl_read.
    destruct (write_lands_step (ds_model s) a p d Ha Hp Hland) as [m' Hstep].
    destruct (write_step_map _ _ _ _ _ Hstep) as [[pa [Hmap Hps]] _].
    rewrite (dftl_write_model s a p d m' Hstep).
    unfold dftl_translate, cmt_lookup.
    rewrite (dftl_write_cmt s a p d m' pa Hstep Hmap).
    cbn [cmt_find ce_addr ce_page]. rewrite lpa_eqb_refl. cbn [ce_ppa].
    rewrite Hps. reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════
     Hyp5: isolation.

     The read at (a1, p1) after a second, unrelated write must still see
     d1.  Two independent things have to hold, and with no shadow contents
     map both are real obligations:

       (i)  the device still backs (a1, p1) with d1 -- proved by carrying
            the framework's refinement relation [CR] across the two
            [step]s, with the abstract device [abs_write] recording the
            two writes;
       (ii) DFTL still *finds* (a1, p1) -- proved from [dftl_ok], which
            survives both writes, and which says the composite
            CMT-then-translation-pages lookup is [l2p_map].  This is where
            the eviction the second write may have performed has to have
            written its dirty entry back.
     ════════════════════════════════════════════════════════════════ *)

  Lemma isolation_property :
    forall s a1 p1 a2 p2 d1 d2,
      (a1 <> a2 \/ p1 <> p2) ->
      admissible s a1 p1 ->
      admissible (user_write s a1 p1 d1) a2 p2 ->
      user_write_ready s a1 p1 ->
      user_write_ready (user_write s a1 p1 d1) a2 p2 ->
      security_contract (user_to_model s) ->
      user_read (user_write (user_write s a1 p1 d1) a2 p2 d2) a1 p1 = Some d1.
  Proof.
    intros s a1 p1 a2 p2 d1 d2 Hne (Ha1 & Hp1 & _ & _) (Ha2 & Hp2 & _ & _)
           (Hok0 & Hland0) (Hok1 & Hland1) Hinv.
    unfold security_contract, user_to_model in Hinv.
    unfold user_read, user_write in *.
    (* the first write *)
    destruct (write_lands_step (ds_model s) a1 p1 d1 Ha1 Hp1 Hland0)
      as [m1 Hstep1].
    pose proof (dftl_write_model s a1 p1 d1 m1 Hstep1) as Hmod1.
    assert (Hinv1 : ftl_invariant m1)
      by exact (step_preserves_invariant_closed _ _ _ Hinv Hstep1).
    (* the second write *)
    rewrite Hmod1 in Hland1.
    destruct (write_lands_step m1 a2 p2 d2 Ha2 Hp2 Hland1) as [m2 Hstep2].
    assert (Hstep2' : step (ds_model (dftl_write s a1 p1 d1))
                        (COpWrite a2 p2 d2) = Some m2)
      by (rewrite Hmod1; exact Hstep2).
    pose proof (dftl_write_model (dftl_write s a1 p1 d1) a2 p2 d2 m2 Hstep2')
      as Hmod2.
    (* (i) the device still backs (a1, p1) with d1 *)
    assert (HCR0 : CR empty_abs (ds_model s))
      by (intros a0 p0 d0 H; discriminate H).
    pose proof (@write_preserves_CR pages_per_block_pos
                  empty_abs (ds_model s) m1 a1 p1 d1 Hinv HCR0 Hstep1) as HCR1.
    pose proof (@write_preserves_CR pages_per_block_pos
                  (abs_write empty_abs a1 p1 d1) m1 m2 a2 p2 d2
                  Hinv1 HCR1 Hstep2) as HCR2.
    assert (Hcell : abs_write (abs_write empty_abs a1 p1 d1) a2 p2 d2 a1 p1
                    = Some d1).
    { rewrite abs_write_other by exact Hne. apply abs_write_here. }
    destruct (HCR2 a1 p1 d1 Hcell) as [pa1 [Hmap1 Hps1]].
    (* (ii) DFTL still finds (a1, p1) *)
    assert (Hok2 : dftl_ok (dftl_write (dftl_write s a1 p1 d1) a2 p2 d2))
      by (apply dftl_ok_write; exact Hok1).
    rewrite (dftl_read_is_read_page _ a1 p1 Hok2).
    rewrite Hmod2. unfold read_page. rewrite Hmap1, Hps1. reflexivity.
  Qed.

End DFTLConcreteFTL.

(* The certificate, instantiated. *)
Module DFTLCertificate := Validator DFTLConcreteFTL.

Check DFTLCertificate.custom_ftl_security_suite.
Print Assumptions DFTLCertificate.custom_ftl_security_suite.
Print Assumptions DFTLConcreteFTL.isolation_property.
