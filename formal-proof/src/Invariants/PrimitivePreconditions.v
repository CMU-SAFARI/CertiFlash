(* PrimitivePreconditions.v: per-call-site precondition bundles for the
   page-granular model.

   This is the bridge from proof to silicon.  [Preservation.v] says that
   every *operation* preserves the 27-clause invariant.  A controller does
   not issue operations; it issues flash commands, and a checker sitting on
   the wire between controller and chip sees only those.  This file states,
   for each of the three ONFI commands, a bundle of conditions that
     (i)  is decidable -- a boolean function of the state and the command's
          arguments, so a combinational in-device checker can evaluate it,
          and
     (ii) is sufficient to carry the invariant across that one command.

   ── WHAT THE BUNDLES ARE NOT ────────────────────────────────────────────

   A bundle cannot be "the invariant holds here".  The invariant is an
   operation-level statement and is *transiently false* inside an expansion.
   The write's expansion is

     BarrierEnter a
     [ Invalidate old ]        (only when the logical page was mapped)
     MapAddr a p pa
     Program pa d (a,p)
     BarrierExit a

   and at the instruction boundary between [MapAddr] and [Program] the
   forward map already points at [pa] while [pa] is still [PS_Empty].  That
   is exactly the negation of

     Inv22 : forall a p pa, l2p_map s a p = Some pa ->
               exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d.

   Inv22 is broken deliberately: [decompose_realizable] in
   [BoundaryAgreement.v] proves that every [PrimProgram] an expansion emits
   targets an *erased* page, which is the one law NAND imposes.  So at every
   program call site, realizability and Inv22 cannot both hold.
   [program_call_sites_break_Inv22] in Part 5 states exactly that.

   Exactly four clauses go transiently false inside an expansion:

     Inv22  (the map points only at live pages)
            false in *both* the write and the reclaim expansion, at every
            [MapAddr]/[Remap] -> [Program] boundary: the map already names
            the destination, which is still erased.  Repaired by the
            [Program] that immediately follows.
     Inv0   (a live page is pointed at by the map)
            false through a reclaim: [program_page] stamps the destination
            but never touches the source, so a page already relocated stays
            [PS_Valid] in the victim while nothing maps to it any more.
            Repaired by the [Erase] that ends the reclaim.
     Inv4   (a live page's OOB stamp is honoured by the map)
            false through a reclaim for the same reason, repaired by the
            same [Erase].
     Inv10  (every block is free, open, mapped, or garbage)
            relativised at the victim through a reclaim; repaired by the
            [Erase], which puts the victim back on the free pool.

   The other twenty-five hold at every instruction boundary of every
   expansion.  Inv0, Inv4 and Inv10 are relativised and the rest carried
   outright by [INVX] in [GCPreservation.v], which is the mid-reclaim
   witness; Inv12 is not even carried there because it is derivable from
   Inv13 and Inv15 ([Inv12_from_Inv13_Inv15]); and this file's item 3 is the
   mid-write witness.  In particular Inv3, Inv7, Inv9, Inv13 and Inv14 do
   *not* break at the [MapAddr] -> [Program] boundary even though they talk
   about the destination: each of them is guarded by the destination being
   [PS_Valid], and at that boundary it is [PS_Empty], so each holds vacuously
   there and acquires real content again when the [Program] lands.

   ── WHAT THE BUNDLES ARE ────────────────────────────────────────────────

   [pre_read]     nothing.  [apply_primitive] leaves the state untouched, so
                  the theorem is [fun _ H _ => H].  Reads are stated rather
                  than invented conditions for.

   [pre_program pa d lpa]  six conjuncts:
                  the destination is in geometry (2), the forward map already
                  points at it and the stamp about to be written names the
                  same logical page (1), everything strictly above the
                  destination inside its block is still erased and unstamped
                  (1), everything strictly below it has been programmed (1),
                  and if this program opens a fresh block for its owner, the
                  block it retires has been written to (1).

   [pre_erase b]  four conjuncts: the block is in range, its free bit is
                  clear, it is not open for any owner, and no forward mapping
                  lands in it.

   ── THE RELATION BETWEEN ITEM 2 AND ITEM 3 ──────────────────────────────

   [pre_sound_program] assumes the full invariant.  Under that assumption
   Inv22 and the bundle's mapping conjunct together force the destination to
   be *already live*: the theorem's reachable instances are in-place
   re-programs, not fresh writes.  That is not a defect of the bundle, it is
   the content of the crux: a state that satisfies both the whole invariant
   and "the map already points at the destination" cannot have an erased
   destination.  The two halves of the file therefore live on opposite sides
   of the transient window --

     item 2  s satisfies all 29 conjuncts ==> Program preserves all 29
     item 3  s satisfies all 29 conjuncts ==> every instruction of the
             expansion of any operation is issued under its bundle

   -- and neither is weakened to make the other go through.  Item 3 never
   assumes the invariant at an instruction boundary; it carries the mid-write
   facts explicitly (see [alloc_install_pre_program]) and reuses [INVX] for
   the mid-reclaim ones.

   No admitted lemmas, no [admit], and no axiom, parameter, variable or
   hypothesis is introduced. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import core.Primitives.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.
Require Import Invariants.GCPreservation.
Require Import core.BoundaryAgreement.
(* required but not imported: its transitive imports would shadow the
   pointwise update lemmas used above with identically-stated copies *)
Require Invariants.Preservation.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 0 -- decidable scaffolding.

   Every conjunct below is a boolean expression over registers a checker can
   read: a comparison, a table lookup, or a scan bounded by the geometry.
   ══════════════════════════════════════════════════════════════════════ *)

Definition ps_emptyb (st : PageState) : bool :=
  match st with PS_Empty => true | _ => false end.

Lemma ps_emptyb_true : forall st, ps_emptyb st = true <-> st = PS_Empty.
Proof.
  intros st; destruct st; cbn.
  - split; intros _; reflexivity.
  - split; intros H; discriminate H.
  - split; intros H; discriminate H.
Qed.

Lemma ps_emptyb_false : forall st, ps_emptyb st = false <-> st <> PS_Empty.
Proof.
  intros st; destruct st; cbn.
  - split; [intros H; discriminate H | intros H; exfalso; apply H; reflexivity].
  - split; [intros _ H; discriminate H | intros _; reflexivity].
  - split; [intros _ H; discriminate H | intros _; reflexivity].
Qed.

(* The OOB area of an erased page: no owner, no tag, no reverse-map stamp. *)
Definition meta_emptyb (m : PageMeta) : bool :=
  Nat.eqb (page_owner_tenant m) 0 &&
  Nat.eqb (page_owner_namespace m) 0 &&
  (match page_tag m with None => true | Some _ => false end) &&
  (match page_lpa m with None => true | Some _ => false end).

Lemma meta_emptyb_correct : forall m, meta_emptyb m = true <-> m = empty_page_meta.
Proof.
  intros m; split.
  - destruct m as [ot on tg lp]. unfold meta_emptyb; cbn. intros H.
    apply andb_true_iff in H; destruct H as [H Hlp].
    apply andb_true_iff in H; destruct H as [H Htg].
    apply andb_true_iff in H; destruct H as [Hot Hon].
    apply Nat.eqb_eq in Hot; apply Nat.eqb_eq in Hon; subst.
    destruct tg; [discriminate Htg|]. destruct lp; [discriminate Hlp|].
    reflexivity.
  - intros H; subst m; reflexivity.
Qed.

Definition pa_eqb (x y : PhysAddr) : bool :=
  Nat.eqb (pa_block x) (pa_block y) && Nat.eqb (pa_page x) (pa_page y).

Lemma pa_eqb_correct : forall x y, pa_eqb x y = true <-> x = y.
Proof.
  intros [b1 q1] [b2 q2]. unfold pa_eqb; cbn. split.
  - intros H. apply andb_true_iff in H; destruct H as [H1 H2].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
  - intros H. injection H as H1 H2; subst. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Definition opa_eqb (x y : option PhysAddr) : bool :=
  match x, y with
  | Some u, Some v => pa_eqb u v
  | None, None => true
  | _, _ => false
  end.

(* Scans bounded by the geometry: a checker unrolls these. *)
Definition forall_pages (f : Page -> bool) : bool :=
  forallb f (seq 0 pages_per_block).

Lemma forall_pages_correct :
  forall f, forall_pages f = true <-> (forall q, q < pages_per_block -> f q = true).
Proof.
  intros f. unfold forall_pages. rewrite forallb_forall. split.
  - intros H q Hq. apply H. apply in_seq. lia.
  - intros H x Hx. apply in_seq in Hx. apply H. lia.
Qed.

Definition forall_addrs (f : Addr -> bool) : bool :=
  forallb f (seq 0 addr_space).

Lemma forall_addrs_correct :
  forall f, forall_addrs f = true <-> (forall a, a < addr_space -> f a = true).
Proof.
  intros f. unfold forall_addrs. rewrite forallb_forall. split.
  - intros H a Ha. apply H. apply in_seq. lia.
  - intros H x Hx. apply in_seq in Hx. apply H. lia.
Qed.

Lemma forall_pages_elim :
  forall f q, forall_pages f = true -> q < pages_per_block -> f q = true.
Proof. intros f q H Hq. exact (proj1 (forall_pages_correct f) H q Hq). Qed.

Lemma forall_pages_intro :
  forall f, (forall q, q < pages_per_block -> f q = true) -> forall_pages f = true.
Proof. intros f H. exact (proj2 (forall_pages_correct f) H). Qed.

Lemma forall_addrs_elim :
  forall f a, forall_addrs f = true -> a < addr_space -> f a = true.
Proof. intros f a H Ha. exact (proj1 (forall_addrs_correct f) H a Ha). Qed.

Lemma forall_addrs_intro :
  forall f, (forall a, a < addr_space -> f a = true) -> forall_addrs f = true.
Proof. intros f H. exact (proj2 (forall_addrs_correct f) H). Qed.

Lemma remove_block_once_absent :
  forall b L, ~ In b L -> remove_block_once b L = L.
Proof.
  intros b L. induction L as [|x tl IH]; intros H; cbn; [reflexivity|].
  destruct (Nat.eqb x b) eqn:E.
  - apply Nat.eqb_eq in E; subst x. exfalso. apply H. left. reflexivity.
  - rewrite IH; [reflexivity|]. intros Hc. apply H. right. exact Hc.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the three bundles.
   ══════════════════════════════════════════════════════════════════════ *)

(* The owner [apply_primitive] attributes a program to.  It reads the
   destination block's ownership, which the [MapAddr]/[Remap] that precedes
   every emitted [Program] has just installed from [addr_tenant]. *)
Definition prog_tenant (s : FTLState) (b : Block) : TenantId :=
  match block_tenant s b with Some t => t | None => 0 end.

Definition prog_ns (s : FTLState) (b : Block) : NamespaceId :=
  match block_namespace s b with Some n => n | None => 0 end.

(* The block this program retires, if any: programming the first page of a
   block that is not yet open claims it as its owner's new frontier and
   closes whatever block that owner had open before. *)
Definition retiring (s : FTLState) (b : Block) : option Block :=
  if is_open s b then None
  else open_block s (prog_tenant s b) (prog_ns s b).

(* ── PrimRead ─────────────────────────────────────────────────────────
   [apply_primitive s (PrimRead pa) = s].  A read mutates nothing, so there
   is nothing for a checker to gate on and nothing for a proof to assume.
   The bundle is [True] rather than an invented in-range test: a read of an
   out-of-range page is a different problem (it is an addressing fault, not
   an invariant break) and stating it here would be a fiction. *)
Definition pre_read (_ : FTLState) (_ : PhysAddr) : Prop := True.

Definition pre_readb (_ : FTLState) (_ : PhysAddr) : bool := true.

Lemma pre_readb_correct :
  forall s pa, pre_readb s pa = true <-> pre_read s pa.
Proof. intros s pa. split; intros _; [exact I | reflexivity]. Qed.

(* ── PrimProgram ──────────────────────────────────────────────────────
   Six checker signals.  PP3 is the one that makes the bundle a per-call-site
   condition rather than a restatement of the invariant: it demands only that
   the forward map already names the destination, which the preceding
   [MapAddr] guarantees, and says nothing about the destination's contents --
   which are, at that moment, erased. *)
Definition pre_program (s : FTLState) (pa : PhysAddr) (d : Data)
                       (lpa : option LPA) : Prop :=
  (* PP1  dest_block_in_range *)
  pa_block pa < total_blocks /\
  (* PP2  dest_page_in_range *)
  pa_page pa < pages_per_block /\
  (* PP3  map_installed: the stamp about to be burned into the OOB names a
     logical page, and the forward map already points that logical page here *)
  (match lpa with
   | Some (a, p) => l2p_map s a p = Some pa
   | None => False
   end) /\
  (* PP4  above_frontier_erased: NAND programs in increasing offset order,
     so everything above the destination in its block must still be erased *)
  (forall q, S (pa_page pa) <= q -> q < pages_per_block ->
     page_state s (pa_block pa) q = PS_Empty /\
     page_meta s (pa_block pa) q = empty_page_meta) /\
  (* PP5  below_frontier_written *)
  (forall q, q < pa_page pa -> page_state s (pa_block pa) q <> PS_Empty) /\
  (* PP6  retired_block_written: opening a fresh block closes the owner's
     outgoing one, which must not be left erased and unaccounted for *)
  (match retiring s (pa_block pa) with
   | Some ob => page_state s ob 0 <> PS_Empty
   | None => True
   end).

Definition pre_programb (s : FTLState) (pa : PhysAddr) (d : Data)
                        (lpa : option LPA) : bool :=
  Nat.ltb (pa_block pa) total_blocks &&
  Nat.ltb (pa_page pa) pages_per_block &&
  (match lpa with
   | Some (a, p) => opa_eqb (l2p_map s a p) (Some pa)
   | None => false
   end) &&
  forall_pages (fun q => if Nat.leb (S (pa_page pa)) q
                         then ps_emptyb (page_state s (pa_block pa) q) &&
                              meta_emptyb (page_meta s (pa_block pa) q)
                         else true) &&
  forall_pages (fun q => if Nat.ltb q (pa_page pa)
                         then negb (ps_emptyb (page_state s (pa_block pa) q))
                         else true) &&
  (match retiring s (pa_block pa) with
   | Some ob => negb (ps_emptyb (page_state s ob 0))
   | None => true
   end).

Lemma pre_programb_correct :
  forall s pa d lpa, pre_programb s pa d lpa = true <-> pre_program s pa d lpa.
Proof.
  intros s pa d lpa. unfold pre_programb, pre_program. split.
  - intros H.
    apply andb_true_iff in H; destruct H as [H H6].
    apply andb_true_iff in H; destruct H as [H H5].
    apply andb_true_iff in H; destruct H as [H H4].
    apply andb_true_iff in H; destruct H as [H H3].
    apply andb_true_iff in H; destruct H as [H1 H2].
    apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
    split; [exact H1|]. split; [exact H2|].
    split.
    { destruct lpa as [[a0 p0]|]; [|discriminate H3].
      destruct (l2p_map s a0 p0) as [pa'|] eqn:E; [|discriminate H3].
      cbn in H3. apply (proj1 (pa_eqb_correct pa' pa)) in H3. rewrite H3. reflexivity. }
    split.
    { intros q Hge Hq.
      pose proof (forall_pages_elim _ q H4 Hq) as Hq4. cbn beta in Hq4.
      rewrite (proj2 (Nat.leb_le _ _) Hge) in Hq4.
      apply andb_true_iff in Hq4; destruct Hq4 as [Ha Hb].
      split; [exact (proj1 (ps_emptyb_true _) Ha)
             | exact (proj1 (meta_emptyb_correct _) Hb)]. }
    split.
    { intros q Hq.
      assert (Hqb : q < pages_per_block) by lia.
      pose proof (forall_pages_elim _ q H5 Hqb) as Hq5. cbn beta in Hq5.
      rewrite (proj2 (Nat.ltb_lt _ _) Hq) in Hq5.
      apply negb_true_iff in Hq5. exact (proj1 (ps_emptyb_false _) Hq5). }
    { destruct (retiring s (pa_block pa)) as [ob|]; [|exact I].
      apply negb_true_iff in H6. exact (proj1 (ps_emptyb_false _) H6). }
  - intros (H1 & H2 & H3 & H4 & H5 & H6).
    apply andb_true_iff; split; [apply andb_true_iff; split;
      [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split | ] | ] | ] | ].
    + apply Nat.ltb_lt; exact H1.
    + apply Nat.ltb_lt; exact H2.
    + destruct lpa as [[a0 p0]|]; [|contradiction H3].
      rewrite H3. cbn. exact (proj2 (pa_eqb_correct pa pa) eq_refl).
    + apply forall_pages_intro. intros q Hq. cbn beta.
      destruct (Nat.leb (S (pa_page pa)) q) eqn:E; [|reflexivity].
      apply Nat.leb_le in E. destruct (H4 q E Hq) as [Ha Hb].
      apply andb_true_iff; split.
      * exact (proj2 (ps_emptyb_true _) Ha).
      * exact (proj2 (meta_emptyb_correct _) Hb).
    + apply forall_pages_intro. intros q Hq. cbn beta.
      destruct (Nat.ltb q (pa_page pa)) eqn:E; [|reflexivity].
      apply Nat.ltb_lt in E. apply negb_true_iff.
      exact (proj2 (ps_emptyb_false _) (H5 q E)).
    + destruct (retiring s (pa_block pa)) as [ob|]; [|reflexivity].
      apply negb_true_iff. apply ps_emptyb_false. exact H6.
Qed.

(* ── PrimErase ────────────────────────────────────────────────────────
   The target must be in range, must be mapped to by nothing, and must be
   absent from the free list.  The frontier adds a fourth condition: a block
   that is open for some owner must not be erased, because the erase would
   put it back on the free list while a write pointer still names it.  The
   "absent from the free list" test is the free *bit*, which is what a
   checker actually has (Inv24 makes the two views agree). *)
Definition pre_erase (s : FTLState) (b : Block) : Prop :=
  (* PE1  blk_in_range *)
  b < total_blocks /\
  (* PE2  blk_not_free *)
  free_block s b = false /\
  (* PE3  blk_not_open *)
  block_open s b = false /\
  (* PE4  no_live_map *)
  (forall a p pa, a < addr_space -> p < pages_per_block ->
     l2p_map s a p = Some pa -> pa_block pa <> b).

Definition pre_eraseb (s : FTLState) (b : Block) : bool :=
  Nat.ltb b total_blocks &&
  negb (free_block s b) &&
  negb (block_open s b) &&
  forall_addrs (fun a => forall_pages (fun p =>
     match l2p_map s a p with
     | Some pa => negb (Nat.eqb (pa_block pa) b)
     | None => true
     end)).

Lemma pre_eraseb_correct :
  forall s b, pre_eraseb s b = true <-> pre_erase s b.
Proof.
  intros s b. unfold pre_eraseb, pre_erase. split.
  - intros H.
    apply andb_true_iff in H; destruct H as [H H4].
    apply andb_true_iff in H; destruct H as [H H3].
    apply andb_true_iff in H; destruct H as [H1 H2].
    apply Nat.ltb_lt in H1. apply negb_true_iff in H2. apply negb_true_iff in H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros a p pa Ha Hp Hm.
    pose proof (forall_addrs_elim _ a H4 Ha) as Ha4. cbn beta in Ha4.
    pose proof (forall_pages_elim _ p Ha4 Hp) as Hp4. cbn beta in Hp4.
    rewrite Hm in Hp4. apply negb_true_iff in Hp4. apply Nat.eqb_neq in Hp4.
    exact Hp4.
  - intros (H1 & H2 & H3 & H4).
    apply andb_true_iff; split; [apply andb_true_iff; split;
      [apply andb_true_iff; split | ] | ].
    + apply Nat.ltb_lt; exact H1.
    + apply negb_true_iff; exact H2.
    + apply negb_true_iff; exact H3.
    + apply forall_addrs_intro. intros a Ha. cbn beta.
      apply forall_pages_intro. intros p Hp. cbn beta.
      destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
      apply negb_true_iff. apply Nat.eqb_neq. exact (H4 a p pa Ha Hp E).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- transporting the invariant along extensional equality.

   [apply_primitive s (PrimErase b)] and [erase_block s b] differ only in the
   wear counter's expression, which no clause mentions; the two are
   extensionally equal but not convertible, so the transport is stated once
   and used for the erase bundle.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma state_eqv_invariant :
  forall s1 s2, state_eqv s1 s2 -> ftl_invariant s1 -> ftl_invariant s2.
Proof.
  intros s1 s2 E Hinv.
  destruct E as [El Eps Epr Eat Ean Ebt Ebn Epm Ert Efbl Efb Ewc Ekt Eob Ewp Ebo].
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  apply make_ftl_invariant.
  - exact I0.
  - intros b p _ _. eexists. reflexivity.
  - intros b p d Hv. rewrite <- Eps in Hv.
    destruct (I2 b p d Hv) as [a [q Hm]]. exists a, q. rewrite <- El. exact Hm.
  - intros a p pa Hm. rewrite <- El in Hm. exact (I3 a p pa Hm).
  - intros a1 p1 a2 p2 pa H1 H2. rewrite <- El in H1, H2. exact (I4 a1 p1 a2 p2 pa H1 H2).
  - intros a p pa d Hm Hv. rewrite <- El in Hm. rewrite <- Eps in Hv.
    rewrite <- Epm. exact (I5 a p pa d Hm Hv).
  - intros a p b q d Hv Hl. rewrite <- Eps in Hv. rewrite <- Epm in Hl.
    rewrite <- El. exact (I6 a p b q d Hv Hl).
  - intros a p pa Hm. rewrite <- El in Hm. rewrite <- Efbl. exact (I7 a p pa Hm).
  - intros b Hin p Hp. rewrite <- Efbl in Hin. rewrite <- Eps, <- Epm.
    exact (I8 b Hin p Hp).
  - intros a p pa d t ns Hm Hv Ha Hn. rewrite <- El in Hm. rewrite <- Eps in Hv.
    rewrite <- Eat in Ha. rewrite <- Ean in Hn. rewrite <- Epm.
    exact (I9 a p pa d t ns Hm Hv Ha Hn).
  - intros b Hin. rewrite <- Efbl in Hin. exact (I10 b Hin).
  - intros b p d Hv. rewrite <- Eps in Hv. rewrite <- Epm. exact (I11 b p d Hv).
  - intros b Hb. rewrite <- Efbl.
    destruct (I12 b Hb) as [H|[[t [ns H]]|[[a [p [pa [Hm Hbk]]]]|[q Hq]]]].
    + left; exact H.
    + right; left. exists t, ns. rewrite <- Eob. exact H.
    + right; right; left. exists a, p, pa. rewrite <- El. split; assumption.
    + right; right; right. exists q. rewrite <- Eps. exact Hq.
  - unfold Inv11. rewrite <- Efbl. exact I13.
  - intros b Hb [p Hr]. rewrite <- Epr in Hr.
    destruct (I14 b Hb (ex_intro _ p Hr)) as [[a [p' [pa [Hm Hbk]]]]|[q Hq]].
    + left. exists a, p', pa. rewrite <- El. split; assumption.
    + right. exists q. rewrite <- Eps. exact Hq.
  - intros b p d Hv. rewrite <- Eps in Hv. rewrite <- Epr. exact (I15 b p d Hv).
  - intros b p Hr. rewrite <- Epr in Hr. destruct (I16 b p Hr) as [d Hd].
    exists d. rewrite <- Eps. exact Hd.
  - intros b p Hr. rewrite <- Epr in Hr. rewrite <- Eps. exact (I17 b p Hr).
  - intros b p Hv. rewrite <- Eps in Hv. rewrite <- Epr. exact (I18 b p Hv).
  - intros b Hf. rewrite <- Efb in Hf. rewrite <- Ebt, <- Ebn. exact (I19 b Hf).
  - intros a p pa Hm. rewrite <- El in Hm. rewrite <- Ebt, <- Ebn, <- Eat, <- Ean.
    exact (I20 a p pa Hm).
  - intros i r Hr. rewrite <- Ert in Hr. exact (I21 i r Hr).
  - intros t ns b Hob. rewrite <- Eob in Hob.
    destruct (I22 t ns b Hob) as (A1&A2&A3&A4&A5&A6&A7&A8).
    split; [exact A1|].
    split; [rewrite <- Efbl; exact A2|].
    split; [rewrite <- Efb; exact A3|].
    split; [rewrite <- Ebo; exact A4|].
    split; [rewrite <- Ewp; exact A5|].
    split; [rewrite <- Ebt; exact A6|].
    split; [rewrite <- Ebn; exact A7|].
    intros t' ns' Hob'. rewrite <- Eob in Hob'. exact (A8 t' ns' Hob').
  - intros t ns b q Hob Hle Hq. rewrite <- Eob in Hob. rewrite <- Ewp in Hle.
    rewrite <- Eps, <- Epm. exact (I23 t ns b q Hob Hle Hq).
  - intros a p pa Hm. rewrite <- El in Hm. destruct (I24 a p pa Hm) as [d Hd].
    exists d. rewrite <- Eps. exact Hd.
  - intros b Hbo. rewrite <- Ebo in Hbo. destruct (I25 b Hbo) as [t [ns H]].
    exists t, ns. rewrite <- Eob. exact H.
  - intros b. rewrite <- Efb, <- Efbl. exact (I26 b).
  - intros t ns b q Hob Hlt. rewrite <- Eob in Hob. rewrite <- Ewp in Hlt.
    rewrite <- Eps. exact (I27 t ns b q Hob Hlt).
  - intros a p pa Hm. rewrite <- El in Hm. rewrite <- Eat, <- Ean.
    exact (I28 a p pa Hm).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- precondition soundness, one theorem per primitive.
   ══════════════════════════════════════════════════════════════════════ *)

(* ── PrimRead: the state is not touched, so there is nothing to prove ── *)

Theorem pre_sound_read :
  forall s pa,
    ftl_invariant s ->
    pre_read s pa ->
    ftl_invariant (apply_primitive s (PrimRead pa)).
Proof. intros s pa Hinv _. exact Hinv. Qed.

(* ── PrimErase ────────────────────────────────────────────────────────
   [GCPreservation] already proves that erasing a block that satisfies the
   relativised bundle [INVX vb []] restores the full invariant.  The erase
   bundle is exactly the extra content of [INVX vb []] over the invariant, so
   the theorem is that observation plus the transport of Part 2. *)

Lemma pre_erase_INVX :
  forall s b, ftl_invariant s -> pre_erase s b -> INVX b [] s.
Proof.
  intros s b Hinv Hpre.
  destruct Hpre as (Hblt & Hfb & Hbo & Hnomap).
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  apply mkINVX; try assumption.
  - intros b0 p0 d0 Hv _. exact (I2 b0 p0 d0 Hv).
  - intros a0 p0 b0 q0 d0 Hv Hl _. exact (I6 a0 p0 b0 q0 d0 Hv Hl).
  - intros b0 Hb0 _. exact (I12 b0 Hb0).
  - constructor.
  - intros a0 p0 pa0 Hm Hblk. exfalso.
    destruct (I3 a0 p0 pa0 Hm) as (_ & _ & Ha & Hp).
    exact (Hnomap a0 p0 pa0 Ha Hp Hm Hblk).
Qed.

Theorem pre_sound_erase :
  forall s b,
    ftl_invariant s ->
    pre_erase s b ->
    ftl_invariant (apply_primitive s (PrimErase b)).
Proof.
  intros s b Hinv Hpre.
  apply (state_eqv_invariant (erase_block s b)).
  - apply erase_eqv.
  - apply erase_ok. exact (pre_erase_INVX s b Hinv Hpre).
Qed.

(* ── PrimProgram ──────────────────────────────────────────────────────
   The interesting theorem.  Note what the hypotheses jointly say: PP3 puts a
   forward mapping onto the destination, and Inv22 then makes the destination
   already live.  Programming is therefore, in the presence of the whole
   invariant, an in-place refresh; the fresh-page case lives on the other side
   of the transient window and is the subject of Part 4.  The proof below
   never needs that distinction -- it works from PP3, PP4, PP5, PP6 and the
   invariant, and each of the four is exactly one checker signal. *)

Ltac prjg :=
  cbn [l2p_map page_state page_role addr_tenant addr_namespace
       block_tenant block_namespace page_meta region_table
       free_block_list free_block wear_count key_table
       open_block write_ptr block_open pa_block pa_page].

Ltac prjh H :=
  cbn [l2p_map page_state page_role addr_tenant addr_namespace
       block_tenant block_namespace page_meta region_table
       free_block_list free_block wear_count key_table
       open_block write_ptr block_open pa_block pa_page] in H.

(* The honest program stamps the tag [Some d] derived from the data, which is
   what every expansion emits.  Its invariant preservation is the special case
   of the unified [PrimProgram] at [tag = Some d]; [pre_sound_program_raw] in
   [MicroOpPreconditions.v] then transports it to an arbitrary real tag. *)
Theorem pre_sound_program :
  forall s pa d lpa,
    ftl_invariant s ->
    pre_program s pa d lpa ->
    ftl_invariant (apply_primitive s (PrimProgram pa d (Some d) lpa)).
Proof.
  intros s pa d lpa Hinv Hpre.
  destruct pa as [b q].
  unfold pre_program in Hpre. cbn [pa_block pa_page] in Hpre.
  destruct Hpre as (Hblt & Hqlt & Hmap & Habove & Hbelow & Hretire).
  destruct lpa as [[a0 p0]|]; [|contradiction Hmap].
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  (* the destination block's ownership: installed by the preceding MapAddr,
     and the frontier this program consumes is that owner's *)
  destruct (I28 a0 p0 _ Hmap) as [[t0 Hat] [n0 Han]].
  pose proof (I20 a0 p0 _ Hmap) as Hown0. cbn [pa_block] in Hown0.
  destruct Hown0 as [Hbt Hbn]. rewrite Hat in Hbt. rewrite Han in Hbn.
  (* under the full invariant the destination is already live: Inv22 *)
  destruct (I24 a0 p0 _ Hmap) as [d0 Hd0]. cbn [pa_block pa_page] in Hd0.
  pose proof (I5 a0 p0 _ d0 Hmap Hd0) as Hlpa0. cbn [pa_block pa_page] in Hlpa0.
  pose proof (I7 a0 p0 _ Hmap) as Hnotfree. cbn [pa_block] in Hnotfree.
  pose proof (I15 b q d0 Hd0) as Hrole0.
  assert (Hfb0 : free_block s b = false).
  { destruct (free_block s b) eqn:E; [|reflexivity].
    exfalso. apply Hnotfree. exact (proj1 (I26 b) E). }
  (* one block is open for at most one owner, and the destination's owner is
     the only owner that can have it open *)
  assert (Hopen_uniq : forall t' ns' b', open_block s t' ns' = Some b' -> b' = b ->
                         t' = t0 /\ ns' = n0).
  { intros t' ns' b' Hob Eb. subst b'.
    destruct (I22 t' ns' b Hob) as (_&_&_&_&_&Hbt'&Hbn'&_).
    split.
    - destruct Hbt' as [Hc|Hc]; rewrite Hbt in Hc;
        [discriminate Hc | injection Hc as Hc; symmetry; exact Hc].
    - destruct Hbn' as [Hc|Hc]; rewrite Hbn in Hc;
        [discriminate Hc | injection Hc as Hc; symmetry; exact Hc]. }
  assert (Hopen_b : block_open s b = true -> open_block s t0 n0 = Some b).
  { intros H. destruct (I25 b H) as [t1 [ns1 Hob1]].
    destruct (Hopen_uniq t1 ns1 b Hob1 eq_refl) as [F1 F2]. subst t1 ns1. exact Hob1. }
  assert (Hretiring : retiring s b = if is_open s b then None else open_block s t0 n0).
  { unfold retiring, prog_tenant, prog_ns. rewrite Hbt, Hbn. reflexivity. }
  assert (Hret : forall ob, open_block s t0 n0 = Some ob -> ob <> b ->
                   page_state s ob 0 <> PS_Empty).
  { intros ob Hob Hne. rewrite Hretiring in Hretire.
    destruct (is_open s b) eqn:Eo.
    - exfalso. rewrite (Hopen_b Eo) in Hob. injection Hob as Hob.
      apply Hne. symmetry. exact Hob.
    - rewrite Hob in Hretire. exact Hretire. }
  (* the resulting state, field by field *)
  rewrite (prim_program_shape s (mkPhysAddr b q) d (Some d) (@Some LPA (a0, p0)) t0 n0 Hbt Hbn).
  cbn [pa_block pa_page].
  (* the free pool does not move: PP3 puts a mapping into b, so Inv5 keeps b
     off the free list and the removal is a no-op *)
  assert (Hfbl : (if is_open s b then free_block_list s
                  else remove_block_once b (free_block_list s)) = free_block_list s).
  { destruct (is_open s b); [reflexivity | apply remove_block_once_absent; exact Hnotfree]. }
  assert (Hfbx : forall x, (if is_open s b then free_block s
                            else set_free_block (free_block s) b false) x
                           = free_block s x).
  { intros x. destruct (is_open s b); [reflexivity|].
    destruct (Nat.eq_dec x b) as [E|E].
    - subst x. rewrite set_fb_here. symmetry. exact Hfb0.
    - apply set_fb_other. exact E. }
  assert (Hbo_b : (if is_open s b then block_open s
                   else set_block_open (close_open s t0 n0) b true) b = true).
  { destruct (is_open s b) eqn:Eo; [exact Eo | apply set_bo_here]. }
  assert (Hbo_true : forall x,
            (if is_open s b then block_open s
             else set_block_open (close_open s t0 n0) b true) x = true ->
            x = b \/ (block_open s x = true /\ open_block s t0 n0 <> Some x)).
  { intros x Hx. destruct (Nat.eq_dec x b) as [E|E]; [left; exact E|].
    right. destruct (is_open s b) eqn:Eo.
    - split; [exact Hx|]. intros Hc. rewrite (Hopen_b Eo) in Hc.
      injection Hc as Hc. apply E. symmetry. exact Hc.
    - rewrite (set_bo_other _ _ _ _ E) in Hx.
      unfold close_open in Hx. destruct (open_block s t0 n0) as [ob|] eqn:Hob.
      + destruct (Nat.eq_dec x ob) as [E2|E2].
        * subst x. rewrite set_bo_here in Hx. discriminate Hx.
        * rewrite (set_bo_other _ _ _ _ E2) in Hx. split; [exact Hx|].
          intros Hc. apply E2. symmetry.
          first [ injection Hc as Hc; exact Hc
                | rewrite Hob in Hc; injection Hc as Hc; exact Hc ].
      + split; [exact Hx|]. intros Hc.
        first [ discriminate Hc | rewrite Hob in Hc; discriminate Hc ]. }
  assert (Hbo_keep : forall x, x <> b -> block_open s x = true ->
            open_block s t0 n0 <> Some x ->
            (if is_open s b then block_open s
             else set_block_open (close_open s t0 n0) b true) x = true).
  { intros x Hne Hx Hnot. destruct (is_open s b) eqn:Eo; [exact Hx|].
    rewrite (set_bo_other _ _ _ _ Hne). unfold close_open.
    destruct (open_block s t0 n0) as [ob|] eqn:Hob; [|exact Hx].
    assert (Hne2 : x <> ob).
    { intros Hc. subst x. apply Hnot. first [ reflexivity | exact Hob ]. }
    rewrite (set_bo_other _ _ _ _ Hne2). exact Hx. }
  (* the role table does not move either: the destination was already RData *)
  assert (Hpr : forall x y,
            set_page_role (page_role s) b q (Some RData) x y = page_role s x y).
  { intros x y. destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    - subst x y. rewrite set_pr_here. symmetry. exact Hrole0.
    - apply set_pr_other. exact E. }
  assert (Hps_inv : forall x y, page_state s x y = PS_Invalid ->
            set_page_state (page_state s) b q (PS_Valid d) x y = PS_Invalid).
  { intros x y H. destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    - subst x y. rewrite Hd0 in H. discriminate H.
    - rewrite (set_ps_other _ _ _ _ _ _ E). exact H. }
  assert (Hps_emp : forall x y,
            set_page_state (page_state s) b q (PS_Valid d) x y = PS_Empty ->
            page_state s x y = PS_Empty).
  { intros x y H. destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    - subst x y. rewrite set_ps_here in H. discriminate H.
    - rewrite (set_ps_other _ _ _ _ _ _ E) in H. exact H. }
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros bx px _ _. eexists. reflexivity.
  - (* Inv0 *) intros bx qx dx Hv. prjh Hv. prjg.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. exists a0, p0. exact Hmap.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv. exact (I2 bx qx dx Hv).
  - (* Inv1 *) intros ax px pax Hm. prjh Hm. exact (I3 ax px pax Hm).
  - (* Inv2 *) intros a1 p1 a2 p2 pax H1 H2. prjh H1. prjh H2.
    exact (I4 a1 p1 a2 p2 pax H1 H2).
  - (* Inv3 *) intros ax px pax dx Hm Hv. prjh Hm. prjh Hv. prjg.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + assert (Hpa : pax = mkPhysAddr b q).
      { rewrite <- E1, <- E2. symmetry. apply physaddr_eta. }
      subst pax. cbn [pa_block pa_page]. rewrite set_pm_here. cbn [page_lpa].
      destruct (I4 ax px a0 p0 _ Hm Hmap) as [Ea Ep]. subst ax px. reflexivity.
    + rewrite (set_pm_other _ _ _ _ _ _ E).
      rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      exact (I5 ax px pax dx Hm Hv).
  - (* Inv4 *) intros ax px bx qx dx Hv Hl. prjh Hv. prjh Hl. prjg.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pm_here in Hl. cbn [page_lpa] in Hl.
      injection Hl as Ea Ep. subst ax px. exact Hmap.
    + rewrite (set_pm_other _ _ _ _ _ _ E) in Hl.
      rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      exact (I6 ax px bx qx dx Hv Hl).
  - (* Inv5 *) intros ax px pax Hm. prjh Hm. prjg. rewrite Hfbl.
    exact (I7 ax px pax Hm).
  - (* Inv6 *) intros bx Hin px Hp. prjh Hin. prjg. rewrite Hfbl in Hin.
    assert (Hne : bx <> b) by (intros Hc; subst bx; exact (Hnotfree Hin)).
    rewrite (set_ps_other _ _ _ _ _ _ (or_introl Hne)).
    rewrite (set_pm_other _ _ _ _ _ _ (or_introl Hne)).
    exact (I8 bx Hin px Hp).
  - (* Inv7 *) intros ax px pax dx tx nx Hm Hv Hatx Hanx.
    prjh Hm. prjh Hv. prjh Hatx. prjh Hanx. prjg.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + assert (Hpa : pax = mkPhysAddr b q).
      { rewrite <- E1, <- E2. symmetry. apply physaddr_eta. }
      subst pax. cbn [pa_block pa_page]. rewrite set_pm_here.
      cbn [page_owner_tenant page_owner_namespace].
      destruct (I4 ax px a0 p0 _ Hm Hmap) as [Ea Ep]. subst ax px.
      rewrite Hat in Hatx. rewrite Han in Hanx.
      injection Hatx as Hatx. injection Hanx as Hanx.
      split; [exact Hatx | exact Hanx].
    + rewrite (set_pm_other _ _ _ _ _ _ E).
      rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      exact (I9 ax px pax dx tx nx Hm Hv Hatx Hanx).
  - (* Inv8 *) intros bx Hin. prjh Hin. rewrite Hfbl in Hin. exact (I10 bx Hin).
  - (* Inv9 *) intros bx qx dx Hv. prjh Hv. prjg.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pm_here. cbn [page_tag]. exists d. reflexivity.
    + rewrite (set_pm_other _ _ _ _ _ _ E).
      rewrite (set_ps_other _ _ _ _ _ _ E) in Hv. exact (I11 bx qx dx Hv).
  - (* Inv10 *) intros bx Hbx. prjg. rewrite Hfbl.
    destruct (Nat.eq_dec bx b) as [Eb|Eb].
    + subst bx. right; left. exists t0, n0. apply set_ob_here.
    + destruct (I12 bx Hbx)
        as [H|[[t' [ns' H]]|[[ax [px [pax [Hm Hbk]]]]|[qx Hqx]]]].
      * left; exact H.
      * destruct (nat_pair_dec t' t0 ns' n0) as [[F1 F2]|F].
        -- subst t' ns'.
           pose proof (Hret bx H Eb) as Hnb.
           destruct (page_state s bx 0) as [| |dd] eqn:Eps.
           ++ exfalso. apply Hnb. reflexivity.
           ++ right; right; right. exists 0. apply Hps_inv. exact Eps.
           ++ right; right; left.
              destruct (I2 bx 0 dd Eps) as [aa [qq Hmm]].
              exists aa, qq, (mkPhysAddr bx 0). split; [exact Hmm | reflexivity].
        -- right; left. exists t', ns'. rewrite (set_ob_other _ _ _ _ _ _ F).
           exact H.
      * right; right; left. exists ax, px, pax. split; assumption.
      * right; right; right. exists qx. apply Hps_inv. exact Hqx.
  - (* Inv11 *) unfold Inv11. prjg. rewrite Hfbl. exact I13.
  - (* Inv12 *) intros bx Hbx [px Hr]. prjh Hr. prjg. rewrite Hpr in Hr.
    destruct (I14 bx Hbx (ex_intro _ px Hr))
      as [[ax [px' [pax [Hm Hbk]]]]|[qx Hqx]].
    + left. exists ax, px', pax. split; assumption.
    + right. exists qx. apply Hps_inv. exact Hqx.
  - (* Inv13 *) intros bx qx dx Hv. prjh Hv. prjg. rewrite Hpr.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. exact Hrole0.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv. exact (I15 bx qx dx Hv).
  - (* Inv14 *) intros bx qx Hr. prjh Hr. prjg. rewrite Hpr in Hr.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. exists d. apply set_ps_here.
    + destruct (I16 bx qx Hr) as [dx Hdx]. exists dx.
      rewrite (set_ps_other _ _ _ _ _ _ E). exact Hdx.
  - (* Inv15 *) intros bx qx Hr. prjh Hr. prjg. rewrite Hpr in Hr.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_ps_here. intros Hc; discriminate Hc.
    + rewrite (set_ps_other _ _ _ _ _ _ E). exact (I17 bx qx Hr).
  - (* Inv16 *) intros bx qx Hv. prjh Hv. prjg. rewrite Hpr.
    exact (I18 bx qx (Hps_emp bx qx Hv)).
  - (* Inv17 *) intros bx Hf. prjh Hf. prjg. rewrite Hfbx in Hf.
    exact (I19 bx Hf).
  - (* Inv18 *) intros ax px pax Hm. prjh Hm. prjg. exact (I20 ax px pax Hm).
  - (* Inv19 *) intros i r Hr. prjh Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t' ns' bx Hob. prjh Hob. prjg.
    destruct (nat_pair_dec t' t0 ns' n0) as [[E1 E2]|E].
    + subst t' ns'. rewrite set_ob_here in Hob. injection Hob as Hob. subst bx.
      split; [exact Hblt|].
      split; [rewrite Hfbl; exact Hnotfree|].
      split; [rewrite Hfbx; exact Hfb0|].
      split; [exact Hbo_b|].
      split; [rewrite set_wp_here; lia|].
      split; [right; exact Hbt|].
      split; [right; exact Hbn|].
      intros t'' ns'' Hob'.
      destruct (nat_pair_dec t'' t0 ns'' n0) as [[F1 F2]|F]; [split; assumption|].
      rewrite (set_ob_other _ _ _ _ _ _ F) in Hob'.
      destruct (Hopen_uniq t'' ns'' b Hob' eq_refl) as [G1 G2].
      destruct F as [F|F]; [exfalso; exact (F G1) | exfalso; exact (F G2)].
    + rewrite (set_ob_other _ _ _ _ _ _ E) in Hob.
      assert (Hne : bx <> b).
      { intros Hc. subst bx. destruct (Hopen_uniq t' ns' b Hob eq_refl) as [G1 G2].
        destruct E as [F|F]; [exact (F G1) | exact (F G2)]. }
      destruct (I22 t' ns' bx Hob) as (A1&A2&A3&A4&A5&A6&A7&A8).
      assert (Hnotret : open_block s t0 n0 <> Some bx).
      { intros Hc. destruct (A8 t0 n0 Hc) as [G1 G2].
        destruct E as [F|F];
          [apply F; symmetry; exact G1 | apply F; symmetry; exact G2]. }
      split; [exact A1|].
      split; [rewrite Hfbl; exact A2|].
      split; [rewrite Hfbx; exact A3|].
      split; [exact (Hbo_keep bx Hne A4 Hnotret)|].
      split; [rewrite (set_wp_other _ _ _ _ _ _ E); exact A5|].
      split; [exact A6|].
      split; [exact A7|].
      intros t'' ns'' Hob'.
      destruct (nat_pair_dec t'' t0 ns'' n0) as [[F1 F2]|F].
      * subst t'' ns''. rewrite set_ob_here in Hob'. injection Hob' as Hc.
        exfalso. apply Hne. symmetry. exact Hc.
      * rewrite (set_ob_other _ _ _ _ _ _ F) in Hob'. exact (A8 t'' ns'' Hob').
  - (* Inv21 *) intros t' ns' bx qx Hob Hle Hqx. prjh Hob. prjh Hle. prjg.
    destruct (nat_pair_dec t' t0 ns' n0) as [[E1 E2]|E].
    + subst t' ns'. rewrite set_ob_here in Hob. injection Hob as Hob. subst bx.
      rewrite set_wp_here in Hle.
      assert (Hne : qx <> q) by lia.
      rewrite (set_ps_other _ _ _ _ _ _ (or_intror Hne)).
      rewrite (set_pm_other _ _ _ _ _ _ (or_intror Hne)).
      exact (Habove qx Hle Hqx).
    + rewrite (set_ob_other _ _ _ _ _ _ E) in Hob.
      rewrite (set_wp_other _ _ _ _ _ _ E) in Hle.
      assert (Hne : bx <> b).
      { intros Hc. subst bx. destruct (Hopen_uniq t' ns' b Hob eq_refl) as [G1 G2].
        destruct E as [F|F]; [exact (F G1) | exact (F G2)]. }
      rewrite (set_ps_other _ _ _ _ _ _ (or_introl Hne)).
      rewrite (set_pm_other _ _ _ _ _ _ (or_introl Hne)).
      exact (I23 t' ns' bx qx Hob Hle Hqx).
  - (* Inv22 *) intros ax px pax Hm. prjh Hm. prjg.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + rewrite E1, E2. exists d. apply set_ps_here.
    + destruct (I24 ax px pax Hm) as [dx Hdx]. exists dx.
      rewrite (set_ps_other _ _ _ _ _ _ E). exact Hdx.
  - (* Inv23 *) intros bx Hbo. prjh Hbo. prjg.
    destruct (Hbo_true bx Hbo) as [Eb|[Hs Hnot]].
    + subst bx. exists t0, n0. apply set_ob_here.
    + destruct (I25 bx Hs) as [t' [ns' Hob]]. exists t', ns'.
      destruct (nat_pair_dec t' t0 ns' n0) as [[F1 F2]|F].
      * subst t' ns'. exfalso. apply Hnot. exact Hob.
      * rewrite (set_ob_other _ _ _ _ _ _ F). exact Hob.
  - (* Inv24 *) intros bx. prjg. rewrite Hfbx, Hfbl. exact (I26 bx).
  - (* Inv25 *) intros t' ns' bx qx Hob Hlt. prjh Hob. prjh Hlt. prjg.
    destruct (nat_pair_dec t' t0 ns' n0) as [[E1 E2]|E].
    + subst t' ns'. rewrite set_ob_here in Hob. injection Hob as Hob. subst bx.
      rewrite set_wp_here in Hlt.
      destruct (Nat.eq_dec qx q) as [Eq|Eq].
      * subst qx. rewrite set_ps_here. intros Hc; discriminate Hc.
      * rewrite (set_ps_other _ _ _ _ _ _ (or_intror Eq)). apply Hbelow. lia.
    + rewrite (set_ob_other _ _ _ _ _ _ E) in Hob.
      rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt.
      assert (Hne : bx <> b).
      { intros Hc. subst bx. destruct (Hopen_uniq t' ns' b Hob eq_refl) as [G1 G2].
        destruct E as [F|F]; [exact (F G1) | exact (F G2)]. }
      rewrite (set_ps_other _ _ _ _ _ _ (or_introl Hne)).
      exact (I27 t' ns' bx qx Hob Hlt).
  - (* Inv26 *) intros ax px pax Hm. prjh Hm. prjg. exact (I28 ax px pax Hm).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- what the bundles are for.

   A bundle that nothing satisfies proves nothing.  This part closes the
   loop: every flash instruction the framework's own expansions emit is
   issued in a state that satisfies that instruction's bundle.  The predicate
   is threaded through the expansion exactly as [trace_realizable] is in
   [BoundaryAgreement.v] -- the state each instruction sees is the state the
   previous instructions left behind -- and, crucially, the invariant is
   assumed only of the state the *operation* starts in, never of an
   instruction boundary inside it.
   ══════════════════════════════════════════════════════════════════════ *)

Definition prim_precondition (s : FTLState) (pr : FlashPrimitive) : Prop :=
  match pr with
  | PrimRead pa => pre_read s pa
  (* every [PrimProgram] an expansion emits carries a real tag stamped from the
     data; the honest-expansion bundle is tag-independent, so the explicit tag
     is not inspected here *)
  | PrimProgram pa d _ lpa => pre_program s pa d lpa
  | PrimErase b => pre_erase s b
  | _ => True
  end.

Fixpoint trace_precondition (s : FTLState) (l : list FlashPrimitive) : Prop :=
  match l with
  | [] => True
  | pr :: l' => prim_precondition s pr /\ trace_precondition (apply_primitive s pr) l'
  end.

Definition prim_preconditionb (s : FTLState) (pr : FlashPrimitive) : bool :=
  match pr with
  | PrimRead pa => pre_readb s pa
  | PrimProgram pa d _ lpa => pre_programb s pa d lpa
  | PrimErase b => pre_eraseb s b
  | _ => true
  end.

Fixpoint trace_preconditionb (s : FTLState) (l : list FlashPrimitive) : bool :=
  match l with
  | [] => true
  | pr :: l' => prim_preconditionb s pr && trace_preconditionb (apply_primitive s pr) l'
  end.

Lemma prim_preconditionb_correct :
  forall s pr, prim_preconditionb s pr = true <-> prim_precondition s pr.
Proof.
  intros s pr. destruct pr; cbn [prim_preconditionb prim_precondition];
    try (split; intros _; first [exact I | reflexivity]).
  - apply pre_programb_correct.
  - apply pre_eraseb_correct.
Qed.

Lemma trace_preconditionb_correct :
  forall l s, trace_preconditionb s l = true <-> trace_precondition s l.
Proof.
  induction l as [|pr l' IH]; intros s;
    cbn [trace_preconditionb trace_precondition].
  - split; [intros _; exact I | intros _; reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [Hp Hrest]. split;
        [exact (proj1 (prim_preconditionb_correct s pr) Hp) | exact Hrest].
    + intros [Hp Hrest]. split;
        [exact (proj2 (prim_preconditionb_correct s pr) Hp) | exact Hrest].
Qed.

Lemma trace_precondition_app_intro :
  forall l1 l2 s,
    trace_precondition s l1 ->
    trace_precondition (exec_primitives s l1) l2 ->
    trace_precondition s (l1 ++ l2).
Proof.
  induction l1 as [|pr l1' IH]; intros l2 s H1 H2;
    cbn [app trace_precondition exec_primitives] in *.
  - exact H2.
  - destruct H1 as [Hp Hrest]. split; [exact Hp|]. exact (IH l2 _ Hrest H2).
Qed.

(* ── the bundles respect extensional equality ─────────────────────────── *)

Lemma retiring_congr :
  forall v w b, state_eqv v w -> retiring v b = retiring w b.
Proof.
  intros v w b E. unfold retiring, is_open, prog_tenant, prog_ns.
  rewrite (eqv_bo _ _ E), (eqv_bt _ _ E), (eqv_bn _ _ E).
  destruct (block_open w b); [reflexivity|]. apply (eqv_ob _ _ E).
Qed.

Lemma pre_program_congr :
  forall v w pa d lpa, state_eqv v w -> pre_program w pa d lpa -> pre_program v pa d lpa.
Proof.
  intros v w pa d lpa E (H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact H1|]. split; [exact H2|].
  split.
  { destruct lpa as [[a p]|]; [|exact H3]. rewrite (eqv_l2p _ _ E). exact H3. }
  split.
  { intros q Hge Hq. rewrite (eqv_ps _ _ E), (eqv_pm _ _ E). exact (H4 q Hge Hq). }
  split.
  { intros q Hq. rewrite (eqv_ps _ _ E). exact (H5 q Hq). }
  { rewrite (retiring_congr v w (pa_block pa) E).
    destruct (retiring w (pa_block pa)) as [ob|]; [|exact I].
    rewrite (eqv_ps _ _ E). exact H6. }
Qed.

Lemma pre_erase_congr :
  forall v w b, state_eqv v w -> pre_erase w b -> pre_erase v b.
Proof.
  intros v w b E (H1 & H2 & H3 & H4).
  split; [exact H1|].
  split; [rewrite (eqv_fb _ _ E); exact H2|].
  split; [rewrite (eqv_bo _ _ E); exact H3|].
  intros a p pa Ha Hp Hm. rewrite (eqv_l2p _ _ E) in Hm.
  exact (H4 a p pa Ha Hp Hm).
Qed.

Lemma prim_precondition_congr :
  forall v w pr, state_eqv v w -> prim_precondition w pr -> prim_precondition v pr.
Proof.
  intros v w pr E H. destruct pr; cbn [prim_precondition] in *; try exact I.
  - exact (pre_program_congr v w pa d lpa E H).
  - exact (pre_erase_congr v w b E H).
Qed.

Lemma trace_precondition_congr :
  forall l v w, state_eqv v w -> trace_precondition w l -> trace_precondition v l.
Proof.
  induction l as [|pr l' IH]; intros v w E Hr; cbn [trace_precondition] in *.
  - exact I.
  - destruct Hr as [Hp Hrest]. split.
    + exact (prim_precondition_congr v w pr E Hp).
    + apply (IH _ (apply_primitive w pr));
        [apply apply_primitive_congr; exact E | exact Hrest].
Qed.

(* ── the mid-expansion facts ──────────────────────────────────────────── *)

(* [alloc_page] never looks at the forward map, so staling a page and
   dropping its mapping cannot change which page the frontier hands out. *)
Lemma alloc_page_l2p_irrelevant :
  forall X Y t ns pa s1,
    open_block Y = open_block X -> write_ptr Y = write_ptr X ->
    free_block_list Y = free_block_list X ->
    alloc_page X t ns = Some (pa, s1) ->
    exists s2, alloc_page Y t ns = Some (pa, s2).
Proof.
  intros X Y t ns pa s1 Hob Hwp Hfbl H.
  unfold alloc_page, open_fresh in *.
  rewrite Hob, Hwp, Hfbl.
  destruct (open_block X t ns) as [b|].
  - destruct (Nat.ltb (write_ptr X t ns) pages_per_block).
    + injection H as H1 _. subst pa. eexists. reflexivity.
    + destruct (free_block_list X) as [|b1 [|b2 r]]; try discriminate H.
      injection H as H1 _. subst pa. eexists. reflexivity.
  - destruct (free_block_list X) as [|b1 [|b2 r]]; try discriminate H.
    injection H as H1 _. subst pa. eexists. reflexivity.
Qed.

(* Field equations for the two bookkeeping primitives an expansion runs
   before its program. *)
Lemma inv_ps : forall s old,
  page_state (invalidate_at s old)
  = set_page_state (page_state s) (pa_block old) (pa_page old) PS_Invalid.
Proof. reflexivity. Qed.

Lemma inv_pm : forall s old,
  page_meta (invalidate_at s old)
  = set_page_meta (page_meta s) (pa_block old) (pa_page old) empty_page_meta.
Proof. reflexivity. Qed.

Lemma inv_fbl : forall s old,
  free_block_list (invalidate_at s old) = free_block_list s.
Proof. reflexivity. Qed.

Lemma inv_ob : forall s old, open_block (invalidate_at s old) = open_block s.
Proof. reflexivity. Qed.

Lemma inv_wp : forall s old, write_ptr (invalidate_at s old) = write_ptr s.
Proof. reflexivity. Qed.

Lemma inv6_invalidate :
  forall s old, Inv6 s -> ~ In (pa_block old) (free_block_list s) ->
    Inv6 (invalidate_at s old).
Proof.
  intros s old I8 Hnf bx Hin px Hp.
  rewrite inv_fbl in Hin.
  assert (Hne : bx <> pa_block old) by (intros Hc; subst bx; exact (Hnf Hin)).
  rewrite inv_ps, inv_pm.
  rewrite (set_ps_other _ _ _ _ _ _ (or_introl Hne)).
  rewrite (set_pm_other _ _ _ _ _ _ (or_introl Hne)).
  exact (I8 bx Hin px Hp).
Qed.

Lemma inv21_invalidate :
  forall s old, Inv21 s ->
    (exists dd, page_state s (pa_block old) (pa_page old) = PS_Valid dd) ->
    Inv21 (invalidate_at s old).
Proof.
  intros s old I23 [dd Hdd] t ns bx qx Hob Hle Hq.
  rewrite inv_ob in Hob. rewrite inv_wp in Hle.
  destruct (I23 t ns bx qx Hob Hle Hq) as [He Hm].
  assert (Hne : bx <> pa_block old \/ qx <> pa_page old).
  { destruct (nat_pair_dec bx (pa_block old) qx (pa_page old)) as [[E1 E2]|E];
      [|exact E]. subst bx qx. rewrite Hdd in He. discriminate He. }
  rewrite inv_ps, inv_pm.
  rewrite (set_ps_other _ _ _ _ _ _ Hne).
  rewrite (set_pm_other _ _ _ _ _ _ Hne).
  split; assumption.
Qed.

Lemma inv25_invalidate :
  forall s old, Inv25 s -> Inv25 (invalidate_at s old).
Proof.
  intros s old I27 t ns bx qx Hob Hlt.
  rewrite inv_ob in Hob. rewrite inv_wp in Hlt. rewrite inv_ps.
  destruct (nat_pair_dec bx (pa_block old) qx (pa_page old)) as [[E1 E2]|E].
  - subst bx qx. rewrite set_ps_here. intros Hc; discriminate Hc.
  - rewrite (set_ps_other _ _ _ _ _ _ E). exact (I27 t ns bx qx Hob Hlt).
Qed.

(* ── the mid-write witness ────────────────────────────────────────────── *)

(* Install the mapping, then program the page the frontier just handed out:
   the shape of every [PrimProgram] any expansion emits.  Five clauses of the
   *pre-instruction* state suffice; the full invariant is never needed, and
   in particular Inv22 and Inv0 -- which are false here -- are not among
   them. *)
Lemma alloc_install_pre_program :
  forall s0 a p d t ns pa s1,
    Inv6 s0 -> Inv8 s0 -> Inv20 s0 -> Inv21 s0 -> Inv25 s0 ->
    addr_tenant s0 a = Some t ->
    addr_namespace s0 a = Some ns ->
    alloc_page s0 t ns = Some (pa, s1) ->
    pre_program (install_mapping s0 a p pa) pa d (Some (a, p)).
Proof.
  intros s0 a p d t ns pa s1 I8 I10 I22 I23 I27 Hat Han Halloc.
  pose proof pages_per_block_pos as Hppb.
  assert (Hbt : block_tenant (install_mapping s0 a p pa) (pa_block pa) = Some t)
    by (rewrite install_mapping_bt; exact Hat).
  assert (Hbn : block_namespace (install_mapping s0 a p pa) (pa_block pa) = Some ns)
    by (rewrite install_mapping_bn; exact Han).
  assert (Hretiring : retiring (install_mapping s0 a p pa) (pa_block pa)
                      = if block_open s0 (pa_block pa) then None
                        else open_block s0 t ns).
  { unfold retiring, is_open, prog_tenant, prog_ns. rewrite Hbt, Hbn. reflexivity. }
  assert (Hmapped : l2p_map (install_mapping s0 a p pa) a p = Some pa)
    by (apply set_l2p_here).
  unfold pre_program.
  destruct (alloc_page_shape s0 t ns pa s1 Halloc)
    as [[b (Hob & Hlt & Hpa & _)] | [Hof Hge]].
  - (* the owner's open block still has room *)
    destruct (I22 t ns b Hob) as (Hblt & _ & _ & Hbo & _).
    subst pa. cbn [pa_block pa_page] in Hretiring |- *.
    split; [exact Hblt|].
    split; [exact Hlt|].
    split; [exact Hmapped|].
    split.
    { intros q Hge' Hq. assert (Hle : write_ptr s0 t ns <= q) by lia.
      exact (I23 t ns b q Hob Hle Hq). }
    split.
    { intros q Hq. exact (I27 t ns b q Hob Hq). }
    { rewrite Hretiring, Hbo. exact I. }
  - (* a fresh block comes off the free pool and the outgoing one is retired *)
    destruct (open_fresh_shape s0 t ns pa s1 Hof) as [fbh [rest (Hfbl0 & Hpa & _)]].
    assert (Hin : In fbh (free_block_list s0)) by (rewrite Hfbl0; left; reflexivity).
    subst pa. cbn [pa_block pa_page] in Hretiring |- *.
    split; [exact (I10 fbh Hin)|].
    split; [exact Hppb|].
    split; [exact Hmapped|].
    split.
    { intros q _ Hq. exact (I8 fbh Hin q Hq). }
    split.
    { intros q Hq. lia. }
    { assert (Hall : forall ob, open_block s0 t ns = Some ob ->
                page_state (install_mapping s0 a p (mkPhysAddr fbh 0)) ob 0
                <> PS_Empty).
      { intros ob Hobo. destruct (I22 t ns ob Hobo) as (_ & _ & _ & _ & Hle & _).
        pose proof (Hge ob Hobo) as Hge'.
        assert (Hlt0 : 0 < write_ptr s0 t ns) by lia.
        exact (I27 t ns ob 0 Hobo Hlt0). }
      rewrite Hretiring.
      destruct (block_open s0 fbh); [exact I|].
      destruct (open_block s0 t ns) as [ob|] eqn:Hobo; [|exact I].
      apply Hall; first [reflexivity | exact Hobo]. }
Qed.

(* ── the write's expansion ────────────────────────────────────────────── *)

(* The state the [Program] is issued in is [install_mapping] applied to the
   state the [Invalidate] left.  Note which clauses of the *starting* state
   are used: Inv6/Inv8/Inv20/Inv21/Inv25 (carried through the invalidate)
   plus Inv5/Inv22/Inv3, the last two only to identify the staled page.
   Inv22 of the *intermediate* state is not used, and is false there. *)
Lemma write_pre :
  forall s a p d l,
    ftl_invariant s ->
    op_primitives s (COpWrite a p d) = Some l ->
    trace_precondition s l.
Proof.
  intros s a p d l Hinv H.
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  cbn [op_primitives] in H.
  destruct (Nat.ltb a addr_space && Nat.ltb p pages_per_block &&
            (match addr_tenant s a, addr_namespace s a with
             | Some _, Some _ => true | _, _ => false end)); [|discriminate H].
  unfold write_primitives in H.
  destruct (addr_tenant s a) as [t|] eqn:Hat; [|discriminate H].
  destruct (addr_namespace s a) as [ns|] eqn:Han; [|discriminate H].
  destruct (l2p_map s a p) as [old|] eqn:Hm.
  - (* the logical page was mapped: stale the old page first *)
    destruct (alloc_page (invalidate_at s old) t ns) as [[pa s3]|] eqn:Ha;
      [|discriminate H].
    injection H as H. subst l.
    assert (Hlive : exists dd, page_state s (pa_block old) (pa_page old) = PS_Valid dd)
      by exact (I24 a p old Hm).
    assert (Hstamp : page_lpa (page_meta s (pa_block old) (pa_page old)) = Some (a, p))
      by exact (mapped_page_stamp s a p old I5 I24 Hm).
    assert (HallocX : exists s4,
              alloc_page (unmap (invalidate_at s old) a p) t ns = Some (pa, s4)).
    { exact (alloc_page_l2p_irrelevant (invalidate_at s old)
               (unmap (invalidate_at s old) a p) t ns pa s3
               eq_refl eq_refl eq_refl Ha). }
    destruct HallocX as [s4 HallocX].
    cbn [app trace_precondition prim_precondition].
    rewrite prim_enter_id.
    rewrite (prim_invalidate_shape s old a p Hstamp).
    rewrite prim_mapaddr_eq.
    refine (conj I (conj I (conj I (conj _ (conj I I))))).
    exact (alloc_install_pre_program (unmap (invalidate_at s old) a p) a p d t ns
             pa s4
             (inv6_invalidate s old I8 (I7 a p old Hm))
             I10 I22
             (inv21_invalidate s old I23 Hlive)
             (inv25_invalidate s old I27)
             Hat Han HallocX).
  - (* fresh logical page: nothing to stale *)
    destruct (alloc_page s t ns) as [[pa s3]|] eqn:Ha; [|discriminate H].
    injection H as H. subst l.
    cbn [app trace_precondition prim_precondition].
    rewrite prim_enter_id. rewrite prim_mapaddr_eq.
    refine (conj I (conj I (conj _ (conj I I)))).
    exact (alloc_install_pre_program s a p d t ns pa s3
             I8 I10 I22 I23 I27 Hat Han Ha).
Qed.

(* ── the reclaim's expansion ──────────────────────────────────────────── *)

(* [INVX vb []] is exactly the erase bundle plus the clauses the erase
   restores; the bundle is the part of it a checker can see. *)
Lemma INVX_pre_erase : forall s vb, INVX vb [] s -> pre_erase s vb.
Proof.
  intros s vb HX.
  split; [exact (xblt _ _ _ HX)|].
  split; [exact (xfree _ _ _ HX)|].
  split; [exact (xopen _ _ _ HX)|].
  intros a p pa _ _ Hm Hbk. exact (xprog _ _ _ HX a p pa Hm Hbk).
Qed.

Lemma reloc_step_pre :
  forall s vb q tl pr,
    INVX vb (q :: tl) s ->
    page_reloc_primitives s vb q = Some pr ->
    trace_precondition s pr.
Proof.
  intros s vb q tl pr HX Hpr.
  pose proof (xI8 _ _ _ HX) as I8.
  pose proof (xI10 _ _ _ HX) as I10.
  pose proof (xI22 _ _ _ HX) as I22.
  pose proof (xI23 _ _ _ HX) as I23.
  pose proof (xI27 _ _ _ HX) as I27.
  unfold page_reloc_primitives in Hpr.
  destruct (page_state s vb q) as [| |dd] eqn:Hps.
  - injection Hpr as Hpr; subst pr; exact I.
  - injection Hpr as Hpr; subst pr; exact I.
  - destruct (page_lpa (page_meta s vb q)) as [[a0 p0]|]; [|discriminate Hpr].
    destruct (addr_tenant s a0) as [t|] eqn:Hat;
      destruct (addr_namespace s a0) as [ns|] eqn:Han;
      cbv beta iota in Hpr; try discriminate Hpr.
    destruct (alloc_page s t ns) as [[pa s1]|] eqn:Ha;
      cbv beta iota in Hpr; [|discriminate Hpr].
    injection Hpr as Hpr; subst pr.
    cbn [trace_precondition prim_precondition].
    rewrite prim_read_id. rewrite prim_remap_eq.
    refine (conj I (conj I (conj _ I))).
    exact (alloc_install_pre_program s a0 p0 dd t ns pa s1
             I8 I10 I22 I23 I27 Hat Han Ha).
Qed.

Lemma reloc_loop_pre :
  forall qs s vb l s',
    INVX vb qs s ->
    reloc_primitives s vb qs = Some l ->
    relocate_pages s vb qs = Some s' ->
    trace_precondition s l.
Proof.
  induction qs as [|q tl IH]; intros s vb l s' HX Hl Hs'.
  - cbn [reloc_primitives] in Hl. injection Hl as Hl. subst l. exact I.
  - cbn [reloc_primitives] in Hl. cbn [relocate_pages] in Hs'.
    destruct (page_reloc_primitives s vb q) as [pr|] eqn:Hpr; [|discriminate Hl].
    destruct (relocate_page s vb q) as [s1|] eqn:Hrel;
      cbv beta iota in Hl, Hs'; [|discriminate Hl].
    destruct (reloc_primitives s1 vb tl) as [rest|] eqn:Hrest; [|discriminate Hl].
    injection Hl as Hl. subst l.
    destruct (reloc_step_ok s vb q tl pr s1 HX Hpr Hrel) as [_ He1].
    apply trace_precondition_app_intro.
    + exact (reloc_step_pre s vb q tl pr HX Hpr).
    + apply (trace_precondition_congr rest _ s1).
      * apply state_eqv_sym. exact He1.
      * exact (IH s1 vb rest s'
                 (relocate_page_INVX s vb q tl s1 HX Hrel) Hrest Hs').
Qed.

Lemma reclaim_pre :
  forall bt s vb l,
    INVX vb all_pages s ->
    reclaim_primitives bt s vb = Some l ->
    (exists s', reclaim s vb = Some s') ->
    trace_precondition s l.
Proof.
  intros bt s vb l HX Hl [s' Hs'].
  unfold reclaim_primitives in Hl. unfold reclaim in Hs'.
  destruct (reloc_primitives s vb all_pages) as [rs|] eqn:Hrs; [|discriminate Hl].
  destruct (relocate_pages s vb all_pages) as [s1|] eqn:Hrel; [|discriminate Hs'].
  injection Hl as Hl. subst l. injection Hs' as Hs'. subst s'.
  destruct (reloc_loop_ok all_pages s vb rs s1 HX Hrs Hrel) as [_ He].
  cbn [app trace_precondition].
  split; [exact I|]. rewrite prim_enter_id.
  apply trace_precondition_app_intro.
  - exact (reloc_loop_pre all_pages s vb rs s1 HX Hrs Hrel).
  - cbn [trace_precondition prim_precondition].
    split; [|split; exact I].
    apply (pre_erase_congr (exec_primitives s rs) s1).
    + apply state_eqv_sym. exact He.
    + exact (INVX_pre_erase s1 vb
               (relocate_pages_INVX all_pages s vb s1 HX Hrel)).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   The statement of what the bundles are for.
   ══════════════════════════════════════════════════════════════════════ *)

(* Every flash instruction an operation's expansion emits is issued in a
   state satisfying that instruction's bundle.  The invariant is a hypothesis
   on the operation's starting state only.  Together with
   [decompose_realizable] this pins down the transient window precisely:
   at the program call site the destination is erased (realizability) and the
   forward map already points at it (PP3), so Inv22 is false exactly there. *)
Theorem decompose_preconditioned :
  forall s op l,
    ftl_invariant s ->
    op_primitives s op = Some l ->
    trace_precondition s l.
Proof.
  intros s op l Hinv H. destruct op as [a p | a p d | a p | a p tag | |].
  - (* COpRead *) cbn [op_primitives] in H.
    destruct (l2p_map s a p) as [pa|]; injection H as H; subst l;
      cbn [trace_precondition prim_precondition]; repeat split; exact I.
  - (* COpWrite *) exact (write_pre s a p d l Hinv H).
  - (* COpInvalidate *) cbn [op_primitives] in H.
    destruct (l2p_map s a p) as [pa|]; injection H as H; subst l;
      cbn [trace_precondition prim_precondition]; repeat split; exact I.
  - (* COpSetTag *) cbn [op_primitives] in H.
    destruct (l2p_map s a p) as [pa|]; injection H as H; subst l;
      cbn [trace_precondition prim_precondition]; repeat split; exact I.
  - (* COpGC *) cbn [op_primitives] in H.
    destruct (find_victim s) as [vb|] eqn:Hv; [|discriminate H].
    assert (Hrec : exists s', reclaim s vb = Some s').
    { destruct (reclaim s vb) as [s'|] eqn:E; [exists s'; reflexivity|].
      exfalso. apply (proj2 (reclaim_primitives_domain 0 s vb)) in E.
      rewrite H in E. discriminate E. }
    exact (reclaim_pre 0 s vb l
             (victim_INVX find_victim s vb find_victim_sound Hinv Hv) H Hrec).
  - (* COpWearLevel: the same expansion over the wear-aware chooser's victim *)
    cbn [op_primitives] in H.
    destruct (find_least_worn_victim s) as [vb|] eqn:Hv; [|discriminate H].
    assert (Hrec : exists s', reclaim s vb = Some s').
    { destruct (reclaim s vb) as [s'|] eqn:E; [exists s'; reflexivity|].
      exfalso. apply (proj2 (reclaim_primitives_domain 1 s vb)) in E.
      rewrite H in E. discriminate E. }
    exact (reclaim_pre 1 s vb l
             (victim_INVX find_least_worn_victim s vb
                find_least_worn_victim_sound Hinv Hv) H Hrec).
Qed.

(* An executable corollary: the checker's per-instruction test passes on
   every expansion a reachable state emits. *)
Corollary decompose_preconditionedb :
  forall s op l,
    ftl_invariant s ->
    op_primitives s op = Some l ->
    trace_preconditionb s l = true.
Proof.
  intros s op l Hinv H. apply trace_preconditionb_correct.
  exact (decompose_preconditioned s op l Hinv H).
Qed.

(* And the same guarantee over a whole reachable trace's first operation:
   the device never issues a flash command outside its bundle. *)
Corollary reachable_preconditioned :
  forall ops s op l,
    exec empty_state ops = Some s ->
    op_primitives s op = Some l ->
    trace_precondition s l.
Proof.
  intros ops s op l Hexec Hop.
  exact (decompose_preconditioned s op l
           (Invariants.Preservation.reachable_states_satisfy_invariant_closed
              ops s Hexec) Hop).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- the transient window, stated rather than described.

   The two lemmas below are the formal content of the header's crux.  They
   are cheap, and they are what stops the reader from having to take the
   commentary on trust.
   ══════════════════════════════════════════════════════════════════════ *)

(* Where the whole invariant holds, the program bundle can only describe an
   in-place refresh: PP3 puts a mapping onto the destination and Inv22 then
   makes the destination live.  This is why [pre_sound_program] and
   [decompose_preconditioned] are statements about disjoint states. *)
Lemma pre_program_under_invariant_targets_a_live_page :
  forall s pa d lpa,
    ftl_invariant s ->
    pre_program s pa d lpa ->
    exists d0, page_state s (pa_block pa) (pa_page pa) = PS_Valid d0.
Proof.
  intros s pa d lpa Hinv Hpre.
  destruct Hpre as (_ & _ & Hmap & _).
  destruct lpa as [[a0 p0]|]; [|contradiction Hmap].
  destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I24&_).
  exact (I24 a0 p0 pa Hmap).
Qed.

(* And conversely: a program call site that obeys NAND -- the destination is
   erased, which is what [decompose_realizable] proves of every emitted
   [PrimProgram] -- is a state at which Inv22 fails.  The instruction that
   follows repairs it; no clause was weakened to make this go away. *)
Theorem program_call_sites_break_Inv22 :
  forall s pa d lpa,
    pre_program s pa d lpa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Empty ->
    ~ Inv22 s.
Proof.
  intros s pa d lpa Hpre Hempty I24.
  destruct Hpre as (_ & _ & Hmap & _).
  destruct lpa as [[a0 p0]|]; [|contradiction Hmap].
  destruct (I24 a0 p0 pa Hmap) as [d0 Hd0].
  rewrite Hempty in Hd0. discriminate Hd0.
Qed.
