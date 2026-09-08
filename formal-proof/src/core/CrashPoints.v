(* CrashPoints.v: power loss inside an operation's instruction expansion,
   over the page-granular model.

   Invariants/CrashRecovery.v and CrashRefinement.v treat a power loss
   between two operations.  This file looks inside: [op_primitives s op]
   expands an operation into a list of instructions, and a power loss can
   strike after any prefix of it.  The k-th *crash point* of an expansion is
   the state reached after its first k instructions ([crash_point]); the device
   then reboots into [recover (crash (crash_point s prims k))].

   A crash point is *covered* when the recovered device refines either the
   abstract device before the operation or the one after it ([covered]).  The
   abstract device then sees a crash inside an operation as either "the
   operation did not happen" or "the operation completed" -- the crash
   semantics a block device is expected to have.

   ── Results ───────────────────────────────────────────────────────────

   1. Any prefix of controller micro-operations only (reads, mappings,
      barriers) leaves the flash untouched, so its crash point recovers like
      the pre-state ([volatile_prefix_covered]).

   2. The final crash point of every expansion is covered
      ([final_point_covered]), and hence reads, tag writes, GC and wear
      levelling are covered at their volatile-prefix and final points.

   3. Two crash points are *not* covered:

      - The out-of-place update stales (and unmaps) the old page before the
        new datum is programmed.  A power loss between the two leaves the
        sector gone: [torn_write_loses_sector] shows the recovered device
        reads [None].

      - During a reclaim, each live page is programmed at its destination
        before the block is erased, so mid-copy two live pages carry the same
        stamp; [duplicate_stamp_breaks_Inv4] shows no recovered mapping
        satisfies Inv4 from such a flash image.  This is the well-known reason
        real FTLs version their OOB stamps. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import core.Primitives.
Require Import core.BoundaryAgreement.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.
Require Import Refinement.
Require Import Specs.
Require Import Invariants.CrashRecovery.
Require Import CrashRefinement.

Import ListNotations.

Section CrashPoints.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* ══════════════════════════════════════════════════════════════════════
   Section 1: crash points and coverage
   ══════════════════════════════════════════════════════════════════════ *)

Definition crash_point (s : FTLState) (prims : list FlashPrimitive) (k : nat)
    : FTLState :=
  exec_primitives s (firstn k prims).

Definition recovered_at (s : FTLState) (prims : list FlashPrimitive) (k : nat)
    : FTLState :=
  recover (crash (crash_point s prims k)).

(* The recovered device refines the abstract device [h] and can continue. *)
Definition recovers_to (h : AbsDev) (s : FTLState) : Prop :=
  CR h s /\ ftl_invariant s.

Definition covered (h h' : AbsDev) (s : FTLState) (prims : list FlashPrimitive) (k : nat)
    : Prop :=
  recovers_to h (recovered_at s prims k) \/ recovers_to h' (recovered_at s prims k).

Lemma recovers_to_of_state :
  forall h s,
    ftl_invariant s ->
    CR h s ->
    recovers_to h (recover (crash s)).
Proof.
  intros h s Hinv HCR. split.
  - apply crash_recover_preserves_CR; assumption.
  - apply recover_preserves_invariant; assumption.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 2: prefixes that leave the flash untouched
   ══════════════════════════════════════════════════════════════════════ *)

Definition volatile_prim (pr : FlashPrimitive) : bool :=
  match pr with
  | PrimRead _ | PrimMapAddr _ _ _ | PrimRemap _ _ _
  | PrimBarrierEnter _ | PrimBarrierExit _
  (* a free-list push touches only DRAM allocator state, which the crash
     transition discards, so it leaves the crash image unchanged *)
  | PrimFreePush _ => true
  | PrimProgram _ _ _ _ | PrimInvalidate _ | PrimSetTag _ _ | PrimErase _
      => false
  end.

Lemma crash_volatile_prim :
  forall s pr,
    volatile_prim pr = true ->
    crash (apply_primitive s pr) = crash s.
Proof.
  intros s pr H. destruct pr; cbn in H; try discriminate; reflexivity.
Qed.

Lemma crash_volatile_prefix :
  forall l s,
    forallb volatile_prim l = true ->
    crash (exec_primitives s l) = crash s.
Proof.
  induction l as [| pr l IH]; intros s H; cbn in *; [reflexivity |].
  apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite (IH _ H2). apply crash_volatile_prim. exact H1.
Qed.

Theorem volatile_prefix_covered :
  forall h s prims k,
    ftl_invariant s ->
    CR h s ->
    forallb volatile_prim (firstn k prims) = true ->
    recovers_to h (recovered_at s prims k).
Proof.
  intros h s prims k Hinv HCR Hvol.
  unfold recovered_at, crash_point.
  rewrite (crash_volatile_prefix _ _ Hvol).
  apply recovers_to_of_state; assumption.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 3: extensionality -- the invariant and the relation are pointwise
   ══════════════════════════════════════════════════════════════════════ *)

Lemma CR_eqv :
  forall h s1 s2,
    (forall a p, l2p_map s1 a p = l2p_map s2 a p) ->
    (forall b p, page_state s1 b p = page_state s2 b p) ->
    CR h s1 ->
    CR h s2.
Proof.
  intros h s1 s2 Hl Hps HCR a p d Hread.
  destruct (HCR a p d Hread) as [pa [Hm Hpa]].
  exists pa. rewrite <- Hl, <- Hps. auto.
Qed.

Lemma ftl_invariant_eqv :
  forall s1 s2, state_eqv s1 s2 -> ftl_invariant s1 -> ftl_invariant s2.
Proof.
  intros s1 s2 H Hinv.
  pose proof (eqv_l2p _ _ H) as El.
  pose proof (eqv_ps  _ _ H) as Eps.
  pose proof (eqv_pr  _ _ H) as Erole.
  pose proof (eqv_at  _ _ H) as Eat.
  pose proof (eqv_an  _ _ H) as Ean.
  pose proof (eqv_bt  _ _ H) as Ebt.
  pose proof (eqv_bn  _ _ H) as Ebn.
  pose proof (eqv_pm  _ _ H) as Emeta.
  pose proof (eqv_rt  _ _ H) as Ert.
  pose proof (eqv_fbl _ _ H) as Efbl.
  pose proof (eqv_fb  _ _ H) as Efb.
  pose proof (eqv_wc  _ _ H) as Ewc.
  pose proof (eqv_kt  _ _ H) as Ekt.
  pose proof (eqv_ob  _ _ H) as Eob.
  pose proof (eqv_wp  _ _ H) as Ewp.
  pose proof (eqv_bo  _ _ H) as Ebo.
  destruct Hinv as (W0&W1&I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15&I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26).
  apply make_ftl_invariant.
  - exact W0.
  - intros b p _ _. eexists. reflexivity.
  - (* Inv0 *)
    intros b p d Hpsv. rewrite <- Eps in Hpsv.
    destruct (I0 b p d Hpsv) as [a [q Hm]]. exists a, q. rewrite <- El. exact Hm.
  - (* Inv1 *)
    intros a p pa Hm. rewrite <- El in Hm. exact (I1 a p pa Hm).
  - (* Inv2 *)
    intros a1 p1 a2 p2 pa Hm1 Hm2. rewrite <- El in Hm1, Hm2.
    exact (I2 a1 p1 a2 p2 pa Hm1 Hm2).
  - (* Inv3 *)
    intros a p pa d Hm Hpsv. rewrite <- El in Hm. rewrite <- Eps in Hpsv.
    rewrite <- Emeta. exact (I3 a p pa d Hm Hpsv).
  - (* Inv4 *)
    intros a p b q d Hpsv Hlpa. rewrite <- Eps in Hpsv. rewrite <- Emeta in Hlpa.
    rewrite <- El. exact (I4 a p b q d Hpsv Hlpa).
  - (* Inv5 *)
    intros a p pa Hm Hin. rewrite <- El in Hm. rewrite <- Efbl in Hin.
    exact (I5 a p pa Hm Hin).
  - (* Inv6 *)
    intros b Hin p Hp. rewrite <- Efbl in Hin. rewrite <- Eps, <- Emeta.
    exact (I6 b Hin p Hp).
  - (* Inv7 *)
    intros a p pa d t ns Hm Hpsv Ht Hns.
    rewrite <- El in Hm. rewrite <- Eps in Hpsv. rewrite <- Eat in Ht. rewrite <- Ean in Hns.
    rewrite <- Emeta. exact (I7 a p pa d t ns Hm Hpsv Ht Hns).
  - (* Inv8 *)
    intros b Hin. rewrite <- Efbl in Hin. exact (I8 b Hin).
  - (* Inv9 *)
    intros b p d Hpsv. rewrite <- Eps in Hpsv. rewrite <- Emeta. exact (I9 b p d Hpsv).
  - (* Inv10 *)
    intros b Hb.
    destruct (I10 b Hb) as [Hfree | [[t [ns Hopen]] | [[a [p [pa [Hm Hpb]]]] | [q Hst]]]].
    + left. rewrite <- Efbl. exact Hfree.
    + right. left. exists t, ns. rewrite <- Eob. exact Hopen.
    + right. right. left. exists a, p, pa. split; [rewrite <- El; exact Hm | exact Hpb].
    + right. right. right. exists q. rewrite <- Eps. exact Hst.
  - (* Inv11 *)
    unfold Inv11. rewrite <- Efbl. exact I11.
  - (* Inv12 *)
    intros b Hb [p Hrole]. rewrite <- Erole in Hrole.
    destruct (I12 b Hb (ex_intro _ p Hrole)) as [[a [p' [pa [Hm Hpb]]]] | [q Hst]].
    + left. exists a, p', pa. split; [rewrite <- El; exact Hm | exact Hpb].
    + right. exists q. rewrite <- Eps. exact Hst.
  - (* Inv13 *)
    intros b p d Hpsv. rewrite <- Eps in Hpsv. rewrite <- Erole. exact (I13 b p d Hpsv).
  - (* Inv14 *)
    intros b p Hrole. rewrite <- Erole in Hrole. rewrite <- Eps. exact (I14 b p Hrole).
  - (* Inv15 *)
    intros b p Hrole. rewrite <- Erole in Hrole. rewrite <- Eps. exact (I15 b p Hrole).
  - (* Inv16 *)
    intros b p Hpsv. rewrite <- Eps in Hpsv. rewrite <- Erole. exact (I16 b p Hpsv).
  - (* Inv17 *)
    intros b Hfree. rewrite <- Efb in Hfree. rewrite <- Ebt, <- Ebn. exact (I17 b Hfree).
  - (* Inv18 *)
    intros a p pa Hm. rewrite <- El in Hm.
    rewrite <- Ebt, <- Ebn, <- Eat, <- Ean. exact (I18 a p pa Hm).
  - (* Inv19 *)
    intros i r Hr. rewrite <- Ert in Hr. exact (I19 i r Hr).
  - (* Inv20 *)
    intros t ns b Hopen. rewrite <- Eob in Hopen.
    destruct (I20 t ns b Hopen) as (Hbound & Hnf & Hfb & Hbo & Hwp & Ht & Hns & Huniq).
    rewrite <- Efbl, <- Efb, <- Ebo, <- Ewp, <- Ebt, <- Ebn.
    split; [exact Hbound |]. split; [exact Hnf |]. split; [exact Hfb |].
    split; [exact Hbo |]. split; [exact Hwp |]. split; [exact Ht |]. split; [exact Hns |].
    intros t2 ns2 Hopen2. rewrite <- Eob in Hopen2. exact (Huniq t2 ns2 Hopen2).
  - (* Inv21 *)
    intros t ns b q Hopen Hge Hlt. rewrite <- Eob in Hopen. rewrite <- Ewp in Hge.
    rewrite <- Eps, <- Emeta. exact (I21 t ns b q Hopen Hge Hlt).
  - (* Inv22 *)
    intros a p pa Hm. rewrite <- El in Hm. rewrite <- Eps. exact (I22 a p pa Hm).
  - (* Inv23 *)
    intros b Hbo. rewrite <- Ebo in Hbo.
    destruct (I23 b Hbo) as [t [ns Hopen]]. exists t, ns. rewrite <- Eob. exact Hopen.
  - (* Inv24 *)
    intros b. rewrite <- Efb, <- Efbl. exact (I24 b).
  - (* Inv25 *)
    intros t ns b q Hopen Hlt. rewrite <- Eob in Hopen. rewrite <- Ewp in Hlt.
    rewrite <- Eps. exact (I25 t ns b q Hopen Hlt).
  - (* Inv26 *)
    intros a p pa Hm. rewrite <- El in Hm. rewrite <- Eat, <- Ean. exact (I26 a p pa Hm).
Qed.

(* A state pointwise equal to one that refines [h] and satisfies the invariant
   also does, after crash+recover. *)
Lemma recovers_to_eqv :
  forall h s1 s2,
    state_eqv s1 s2 ->
    ftl_invariant s1 ->
    CR h s1 ->
    recovers_to h (recover (crash s2)).
Proof.
  intros h s1 s2 Heqv Hinv HCR.
  apply recovers_to_of_state.
  - exact (ftl_invariant_eqv s1 s2 Heqv Hinv).
  - exact (CR_eqv h s1 s2 (eqv_l2p _ _ Heqv) (eqv_ps _ _ Heqv) HCR).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 4: the final crash point of every expansion
   ══════════════════════════════════════════════════════════════════════

   After the last instruction the device holds the decomposed result, which
   [decompose_correct] proves equal to the atomic result field by field.
   The atomic result refines [abs_step h op] and satisfies the invariant, so
   the recovered device does too. *)

Theorem final_point_covered :
  forall h s op s' prims k,
    ftl_invariant s ->
    step s op = Some s' ->
    op_primitives s op = Some prims ->
    CR h s ->
    k >= length prims ->
    recovers_to (abs_step h op) (recovered_at s prims k).
Proof.
  intros h s op s' prims k Hinv Hstep Hprims HCR Hk.
  unfold recovered_at, crash_point.
  rewrite firstn_all2 by exact Hk.
  pose proof (decompose_correct s op Hinv) as Hf.
  unfold faithful_at in Hf. rewrite Hstep in Hf.
  unfold step_mqsim in Hf. rewrite Hprims in Hf.
  (* Hf : state_eqv s' (exec_primitives s prims) *)
  apply recovers_to_eqv with (s1 := s').
  - exact Hf.
  - exact (@step_preserves_invariant pages_per_block_gt0 s op s' Hinv Hstep).
  - exact (@step_simulates pages_per_block_gt0 h s op s' Hinv HCR Hstep).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 5: coverage, operation by operation
   ══════════════════════════════════════════════════════════════════════ *)

(* Reads: every crash point (the expansion is at most one [PrimRead]). *)
Theorem read_crash_points :
  forall h s a p prims k,
    ftl_invariant s ->
    CR h s ->
    op_primitives s (COpRead a p) = Some prims ->
    recovers_to h (recovered_at s prims k).
Proof.
  intros h s a p prims k Hinv HCR Hprims.
  apply volatile_prefix_covered; try assumption.
  unfold op_primitives in Hprims.
  destruct (l2p_map s a p); injection Hprims as <-;
    destruct k as [| [| k]]; reflexivity.
Qed.

(* Tag writes: every crash point.  The tag lives in the OOB, which [CR] does
   not observe, so the abstract device is unchanged ([abs_step h] = h). *)
Theorem set_tag_crash_points :
  forall h s a p tag s' prims k,
    ftl_invariant s ->
    CR h s ->
    step s (COpSetTag a p tag) = Some s' ->
    op_primitives s (COpSetTag a p tag) = Some prims ->
    recovers_to h (recovered_at s prims k).
Proof.
  intros h s a p tag s' prims k Hinv HCR Hstep Hprims.
  destruct k as [| k].
  - apply volatile_prefix_covered; try assumption. reflexivity.
  - replace h with (abs_step h (COpSetTag a p tag)) by reflexivity.
    apply final_point_covered with (s' := s'); try assumption.
    unfold op_primitives in Hprims.
    destruct (l2p_map s a p); injection Hprims as <-; cbn; lia.
Qed.

(* Garbage collection and wear levelling: the recovered device refines [h]
   unchanged at every volatile-prefix point and at the final point.  The
   copy phase in between is the duplicate-stamp situation of Section 6. *)
Theorem gc_crash_points :
  forall h s s' prims k,
    ftl_invariant s ->
    CR h s ->
    step s COpGC = Some s' ->
    op_primitives s COpGC = Some prims ->
    forallb volatile_prim (firstn k prims) = true \/ k >= length prims ->
    recovers_to h (recovered_at s prims k).
Proof.
  intros h s s' prims k Hinv HCR Hstep Hprims Hk.
  destruct Hk as [Hvol | Hk].
  - apply volatile_prefix_covered; assumption.
  - replace h with (abs_step h COpGC) by reflexivity.
    apply final_point_covered with (s' := s'); assumption.
Qed.

Theorem wear_level_crash_points :
  forall h s s' prims k,
    ftl_invariant s ->
    CR h s ->
    step s COpWearLevel = Some s' ->
    op_primitives s COpWearLevel = Some prims ->
    forallb volatile_prim (firstn k prims) = true \/ k >= length prims ->
    recovers_to h (recovered_at s prims k).
Proof.
  intros h s s' prims k Hinv HCR Hstep Hprims Hk.
  destruct Hk as [Hvol | Hk].
  - apply volatile_prefix_covered; assumption.
  - replace h with (abs_step h COpWearLevel) by reflexivity.
    apply final_point_covered with (s' := s'); assumption.
Qed.

(* Writes: the opening barrier (and any earlier volatile prefix) recovers to
   the pre-state [h]; the final point recovers to the updated device
   [abs_write h a p d].  The points in between lose the sector (Section 6). *)
Theorem write_crash_points :
  forall h s a p d s' prims k,
    ftl_invariant s ->
    CR h s ->
    step s (COpWrite a p d) = Some s' ->
    op_primitives s (COpWrite a p d) = Some prims ->
    (forallb volatile_prim (firstn k prims) = true ->
       recovers_to h (recovered_at s prims k)) /\
    (k >= length prims ->
       recovers_to (abs_write h a p d) (recovered_at s prims k)).
Proof.
  intros h s a p d s' prims k Hinv HCR Hstep Hprims.
  split.
  - intros Hvol. apply volatile_prefix_covered; assumption.
  - intros Hk.
    replace (abs_write h a p d) with (abs_step h (COpWrite a p d)) by reflexivity.
    apply final_point_covered with (s' := s'); assumption.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 6: the two uncovered crash points
   ══════════════════════════════════════════════════════════════════════ *)

(* Relocation: a live page copied to the destination but not yet made
   redundant leaves two live pages, at different physical pages, stamped with
   the same logical page.  No recovered mapping satisfies Inv4. *)
Theorem duplicate_stamp_breaks_Inv4 :
  forall s a q b1 p1 b2 p2 d1 d2,
    (b1, p1) <> (b2, p2) ->
    p1 < pages_per_block ->
    p2 < pages_per_block ->
    page_state s b1 p1 = PS_Valid d1 ->
    page_lpa (page_meta s b1 p1) = Some (a, q) ->
    page_state s b2 p2 = PS_Valid d2 ->
    page_lpa (page_meta s b2 p2) = Some (a, q) ->
    ~ Inv4 (recover (crash s)).
Proof.
  intros s a q b1 p1 b2 p2 d1 d2 Hne Hp1 Hp2 Hps1 Hlpa1 Hps2 Hlpa2 HInv4.
  rewrite recover_crash in HInv4.
  assert (Hr1 : reclaimb s b1 = false)
    by exact (live_not_reclaimed s b1 (block_liveb_of_valid s b1 p1 d1 Hp1 Hps1)).
  assert (Hr2 : reclaimb s b2 = false)
    by exact (live_not_reclaimed s b2 (block_liveb_of_valid s b2 p2 d2 Hp2 Hps2)).
  assert (Hm1 : l2p_map (recover s) a q = Some (mkPhysAddr b1 p1)).
  { apply HInv4 with (d := d1); cbn; rewrite ?Hr1; assumption. }
  assert (Hm2 : l2p_map (recover s) a q = Some (mkPhysAddr b2 p2)).
  { apply HInv4 with (d := d2); cbn; rewrite ?Hr2; assumption. }
  rewrite Hm1 in Hm2. injection Hm2 as Hb Hp. apply Hne. rewrite Hb, Hp. reflexivity.
Qed.

(* A tag write changes neither page contents nor stamps. *)
Lemma set_page_tag_at_page_state_eq :
  forall s pa tag b' p',
    page_state (set_page_tag_at s pa tag) b' p' = page_state s b' p'.
Proof. intros. unfold set_page_tag_at. reflexivity. Qed.

Lemma set_page_tag_at_page_lpa_eq :
  forall s pa tag b' p',
    page_lpa (page_meta (set_page_tag_at s pa tag) b' p') = page_lpa (page_meta s b' p').
Proof.
  intros s pa tag b' p'. unfold set_page_tag_at. cbn. unfold set_page_meta.
  destruct (andb (Nat.eqb b' (pa_block pa)) (Nat.eqb p' (pa_page pa))) eqn:E;
    [| reflexivity].
  apply andb_true_iff in E. destruct E as [E1 E2].
  apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. subst. reflexivity.
Qed.

(* The mid-copy crash point has exactly that shape: programming the copy of a
   live page stamped (a, q_l) at the destination, while the source still holds
   it.  The tag write that may follow does not change the picture. *)
Theorem copy_program_point_unrecoverable :
  forall s a ql src dst q d0 d tag,
    src <> dst ->
    q < pages_per_block ->
    page_state s src q = PS_Valid d0 ->
    page_lpa (page_meta s src q) = Some (a, ql) ->
    ~ Inv4 (recover (crash
              (apply_primitive s (PrimProgram (mkPhysAddr dst q) d (Some d) (Some (a, ql)))))) /\
    ~ Inv4 (recover (crash
              (apply_primitive
                 (apply_primitive s (PrimProgram (mkPhysAddr dst q) d (Some d) (Some (a, ql))))
                 (PrimSetTag (mkPhysAddr dst q) tag)))).
Proof.
  intros s a ql src dst q d0 d tag Hne Hq Hps Hlpa.
  assert (Hne' : Nat.eqb src dst = false) by (apply Nat.eqb_neq; exact Hne).
  assert (Hphys : (src, q) <> (dst, q)) by (intros HC; injection HC as HC; exact (Hne HC)).
  (* the programmed destination page after PrimProgram *)
  set (sp := apply_primitive s (PrimProgram (mkPhysAddr dst q) d (Some d) (Some (a, ql)))).
  assert (Hdst_ps : page_state sp dst q = PS_Valid d).
  { unfold sp. cbn. unfold set_page_state. rewrite !Nat.eqb_refl. reflexivity. }
  assert (Hdst_lpa : page_lpa (page_meta sp dst q) = Some (a, ql)).
  { unfold sp. cbn. unfold set_page_meta. rewrite !Nat.eqb_refl. reflexivity. }
  assert (Hsrc_ps : page_state sp src q = PS_Valid d0).
  { unfold sp. cbn. unfold set_page_state.
    rewrite (proj2 (andb_false_iff _ _) (or_introl Hne')). exact Hps. }
  assert (Hsrc_lpa : page_lpa (page_meta sp src q) = Some (a, ql)).
  { unfold sp. cbn. unfold set_page_meta.
    rewrite (proj2 (andb_false_iff _ _) (or_introl Hne')). exact Hlpa. }
  split.
  - apply duplicate_stamp_breaks_Inv4 with
      (a := a) (q := ql) (b1 := src) (p1 := q) (b2 := dst) (p2 := q)
      (d1 := d0) (d2 := d); assumption.
  - (* after the following tag write, contents and stamps are unchanged *)
    set (st := apply_primitive sp (PrimSetTag (mkPhysAddr dst q) tag)).
    assert (Hst : st = set_page_tag_at sp (mkPhysAddr dst q) tag).
    { unfold st.
      change (apply_primitive sp (PrimSetTag (mkPhysAddr dst q) tag))
        with (match page_state sp dst q with
              | PS_Valid _ => set_page_tag_at sp (mkPhysAddr dst q) tag
              | _ => sp end).
      rewrite Hdst_ps. reflexivity. }
    apply duplicate_stamp_breaks_Inv4 with
      (a := a) (q := ql) (b1 := src) (p1 := q) (b2 := dst) (p2 := q)
      (d1 := d0) (d2 := d); try assumption.
    + rewrite Hst, set_page_tag_at_page_state_eq. exact Hsrc_ps.
    + rewrite Hst, set_page_tag_at_page_lpa_eq. exact Hsrc_lpa.
    + rewrite Hst, set_page_tag_at_page_state_eq. exact Hdst_ps.
    + rewrite Hst, set_page_tag_at_page_lpa_eq. exact Hdst_lpa.
Qed.

(* Out-of-place update: a [PrimInvalidate] stales the old page and drops the
   forward mapping before the new datum is programmed.  A power loss at that
   point leaves the sector gone -- the recovered device reads [None].  The
   abstract device of Refinement has no "sector lost" transition, so this
   crash point is not covered by the design of the expansion; a crash-safe
   expansion would program the new page before staling the old one and resolve
   the transient duplicate at recovery. *)
Lemma torn_write_loses_sector :
  forall s a p old,
    ftl_invariant s ->
    l2p_map s a p = Some old ->
    read_page (recover (crash (apply_primitive s (PrimInvalidate old)))) a p = None.
Proof.
  intros s a p old Hinv Hmap.
  destruct Hinv as (_&_&_&_&_&I3&I4&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I22&_&_&_&_).
  destruct (I22 a p old Hmap) as [d0 Hold_valid].
  pose proof (I3 a p old d0 Hmap Hold_valid) as Hold_stamp.
  assert (Hsi : apply_primitive s (PrimInvalidate old)
                = unmap (invalidate_at s old) a p).
  { cbn [apply_primitive]. rewrite Hold_stamp. reflexivity. }
  rewrite Hsi, recover_crash. unfold read_page.
  destruct (l2p_map (recover (unmap (invalidate_at s old) a p)) a p) as [pa'|] eqn:Hrec;
    [| reflexivity].
  exfalso.
  apply recover_l2p_found in Hrec.
  destruct Hrec as [_ [_ [[d' Hvs] Hlpas]]].
  set (b' := pa_block pa') in *. set (q' := pa_page pa') in *.
  change (page_state (unmap (invalidate_at s old) a p) b' q')
    with (set_page_state (page_state s) (pa_block old) (pa_page old) PS_Invalid b' q')
    in Hvs.
  change (page_lpa (page_meta (unmap (invalidate_at s old) a p) b' q'))
    with (page_lpa (set_page_meta (page_meta s) (pa_block old) (pa_page old)
                                  empty_page_meta b' q'))
    in Hlpas.
  unfold set_page_state in Hvs. unfold set_page_meta in Hlpas.
  destruct (andb (Nat.eqb b' (pa_block old)) (Nat.eqb q' (pa_page old))) eqn:Heq.
  - discriminate Hvs.
  - pose proof (I4 a p b' q' d' Hvs Hlpas) as Hmap'.
    rewrite Hmap in Hmap'. injection Hmap' as Ho.
    assert (Hob1 : pa_block old = b') by (rewrite Ho; reflexivity).
    assert (Hob2 : pa_page old = q') by (rewrite Ho; reflexivity).
    rewrite Hob1, Hob2, !Nat.eqb_refl in Heq. discriminate Heq.
Qed.

End CrashPoints.
