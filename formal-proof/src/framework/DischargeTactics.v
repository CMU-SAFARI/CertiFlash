(* DischargeTactics.v: proof automation for the five [CUSTOM_FTL]
   hypotheses, page-granular, plus a measured demonstration on DFTL.

   ══════════════════════════════════════════════════════════════════════
   THE HONEST FIGURE
   ══════════════════════════════════════════════════════════════════════

   DFTL's five hypotheses, discharged twice over the same definitions --
   manually in [dftl/DFTL.v], and again in [DFTLAutoFTL] below with this
   pack.  Counting lines strictly between [Proof.] and [Qed.], blank lines
   excluded; the second column of the manual count also excludes in-proof
   comment lines, so that neither measurement is flattered by prose.

     hypothesis                          without pack     with pack
     ------------------------------------------------------------------
     invariants_preserved_on_write            8 (8)            2
     invariants_preserved_on_gc               6 (6)            2
     invariants_preserved_on_wear_level       6 (6)            2
     read_after_write_correctness             9 (9)            4
     isolation_property                      35 (31)           5
     ------------------------------------------------------------------
     TOTAL                                   64 (60)          15

   And the number that must not be dropped:

     FTL-specific glue the pack needs to be applicable at all
       ([dftl_ops], [dftl_reads], [dftl_write_step],
        [dftl_to_read_page], marked GLUE-BEGIN/GLUE-END below)    33

   So the honest comparison for DFTL's designer is

     64 lines of proof script      versus      15 script + 33 glue = 48.

   Not 64:15.  The ratio that hides the glue is 4.3x; the ratio that does
   not is 1.3x.  Quoting the first would be a lie about what a designer
   actually writes.

   Two further numbers, so that nothing is hidden by scope:

     - The pack itself (PART A) is 80 lines.  Those are written once and
       are FTL-independent: six [Ltac]s and two lemmas about [step] and
       the framework's refinement relation [CR].  They are not charged to
       DFTL, but they are also not free -- they are the framework's cost.

     - DFTL's supporting development (PARTS 0-5 of [dftl/DFTL.v]) is
       474 non-comment lines and the pack removes exactly zero of them.
       That development is the CMT bookkeeping: [cmt_find], [cmt_remove],
       eviction, write-back, resync, and the four clauses of [dftl_ok]
       with their preservation proofs.  It is not a recurring pattern.
       It is what a demand-paged FTL *is*, and no tactic pack can know it.

   ══════════════════════════════════════════════════════════════════════
   WHERE THE PATTERNS STOP
   ══════════════════════════════════════════════════════════════════════

   Hypotheses 1-3 automate cleanly and completely: after the designer's
   operation names are unfolded, each is [ftl_preservation] -- split on
   whether the device [step] succeeded, and in the success branch hand
   the goal to [step_preserves_invariant_closed].  8/6/6 lines become
   2/2/2, and one of those two lines is the [intros].  This is the
   pattern the interface was designed to make cheap, and it is cheap.

   Hypotheses 4 and 5 automate to [Qed.] as well, but they are where 24
   of the 33 glue lines go, and the reason is specific and worth naming:

     (a) Readiness is the designer's predicate, not the framework's.
         DFTL's [write_lands] is a statement about [alloc_page] on a
         state derived from [l2p_map]; the framework has no lemma
         "readiness implies the step succeeds" because it does not know
         what readiness the designer chose.  [dftl_write_step] (10 lines)
         supplies that bridge via DFTL's own [write_lands_step].

     (b) [dftl_write] is a *two-level* operation.  It advances the device
         by one [step] and then admits an entry into the CMT, so
         [ds_model (dftl_write s a p d)] is not convertible to the step's
         result -- it is only provably equal to it, via DFTL's
         [dftl_write_model], and only once the step is known to succeed.
         Every framework lemma about the post-state has to be transported
         across that equation, and in the isolation proof it has to be
         transported twice, in opposite directions (the second write's
         readiness is stated over the designer's post-state; the second
         write's [step] is stated over the device's).  [dftl_to_read_page]
         (14 lines) is that transport.

   Both are genuinely FTL-specific.  An FTL whose [user_to_model] is the
   identity, or whose write is a bare [step], pays neither: [ModelFTL] in
   [framework/Composition.v] is exactly that case, and the orthogonal
   extensions built on it pay zero.  The recurring pattern stops at the
   point where the designer's operation stops being the device's
   operation.  DFTL is on the far side of that line, which is why it is
   the right thing to measure against.

   ══════════════════════════════════════════════════════════════════════

   No admitted lemmas, no [admit], no axiom declarations, and no parameters, variables
   or hypotheses introduced here; the
   re-proof lives in [DFTLAutoFTL] alongside [DFTLConcreteFTL], reuses
   the same definitions, and is checked against the manual statements by
   the five theorems at the end of the file.  [Print Assumptions] on the
   certificate reports "Closed under the global context". *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import core.CustomFTLInterface.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.
Require Import Refinement.
Require Import dftl.DFTL.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART A -- the pack
   ══════════════════════════════════════════════════════════════════════ *)

(* ── A.0  case analysis on "did the device step succeed?" ─────────── *)

Ltac ftl_case_steps :=
  repeat match goal with
  | |- context [ match ?x with Some _ => _ | None => _ end ] =>
      let E := fresh "Hcase" in destruct x eqn:E
  | |- context [ match ?x with (_, _) => _ end ] => destruct x
  end.

(* ── A.1  reduce a designer operation to its effect on [FTLState] ─── *)

Ltac ftl_apply_step_preservation :=
  match goal with
  | Hstep : step ?m ?op = Some ?m', Hinv : ftl_invariant ?m
    |- ftl_invariant _ =>
      exact (step_preserves_invariant_closed m op m' Hinv Hstep)
  end.

Ltac ftl_preservation :=
  ftl_case_steps;
  solve [ assumption | ftl_apply_step_preservation | eauto ].

(* ── A.2  push a read goal through a projection refinement map ────── *)

Ltac ftl_finish_read :=
  unfold read_page in *;
  repeat match goal with
  | H : l2p_map ?m ?a ?p = Some _ |- context [ l2p_map ?m ?a ?p ] => rewrite H
  | H : page_state ?m ?b ?q = PS_Valid _ |- context [ page_state ?m ?b ?q ] =>
      rewrite H
  end;
  reflexivity.

(* ── A.3  split a compound readiness precondition ─────────────────── *)

Ltac ftl_split_ready :=
  repeat match goal with
  | H : _ /\ _ |- _ =>
      lazymatch type of H with
      | ftl_invariant _ => fail
      | _ => destruct H
      end
  | H : @ex _ _ |- _ => destruct H
  end.

(* ── A.4  what a write leaves behind, from the framework's [CR] ───── *)

Lemma write_backs_datum : forall m m' a p d,
  ftl_invariant m ->
  step m (COpWrite a p d) = Some m' ->
  backs m' a p d.
Proof.
  intros m m' a p d Hinv Hstep.
  assert (HCR : CR empty_abs m) by (intros a0 p0 d0 H; discriminate H).
  pose proof (@write_preserves_CR pages_per_block_pos
                empty_abs m m' a p d Hinv HCR Hstep) as HCR'.
  exact (HCR' a p d (abs_write_here empty_abs a p d)).
Qed.

Lemma two_writes_back_first : forall m m1 m2 a1 p1 d1 a2 p2 d2,
  (a1 <> a2 \/ p1 <> p2) ->
  ftl_invariant m ->
  step m (COpWrite a1 p1 d1) = Some m1 ->
  step m1 (COpWrite a2 p2 d2) = Some m2 ->
  backs m2 a1 p1 d1.
Proof.
  intros m m1 m2 a1 p1 d1 a2 p2 d2 Hne Hinv H1 H2.
  assert (HCR0 : CR empty_abs m) by (intros a0 p0 d0 H; discriminate H).
  pose proof (@write_preserves_CR pages_per_block_pos
                empty_abs m m1 a1 p1 d1 Hinv HCR0 H1) as HCR1.
  assert (Hinv1 : ftl_invariant m1)
    by exact (step_preserves_invariant_closed _ _ _ Hinv H1).
  pose proof (@write_preserves_CR pages_per_block_pos
                (abs_write empty_abs a1 p1 d1) m1 m2 a2 p2 d2 Hinv1 HCR1 H2)
    as HCR2.
  apply HCR2.
  rewrite abs_write_other by exact Hne.
  apply abs_write_here.
Qed.

Ltac ftl_write_chain_backs :=
  match goal with
  | Hne : (?a1 <> ?a2 \/ ?p1 <> ?p2), Hinv : ftl_invariant ?m,
    H1 : step ?m (COpWrite ?a1 ?p1 ?d1) = Some ?m1,
    H2 : step ?m1 (COpWrite ?a2 ?p2 ?d2) = Some ?m2 |- _ =>
      let pa := fresh "pa" in let Hm := fresh "Hmap" in
      let Hs := fresh "Hps" in
      destruct (two_writes_back_first m m1 m2 a1 p1 d1 a2 p2 d2
                  Hne Hinv H1 H2) as [pa [Hm Hs]]
  | Hinv : ftl_invariant ?m,
    H1 : step ?m (COpWrite ?a ?p ?d) = Some ?m1 |- _ =>
      let pa := fresh "pa" in let Hm := fresh "Hmap" in
      let Hs := fresh "Hps" in
      destruct (write_backs_datum m m1 a p d Hinv H1) as [pa [Hm Hs]]
  end.

(* ══════════════════════════════════════════════════════════════════════
   PART B -- the measured demonstration: DFTL, re-proved
   ══════════════════════════════════════════════════════════════════════ *)

Module DFTLAutoFTL <: CUSTOM_FTL.

  Definition user_state := DFTLState.

  Definition user_read       := dftl_read.
  Definition user_write      := dftl_write.
  Definition user_gc         := dftl_gc.
  Definition user_wear_level := dftl_wear_level.

  Definition user_to_model (s : DFTLState) : FTLState := ds_model s.

  Definition user_write_ready := dftl_write_ready.

  Definition admissible (s : user_state) (a : Addr) (p : Page) : Prop :=
    a < addr_space /\ p < pages_per_block /\
    (exists t, addr_tenant (user_to_model s) a = Some t) /\
    (exists ns, addr_namespace (user_to_model s) a = Some ns).

  Definition security_contract (m : FTLState) : Prop := ftl_invariant m.

  (* ── the FTL-specific glue (GLUE-BEGIN) ─────────────────────────── *)
  Ltac dftl_ops :=
    unfold security_contract, user_to_model, user_write, user_gc,
           user_wear_level, dftl_write, dftl_gc, dftl_wear_level in *.
  Ltac dftl_reads :=
    unfold security_contract, user_to_model, user_read, user_write,
           user_write_ready, dftl_write_ready, admissible in *.
  Ltac dftl_write_step a p d :=
    match goal with
    | Hl : write_lands ?m a p, Ha : a < addr_space, Hp : p < pages_per_block
      |- _ =>
        let m' := fresh "m'" in let H := fresh "Hstep" in
        destruct (write_lands_step m a p d Ha Hp Hl) as [m' H];
        repeat match goal with
        | Hq : write_lands (ds_model (dftl_write ?s a p d)) ?x ?y |- _ =>
            rewrite (dftl_write_model s a p d m' H) in Hq
        end
    end.
  Ltac dftl_to_read_page :=
    match goal with
    | |- context [ dftl_read ?s ?a ?p ] =>
        rewrite (dftl_read_is_read_page s a p
          ltac:(solve [ assumption | repeat apply dftl_ok_write; assumption ]))
    end;
    repeat match goal with
    | H : step (ds_model ?X) (COpWrite ?a ?p ?d) = Some ?m
      |- context [ ds_model (dftl_write ?X ?a ?p ?d) ] =>
        rewrite (dftl_write_model X a p d m H)
    | Hs : step (ds_model ?X) (COpWrite ?a0 ?p0 ?d0) = Some ?m0,
      H : step ?m0 (COpWrite ?a ?p ?d) = Some ?m
      |- context [ ds_model (dftl_write (dftl_write ?X ?a0 ?p0 ?d0) ?a ?p ?d) ] =>
        rewrite (dftl_write_model (dftl_write X a0 p0 d0) a p d m
          ltac:(rewrite (dftl_write_model X a0 p0 d0 m0 Hs); exact H))
    end.
  (* ── (GLUE-END) ─────────────────────────────────────────────────── *)

  Lemma invariants_preserved_on_write :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_write s a p d)).
  Proof.
    intros s a p d _ _ Hinv.
    dftl_ops. ftl_preservation.
  Qed.

  Lemma invariants_preserved_on_gc :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_gc s)).
  Proof.
    intros s Hinv.
    dftl_ops. ftl_preservation.
  Qed.

  Lemma invariants_preserved_on_wear_level :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_wear_level s)).
  Proof.
    intros s Hinv.
    dftl_ops. ftl_preservation.
  Qed.

  Lemma read_after_write_correctness :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      user_read (user_write s a p d) a p = Some d.
  Proof.
    intros s a p d Hadm Hrdy Hinv.
    dftl_reads. ftl_split_ready.
    dftl_write_step a p d. ftl_write_chain_backs.
    dftl_to_read_page. ftl_finish_read.
  Qed.

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
    intros s a1 p1 a2 p2 d1 d2 Hne Hadm1 Hadm2 Hrdy1 Hrdy2 Hinv.
    dftl_reads. ftl_split_ready.
    dftl_write_step a1 p1 d1. dftl_write_step a2 p2 d2.
    ftl_write_chain_backs.
    dftl_to_read_page. ftl_finish_read.
  Qed.

End DFTLAutoFTL.

Module DFTLAutoCertificate := Validator DFTLAutoFTL.

(* ══════════════════════════════════════════════════════════════════════
   PART C -- the re-proof is of the *same* statements
   ══════════════════════════════════════════════════════════════════════

   A tactic pack that shrinks a proof by weakening what is proved would
   be worthless.  Each theorem below states the hypothesis in the manual
   module's own vocabulary ([DFTLConcreteFTL.*]) and discharges it with
   the automated proof.  [exact] checks up to conversion, so these five
   pass only if the two ascriptions really do state the same thing. *)

Theorem auto_discharges_manual_hyp1 :
  forall s a p d,
    DFTLConcreteFTL.admissible s a p ->
    DFTLConcreteFTL.user_write_ready s a p ->
    DFTLConcreteFTL.security_contract (DFTLConcreteFTL.user_to_model s) ->
    DFTLConcreteFTL.security_contract
      (DFTLConcreteFTL.user_to_model (DFTLConcreteFTL.user_write s a p d)).
Proof. exact DFTLAutoFTL.invariants_preserved_on_write. Qed.

Theorem auto_discharges_manual_hyp2 :
  forall s,
    DFTLConcreteFTL.security_contract (DFTLConcreteFTL.user_to_model s) ->
    DFTLConcreteFTL.security_contract
      (DFTLConcreteFTL.user_to_model (DFTLConcreteFTL.user_gc s)).
Proof. exact DFTLAutoFTL.invariants_preserved_on_gc. Qed.

Theorem auto_discharges_manual_hyp3 :
  forall s,
    DFTLConcreteFTL.security_contract (DFTLConcreteFTL.user_to_model s) ->
    DFTLConcreteFTL.security_contract
      (DFTLConcreteFTL.user_to_model (DFTLConcreteFTL.user_wear_level s)).
Proof. exact DFTLAutoFTL.invariants_preserved_on_wear_level. Qed.

Theorem auto_discharges_manual_hyp4 :
  forall s a p d,
    DFTLConcreteFTL.admissible s a p ->
    DFTLConcreteFTL.user_write_ready s a p ->
    DFTLConcreteFTL.security_contract (DFTLConcreteFTL.user_to_model s) ->
    DFTLConcreteFTL.user_read (DFTLConcreteFTL.user_write s a p d) a p = Some d.
Proof. exact DFTLAutoFTL.read_after_write_correctness. Qed.

Theorem auto_discharges_manual_hyp5 :
  forall s a1 p1 a2 p2 d1 d2,
    (a1 <> a2 \/ p1 <> p2) ->
    DFTLConcreteFTL.admissible s a1 p1 ->
    DFTLConcreteFTL.admissible (DFTLConcreteFTL.user_write s a1 p1 d1) a2 p2 ->
    DFTLConcreteFTL.user_write_ready s a1 p1 ->
    DFTLConcreteFTL.user_write_ready
      (DFTLConcreteFTL.user_write s a1 p1 d1) a2 p2 ->
    DFTLConcreteFTL.security_contract (DFTLConcreteFTL.user_to_model s) ->
    DFTLConcreteFTL.user_read
      (DFTLConcreteFTL.user_write
         (DFTLConcreteFTL.user_write s a1 p1 d1) a2 p2 d2) a1 p1 = Some d1.
Proof. exact DFTLAutoFTL.isolation_property. Qed.

Check DFTLAutoCertificate.custom_ftl_security_suite.
Print Assumptions DFTLAutoCertificate.custom_ftl_security_suite.
Print Assumptions DFTLAutoFTL.isolation_property.
Print Assumptions auto_discharges_manual_hyp5.
