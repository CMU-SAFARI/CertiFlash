(* CrashRefinement.v: crash refinement at operation boundaries, over the
   page-granular refinement of Refinement / Specs.

   Refinement relates the device to the page-granular abstract device
   [AbsDev = Addr -> Page -> option Data] through [CR], and Specs proves that
   every [step] is simulated by [abs_step].  This file adds a third kind of
   event, a power loss followed by the start-up recovery of
   [Invariants.CrashRecovery], and shows that it is a stuttering step for the
   abstract device:

     CR h s  ->  CR h (recover (crash s))          [crash_recover_preserves_CR]

   The trace-level theorem [refines_with_crashes] then admits crash events
   anywhere between operations: the abstract device executes the operations of
   the trace and never sees the crashes, and the invariant survives every
   event.

   A power loss *inside* an operation's instruction expansion is the subject
   of core/CrashPoints.v.

   One remark on the trace theorem: it takes the success of the concrete run
   ([exec_events s evs = Some s']) as a hypothesis, exactly as
   Specs.exec_simulates takes [exec s ops = Some s'].  Whether a write can
   allocate is a refinement/readiness concern discharged in Refinement, not a
   crash-recovery one; a crash never causes a later operation to fail, and
   the recovered state satisfies every clause an operation needs of its start
   state. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.
Require Import Refinement.
Require Import Specs.
Require Import Invariants.CrashRecovery.

Import ListNotations.

Section CrashRefinement.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* ══════════════════════════════════════════════════════════════════════
   Section 1: crash and recovery preserve the refinement relation
   ══════════════════════════════════════════════════════════════════════ *)

Theorem crash_recover_preserves_CR :
  forall h s,
    ftl_invariant s ->
    CR h s ->
    CR h (recover (crash s)).
Proof.
  intros h s Hinv HCR a p d Hread.
  destruct (HCR a p d Hread) as [pa [Hmap Hps]].
  exists pa. split.
  - apply l2p_reconstruction_complete with (d := d); assumption.
  - rewrite recover_crash. cbn.
    (* the block is live, so recovery does not reclaim it *)
    destruct Hinv as (_&HWF1&_&HInv1&_).
    pose proof (HInv1 a p pa Hmap) as [_ [Hpp _]].
    rewrite (live_not_reclaimed s (pa_block pa)
               (block_liveb_of_valid s (pa_block pa) (pa_page pa) d Hpp Hps)).
    exact Hps.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 2: traces with crash events
   ══════════════════════════════════════════════════════════════════════ *)

Inductive cdisk_event :=
  | CEvOp (op : COp)
  | CEvCrash.

(* What the abstract device sees: the operations, and nothing else. *)
Fixpoint events_ops (evs : list cdisk_event) : list COp :=
  match evs with
  | [] => []
  | CEvOp op :: evs' => op :: events_ops evs'
  | CEvCrash :: evs' => events_ops evs'
  end.

(* What the concrete device does: a crash event is a power loss followed by
   start-up recovery. *)
Definition step_event (s : FTLState) (e : cdisk_event) : option FTLState :=
  match e with
  | CEvOp op => step s op
  | CEvCrash => Some (recover (crash s))
  end.

Fixpoint exec_events (s : FTLState) (evs : list cdisk_event) : option FTLState :=
  match evs with
  | [] => Some s
  | e :: evs' =>
      match step_event s e with
      | Some s' => exec_events s' evs'
      | None => None
      end
  end.

(* A crash event is a stuttering step for the abstract device: the recovered
   state refines the same abstract device and again satisfies the invariant. *)
Theorem crash_event_stutters :
  forall h s,
    ftl_invariant s ->
    CR h s ->
    exists s',
      step_event s CEvCrash = Some s' /\
      CR h s' /\ ftl_invariant s'.
Proof.
  intros h s Hinv HCR.
  exists (recover (crash s)).
  split; [reflexivity |].
  split; [apply crash_recover_preserves_CR; assumption |].
  apply recover_preserves_invariant; assumption.
Qed.

(* Executing a list of events, with crashes interleaved, refines the abstract
   device running the operations alone, and the invariant survives every
   event.  The concrete run is assumed to succeed, exactly as in
   Specs.exec_simulates. *)
Theorem refines_with_crashes :
  forall evs h s s',
    ftl_invariant s ->
    CR h s ->
    exec_events s evs = Some s' ->
    CR (abs_exec h (events_ops evs)) s' /\ ftl_invariant s'.
Proof.
  induction evs as [| e evs IH]; intros h s s' Hinv HCR Hexec.
  - cbn in Hexec. injection Hexec as <-. cbn. split; assumption.
  - destruct e as [op |].
    + cbn in Hexec |- *.
      destruct (step s op) as [s1|] eqn:Hstep; [| discriminate].
      apply (IH (abs_step h op) s1 s').
      * exact (@step_preserves_invariant pages_per_block_gt0 s op s1 Hinv Hstep).
      * exact (@step_simulates pages_per_block_gt0 h s op s1 Hinv HCR Hstep).
      * exact Hexec.
    + cbn in Hexec |- *.
      (* step_event s CEvCrash = Some (recover (crash s)) *)
      apply (IH h (recover (crash s)) s').
      * apply recover_preserves_invariant; assumption.
      * apply crash_recover_preserves_CR; assumption.
      * exact Hexec.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   Section 3: the read-only view under repeated crashes
   ══════════════════════════════════════════════════════════════════════ *)

Fixpoint iter_crash (n : nat) (s : FTLState) : FTLState :=
  match n with
  | O => s
  | S n' => recover (crash (iter_crash n' s))
  end.

Lemma iter_crash_secure :
  forall n s,
    ftl_invariant s ->
    in_geometry s ->
    ftl_invariant (iter_crash n s) /\ in_geometry (iter_crash n s).
Proof.
  intros n s Hinv Hgeo.
  induction n as [| n [IHi IHg]]; [auto |].
  change (iter_crash (S n) s) with (recover (crash (iter_crash n s))).
  split.
  - apply recover_preserves_invariant; assumption.
  - apply recover_preserves_in_geometry; assumption.
Qed.

Corollary crashes_preserve_reads :
  forall s n a p,
    ftl_invariant s ->
    in_geometry s ->
    read_page (iter_crash n s) a p = read_page s a p.
Proof.
  intros s n a p Hinv Hgeo.
  induction n as [| n IH]; [reflexivity |].
  change (iter_crash (S n) s) with (recover (crash (iter_crash n s))).
  destruct (iter_crash_secure n s Hinv Hgeo) as [Hinv_n Hgeo_n].
  rewrite read_page_after_recovery; assumption.
Qed.

End CrashRefinement.
