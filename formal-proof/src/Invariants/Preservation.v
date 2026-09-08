(* Preservation.v: the operation-level and trace-level guarantees.

   Every per-operation preservation lemma is proved elsewhere, one file per
   operation family.  This file does the composition: every operation
   preserves the invariant, and therefore so does every trace. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.
Require Import Invariants.WritePreservation.
Require Import Invariants.GCPreservation.

Import ListNotations.

Section Preservation.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* Theorem 1, over all six operations with no operation singled out. *)
Theorem step_preserves_invariant :
  forall s op s',
    ftl_invariant s ->
    step s op = Some s' ->
    ftl_invariant s'.
Proof.
  intros s op s' Hinv Hstep.
  destruct op as [a p | a p d | a p | a p tag | |].
  - exact (read_preserves_invariant s a p s' Hinv Hstep).
  - exact (@write_preserves_invariant pages_per_block_gt0 s a p d s' Hinv Hstep).
  - exact (@invalidate_preserves_invariant pages_per_block_gt0 s a p s' Hinv Hstep).
  - exact (@set_tag_preserves_invariant pages_per_block_gt0 s a p tag s' Hinv Hstep).
  - exact (gc_preserves_invariant s s' Hinv Hstep).
  - exact (wear_level_preserves_invariant s s' Hinv Hstep).
Qed.

(* Traces: a valid execution never leaves the invariant. *)
Theorem exec_preserves_invariant :
  forall ops s s',
    ftl_invariant s ->
    exec s ops = Some s' ->
    ftl_invariant s'.
Proof.
  induction ops as [|op tl IH]; intros s s' Hinv Hexec.
  - cbn in Hexec. inversion Hexec; subst. exact Hinv.
  - cbn in Hexec.
    destruct (step s op) as [s1|] eqn:Hstep; [|discriminate].
    exact (IH s1 s' (step_preserves_invariant s op s1 Hinv Hstep) Hexec).
Qed.

(* Every state reachable from a freshly formatted device satisfies all 29
   clauses.  This is the end-to-end operation-level guarantee. *)
Theorem reachable_states_satisfy_invariant :
  forall ops s',
    exec empty_state ops = Some s' ->
    ftl_invariant s'.
Proof.
  intros ops s' Hexec.
  exact (exec_preserves_invariant ops empty_state s' (@empty_state_invariant pages_per_block_gt0) Hexec).
Qed.

End Preservation.

(* Geometry hypothesis discharged. *)
Theorem step_preserves_invariant_closed :
  forall s op s',
    ftl_invariant s ->
    step s op = Some s' ->
    ftl_invariant s'.
Proof. exact (@step_preserves_invariant pages_per_block_pos). Qed.

Theorem reachable_states_satisfy_invariant_closed :
  forall ops s',
    exec empty_state ops = Some s' ->
    ftl_invariant s'.
Proof. exact (@reachable_states_satisfy_invariant pages_per_block_pos). Qed.
