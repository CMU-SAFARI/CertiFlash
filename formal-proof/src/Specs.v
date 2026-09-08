(* Specs.v: the whole-trace guarantee.

   Per-operation simulation lives in [Refinement], per-operation
   preservation in [Invariants.Preservation].  A trace needs both at once,
   because the simulation cases for the maintenance operations are
   conditioned on the invariant holding at the state they start from. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.
Require Import Refinement.

Import ListNotations.

Section Specs.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* The abstract effect of an operation.  Read and set-tag do not change what
   the host can observe; garbage collection and wear levelling move data
   without changing it. *)
Definition abs_step (h : AbsDev) (op : COp) : AbsDev :=
  match op with
  | COpRead _ _ => h
  | COpWrite a p d => abs_write h a p d
  | COpInvalidate a p => abs_invalidate h a p
  | COpSetTag _ _ _ => h
  | COpGC => h
  | COpWearLevel => h
  end.

Fixpoint abs_exec (h : AbsDev) (ops : list COp) : AbsDev :=
  match ops with
  | [] => h
  | op :: tl => abs_exec (abs_step h op) tl
  end.

Lemma step_simulates :
  forall h s op s',
    ftl_invariant s -> CR h s ->
    step s op = Some s' ->
    CR (abs_step h op) s'.
Proof.
  intros h s op s' Hinv HR Hstep.
  destruct op as [a p | a p d | a p | a p tag | |]; cbn [abs_step].
  - exact (read_preserves_CR h s s' a p HR Hstep).
  - exact (@write_preserves_CR pages_per_block_gt0 h s s' a p d Hinv HR Hstep).
  - exact (invalidate_preserves_CR h s s' a p Hinv HR Hstep).
  - exact (set_tag_preserves_CR h s s' a p tag HR Hstep).
  - exact (@gc_preserves_CR pages_per_block_gt0 h s s' Hinv HR Hstep).
  - exact (@wear_level_preserves_CR pages_per_block_gt0 h s s' Hinv HR Hstep).
Qed.

(* Whole-trace simulation.  The invariant travels alongside because the
   maintenance cases consume it. *)
Theorem exec_simulates :
  forall ops h s s',
    ftl_invariant s -> CR h s ->
    exec s ops = Some s' ->
    CR (abs_exec h ops) s' /\ ftl_invariant s'.
Proof.
  induction ops as [|op tl IH]; intros h s s' Hinv HR Hexec.
  - cbn in Hexec |- *. inversion Hexec; subst. split; assumption.
  - cbn in Hexec |- *.
    destruct (step s op) as [s1|] eqn:Hstep; [|discriminate].
    exact (IH (abs_step h op) s1 s'
             (@step_preserves_invariant pages_per_block_gt0 s op s1 Hinv Hstep)
             (step_simulates h s op s1 Hinv HR Hstep) Hexec).
Qed.

(* The end-to-end statement: from a freshly formatted device, every valid
   trace lands in a state that satisfies all 29 conjuncts and that refines the
   idealized block device's own run of the same trace. *)
Theorem device_refines_idealized_block_device :
  forall ops s',
    exec empty_state ops = Some s' ->
    CR (abs_exec empty_abs ops) s' /\ ftl_invariant s'.
Proof.
  intros ops s' Hexec.
  exact (exec_simulates ops empty_abs empty_state s'
           (@empty_state_invariant pages_per_block_gt0) CR_empty Hexec).
Qed.

End Specs.

Theorem device_refines_idealized_block_device_closed :
  forall ops s',
    exec empty_state ops = Some s' ->
    CR (abs_exec empty_abs ops) s' /\ ftl_invariant s'.
Proof. exact (@device_refines_idealized_block_device pages_per_block_pos). Qed.
