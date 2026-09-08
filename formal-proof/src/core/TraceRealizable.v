(* TraceRealizable.v: physical realizability of an emitted instruction trace,
 * in the page-granular model (core.Primitives).
 *
 * The predicate is an *independent* check on an emitted primitive trace.  It
 * never mentions [step]: it constrains the trace against the flash state
 * alone, using the one law the hardware imposes on the flash primitives -- a
 * NAND page is programmable only while erased, because programming drives
 * cells one way only.  Every other primitive (read, map, remap, invalidate,
 * set-tag, erase, barriers) is unconstrained by this law.
 *
 * Only the realizability of the flash primitives is covered here: that is
 * all the failure-surface reachability results that consume this predicate
 * need of it.
 *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import core.Model.
Require Import core.Primitives.

Import ListNotations.

(* ── The predicate ────────────────────────────────────────────────────── *)

(* A program must target an erased page.  Every other instruction is
   unconstrained by this law.  [PrimProgram] carries an [option LPA] (a
   logical address / page-offset pair), but the realizability law depends
   only on the physical target [pa]. *)
Definition prim_realizable (s : FTLState) (pr : FlashPrimitive) : Prop :=
  match pr with
  | PrimProgram pa _ _ _ => page_state s (pa_block pa) (pa_page pa) = PS_Empty
  | _ => True
  end.

Fixpoint trace_realizable (s : FTLState) (l : list FlashPrimitive) : Prop :=
  match l with
  | [] => True
  | pr :: l' => prim_realizable s pr /\ trace_realizable (apply_primitive s pr) l'
  end.

Lemma trace_realizable_app :
  forall l1 l2 s,
    trace_realizable s (l1 ++ l2) <->
    trace_realizable s l1 /\ trace_realizable (exec_primitives s l1) l2.
Proof.
  induction l1 as [|pr l1' IH]; intros l2 s; simpl.
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - split.
    + intros [Hp Hrest]. apply IH in Hrest. destruct Hrest as [H1 H2].
      split; [split; assumption | exact H2].
    + intros [[Hp H1] H2]. split; [exact Hp|]. apply IH. split; assumption.
Qed.

(* ── An executable form of the same check ─────────────────────────────── *)

Fixpoint trace_realizableb (s : FTLState) (l : list FlashPrimitive) : bool :=
  match l with
  | [] => true
  | pr :: l' =>
      (match pr with
       | PrimProgram pa _ _ _ =>
           match page_state s (pa_block pa) (pa_page pa) with
           | PS_Empty => true
           | _ => false
           end
       | _ => true
       end) && trace_realizableb (apply_primitive s pr) l'
  end.

Lemma trace_realizableb_correct :
  forall l s, trace_realizableb s l = true <-> trace_realizable s l.
Proof.
  induction l as [|pr l' IH]; intros s; cbn.
  - split; [intros _; exact I | intros _; reflexivity].
  - rewrite Bool.andb_true_iff. rewrite IH. split.
    + intros [Hp Hrest]. split; [|exact Hrest].
      destruct pr; cbn in Hp |- *; try exact I;
        destruct (page_state s (pa_block pa) (pa_page pa)); try discriminate;
        reflexivity.
    + intros [Hp Hrest]. split; [|exact Hrest].
      destruct pr; cbn in Hp |- *; try reflexivity; rewrite Hp; reflexivity.
Qed.
