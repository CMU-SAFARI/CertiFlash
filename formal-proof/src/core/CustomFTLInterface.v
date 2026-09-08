(* CustomFTLInterface.v: the modular-verification interface.

   A designer supplies a state type, four operations, a readiness predicate
   and a refinement map, then discharges five hypotheses stated over that
   map.  The Validator functor turns those five into the same guarantees
   direct verification proves for CertiFlash's own model. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.

Import ListNotations.

(* The inherited contract is the framework's own invariant, read through the
   designer's refinement map.  Nothing about it is a parameter, which is what
   lets its clauses transfer rather than being restated per FTL. *)
Module Type CUSTOM_FTL.
  Parameter user_state : Type.

  Parameter user_read : user_state -> Addr -> Page -> option Data.
  Parameter user_write : user_state -> Addr -> Page -> Data -> user_state.
  Parameter user_gc : user_state -> user_state.
  Parameter user_wear_level : user_state -> user_state.

  Parameter user_to_model : user_state -> FTLState.
  Parameter user_write_ready : user_state -> Addr -> Page -> Prop.

  (* A write is admissible only for an in-range logical page whose address
     carries the ownership the vendor installed.  These are the guards
     [step] itself applies; a designer inherits them rather than restating
     them. *)
  Definition admissible (s : user_state) (a : Addr) (p : Page) : Prop :=
    a < addr_space /\ p < pages_per_block /\
    (exists t, addr_tenant (user_to_model s) a = Some t) /\
    (exists ns, addr_namespace (user_to_model s) a = Some ns).

  Definition security_contract (m : FTLState) : Prop := ftl_invariant m.

  Parameter invariants_preserved_on_write :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_write s a p d)).

  Parameter invariants_preserved_on_gc :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_gc s)).

  Parameter invariants_preserved_on_wear_level :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_wear_level s)).

  Parameter read_after_write_correctness :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      user_read (user_write s a p d) a p = Some d.

  Parameter isolation_property :
    forall s a1 p1 a2 p2 d1 d2,
      (a1 <> a2 \/ p1 <> p2) ->
      admissible s a1 p1 ->
      admissible (user_write s a1 p1 d1) a2 p2 ->
      user_write_ready s a1 p1 ->
      user_write_ready (user_write s a1 p1 d1) a2 p2 ->
      security_contract (user_to_model s) ->
      user_read (user_write (user_write s a1 p1 d1) a2 p2 d2) a1 p1 = Some d1.
End CUSTOM_FTL.

(* The certificate.  No proof search: the five discharged hypotheses are
   packaged into one theorem per guarantee. *)
Module Validator (F : CUSTOM_FTL).
  Import F.

  Theorem custom_ftl_security_suite :
    (forall s a p d, admissible s a p -> user_write_ready s a p ->
       security_contract (user_to_model s) ->
       security_contract (user_to_model (user_write s a p d)))
    /\ (forall s, security_contract (user_to_model s) ->
          security_contract (user_to_model (user_gc s)))
    /\ (forall s, security_contract (user_to_model s) ->
          security_contract (user_to_model (user_wear_level s)))
    /\ (forall s a p d, admissible s a p -> user_write_ready s a p ->
          security_contract (user_to_model s) ->
          user_read (user_write s a p d) a p = Some d)
    /\ (forall s a1 p1 a2 p2 d1 d2,
          (a1 <> a2 \/ p1 <> p2) ->
          admissible s a1 p1 ->
          admissible (user_write s a1 p1 d1) a2 p2 ->
          user_write_ready s a1 p1 ->
          user_write_ready (user_write s a1 p1 d1) a2 p2 ->
          security_contract (user_to_model s) ->
          user_read (user_write (user_write s a1 p1 d1) a2 p2 d2) a1 p1 = Some d1).
  Proof.
    split; [exact invariants_preserved_on_write|].
    split; [exact invariants_preserved_on_gc|].
    split; [exact invariants_preserved_on_wear_level|].
    split; [exact read_after_write_correctness|].
    exact isolation_property.
  Qed.
End Validator.
