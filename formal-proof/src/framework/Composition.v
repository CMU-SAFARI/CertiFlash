(* Composition.v: the cheapest point of the extension-effort taxonomy.

   An FTL extension can cost a designer anywhere between "nothing" and "a
   fresh preservation proof for every clause".  Four points on that scale:

     (1) new state, no new obligations   -- this file;
     (2) new state, new operations that touch the base state;
     (3) new clauses added to the invariant;
     (4) a change to the base model itself.

   Case (1) is the *orthogonal* extension: the designer widens the FTL's
   state with fields that none of the four host-visible operations reads or
   writes, and adds operations that touch only the new fields.  The claim
   this file tests is that such an extension should cost zero lines of
   designer-written proof: the five [CUSTOM_FTL] hypotheses ought to fall
   out of the base FTL's proofs, pushed through the projection that forgets
   the new fields.

   What is here:

     A. [ModelFTL] -- a base [CUSTOM_FTL] to instantiate against, built
        from the framework's own model.  Its four operations are [step],
        its refinement map is the identity, and its five hypotheses
        delegate to [Invariants.Preservation.step_preserves_invariant_closed]
        and to [Refinement]'s simulation lemmas.  Nothing here is part of
        the contribution; it is the object of study for the functor.

     B. [STATE_EXTENSION] -- a Module Type characterising an orthogonal
        extension: an extended state, an injection/projection pair back to
        the base state, and a commutation proof for each of the four
        operations.  Plus a slot for the extension's *own* operations,
        which by definition leave the projection fixed.

     C. [LayeredCUSTOM_FTL] -- the functor.  Given a verified base and a
        [STATE_EXTENSION] over it, it produces a new [CUSTOM_FTL] whose
        five hypotheses are discharged by rewriting with the commutation
        equations and applying the base's proof.  It also proves, once,
        that every extension-local operation preserves the security
        contract and every read.

     D. [PairExtension] -- a functor that manufactures a [STATE_EXTENSION]
        from nothing but a type of extra fields.  This is what makes the
        designer's proof budget zero rather than five [reflexivity]s: the
        commutation proofs are discharged here, inside the framework, once
        for all orthogonal extensions.

     E. [ReadDisturbFields] / [ReadDisturbFTL] -- the concrete instance.
        Real NAND accumulates disturbance on the neighbours of a page that
        is read, and an FTL tracks it per block so it can schedule a
        refresh before the disturbed pages become unreadable.  Modelled as
        a per-block counter plus one operation that bumps it.

   No admitted lemmas, no [admit], no axiom declarations, and no parameters, variables or
   hypotheses outside the two Module Types, where they are the declared
   interface rather than an assumption.

   The honest line count is recorded at the end of the file. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import core.Model.
Require Import core.Operational.
Require Import core.CustomFTLInterface.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.
Require Import Refinement.

Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════
   A.  A base [CUSTOM_FTL]: the framework's own model
   ═══════════════════════════════════════════════════════════════════

   The simplest legitimate ascription.  The user state *is* [FTLState],
   the refinement map is the identity, and each operation is [step] with
   the failure case pinned to the input state -- a refused operation
   leaves the device alone, which is what [step] returning [None] means.

   Readiness says the write step succeeds.  It is phrased at one fixed
   datum because success does not depend on the datum written:
   [write_ready_indep] below proves exactly that, so the choice of [0] is
   not a hidden restriction. *)

Module ModelFTL <: CUSTOM_FTL.

  Definition user_state : Type := FTLState.

  Definition user_read (s : user_state) (a : Addr) (p : Page) : option Data :=
    read_page s a p.

  Definition user_write (s : user_state) (a : Addr) (p : Page) (d : Data)
    : user_state :=
    match step s (COpWrite a p d) with Some s' => s' | None => s end.

  Definition user_gc (s : user_state) : user_state :=
    match step s COpGC with Some s' => s' | None => s end.

  Definition user_wear_level (s : user_state) : user_state :=
    match step s COpWearLevel with Some s' => s' | None => s end.

  Definition user_to_model (s : user_state) : FTLState := s.

  Definition user_write_ready (s : user_state) (a : Addr) (p : Page) : Prop :=
    exists s', step s (COpWrite a p 0) = Some s'.

  Definition admissible (s : user_state) (a : Addr) (p : Page) : Prop :=
    a < addr_space /\ p < pages_per_block /\
    (exists t, addr_tenant (user_to_model s) a = Some t) /\
    (exists ns, addr_namespace (user_to_model s) a = Some ns).

  Definition security_contract (m : FTLState) : Prop := ftl_invariant m.

  (* Whether a write step succeeds is independent of the datum written:
     the guard, the staling of the old page and the allocation of the new
     one all read the state and the address only.  [d] first appears in
     [program_page], which is total. *)
  Lemma write_ready_indep :
    forall s a p d d',
      (exists s', step s (COpWrite a p d) = Some s') ->
      (exists s', step s (COpWrite a p d') = Some s').
  Proof.
    intros s a p d d' [s0 H0]. cbn [step] in *.
    destruct (andb (andb (Nat.ltb a addr_space) (Nat.ltb p pages_per_block))
                   (match addr_tenant s a, addr_namespace s a with
                    | Some _, Some _ => true | _, _ => false end)) eqn:Hg;
      [|discriminate].
    unfold exec_write in *. cbv zeta in *.
    destruct (addr_tenant s a) as [t|] eqn:Ht; [|discriminate].
    destruct (addr_namespace s a) as [ns|] eqn:Hns; [|discriminate].
    destruct (alloc_page
                match l2p_map s a p with
                | Some old => invalidate_at s old
                | None => s
                end t ns) as [[pa s2]|] eqn:Halloc; [|discriminate].
    eexists. reflexivity.
  Qed.

  Lemma write_ready_step :
    forall s a p d,
      user_write_ready s a p ->
      exists s', step s (COpWrite a p d) = Some s'.
  Proof.
    intros s a p d H. exact (write_ready_indep s a p 0 d H).
  Qed.

  (* The empty abstract device is refined by every state, vacuously. *)
  Lemma CR_empty_any : forall s, CR empty_abs s.
  Proof. intros s a p d H. discriminate H. Qed.

  (* ── Hyp1..Hyp3: preservation, from [Preservation] ─────────────── *)

  Lemma invariants_preserved_on_write :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_write s a p d)).
  Proof.
    intros s a p d _ _ Hinv. unfold security_contract, user_to_model, user_write.
    destruct (step s (COpWrite a p d)) as [s'|] eqn:E; [|exact Hinv].
    exact (step_preserves_invariant_closed s (COpWrite a p d) s' Hinv E).
  Qed.

  Lemma invariants_preserved_on_gc :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_gc s)).
  Proof.
    intros s Hinv. unfold security_contract, user_to_model, user_gc.
    destruct (step s COpGC) as [s'|] eqn:E; [|exact Hinv].
    exact (step_preserves_invariant_closed s COpGC s' Hinv E).
  Qed.

  Lemma invariants_preserved_on_wear_level :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_wear_level s)).
  Proof.
    intros s Hinv. unfold security_contract, user_to_model, user_wear_level.
    destruct (step s COpWearLevel) as [s'|] eqn:E; [|exact Hinv].
    exact (step_preserves_invariant_closed s COpWearLevel s' Hinv E).
  Qed.

  (* ── Hyp4, Hyp5: data observation, from [Refinement] ───────────── *)

  (* One write, seen through the refinement relation: start from the empty
     abstract device, which every state refines, and let the simulation
     lemma carry the single written cell across. *)
  Lemma write_installs :
    forall s a p d s',
      ftl_invariant s ->
      step s (COpWrite a p d) = Some s' ->
      CR (abs_write empty_abs a p d) s'.
  Proof.
    intros s a p d s' Hinv Hstep.
    exact (@write_preserves_CR pages_per_block_pos
             empty_abs s s' a p d Hinv (CR_empty_any s) Hstep).
  Qed.

  Lemma read_after_write_correctness :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      user_read (user_write s a p d) a p = Some d.
  Proof.
    intros s a p d _ Hready Hinv.
    unfold security_contract, user_to_model in Hinv.
    destruct (write_ready_step s a p d Hready) as [s' Hs'].
    unfold user_read, user_write. rewrite Hs'.
    apply (CR_read_agrees (abs_write empty_abs a p d) s' a p d
             (write_installs s a p d s' Hinv Hs')).
    unfold abs_read. apply abs_write_here.
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
    intros s a1 p1 a2 p2 d1 d2 Hne _ _ Hr1 Hr2 Hinv.
    unfold security_contract, user_to_model in Hinv.
    destruct (write_ready_step s a1 p1 d1 Hr1) as [s1 Hs1].
    unfold user_read, user_write in *. rewrite Hs1 in *.
    assert (Hinv1 : ftl_invariant s1)
      by exact (step_preserves_invariant_closed s (COpWrite a1 p1 d1) s1 Hinv Hs1).
    destruct (write_ready_step s1 a2 p2 d2 Hr2) as [s2 Hs2].
    rewrite Hs2.
    assert (HCR1 : CR (abs_write empty_abs a1 p1 d1) s1)
      by exact (write_installs s a1 p1 d1 s1 Hinv Hs1).
    assert (HCR2 : CR (abs_write (abs_write empty_abs a1 p1 d1) a2 p2 d2) s2)
      by exact (@write_preserves_CR pages_per_block_pos
                  (abs_write empty_abs a1 p1 d1) s1 s2 a2 p2 d2
                  Hinv1 HCR1 Hs2).
    apply (CR_read_agrees _ s2 a1 p1 d1 HCR2).
    unfold abs_read. rewrite abs_write_other by exact Hne.
    apply abs_write_here.
  Qed.

End ModelFTL.

(* The base is a genuine [CUSTOM_FTL]: the framework's own certificate
   functor accepts it. *)
Module ModelFTLCertificate := Validator ModelFTL.

(* ═══════════════════════════════════════════════════════════════════
   B.  What an orthogonal state extension is
   ═══════════════════════════════════════════════════════════════════

   [ext_state] widens [Base.user_state] with fields that none of the four
   host-visible operations consults.  "Does not consult" is not a property
   one can state directly about a record, so it is stated about the
   observable behaviour instead: the projection [proj] that forgets the new
   fields commutes with every operation.  Read the four commutation
   equations as "running an operation upstairs and then forgetting is the
   same as forgetting and then running it downstairs" -- which is precisely
   the statement that the new fields are invisible to the base.

   [inj] with [proj_inj] is the well-formedness half of the pair: every
   base state is representable upstairs, so the extension genuinely adds
   fields rather than also restricting which base states can occur.  A
   [STATE_EXTENSION] with an empty [ext_state] would satisfy the four
   commutation equations vacuously; [proj_inj] rules that out.

   [ext_local] is the extension's own operation set: operations that touch
   only the new fields, and therefore leave [proj] fixed.  The read-disturb
   counter's bump is one of these.  Giving them a slot in the Module Type
   is what lets the functor prove them harmless once, generically, instead
   of leaving that to each designer. *)

Module Type STATE_EXTENSION (Base : CUSTOM_FTL).

  Parameter ext_state : Type.

  (* The projection/injection pair. *)
  Parameter proj : ext_state -> Base.user_state.
  Parameter inj : Base.user_state -> ext_state.
  Parameter proj_inj : forall b, proj (inj b) = b.

  (* The four operations, lifted. *)
  Parameter ext_read : ext_state -> Addr -> Page -> option Data.
  Parameter ext_write : ext_state -> Addr -> Page -> Data -> ext_state.
  Parameter ext_gc : ext_state -> ext_state.
  Parameter ext_wear_level : ext_state -> ext_state.

  (* Each of the four commutes with the projection. *)
  Parameter read_commutes :
    forall s a p, ext_read s a p = Base.user_read (proj s) a p.
  Parameter write_commutes :
    forall s a p d, proj (ext_write s a p d) = Base.user_write (proj s) a p d.
  Parameter gc_commutes :
    forall s, proj (ext_gc s) = Base.user_gc (proj s).
  Parameter wear_level_commutes :
    forall s, proj (ext_wear_level s) = Base.user_wear_level (proj s).

  (* The extension's own operations, which move only the new fields. *)
  Parameter ext_local : Type.
  Parameter ext_apply : ext_local -> ext_state -> ext_state.
  Parameter apply_commutes : forall o s, proj (ext_apply o s) = proj s.

End STATE_EXTENSION.

(* ═══════════════════════════════════════════════════════════════════
   C.  The layering functor
   ═══════════════════════════════════════════════════════════════════

   Every hypothesis proof has the same three-step shape: unfold to the
   projection, rewrite with the commutation equation for the operation in
   question, apply the base's proof.  No case analysis on the extension,
   because the Module Type left it nothing to analyse. *)

Module LayeredCUSTOM_FTL (Base : CUSTOM_FTL) (E : STATE_EXTENSION Base)
    <: CUSTOM_FTL.

  Definition user_state : Type := E.ext_state.

  Definition user_read (s : user_state) (a : Addr) (p : Page) : option Data :=
    E.ext_read s a p.

  Definition user_write (s : user_state) (a : Addr) (p : Page) (d : Data)
    : user_state := E.ext_write s a p d.

  Definition user_gc (s : user_state) : user_state := E.ext_gc s.

  Definition user_wear_level (s : user_state) : user_state := E.ext_wear_level s.

  Definition user_to_model (s : user_state) : FTLState :=
    Base.user_to_model (E.proj s).

  Definition user_write_ready (s : user_state) (a : Addr) (p : Page) : Prop :=
    Base.user_write_ready (E.proj s) a p.

  Definition admissible (s : user_state) (a : Addr) (p : Page) : Prop :=
    a < addr_space /\ p < pages_per_block /\
    (exists t, addr_tenant (user_to_model s) a = Some t) /\
    (exists ns, addr_namespace (user_to_model s) a = Some ns).

  Definition security_contract (m : FTLState) : Prop := ftl_invariant m.

  (* [admissible] upstairs and [Base.admissible] downstairs are the same
     proposition, because [user_to_model] is [Base.user_to_model] after
     projecting.  Recorded as a lemma so the hypothesis proofs below can
     name the step rather than rely on it silently. *)
  Lemma admissible_proj :
    forall s a p, admissible s a p <-> Base.admissible (E.proj s) a p.
  Proof.
    intros s a p. unfold admissible, Base.admissible, user_to_model.
    split; intro H; exact H.
  Qed.

  Lemma invariants_preserved_on_write :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_write s a p d)).
  Proof.
    intros s a p d Hadm Hready Hinv.
    unfold security_contract, user_to_model, user_write, user_write_ready in *.
    rewrite E.write_commutes.
    exact (Base.invariants_preserved_on_write (E.proj s) a p d
             (proj1 (admissible_proj s a p) Hadm) Hready Hinv).
  Qed.

  Lemma invariants_preserved_on_gc :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_gc s)).
  Proof.
    intros s Hinv.
    unfold security_contract, user_to_model, user_gc in *.
    rewrite E.gc_commutes.
    exact (Base.invariants_preserved_on_gc (E.proj s) Hinv).
  Qed.

  Lemma invariants_preserved_on_wear_level :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_wear_level s)).
  Proof.
    intros s Hinv.
    unfold security_contract, user_to_model, user_wear_level in *.
    rewrite E.wear_level_commutes.
    exact (Base.invariants_preserved_on_wear_level (E.proj s) Hinv).
  Qed.

  Lemma read_after_write_correctness :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      user_read (user_write s a p d) a p = Some d.
  Proof.
    intros s a p d Hadm Hready Hinv.
    unfold security_contract, user_to_model, user_read, user_write,
           user_write_ready in *.
    rewrite E.read_commutes, E.write_commutes.
    exact (Base.read_after_write_correctness (E.proj s) a p d
             (proj1 (admissible_proj s a p) Hadm) Hready Hinv).
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
    intros s a1 p1 a2 p2 d1 d2 Hne Hadm1 Hadm2 Hr1 Hr2 Hinv.
    apply (proj1 (admissible_proj _ _ _)) in Hadm1.
    apply (proj1 (admissible_proj _ _ _)) in Hadm2.
    unfold security_contract, user_to_model, user_read, user_write,
           user_write_ready in *.
    rewrite E.write_commutes in Hadm2, Hr2.
    rewrite E.read_commutes, !E.write_commutes.
    exact (Base.isolation_property (E.proj s) a1 p1 a2 p2 d1 d2
             Hne Hadm1 Hadm2 Hr1 Hr2 Hinv).
  Qed.

  (* ── The extension's own operations, proved harmless once ────────── *)

  (* An extension-local operation cannot break the security contract: the
     contract is a property of the projection, and the operation does not
     move it.  Proved here so that no designer has to prove it. *)
  Lemma local_op_preserves_contract :
    forall o s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (E.ext_apply o s)).
  Proof.
    intros o s Hinv. unfold user_to_model in *.
    rewrite E.apply_commutes. exact Hinv.
  Qed.

  (* Nor can it change what the host reads. *)
  Lemma local_op_preserves_reads :
    forall o s a p, user_read (E.ext_apply o s) a p = user_read s a p.
  Proof.
    intros o s a p. unfold user_read.
    rewrite !E.read_commutes, E.apply_commutes. reflexivity.
  Qed.

  (* Nor which writes are admissible or ready. *)
  Lemma local_op_preserves_admissible :
    forall o s a p, admissible (E.ext_apply o s) a p <-> admissible s a p.
  Proof.
    intros o s a p. unfold admissible, user_to_model.
    rewrite E.apply_commutes. split; intro H; exact H.
  Qed.

  Lemma local_op_preserves_ready :
    forall o s a p, user_write_ready (E.ext_apply o s) a p <-> user_write_ready s a p.
  Proof.
    intros o s a p. unfold user_write_ready.
    rewrite E.apply_commutes. split; intro H; exact H.
  Qed.

End LayeredCUSTOM_FTL.

(* ═══════════════════════════════════════════════════════════════════
   D.  Manufacturing a [STATE_EXTENSION] from a bare field type
   ═══════════════════════════════════════════════════════════════════

   [LayeredCUSTOM_FTL] already reduces the designer's obligation from five
   hypotheses to five commutation equations.  For the orthogonal case those
   five are all [reflexivity], and there is no reason to make anyone write
   them: [PairExtension] pairs the base state with an arbitrary record of
   extra fields and discharges them here, once.

   What is left for the designer of an orthogonal extension is a type and a
   default value.  No proof. *)

Module Type EXTRA_STATE.
  Parameter T : Type.
  Parameter init : T.
End EXTRA_STATE.

Module PairExtension (Base : CUSTOM_FTL) (X : EXTRA_STATE)
    <: STATE_EXTENSION Base.

  Record pair_state : Type := mkPair {
    pair_base : Base.user_state;
    pair_extra : X.T
  }.

  Definition ext_state : Type := pair_state.

  Definition proj (s : ext_state) : Base.user_state := pair_base s.
  Definition inj (b : Base.user_state) : ext_state := mkPair b X.init.

  Lemma proj_inj : forall b, proj (inj b) = b.
  Proof. intros b. reflexivity. Qed.

  Definition ext_read (s : ext_state) (a : Addr) (p : Page) : option Data :=
    Base.user_read (pair_base s) a p.

  Definition ext_write (s : ext_state) (a : Addr) (p : Page) (d : Data)
    : ext_state :=
    mkPair (Base.user_write (pair_base s) a p d) (pair_extra s).

  Definition ext_gc (s : ext_state) : ext_state :=
    mkPair (Base.user_gc (pair_base s)) (pair_extra s).

  Definition ext_wear_level (s : ext_state) : ext_state :=
    mkPair (Base.user_wear_level (pair_base s)) (pair_extra s).

  Lemma read_commutes :
    forall s a p, ext_read s a p = Base.user_read (proj s) a p.
  Proof. intros. reflexivity. Qed.

  Lemma write_commutes :
    forall s a p d, proj (ext_write s a p d) = Base.user_write (proj s) a p d.
  Proof. intros. reflexivity. Qed.

  Lemma gc_commutes : forall s, proj (ext_gc s) = Base.user_gc (proj s).
  Proof. intros. reflexivity. Qed.

  Lemma wear_level_commutes :
    forall s, proj (ext_wear_level s) = Base.user_wear_level (proj s).
  Proof. intros. reflexivity. Qed.

  (* An extension-local operation is any update of the extra fields. *)
  Definition ext_local : Type := X.T -> X.T.

  Definition ext_apply (o : ext_local) (s : ext_state) : ext_state :=
    mkPair (pair_base s) (o (pair_extra s)).

  Lemma apply_commutes : forall o s, proj (ext_apply o s) = proj s.
  Proof. intros. reflexivity. Qed.

End PairExtension.

(* ═══════════════════════════════════════════════════════════════════
   E.  The instance: a read-disturb tracker
   ═══════════════════════════════════════════════════════════════════

   Reading a NAND page raises the pass-through voltage on the other pages
   of the same block, and enough of that shifts their threshold voltages
   far enough to flip bits.  Controllers therefore count reads per block
   and refresh -- rewrite the block elsewhere -- once the count crosses a
   vendor threshold.  The counter is pure bookkeeping: it never decides
   where a write lands, which block garbage collection picks, or what a
   read returns.  That is what makes it the canonical orthogonal
   extension.

   Everything the designer writes is in the next eight lines. *)

Module ReadDisturbFields <: EXTRA_STATE.
  (* One counter per block. *)
  Definition T : Type := Block -> nat.
  Definition init : T := fun _ => 0.
End ReadDisturbFields.

Module RDExtension := PairExtension ModelFTL ReadDisturbFields.
Module ReadDisturbFTL := LayeredCUSTOM_FTL ModelFTL RDExtension.

(* The new operation: charge one read to block [b]. *)
Definition rd_bump (b : Block) : RDExtension.ext_local :=
  fun c => fun x => if Nat.eqb x b then S (c x) else c x.

Definition read_disturb (s : ReadDisturbFTL.user_state) (b : Block)
  : ReadDisturbFTL.user_state :=
  RDExtension.ext_apply (rd_bump b) s.

Definition rd_count (s : ReadDisturbFTL.user_state) (b : Block) : nat :=
  RDExtension.pair_extra s b.

(* Whether the block is due a refresh.  A policy, not a proof obligation. *)
Definition rd_needs_refresh (threshold : nat) (s : ReadDisturbFTL.user_state)
                            (b : Block) : bool :=
  Nat.leb threshold (rd_count s b).

(* ── The five hypotheses, with no designer proof ─────────────────────

   [ReadDisturbFTL] is a [CUSTOM_FTL] by construction: the functor
   ascribed it.  The theorems below only *name* the five, to make it
   visible that they hold for the extended FTL and that each is the
   functor's proof rather than a new one.  Each is [exact <the functor's
   field>]; none contains a proof step. *)

Theorem rd_hyp1_invariants_preserved_on_write :
  forall s a p d,
    ReadDisturbFTL.admissible s a p ->
    ReadDisturbFTL.user_write_ready s a p ->
    ReadDisturbFTL.security_contract (ReadDisturbFTL.user_to_model s) ->
    ReadDisturbFTL.security_contract
      (ReadDisturbFTL.user_to_model (ReadDisturbFTL.user_write s a p d)).
Proof. exact ReadDisturbFTL.invariants_preserved_on_write. Qed.

Theorem rd_hyp2_invariants_preserved_on_gc :
  forall s,
    ReadDisturbFTL.security_contract (ReadDisturbFTL.user_to_model s) ->
    ReadDisturbFTL.security_contract
      (ReadDisturbFTL.user_to_model (ReadDisturbFTL.user_gc s)).
Proof. exact ReadDisturbFTL.invariants_preserved_on_gc. Qed.

Theorem rd_hyp3_invariants_preserved_on_wear_level :
  forall s,
    ReadDisturbFTL.security_contract (ReadDisturbFTL.user_to_model s) ->
    ReadDisturbFTL.security_contract
      (ReadDisturbFTL.user_to_model (ReadDisturbFTL.user_wear_level s)).
Proof. exact ReadDisturbFTL.invariants_preserved_on_wear_level. Qed.

Theorem rd_hyp4_read_after_write :
  forall s a p d,
    ReadDisturbFTL.admissible s a p ->
    ReadDisturbFTL.user_write_ready s a p ->
    ReadDisturbFTL.security_contract (ReadDisturbFTL.user_to_model s) ->
    ReadDisturbFTL.user_read (ReadDisturbFTL.user_write s a p d) a p = Some d.
Proof. exact ReadDisturbFTL.read_after_write_correctness. Qed.

Theorem rd_hyp5_isolation :
  forall s a1 p1 a2 p2 d1 d2,
    (a1 <> a2 \/ p1 <> p2) ->
    ReadDisturbFTL.admissible s a1 p1 ->
    ReadDisturbFTL.admissible (ReadDisturbFTL.user_write s a1 p1 d1) a2 p2 ->
    ReadDisturbFTL.user_write_ready s a1 p1 ->
    ReadDisturbFTL.user_write_ready
      (ReadDisturbFTL.user_write s a1 p1 d1) a2 p2 ->
    ReadDisturbFTL.security_contract (ReadDisturbFTL.user_to_model s) ->
    ReadDisturbFTL.user_read
      (ReadDisturbFTL.user_write
         (ReadDisturbFTL.user_write s a1 p1 d1) a2 p2 d2) a1 p1 = Some d1.
Proof. exact ReadDisturbFTL.isolation_property. Qed.

(* And the framework's certificate functor accepts the extended FTL. *)
Module ReadDisturbCertificate := Validator ReadDisturbFTL.

(* ── The new operation is harmless, also with no designer proof ────── *)

Theorem read_disturb_preserves_contract :
  forall s b,
    ReadDisturbFTL.security_contract (ReadDisturbFTL.user_to_model s) ->
    ReadDisturbFTL.security_contract
      (ReadDisturbFTL.user_to_model (read_disturb s b)).
Proof. exact (fun s b => ReadDisturbFTL.local_op_preserves_contract (rd_bump b) s). Qed.

Theorem read_disturb_preserves_reads :
  forall s b a p,
    ReadDisturbFTL.user_read (read_disturb s b) a p =
    ReadDisturbFTL.user_read s a p.
Proof. exact (fun s b => ReadDisturbFTL.local_op_preserves_reads (rd_bump b) s). Qed.

(* ── The tracker is not vacuous ──────────────────────────────────────

   Two checks that the extension actually carries state: the counter goes
   up when charged, and the base state does not move when it does.  Both
   by computation. *)

Definition rd_initial : ReadDisturbFTL.user_state :=
  RDExtension.inj empty_state.

Example rd_counter_starts_at_zero : rd_count rd_initial 3 = 0.
Proof. reflexivity. Qed.

Example rd_counter_counts :
  rd_count (read_disturb (read_disturb rd_initial 3) 3) 3 = 2.
Proof. reflexivity. Qed.

Example rd_counter_is_per_block :
  rd_count (read_disturb (read_disturb rd_initial 3) 3) 5 = 0.
Proof. reflexivity. Qed.

Example rd_refresh_fires_at_threshold :
  rd_needs_refresh 2 (read_disturb (read_disturb rd_initial 3) 3) 3 = true.
Proof. reflexivity. Qed.

Example rd_refresh_does_not_fire_early :
  rd_needs_refresh 2 (read_disturb rd_initial 3) 3 = false.
Proof. reflexivity. Qed.

(* The base state is untouched by any number of read charges: the tracker
   is bookkeeping and nothing else. *)
Theorem read_disturb_does_not_move_the_base :
  forall s b, RDExtension.proj (read_disturb s b) = RDExtension.proj s.
Proof. exact (fun s b => RDExtension.apply_commutes (rd_bump b) s). Qed.

(* ═══════════════════════════════════════════════════════════════════
   The honest accounting
   ═══════════════════════════════════════════════════════════════════

   The claim under test was that an orthogonal state extension costs its
   designer zero lines of proof.  Counting what the designer of the
   read-disturb tracker actually had to write:

     Definitions (not proofs)
       [ReadDisturbFields]            3 lines  (a type and a default)
       [RDExtension], [ReadDisturbFTL] 2 lines  (two functor applications)
       [rd_bump], [read_disturb]      3 lines  (the new operation)
       [rd_count], [rd_needs_refresh] 3 lines  (policy, optional)
       ------------------------------------------------------------
       total definitions             11 lines

     Proof script lines written by the designer
       for [invariants_preserved_on_write]      0
       for [invariants_preserved_on_gc]         0
       for [invariants_preserved_on_wear_level] 0
       for [read_after_write_correctness]       0
       for [isolation_property]                 0
       for the [STATE_EXTENSION] obligations    0
       for [read_disturb]'s own safety          0
       ------------------------------------------------------------
       total proof lines                        0

   The claim holds, with one qualification worth stating plainly.  Zero is
   the count for a designer who routes through [PairExtension].  A designer
   who ascribes [STATE_EXTENSION] by hand -- a record shape [PairExtension]
   does not cover, say, extra fields whose type depends on the base state --
   writes five [reflexivity]s, one per commutation equation, and still zero
   lines for the five [CUSTOM_FTL] hypotheses.  So the honest statement is:

     the five hypotheses cost zero unconditionally; the commutation
     equations cost zero for pair-shaped extensions and five trivial
     lines otherwise.

   The [Theorem]s named [rd_hyp1..rd_hyp5] and
   [read_disturb_preserves_contract] above are each a statement plus
   [exact <framework lemma>].  Counting an [exact] that names an existing
   result as a proof line would put the figure at six; counting only lines
   that do proof work leaves it at zero.  Both numbers are visible in the
   file, so neither is hidden.

   What made this cheap is stated in one sentence: the four commutation
   equations say the base cannot see the new fields, so the base's proofs
   never mention them, so they transfer by rewriting rather than by
   reproof.  An extension whose new state feeds back into where a write
   lands breaks the first clause and lands at case (2) of the taxonomy,
   where the functor does not apply.  This file bounds the cheap case; it
   does not claim the expensive ones away. *)
