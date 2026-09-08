(* Invariants.v: invariant bundle over the unified FTLState. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import core.Model.

Import ListNotations.

Section Invariants.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* Well-formedness side conditions.  Neither constrains an FTL: WF0 ignores
   its state argument and restates the section's own pages_per_block > 0,
   and WF1 holds of every state because page_state is a total function.
   They are kept in the conjunction so that the positional destructuring of
   ftl_invariant is unchanged, and are not counted among the clauses. *)
Definition WF0 (_ : FTLState) : Prop :=
  pages_per_block > 0.

Definition WF1 (s : FTLState) : Prop :=
  forall b p,
    b < total_blocks ->
    p < pages_per_block ->
    exists st, page_state s b p = st.

(* Mapping *)
Definition Inv0 (s : FTLState) : Prop :=
  forall b p d,
    page_state s b p = PS_Valid d ->
    exists a q, l2p_map s a q = Some (mkPhysAddr b p).

Definition Inv1 (s : FTLState) : Prop :=
  forall a p pa, l2p_map s a p = Some pa ->
    pa_block pa < total_blocks /\ pa_page pa < pages_per_block /\
    a < addr_space /\ p < pages_per_block.

Definition Inv2 (s : FTLState) : Prop :=
  forall a1 p1 a2 p2 pa,
    l2p_map s a1 p1 = Some pa -> l2p_map s a2 p2 = Some pa ->
    a1 = a2 /\ p1 = p2.

(* Inv3 and Inv4 tie the forward mapping to the reverse mapping that each live
   page carries in its OOB area.  Inv3 is the forward direction: a live page of
   a mapped block is stamped with the logical address that maps to it.  Inv4 is
   the reverse direction: a live page's stamp is honoured by the mapping.  An
   FTL that relocates a live page and stamps the destination without repairing
   the mapping violates Inv4; one that repairs the mapping without stamping the
   destination violates Inv3. *)
Definition Inv3 (s : FTLState) : Prop :=
  forall a p pa d,
    l2p_map s a p = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    page_lpa (page_meta s (pa_block pa) (pa_page pa)) = Some (a, p).

Definition Inv4 (s : FTLState) : Prop :=
  forall a p b q d,
    page_state s b q = PS_Valid d ->
    page_lpa (page_meta s b q) = Some (a, p) ->
    l2p_map s a p = Some (mkPhysAddr b q).

(* Isolation *)
Definition Inv5 (s : FTLState) : Prop :=
  forall a p pa,
    l2p_map s a p = Some pa ->
    ~ In (pa_block pa) (free_block_list s).

Definition Inv6 (s : FTLState) : Prop :=
  forall b,
    In b (free_block_list s) ->
    forall p,
      p < pages_per_block ->
      page_state s b p = PS_Empty /\
      page_meta s b p = empty_page_meta.

Definition Inv7 (s : FTLState) : Prop :=
  forall a p pa d t ns,
    l2p_map s a p = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    addr_tenant s a = Some t ->
    addr_namespace s a = Some ns ->
    page_owner_tenant (page_meta s (pa_block pa) (pa_page pa)) = t /\
    page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)) = ns.

Definition Inv8 (s : FTLState) : Prop :=
  forall b,
    In b (free_block_list s) ->
    b < total_blocks.

(* Integrity *)
Definition Inv9 (s : FTLState) : Prop :=
  forall b p d,
    page_state s b p = PS_Valid d ->
    exists tag, page_tag (page_meta s b p) = Some tag.

(* A block is free, open for some tenant, holds a mapped page, or is a
   garbage block: closed, holding at least one stale page, and awaiting
   reclamation.  The fourth case is the normal resting state of a block once
   an out-of-place write has moved its last live page elsewhere and erase has
   been deferred to GC. *)
Definition Inv10 (s : FTLState) : Prop :=
  forall b,
    b < total_blocks ->
    In b (free_block_list s) \/ (exists t ns, open_block s t ns = Some b) \/
    (exists a p pa, l2p_map s a p = Some pa /\ pa_block pa = b) \/
    (exists q, page_state s b q = PS_Invalid).

Definition Inv11 (s : FTLState) : Prop :=
  NoDup (free_block_list s).

Definition Inv12 (s : FTLState) : Prop :=
  forall b,
    b < total_blocks ->
    (exists p, page_role s b p = Some RMeta) ->
    (exists a p pa, l2p_map s a p = Some pa /\ pa_block pa = b) \/
    (exists q, page_state s b q = PS_Invalid).

Definition Inv13 (s : FTLState) : Prop :=
  forall b p d, page_state s b p = PS_Valid d -> page_role s b p = Some RData.

Definition Inv14 (s : FTLState) : Prop :=
  forall b p, page_role s b p = Some RData -> exists d, page_state s b p = PS_Valid d.

Definition Inv15 (s : FTLState) : Prop :=
  forall b p, page_role s b p = Some RMeta -> page_state s b p <> PS_Empty.

Definition Inv16 (s : FTLState) : Prop :=
  forall b p, page_state s b p = PS_Empty -> page_role s b p = None.

(* Block Ownership *)
(* Inv17: every block marked free in the free_block bitmap has no tenant or
   namespace assignment.  This ensures that no tenant can observe stale
   ownership metadata on a recycled block. *)
Definition Inv17 (s : FTLState) : Prop :=
  forall b,
    free_block s b = true ->
    block_tenant s b = None /\ block_namespace s b = None.

(* Inv18: the mapping is ownership-consistent: whenever logical address a maps
   to physical block b, the block-level tenant and namespace fields agree with
   the address-level tenant and namespace.  This bridges page-granularity
   isolation (Inv7) to block-granularity ownership, which is what the ACU
   enforces at the hardware level. *)
Definition Inv18 (s : FTLState) : Prop :=
  forall a p pa,
    l2p_map s a p = Some pa ->
    block_tenant s (pa_block pa) = addr_tenant s a /\
    block_namespace s (pa_block pa) = addr_namespace s a.

(* Inv19: every entry in the region table whose logical range is defined fits
   within the device address space.  The region table is an immutable hardware
   structure initialised at boot and never modified by any FTL operation, so
   this invariant is trivially preserved; it is stated here to make the ACU's
   bounds-check guarantee explicit in the formal model. *)
Definition Inv19 (s : FTLState) : Prop :=
  forall i r,
    region_table s i = Some r ->
    region_start r + region_len r <= addr_space.

(* Frontier well-formedness.  Page-granular translation needs an allocation
   point, and these two clauses say the open block is not simultaneously on
   the free list and that everything at or beyond the write pointer is
   still erased, which is what makes [alloc_page] hand out a programmable
   page. *)
Definition Inv20 (s : FTLState) : Prop :=
  forall t ns b, open_block s t ns = Some b ->
    b < total_blocks /\ ~ In b (free_block_list s) /\
    free_block s b = false /\ block_open s b = true /\
    write_ptr s t ns <= pages_per_block /\
    (* the open block belongs to its owner, or to nobody yet.  Without this
       a write retags a block that already holds another owner's pages. *)
    (block_tenant s b = None \/ block_tenant s b = Some t) /\
    (block_namespace s b = None \/ block_namespace s b = Some ns) /\
    (* one block is open for at most one (tenant, namespace) pair.  Without
       this a write for one owner programs above another's frontier. *)
    (forall t' ns', open_block s t' ns' = Some b -> t' = t /\ ns' = ns).

Definition Inv21 (s : FTLState) : Prop :=
  forall t ns b q, open_block s t ns = Some b -> write_ptr s t ns <= q ->
    q < pages_per_block ->
    page_state s b q = PS_Empty /\ page_meta s b q = empty_page_meta.

(* (2) The forward map points only at live pages.  Without this an operation
   can invalidate a page that was never programmed, which turns an erased
   page above the frontier into a stale one and breaks Inv21. *)
Definition Inv22 (s : FTLState) : Prop :=
  forall a p pa, l2p_map s a p = Some pa ->
    exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d.

(* [block_open] mirrors [open_block]; the converse direction is what makes
   [reclaimable] sound, since it never picks a block open for some tenant. *)
Definition Inv23 (s : FTLState) : Prop :=
  forall b, block_open s b = true ->
    exists t ns, open_block s t ns = Some b.

(* The free bitmap and the free list are two views of one pool.  Without this
   a block can sit on the list with its bit clear, be picked as a garbage
   collection victim, and be pushed onto the list a second time. *)
Definition Inv24 (s : FTLState) : Prop :=
  forall b, free_block s b = true <-> In b (free_block_list s).

(* Everything below a tenant's frontier has been programmed.  Inv21 covers
   only what lies at or above it, which leaves a fully erased block that has
   been closed satisfying every clause and belonging to no one. *)
Definition Inv25 (s : FTLState) : Prop :=
  forall t ns b q, open_block s t ns = Some b -> q < write_ptr s t ns ->
    page_state s b q <> PS_Empty.

(* A mapped address carries the ownership the vendor installed.  Allocation
   needs a tenant, and inventing one for an unlabelled address relabels a
   real tenant's block. *)
Definition Inv26 (s : FTLState) : Prop :=
  forall a p pa, l2p_map s a p = Some pa ->
    (exists t, addr_tenant s a = Some t) /\
    (exists ns, addr_namespace s a = Some ns).

Definition  ftl_invariant (s : FTLState) : Prop :=
  WF0 s /\
  WF1 s /\
  Inv0 s /\
  Inv1 s /\
  Inv2 s /\
  Inv3 s /\
  Inv4 s /\
  Inv5 s /\
  Inv6 s /\
  Inv7 s /\
  Inv8 s /\
  Inv9 s /\
  Inv10 s /\
  Inv11 s /\
  Inv12 s /\
  Inv13 s /\
  Inv14 s /\
  Inv15 s /\
  Inv16 s /\
  Inv17 s /\
  Inv18 s /\
  Inv19 s /\
  Inv20 s /\
  Inv21 s /\
  Inv22 s /\
  Inv23 s /\
  Inv24 s /\
  Inv25 s /\
  Inv26 s.

(* A mapped address is in range (Inv1).  Operations that touch an address
   already present in [l2p_map] therefore get the bound from the invariant
   and need no side condition; only a write to a fresh address does, and
   [step] rejects that case outright. *)
Lemma invariant_addr_in_range :
  forall s a p pa,
    ftl_invariant s ->
    l2p_map s a p = Some pa ->
    a < addr_space.
Proof.
  intros s a p pa Hinv Hmap.
  destruct Hinv as [_ [_ [_ [HInv3 _]]]].
  destruct (HInv3 a p pa Hmap) as [_ [_ [Ha _]]]. exact Ha.
Qed.

Lemma make_ftl_invariant :
  forall s,
    WF0 s ->
    WF1 s ->
    Inv0 s ->
    Inv1 s ->
    Inv2 s ->
    Inv3 s ->
    Inv4 s ->
    Inv5 s ->
    Inv6 s ->
    Inv7 s ->
    Inv8 s ->
    Inv9 s ->
    Inv10 s ->
    Inv11 s ->
    Inv12 s ->
    Inv13 s ->
    Inv14 s ->
    Inv15 s ->
    Inv16 s ->
    Inv17 s ->
    Inv18 s ->
    Inv19 s ->
    Inv20 s ->
    Inv21 s ->
    Inv22 s ->
    Inv23 s ->
    Inv24 s ->
    Inv25 s ->
    Inv26 s ->
     ftl_invariant s.
Proof.
  intros s H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
  unfold  ftl_invariant.
  do 28 (split; [assumption|]).
  assumption.
Qed.

Lemma empty_state_invariant :
   ftl_invariant empty_state.
Proof.
  apply make_ftl_invariant.
  - exact pages_per_block_gt0.
  - unfold WF1, empty_state. intros b p Hb Hp. exists PS_Empty. reflexivity.
  - unfold Inv0, empty_state. intros b p d Hps. discriminate Hps.
  - unfold Inv1, empty_state. intros a0 p0 pa0 Hm. discriminate Hm.
  - unfold Inv2, empty_state. intros a1 p1 a2 p2 pa0 H1 _. discriminate H1.
  - unfold Inv3, empty_state. intros a0 p0 pa0 d Hm _. discriminate Hm.
  - unfold Inv4, empty_state. intros a0 p0 b0 q0 d Hps _. discriminate Hps.
  - unfold Inv5, empty_state. intros a p0 pa0 Hm. discriminate Hm.
  - unfold Inv6, empty_state. intros b Hin p Hp. split; reflexivity.
  - unfold Inv7, empty_state. intros a p0 pa0 d t ns Hm _ _ _. discriminate Hm.
  - unfold Inv8, empty_state. intros b0 Hin.
    unfold empty_state in Hin.
    change (In b0 (seq 0 total_blocks)) in Hin.
    apply in_seq in Hin.
    lia.
  - unfold Inv9, empty_state. intros b p d Hps. discriminate Hps.
  - unfold Inv10, empty_state. intros b Hb. left.
    change (In b (seq 0 total_blocks)).
    apply in_seq. lia.
  - unfold Inv11, empty_state.
    change (NoDup (seq 0 total_blocks)).
    apply seq_NoDup.
  - unfold Inv12, empty_state. intros b Hb [p Hrole]. discriminate Hrole.
  - unfold Inv13, empty_state. intros b0 p0 d Hps. discriminate Hps.
  - unfold Inv14, empty_state. intros b0 p0 Hrole. discriminate Hrole.
  - unfold Inv15, empty_state. intros b0 p0 Hrole. discriminate Hrole.
  - unfold Inv16, empty_state. intros b0 p0 Hempty. reflexivity.
  - unfold Inv17, empty_state. intros b0 Hfree. cbn in Hfree.
    unfold free_block in Hfree. cbn in Hfree.
    split; reflexivity.
  - unfold Inv18, empty_state. intros a0 p0 pa0 Hmap. discriminate Hmap.
  - unfold Inv19, empty_state. intros i0 r0 Hr0. discriminate Hr0.
  - unfold Inv20, empty_state. intros t0 ns0 b0 Hob. discriminate Hob.
  - unfold Inv21, empty_state. intros t0 ns0 b0 q0 Hob. discriminate Hob.
  - unfold Inv22, empty_state. intros a0 p0 pa0 Hm. discriminate Hm.
  - unfold Inv23, empty_state. intros b0 Hbo. discriminate Hbo.
  - unfold Inv24. cbn [free_block free_block_list empty_state]. intros b0. split.
    + intros H. apply Nat.ltb_lt in H. apply in_seq. lia.
    + intros H. apply in_seq in H. apply Nat.ltb_lt. lia.
  - unfold Inv25, empty_state. intros t0 ns0 b0 q0 Hob. discriminate Hob.
  - unfold Inv26, empty_state. intros a0 p0 pa0 Hm. discriminate Hm.
Qed.

End Invariants.
