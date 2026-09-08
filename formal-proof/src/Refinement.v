(* Refinement.v: the refinement layer under page-granular translation.

   The abstract device is a partial map from logical pages to data.  The
   refinement relation [CR] says that every cell the abstract device holds is
   backed by a live physical page that the forward map points at.  It is a
   statement about physical pages, and the per-operation simulation lemmas
   follow the shape of [Operational.v]'s out-of-place write and page-at-a-time
   garbage collection.

   Structure:
     1. the abstract device and its two operations;
     2. the relation [CR] and the initial state;
     3. the frontier bundle [AllocOK] and what [alloc_page] guarantees;
     4. the six per-operation simulation lemmas;
     5. one negative result: identity is *not* the abstract effect of
        [COpInvalidate], and a witness state showing the refutation is not
        vacuous under the 27-clause invariant.

   Nothing is admitted, and no axiom, parameter, variable or hypothesis is
   introduced.  The whole-trace theorem is deliberately absent: it composes
   with the preservation lemmas, which live elsewhere. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.

Import ListNotations.

Section Refinement.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* ══════════════════════════════════════════════════════════════════
   1.  The abstract device
   ══════════════════════════════════════════════════════════════════ *)

(* A partial map from logical pages to data.  It has no notion of blocks,
   frontiers, staleness or erase: those are exactly what the FTL implements
   and what the refinement relation has to justify. *)
Definition AbsDev := Addr -> Page -> option Data.

Definition abs_read (h : AbsDev) (a : Addr) (p : Page) : option Data := h a p.

Definition abs_write (h : AbsDev) (a0 : Addr) (p0 : Page) (d : Data) : AbsDev :=
  fun a p => if andb (Nat.eqb a a0) (Nat.eqb p p0) then Some d else h a p.

(* The abstract effect of detaching a logical page.  [COpInvalidate] drops the
   forward mapping, so identity is not its abstract effect; see
   [invalidate_identity_is_not_a_simulation] at the end of the file. *)
Definition abs_invalidate (h : AbsDev) (a0 : Addr) (p0 : Page) : AbsDev :=
  fun a p => if andb (Nat.eqb a a0) (Nat.eqb p p0) then None else h a p.

Definition empty_abs : AbsDev := fun _ _ => None.

Lemma abs_write_here : forall h a p d, abs_write h a p d a p = Some d.
Proof. intros. unfold abs_write. now rewrite !Nat.eqb_refl. Qed.

Lemma abs_write_other : forall h a0 p0 d a p,
  (a <> a0 \/ p <> p0) -> abs_write h a0 p0 d a p = h a p.
Proof.
  intros h a0 p0 d a p H. unfold abs_write.
  destruct (Nat.eqb a a0) eqn:Ea; destruct (Nat.eqb p p0) eqn:Ep; cbn; auto.
  apply Nat.eqb_eq in Ea; apply Nat.eqb_eq in Ep. destruct H; congruence.
Qed.

Lemma abs_invalidate_here : forall h a p, abs_invalidate h a p a p = None.
Proof. intros. unfold abs_invalidate. now rewrite !Nat.eqb_refl. Qed.

Lemma abs_invalidate_other : forall h a0 p0 a p,
  (a <> a0 \/ p <> p0) -> abs_invalidate h a0 p0 a p = h a p.
Proof.
  intros h a0 p0 a p H. unfold abs_invalidate.
  destruct (Nat.eqb a a0) eqn:Ea; destruct (Nat.eqb p p0) eqn:Ep; cbn; auto.
  apply Nat.eqb_eq in Ea; apply Nat.eqb_eq in Ep. destruct H; congruence.
Qed.

(* ══════════════════════════════════════════════════════════════════
   2.  The refinement relation
   ══════════════════════════════════════════════════════════════════ *)

Definition CR (h : AbsDev) (s : FTLState) : Prop :=
  forall a p d, h a p = Some d ->
    exists pa, l2p_map s a p = Some pa /\
               page_state s (pa_block pa) (pa_page pa) = PS_Valid d.

(* The same statement one cell at a time; the simulation proofs move cells
   across states individually, so it is convenient to have a name for it. *)
Definition backs (s : FTLState) (a : Addr) (p : Page) (d : Data) : Prop :=
  exists pa, l2p_map s a p = Some pa /\
             page_state s (pa_block pa) (pa_page pa) = PS_Valid d.

Lemma CR_backs : forall h s, CR h s <-> (forall a p d, h a p = Some d -> backs s a p d).
Proof. intros h s. unfold CR, backs. split; auto. Qed.

Lemma CR_empty : CR empty_abs empty_state.
Proof. intros a p d Hread. discriminate Hread. Qed.

(* Reading the abstract device agrees with reading the device, whenever the
   abstract cell is populated.  Not needed below, but it is what makes [CR]
   the right relation to have chosen. *)
Lemma CR_read_agrees : forall h s a p d,
  CR h s -> abs_read h a p = Some d -> read_page s a p = Some d.
Proof.
  intros h s a p d HCR Hread. unfold abs_read in Hread.
  destruct (HCR a p d Hread) as [pa [Hm Hps]].
  unfold read_page. rewrite Hm, Hps. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════
   3.  The allocation frontier
   ══════════════════════════════════════════════════════════════════ *)

(* What a simulation proof needs to know about the frontier, and no more:
   an open block is not in the free pool, is flagged open, and is open for a
   single owner.  This is Inv20 with the bounds and ownership conjuncts
   dropped; those matter to preservation, not to refinement. *)
Definition FrontierOK (s : FTLState) : Prop :=
  forall t ns b, open_block s t ns = Some b ->
    ~ In b (free_block_list s) /\ block_open s b = true /\
    (forall t' ns', open_block s t' ns' = Some b -> t' = t /\ ns' = ns).

(* The bundle under which [alloc_page] returns an *erased* page.  That single
   fact -- the destination of an allocation holds nothing -- is what every
   simulation case turns on, because a page that holds nothing backs no
   abstract cell. *)
Definition AllocOK (s : FTLState) : Prop :=
  FrontierOK s /\ Inv6 s /\ Inv11 s /\ Inv21 s.

Lemma frontier_ok_of_invariant : forall s, ftl_invariant s -> FrontierOK s.
Proof.
  intros s Hinv t ns b Hob.
  destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I22&_).
  destruct (I22 t ns b Hob) as (_&Hnf&_&Hbo&_&_&_&Huniq).
  split; [exact Hnf|]. split; [exact Hbo|]. exact Huniq.
Qed.

Lemma alloc_ok_of_invariant : forall s, ftl_invariant s -> AllocOK s.
Proof.
  intros s Hinv.
  split; [now apply frontier_ok_of_invariant|].
  destruct Hinv as (_&_&_&_&_&_&_&_&I8&_&_&_&_&I13&_&_&_&_&_&_&_&_&_&I23&_).
  split; [exact I8|]. split; [exact I13|]. exact I23.
Qed.

(* A block that is neither in the free pool nor open: the shape of a garbage
   collection victim, and the property that keeps an allocation from handing
   out a page of the very block being reclaimed. *)
Definition NotVictim (s : FTLState) (b : Block) : Prop :=
  ~ In b (free_block_list s) /\ block_open s b = false.

(* [alloc_page] has exactly two outcomes: a page from the current frontier, or
   the head of the free list opened as a fresh block. *)
Lemma alloc_page_inv : forall s t ns pa s1,
  alloc_page s t ns = Some (pa, s1) ->
  (open_block s t ns = Some (pa_block pa) /\
   pa_page pa = write_ptr s t ns /\
   write_ptr s t ns < pages_per_block /\
   s1 = with_frontier s t ns (Some (pa_block pa)) (S (pa_page pa))
          (free_block_list s) (free_block s) (block_open s))
  \/
  (exists rest, free_block_list s = pa_block pa :: rest /\
   pa_page pa = 0 /\
   s1 = with_frontier s t ns (Some (pa_block pa)) 1 rest
          (set_free_block (free_block s) (pa_block pa) false)
          (set_block_open (close_open s t ns) (pa_block pa) true)).
Proof.
  intros s t ns pa s1 Halloc.
  unfold alloc_page in Halloc.
  destruct (open_block s t ns) as [bo|] eqn:Hob.
  - destruct (Nat.ltb (write_ptr s t ns) pages_per_block) eqn:Hlt.
    + injection Halloc as Hpa Hs1. subst pa s1.
      left. cbn [pa_block pa_page].
      split; [reflexivity|]. split; [reflexivity|].
      split; [now apply Nat.ltb_lt in Hlt|]. reflexivity.
    + unfold open_fresh in Halloc.
      destruct (free_block_list s) as [|bf [|c rest]] eqn:Hfl; try discriminate.
      injection Halloc as Hpa Hs1. subst pa s1.
      right. exists (c :: rest). cbn [pa_block pa_page].
      rewrite Nat.eqb_refl.
      split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - unfold open_fresh in Halloc.
    destruct (free_block_list s) as [|bf [|c rest]] eqn:Hfl; try discriminate.
    injection Halloc as Hpa Hs1. subst pa s1.
    right. exists (c :: rest). cbn [pa_block pa_page].
    rewrite Nat.eqb_refl.
    split; [reflexivity|]. split; [reflexivity|]. reflexivity.
Qed.

(* [alloc_page] rewrites only the frontier fields. *)
Lemma alloc_page_fields : forall s t ns pa s1,
  alloc_page s t ns = Some (pa, s1) ->
  l2p_map s1 = l2p_map s /\ page_state s1 = page_state s /\
  page_role s1 = page_role s /\ page_meta s1 = page_meta s /\
  addr_tenant s1 = addr_tenant s /\ addr_namespace s1 = addr_namespace s /\
  block_tenant s1 = block_tenant s /\ block_namespace s1 = block_namespace s.
Proof.
  intros s t ns pa s1 Halloc.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(_&_&_&Hs1)|[rest (_&_&Hs1)]];
    subst s1; cbn; repeat split; reflexivity.
Qed.

Lemma alloc_page_dest_bound : forall s t ns pa s1,
  alloc_page s t ns = Some (pa, s1) -> pa_page pa < pages_per_block.
Proof.
  intros s t ns pa s1 Halloc.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(_&Hpp&Hlt&_)|[rest (_&Hpp&_)]].
  - rewrite Hpp. exact Hlt.
  - rewrite Hpp. exact pages_per_block_gt0.
Qed.

(* The destination of an allocation is an erased page.  In the frontier branch
   that is Inv21, in the fresh branch it is Inv6. *)
Lemma alloc_page_dest_empty : forall s t ns pa s1,
  AllocOK s -> alloc_page s t ns = Some (pa, s1) ->
  page_state s (pa_block pa) (pa_page pa) = PS_Empty /\
  page_meta s (pa_block pa) (pa_page pa) = empty_page_meta.
Proof.
  intros s t ns pa s1 [Hfr [H8 [H13 H23]]] Halloc.
  pose proof (alloc_page_dest_bound s t ns pa s1 Halloc) as Hbound.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(Hob&Hpp&Hlt&_)|[rest (Hfl&Hpp&_)]].
  - apply (H23 t ns (pa_block pa) (pa_page pa) Hob); [lia | exact Hbound].
  - apply (H8 (pa_block pa)); [rewrite Hfl; left; reflexivity | exact Hbound].
Qed.

(* The frontier after an allocation points at the block the page came from,
   strictly above the page just handed out. *)
Lemma alloc_page_frontier : forall s t ns pa s1,
  alloc_page s t ns = Some (pa, s1) ->
  open_block s1 t ns = Some (pa_block pa) /\ pa_page pa < write_ptr s1 t ns.
Proof.
  intros s t ns pa s1 Halloc.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(Hob&Hpp&Hlt&Hs1)|[rest (Hfl&Hpp&Hs1)]];
    subst s1; cbn; unfold set_open_block, set_write_ptr;
    rewrite !Nat.eqb_refl; cbn; split; try reflexivity; lia.
Qed.

Lemma alloc_page_free_list : forall s t ns pa s1,
  alloc_page s t ns = Some (pa, s1) ->
  forall x, In x (free_block_list s1) -> In x (free_block_list s).
Proof.
  intros s t ns pa s1 Halloc x Hin.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(_&_&_&Hs1)|[rest (Hfl&_&Hs1)]];
    subst s1; cbn in Hin.
  - exact Hin.
  - rewrite Hfl. right. exact Hin.
Qed.

Lemma alloc_dest_not_victim : forall s t ns pa s1 b,
  FrontierOK s -> NotVictim s b -> alloc_page s t ns = Some (pa, s1) ->
  pa_block pa <> b.
Proof.
  intros s t ns pa s1 b Hfr [Hnf Hbo] Halloc.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(Hob&_)|[rest (Hfl&_)]].
  - intros Heq. destruct (Hfr t ns (pa_block pa) Hob) as (_&Hopen&_).
    rewrite Heq in Hopen. rewrite Hbo in Hopen. discriminate.
  - intros Heq. apply Hnf. rewrite Hfl, Heq. left. reflexivity.
Qed.

Lemma alloc_preserves_NotVictim : forall s t ns pa s1 b,
  FrontierOK s -> NotVictim s b -> alloc_page s t ns = Some (pa, s1) ->
  NotVictim s1 b.
Proof.
  intros s t ns pa s1 b Hfr Hnv Halloc.
  pose proof (alloc_dest_not_victim s t ns pa s1 b Hfr Hnv Halloc) as Hne.
  destruct Hnv as [Hnf Hbo]. split.
  - intros Hin. apply Hnf. exact (alloc_page_free_list s t ns pa s1 Halloc b Hin).
  - destruct (alloc_page_inv s t ns pa s1 Halloc) as [(_&_&_&Hs1)|[rest (Hfl&_&Hs1)]];
      subst s1; cbn.
    + exact Hbo.
    + unfold set_block_open.
      destruct (Nat.eqb b (pa_block pa)) eqn:E.
      * apply Nat.eqb_eq in E. congruence.
      * unfold close_open. destruct (open_block s t ns) as [ob|] eqn:Hob; [|exact Hbo].
        unfold set_block_open. destruct (Nat.eqb b ob) eqn:E2; [|exact Hbo].
        reflexivity.
Qed.

(* Pointwise views of the two frontier updates. *)

Lemma set_open_here : forall f t ns ob, set_open_block f t ns ob t ns = ob.
Proof. intros. unfold set_open_block. now rewrite !Nat.eqb_refl. Qed.

Lemma set_open_other : forall f t ns ob t' ns',
  (t' <> t \/ ns' <> ns) -> set_open_block f t ns ob t' ns' = f t' ns'.
Proof.
  intros f t ns ob t' ns' H. unfold set_open_block.
  destruct (Nat.eqb t' t) eqn:E1; destruct (Nat.eqb ns' ns) eqn:E2; cbn; auto.
  apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2. destruct H; congruence.
Qed.

Lemma set_wp_here : forall f t ns v, set_write_ptr f t ns v t ns = v.
Proof. intros. unfold set_write_ptr. now rewrite !Nat.eqb_refl. Qed.

Lemma set_wp_other : forall f t ns v t' ns',
  (t' <> t \/ ns' <> ns) -> set_write_ptr f t ns v t' ns' = f t' ns'.
Proof.
  intros f t ns v t' ns' H. unfold set_write_ptr.
  destruct (Nat.eqb t' t) eqn:E1; destruct (Nat.eqb ns' ns) eqn:E2; cbn; auto.
  apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2. destruct H; congruence.
Qed.

(* Re-opening the block that is already open is a no-op. *)
Lemma set_open_idem : forall f t ns b t' ns',
  f t ns = Some b -> set_open_block f t ns (Some b) t' ns' = f t' ns'.
Proof.
  intros f t ns b t' ns' Hf.
  destruct (Nat.eq_dec t' t) as [Ht|Ht]; destruct (Nat.eq_dec ns' ns) as [Hns|Hns];
    try (rewrite set_open_other by auto; reflexivity).
  subst t' ns'. rewrite set_open_here. now symmetry.
Qed.

(* [AllocOK] survives an allocation.  The frontier moved up by one page, and
   everything at or above the new frontier was already erased. *)
Lemma alloc_preserves_AllocOK : forall s t ns pa s1,
  AllocOK s -> alloc_page s t ns = Some (pa, s1) -> AllocOK s1.
Proof.
  intros s t ns pa s1 [Hfr [H8 [H13 H23]]] Halloc.
  destruct (alloc_page_inv s t ns pa s1 Halloc) as [(Hob&Hpp&Hlt&Hs1)|[rest (Hfl&Hpp&Hs1)]].
  - (* frontier branch: only [write_ptr] moved *)
    subst s1. split; [|split; [|split]].
    + intros t' ns' b' Hob'. cbn in Hob' |- *.
      rewrite (set_open_idem _ _ _ _ _ _ Hob) in Hob'.
      destruct (Hfr t' ns' b' Hob') as (Hnf&Hopen&Huniq).
      split; [exact Hnf|]. split; [exact Hopen|].
      intros t'' ns'' Hob''. cbn in Hob''.
      rewrite (set_open_idem _ _ _ _ _ _ Hob) in Hob''.
      exact (Huniq t'' ns'' Hob'').
    + exact H8.
    + exact H13.
    + intros t' ns' b' q' Hob' Hwp Hq'. cbn in Hob', Hwp |- *.
      rewrite (set_open_idem _ _ _ _ _ _ Hob) in Hob'.
      destruct (Nat.eq_dec t' t) as [Ht|Ht]; destruct (Nat.eq_dec ns' ns) as [Hns|Hns];
        try (rewrite set_wp_other in Hwp by auto;
             exact (H23 t' ns' b' q' Hob' Hwp Hq')).
      subst t' ns'. rewrite set_wp_here in Hwp.
      apply (H23 t ns b' q' Hob'); [lia | exact Hq'].
  - (* fresh branch: the head of the free list becomes the open block *)
    assert (Hin : In (pa_block pa) (free_block_list s))
      by (rewrite Hfl; left; reflexivity).
    assert (Hnodup : ~ In (pa_block pa) rest).
    { unfold Inv11 in H13. rewrite Hfl in H13. inversion H13; subst. assumption. }
    (* an already-open block is distinct from the one just taken off the pool *)
    assert (Hopen_ne : forall t' ns' b', open_block s t' ns' = Some b' ->
                       b' <> pa_block pa).
    { intros t' ns' b' Hob' Heq. subst b'.
      destruct (Hfr t' ns' (pa_block pa) Hob') as (Hnf&_). exact (Hnf Hin). }
    (* the frontier clause for every owner other than the allocating one *)
    assert (Hother : forall t' ns' b',
      (t' <> t \/ ns' <> ns) -> open_block s t' ns' = Some b' ->
      ~ In b' rest /\
      set_block_open (close_open s t ns) (pa_block pa) true b' = true /\
      (forall t'' ns'',
         set_open_block (open_block s) t ns (Some (pa_block pa)) t'' ns'' = Some b' ->
         t'' = t' /\ ns'' = ns')).
    { intros t' ns' b' Hdiff Hob'.
      pose proof (Hopen_ne _ _ _ Hob') as Hne.
      destruct (Hfr t' ns' b' Hob') as (Hnf&Hopen&Huniq).
      split; [intros Hin'; apply Hnf; rewrite Hfl; right; exact Hin'|].
      split.
      - unfold set_block_open at 1. apply Nat.eqb_neq in Hne. rewrite Hne.
        unfold close_open.
        destruct (open_block s t ns) as [ob|] eqn:Hob2; [|exact Hopen].
        unfold set_block_open. destruct (Nat.eqb b' ob) eqn:E2; [|exact Hopen].
        exfalso. apply Nat.eqb_eq in E2. subst ob.
        destruct (Huniq t ns Hob2) as [Ht3 Hns3]. subst t' ns'.
        destruct Hdiff as [Hc|Hc]; apply Hc; reflexivity.
      - intros t'' ns'' Hob''.
        destruct (Nat.eq_dec t'' t) as [Ht2|Ht2];
          [destruct (Nat.eq_dec ns'' ns) as [Hns2|Hns2]|].
        + subst t'' ns''. rewrite set_open_here in Hob''. injection Hob'' as Hb.
          exfalso. apply Hne. now symmetry.
        + rewrite set_open_other in Hob'' by tauto. exact (Huniq t'' ns'' Hob'').
        + rewrite set_open_other in Hob'' by tauto. exact (Huniq t'' ns'' Hob''). }
    subst s1. split; [|split; [|split]].
    + intros t' ns' b' Hob'. cbn in Hob' |- *.
      destruct (Nat.eq_dec t' t) as [Ht|Ht];
        [destruct (Nat.eq_dec ns' ns) as [Hns|Hns]|].
      * subst t' ns'. rewrite set_open_here in Hob'. injection Hob' as Hb'. subst b'.
        split; [exact Hnodup|].
        split; [unfold set_block_open; now rewrite Nat.eqb_refl|].
        intros t'' ns'' Hob''.
        destruct (Nat.eq_dec t'' t) as [Ht2|Ht2];
          [destruct (Nat.eq_dec ns'' ns) as [Hns2|Hns2]|].
        -- subst t'' ns''. auto.
        -- rewrite set_open_other in Hob'' by tauto. exfalso.
           exact (Hopen_ne t'' ns'' (pa_block pa) Hob'' eq_refl).
        -- rewrite set_open_other in Hob'' by tauto. exfalso.
           exact (Hopen_ne t'' ns'' (pa_block pa) Hob'' eq_refl).
      * rewrite set_open_other in Hob' by tauto. apply Hother; tauto.
      * rewrite set_open_other in Hob' by tauto. apply Hother; tauto.
    + intros b0 Hin0 q0 Hq0. cbn in Hin0 |- *.
      apply (H8 b0); [rewrite Hfl; right; exact Hin0 | exact Hq0].
    + unfold Inv11. cbn. unfold Inv11 in H13. rewrite Hfl in H13.
      inversion H13; subst. assumption.
    + intros t' ns' b' q' Hob' Hwp Hq'. cbn in Hob', Hwp |- *.
      destruct (Nat.eq_dec t' t) as [Ht|Ht];
        [destruct (Nat.eq_dec ns' ns) as [Hns|Hns]|].
      * subst t' ns'. rewrite set_open_here in Hob'. injection Hob' as Hb'. subst b'.
        apply (H8 (pa_block pa)); [exact Hin | exact Hq'].
      * rewrite set_open_other in Hob' by tauto.
        rewrite set_wp_other in Hwp by tauto.
        exact (H23 t' ns' b' q' Hob' Hwp Hq').
      * rewrite set_open_other in Hob' by tauto.
        rewrite set_wp_other in Hwp by tauto.
        exact (H23 t' ns' b' q' Hob' Hwp Hq').
Qed.

(* [program_page] leaves the frontier fields alone, so [AllocOK] survives it as
   long as the page programmed lies below the frontier of the block it went
   into -- which is what [alloc_page_frontier] just established. *)
Lemma program_preserves_AllocOK : forall s t ns a p d pa,
  AllocOK s ->
  open_block s t ns = Some (pa_block pa) ->
  pa_page pa < write_ptr s t ns ->
  AllocOK (program_page s a p d pa).
Proof.
  intros s t ns a p d pa [Hfr [H8 [H13 H23]]] Hob Hlt.
  split; [|split; [|split]].
  - intros t' ns' b' Hob'. cbn in Hob'. cbn. exact (Hfr t' ns' b' Hob').
  - intros b0 Hin0 q0 Hq0. cbn in Hin0. cbn.
    assert (Hne : b0 <> pa_block pa).
    { intros Heq. subst b0. destruct (Hfr t ns (pa_block pa) Hob) as (Hnf&_).
      exact (Hnf Hin0). }
    destruct (H8 b0 Hin0 q0 Hq0) as [Hps Hpm].
    split.
    + rewrite set_ps_other by (left; exact Hne). exact Hps.
    + rewrite set_pm_other by (left; exact Hne). exact Hpm.
  - exact H13.
  - intros t' ns' b' q' Hob' Hwp Hq'. cbn in Hob', Hwp. cbn.
    assert (Hne : (b' <> pa_block pa \/ q' <> pa_page pa)).
    { destruct (Nat.eq_dec b' (pa_block pa)) as [Heq|Hne]; [|now left].
      right. subst b'.
      destruct (Hfr t' ns' (pa_block pa) Hob') as (_&_&Huniq).
      destruct (Huniq t ns Hob) as [Ht Hns]. subst t ns. lia. }
    destruct (H23 t' ns' b' q' Hob' Hwp Hq') as [Hps Hpm].
    split.
    + rewrite set_ps_other by exact Hne. exact Hps.
    + rewrite set_pm_other by exact Hne. exact Hpm.
Qed.

(* Invalidating a live page cannot disturb the frontier bundle: the page is
   live, and every page the bundle talks about is erased. *)
Lemma invalidate_preserves_AllocOK : forall s pa d,
  AllocOK s ->
  page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
  AllocOK (invalidate_at s pa).
Proof.
  intros s pa d [Hfr [H8 [H13 H23]]] Hlive.
  split; [|split; [|split]].
  - intros t' ns' b' Hob'. cbn in Hob'. cbn. exact (Hfr t' ns' b' Hob').
  - intros b0 Hin0 q0 Hq0. cbn in Hin0. cbn.
    destruct (H8 b0 Hin0 q0 Hq0) as [Hps Hpm].
    assert (Hne : (b0 <> pa_block pa \/ q0 <> pa_page pa)).
    { destruct (Nat.eq_dec b0 (pa_block pa)) as [Heq|Hne]; [|now left].
      destruct (Nat.eq_dec q0 (pa_page pa)) as [Heq2|Hne2]; [|now right].
      subst b0 q0. rewrite Hlive in Hps. discriminate. }
    split.
    + rewrite set_ps_other by exact Hne. exact Hps.
    + rewrite set_pm_other by exact Hne. exact Hpm.
  - exact H13.
  - intros t' ns' b' q' Hob' Hwp Hq'. cbn in Hob', Hwp. cbn.
    destruct (H23 t' ns' b' q' Hob' Hwp Hq') as [Hps Hpm].
    assert (Hne : (b' <> pa_block pa \/ q' <> pa_page pa)).
    { destruct (Nat.eq_dec b' (pa_block pa)) as [Heq|Hne]; [|now left].
      destruct (Nat.eq_dec q' (pa_page pa)) as [Heq2|Hne2]; [|now right].
      subst b' q'. rewrite Hlive in Hps. discriminate. }
    split.
    + rewrite set_ps_other by exact Hne. exact Hps.
    + rewrite set_pm_other by exact Hne. exact Hpm.
Qed.

(* ══════════════════════════════════════════════════════════════════
   4.  Per-operation simulation: read, set-tag, invalidate, write
   ══════════════════════════════════════════════════════════════════ *)

(* ── COpRead: neither side moves ──────────────────────────────────── *)

Lemma read_preserves_CR : forall h s s' a p,
  CR h s -> step s (COpRead a p) = Some s' -> CR h s'.
Proof.
  intros h s s' a p HCR Hstep. cbn [step] in Hstep.
  injection Hstep as Hs'. subst s'. exact HCR.
Qed.

(* ── COpSetTag: only the tag field of one page meta moves ─────────── *)

Lemma set_tag_preserves_CR : forall h s s' a p tag,
  CR h s -> step s (COpSetTag a p tag) = Some s' -> CR h s'.
Proof.
  intros h s s' a p tag HCR Hstep. cbn [step] in Hstep.
  injection Hstep as Hs'. subst s'.
  unfold exec_set_tag.
  destruct (l2p_map s a p) as [pa|] eqn:Hm; [|exact HCR].
  (* [set_page_tag_at] rewrites [page_meta] alone, so the mapping and the page
     states the relation talks about are unchanged up to conversion. *)
  destruct (page_state s (pa_block pa) (pa_page pa)) eqn:Hps; exact HCR.
Qed.

(* ── COpInvalidate: the abstract effect is *not* the identity ─────── *)

Lemma abs_invalidate_le : forall h a0 p0 a p d,
  abs_invalidate h a0 p0 a p = Some d -> h a p = Some d /\ (a <> a0 \/ p <> p0).
Proof.
  intros h a0 p0 a p d H.
  destruct (Nat.eq_dec a a0) as [Ha|Ha]; destruct (Nat.eq_dec p p0) as [Hp|Hp].
  - subst a p. rewrite abs_invalidate_here in H. discriminate.
  - rewrite abs_invalidate_other in H by tauto. split; [exact H | tauto].
  - rewrite abs_invalidate_other in H by tauto. split; [exact H | tauto].
  - rewrite abs_invalidate_other in H by tauto. split; [exact H | tauto].
Qed.

Lemma invalidate_preserves_CR : forall h s s' a p,
  ftl_invariant s -> CR h s -> step s (COpInvalidate a p) = Some s' ->
  CR (abs_invalidate h a p) s'.
Proof.
  intros h s s' a p Hinv HCR Hstep. cbn [step] in Hstep.
  injection Hstep as Hs'. subst s'.
  destruct Hinv as (_&_&_&_&I4&_).
  unfold exec_invalidate.
  destruct (l2p_map s a p) as [old|] eqn:Hold.
  - intros a0 p0 d0 Hread.
    destruct (abs_invalidate_le h a p a0 p0 d0 Hread) as [Hread' Hne].
    destruct (HCR a0 p0 d0 Hread') as [pa0 [Hm0 Hps0]].
    exists pa0. split.
    + cbn [l2p_map unmap]. rewrite set_l2p_other by exact Hne.
      cbn [l2p_map invalidate_at]. exact Hm0.
    + assert (Hpne : pa_block pa0 <> pa_block old \/ pa_page pa0 <> pa_page old).
      { destruct (Nat.eq_dec (pa_block pa0) (pa_block old)) as [Eb|Eb]; [|now left].
        destruct (Nat.eq_dec (pa_page pa0) (pa_page old)) as [Ep|Ep]; [|now right].
        exfalso.
        assert (Hsame : pa0 = old)
          by (destruct pa0; destruct old; cbn in Eb, Ep; congruence).
        subst pa0. destruct (I4 a0 p0 a p old Hm0 Hold) as [Ha Hp].
        destruct Hne as [Hc|Hc]; auto. }
      cbn [page_state unmap invalidate_at].
      rewrite set_ps_other by exact Hpne. exact Hps0.
  - intros a0 p0 d0 Hread.
    destruct (abs_invalidate_le h a p a0 p0 d0 Hread) as [Hread' _].
    exact (HCR a0 p0 d0 Hread').
Qed.

(* The identity is not a simulation for [COpInvalidate], and this is not a
   statement about some pathological state: whenever the abstract device holds
   the cell being detached, carrying the cell across the step is unsound.  The
   FTL drops the forward mapping, so nothing backs the cell afterwards.  A
   whole-trace theorem must therefore push [abs_invalidate] through this
   operation, not the identity. *)
Theorem invalidate_identity_is_not_a_simulation : forall h s s' a p d,
  CR h s -> h a p = Some d -> step s (COpInvalidate a p) = Some s' -> ~ CR h s'.
Proof.
  intros h s s' a p d HCR Hcell Hstep HCR'.
  destruct (HCR a p d Hcell) as [pa [Hm _]].
  cbn [step] in Hstep. injection Hstep as Hs'. subst s'.
  unfold exec_invalidate in HCR'. rewrite Hm in HCR'.
  destruct (HCR' a p d Hcell) as [pa' [Hm' _]].
  cbn [l2p_map unmap] in Hm'. rewrite set_l2p_here in Hm'. discriminate.
Qed.

(* ── COpWrite: out of place, with no relocation and no erase ──────── *)

(* The final two steps of a write: take a fresh page and program it.  [s1] is
   the state after the old page has been staled, which is why the hypothesis
   about surviving cells excludes the cell being rewritten. *)
Lemma write_install_CR : forall h s s1 s2 a p d pa t ns,
  CR h s ->
  l2p_map s1 = l2p_map s ->
  (forall a0 p0 pa0 d0, (a0 <> a \/ p0 <> p) -> l2p_map s a0 p0 = Some pa0 ->
     page_state s (pa_block pa0) (pa_page pa0) = PS_Valid d0 ->
     page_state s1 (pa_block pa0) (pa_page pa0) = PS_Valid d0) ->
  AllocOK s1 ->
  alloc_page s1 t ns = Some (pa, s2) ->
  CR (abs_write h a p d) (program_page s2 a p d pa).
Proof.
  intros h s s1 s2 a p d pa t ns HCR Hl2p Hsurvive Hok Halloc.
  destruct (alloc_page_fields s1 t ns pa s2 Halloc) as (Hf1&Hf2&_).
  destruct (alloc_page_dest_empty s1 t ns pa s2 Hok Halloc) as [Hempty _].
  intros a0 p0 d0 Hread.
  destruct (Nat.eq_dec a0 a) as [Ha|Ha]; [destruct (Nat.eq_dec p0 p) as [Hp|Hp]|].
  - (* the cell just written *)
    subst a0 p0. rewrite abs_write_here in Hread. injection Hread as Hd. subst d0.
    exists pa. split.
    + cbn [l2p_map program_page]. apply set_l2p_here.
    + cbn [page_state program_page]. apply set_ps_here.
  - (* same address, another page: survives *)
    subst a0. rewrite abs_write_other in Hread by tauto.
    destruct (HCR a p0 d0 Hread) as [pa0 [Hm0 Hps0]].
    assert (Hps1 : page_state s1 (pa_block pa0) (pa_page pa0) = PS_Valid d0)
      by (apply (Hsurvive a p0 pa0 d0); [tauto | exact Hm0 | exact Hps0]).
    assert (Hpne : pa_block pa0 <> pa_block pa \/ pa_page pa0 <> pa_page pa).
    { destruct (Nat.eq_dec (pa_block pa0) (pa_block pa)) as [Eb|Eb]; [|now left].
      destruct (Nat.eq_dec (pa_page pa0) (pa_page pa)) as [Ep|Ep]; [|now right].
      exfalso. rewrite Eb, Ep, Hempty in Hps1. discriminate. }
    exists pa0. split.
    + cbn [l2p_map program_page]. rewrite set_l2p_other by tauto.
      rewrite Hf1, Hl2p. exact Hm0.
    + cbn [page_state program_page]. rewrite set_ps_other by exact Hpne.
      rewrite Hf2. exact Hps1.
  - (* another address *)
    rewrite abs_write_other in Hread by tauto.
    destruct (HCR a0 p0 d0 Hread) as [pa0 [Hm0 Hps0]].
    assert (Hps1 : page_state s1 (pa_block pa0) (pa_page pa0) = PS_Valid d0)
      by (apply (Hsurvive a0 p0 pa0 d0); [tauto | exact Hm0 | exact Hps0]).
    assert (Hpne : pa_block pa0 <> pa_block pa \/ pa_page pa0 <> pa_page pa).
    { destruct (Nat.eq_dec (pa_block pa0) (pa_block pa)) as [Eb|Eb]; [|now left].
      destruct (Nat.eq_dec (pa_page pa0) (pa_page pa)) as [Ep|Ep]; [|now right].
      exfalso. rewrite Eb, Ep, Hempty in Hps1. discriminate. }
    exists pa0. split.
    + cbn [l2p_map program_page]. rewrite set_l2p_other by tauto.
      rewrite Hf1, Hl2p. exact Hm0.
    + cbn [page_state program_page]. rewrite set_ps_other by exact Hpne.
      rewrite Hf2. exact Hps1.
Qed.

Lemma write_preserves_CR : forall h s s' a p d,
  ftl_invariant s -> CR h s -> step s (COpWrite a p d) = Some s' ->
  CR (abs_write h a p d) s'.
Proof.
  intros h s s' a p d Hinv HCR Hstep.
  pose proof (alloc_ok_of_invariant s Hinv) as Hok.
  assert (I4 : Inv2 s) by (destruct Hinv as (_&_&_&_&I&_); exact I).
  assert (I24 : Inv22 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I&_); exact I).
  cbn [step] in Hstep.
  match type of Hstep with
  | (if ?c then _ else _) = _ => destruct c eqn:Hguard
  end; [|discriminate].
  unfold exec_write in Hstep. cbv zeta in Hstep.
  destruct (addr_tenant s a) as [t|] eqn:Ht; [|discriminate].
  destruct (addr_namespace s a) as [ns|] eqn:Hns; [|discriminate].
  destruct (l2p_map s a p) as [old|] eqn:Hold.
  - (* the logical page already had a home; it is staled first *)
    assert (Hlive : exists dold,
      page_state s (pa_block old) (pa_page old) = PS_Valid dold)
      by (exact (I24 a p old Hold)).
    destruct Hlive as [dold Hlive].
    destruct (alloc_page (invalidate_at s old) t ns) as [[pa s2]|] eqn:Halloc;
      [|discriminate].
    injection Hstep as Hs'. subst s'.
    apply (write_install_CR h s (invalidate_at s old) s2 a p d pa t ns).
    + exact HCR.
    + reflexivity.
    + intros a0 p0 pa0 d0 Hne Hm0 Hps0.
      assert (Hpne : pa_block pa0 <> pa_block old \/ pa_page pa0 <> pa_page old).
      { destruct (Nat.eq_dec (pa_block pa0) (pa_block old)) as [Eb|Eb]; [|now left].
        destruct (Nat.eq_dec (pa_page pa0) (pa_page old)) as [Ep|Ep]; [|now right].
        exfalso.
        assert (Hsame : pa0 = old)
          by (destruct pa0; destruct old; cbn in Eb, Ep; congruence).
        subst pa0. destruct (I4 a0 p0 a p old Hm0 Hold) as [Ha Hp].
        destruct Hne as [Hc|Hc]; auto. }
      cbn [page_state invalidate_at]. rewrite set_ps_other by exact Hpne. exact Hps0.
    + exact (invalidate_preserves_AllocOK s old dold Hok Hlive).
    + exact Halloc.
  - (* a fresh logical page: nothing to stale *)
    destruct (alloc_page s t ns) as [[pa s2]|] eqn:Halloc; [|discriminate].
    injection Hstep as Hs'. subst s'.
    apply (write_install_CR h s s s2 a p d pa t ns).
    + exact HCR.
    + reflexivity.
    + intros a0 p0 pa0 d0 _ _ Hps0. exact Hps0.
    + exact Hok.
    + exact Halloc.
Qed.

(* ══════════════════════════════════════════════════════════════════
   5.  COpGC and COpWearLevel
   ══════════════════════════════════════════════════════════════════ *)

(* A two-way decision on logical pages, so that the case analyses below split
   into two branches rather than four. *)
Definition lp_dec (a1 p1 a2 p2 : nat) : {a1 = a2 /\ p1 = p2} + {a1 <> a2 \/ p1 <> p2}.
Proof.
  destruct (Nat.eq_dec a1 a2) as [Ha|Ha]; destruct (Nat.eq_dec p1 p2) as [Hp|Hp].
  - left; split; assumption.
  - right; right; assumption.
  - right; left; assumption.
  - right; left; assumption.
Defined.

(* Reclaiming a block relocates its live pages one at a time, and the states
   in between do NOT satisfy the invariant: [program_page] stamps the
   destination and repairs the mapping but never touches the source, so a page
   already moved stays PS_Valid in the victim while nothing maps to it.  Inv4
   is therefore false in the middle of the fold, and the loop has to run
   against a version of it relativised by the victim and by the pages still to
   be processed. *)
Definition Inv4_rel (s : FTLState) (b : Block) (ps : list Page) : Prop :=
  forall a p b0 q d,
    page_state s b0 q = PS_Valid d ->
    page_lpa (page_meta s b0 q) = Some (a, p) ->
    (b0 <> b \/ In q ps) ->
    l2p_map s a p = Some (mkPhysAddr b0 q).

(* Every mapping into the victim still lands on a page the fold has yet to
   reach.  At [ps = []] this is exactly what [erase_block] needs. *)
Definition Progress (s : FTLState) (b : Block) (ps : list Page) : Prop :=
  forall a p pa, l2p_map s a p = Some pa -> pa_block pa = b -> In (pa_page pa) ps.

Definition GCLoop (s : FTLState) (b : Block) (ps : list Page) : Prop :=
  AllocOK s /\ Inv2 s /\ Inv22 s /\ Inv4_rel s b ps /\ Progress s b ps /\
  NoDup ps /\ NotVictim s b.

(* A page of the victim that is not live is skipped, and nothing maps to it. *)
Lemma gcloop_skip : forall s b q tl,
  GCLoop s b (q :: tl) ->
  (forall d, page_state s b q <> PS_Valid d) ->
  GCLoop s b tl.
Proof.
  intros s b q tl (Hok&I4&I24&I6&Hprog&Hnd&Hnv) Hdead.
  split; [exact Hok|]. split; [exact I4|]. split; [exact I24|].
  split.
  - intros a p b0 q0 d Hps Hlpa Hcase.
    apply (I6 a p b0 q0 d Hps Hlpa).
    destruct Hcase as [Hc|Hc]; [now left | right; now right].
  - split.
    + intros a p pa Hm Hblk.
      destruct (Hprog a p pa Hm Hblk) as [Hq|Hin]; [|exact Hin].
      exfalso. destruct (I24 a p pa Hm) as [d Hd].
      apply (Hdead d). rewrite <- Hblk, Hq. exact Hd.
    + split; [now inversion Hnd | exact Hnv].
Qed.

(* The step of the fold.  Everything the abstract device holds survives the
   relocation of one page, and the relativised bundle shrinks by that page. *)
Lemma relocate_page_step : forall s b q tl s2,
  GCLoop s b (q :: tl) ->
  relocate_page s b q = Some s2 ->
  GCLoop s2 b tl /\ (forall a p d, backs s a p d -> backs s2 a p d).
Proof.
  intros s b q tl s2 Hloop Hrel.
  pose proof Hloop as (Hok&I4&I24&I6&Hprog&Hnd&Hnv).
  unfold relocate_page in Hrel.
  destruct (page_state s b q) as [| |d0] eqn:Hpsq.
  - injection Hrel as Hs2. subst s2.
    split; [apply (gcloop_skip s b q tl Hloop); intros d Hc; rewrite Hpsq in Hc;
            discriminate | auto].
  - injection Hrel as Hs2. subst s2.
    split; [apply (gcloop_skip s b q tl Hloop); intros d Hc; rewrite Hpsq in Hc;
            discriminate | auto].
  - (* the page is live: it moves, carrying its OOB stamp *)
    destruct (page_lpa (page_meta s b q)) as [[a0 p0]|] eqn:Hlpa; [|discriminate].
    destruct (addr_tenant s a0) as [t|] eqn:Ht; [|discriminate].
    destruct (addr_namespace s a0) as [ns|] eqn:Hns; [|discriminate].
    destruct (alloc_page s t ns) as [[pa s1]|] eqn:Halloc; [|discriminate].
    injection Hrel as Hs2. subst s2.
    destruct (alloc_page_fields s t ns pa s1 Halloc) as (Hf1&Hf2&_&Hf4&_).
    destruct (alloc_page_dest_empty s t ns pa s1 Hok Halloc) as [Hempty _].
    pose proof (alloc_dest_not_victim s t ns pa s1 b (proj1 Hok) Hnv Halloc) as Hbne.
    (* the source page is mapped exactly at its own stamp *)
    assert (H6q : l2p_map s a0 p0 = Some (mkPhysAddr b q))
      by (apply (I6 a0 p0 b q d0 Hpsq Hlpa); right; now left).
    (* nothing maps to the destination: it is erased *)
    assert (Hnotmapped : forall x y, l2p_map s x y <> Some pa).
    { intros x y Hc. destruct (I24 x y pa Hc) as [dd Hdd].
      rewrite Hempty in Hdd. discriminate. }
    assert (Hdiff : forall x, (exists dd, page_state s (pa_block x) (pa_page x) = PS_Valid dd) ->
                    (pa_block x <> pa_block pa \/ pa_page x <> pa_page pa)).
    { intros x [dd Hdd].
      destruct (Nat.eq_dec (pa_block x) (pa_block pa)) as [Eb|Eb]; [|now left].
      destruct (Nat.eq_dec (pa_page x) (pa_page pa)) as [Ep|Ep]; [|now right].
      exfalso. rewrite Eb, Ep, Hempty in Hdd. discriminate. }
    (* pointwise views of the programmed state *)
    assert (Hl2ph : l2p_map (program_page s1 a0 p0 d0 pa) a0 p0 = Some pa)
      by (cbn [l2p_map program_page]; apply set_l2p_here).
    assert (Hl2po : forall x y, (x <> a0 \/ y <> p0) ->
              l2p_map (program_page s1 a0 p0 d0 pa) x y = l2p_map s x y).
    { intros x y H. cbn [l2p_map program_page].
      rewrite set_l2p_other by exact H. now rewrite Hf1. }
    assert (Hpsh : page_state (program_page s1 a0 p0 d0 pa)
                     (pa_block pa) (pa_page pa) = PS_Valid d0)
      by (cbn [page_state program_page]; apply set_ps_here).
    assert (Hpso : forall x y, (x <> pa_block pa \/ y <> pa_page pa) ->
              page_state (program_page s1 a0 p0 d0 pa) x y = page_state s x y).
    { intros x y H. cbn [page_state program_page].
      rewrite set_ps_other by exact H. now rewrite Hf2. }
    assert (Hpmh : page_lpa (page_meta (program_page s1 a0 p0 d0 pa)
                     (pa_block pa) (pa_page pa)) = Some (a0, p0))
      by (cbn [page_meta program_page]; now rewrite set_pm_here).
    assert (Hpmo : forall x y, (x <> pa_block pa \/ y <> pa_page pa) ->
              page_meta (program_page s1 a0 p0 d0 pa) x y = page_meta s x y).
    { intros x y H. cbn [page_meta program_page].
      rewrite set_pm_other by exact H. now rewrite Hf4. }
    split.
    + (* the bundle, minus the page just moved *)
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      * (* AllocOK *)
        destruct (alloc_page_frontier s t ns pa s1 Halloc) as [Hob1 Hwp1].
        apply (program_preserves_AllocOK s1 t ns a0 p0 d0 pa);
          [ exact (alloc_preserves_AllocOK s t ns pa s1 Hok Halloc)
          | exact Hob1 | exact Hwp1 ].
      * (* Inv2 *)
        intros a1 p1 a2 p2 x Hm1 Hm2.
        destruct (lp_dec a1 p1 a0 p0) as [[E1 E2]|Hne1];
          destruct (lp_dec a2 p2 a0 p0) as [[F1 F2]|Hne2].
        -- subst. auto.
        -- exfalso. subst a1 p1. rewrite Hl2ph in Hm1. injection Hm1 as Hx. subst x.
           rewrite Hl2po in Hm2 by exact Hne2. exact (Hnotmapped a2 p2 Hm2).
        -- exfalso. subst a2 p2. rewrite Hl2ph in Hm2. injection Hm2 as Hx. subst x.
           rewrite Hl2po in Hm1 by exact Hne1. exact (Hnotmapped a1 p1 Hm1).
        -- rewrite Hl2po in Hm1 by exact Hne1. rewrite Hl2po in Hm2 by exact Hne2.
           exact (I4 a1 p1 a2 p2 x Hm1 Hm2).
      * (* Inv22 *)
        intros a1 p1 x Hm.
        destruct (lp_dec a1 p1 a0 p0) as [[E1 E2]|Hne1].
        -- subst a1 p1. rewrite Hl2ph in Hm. injection Hm as Hx. subst x.
           exists d0. exact Hpsh.
        -- rewrite Hl2po in Hm by exact Hne1.
           destruct (I24 a1 p1 x Hm) as [dd Hdd].
           exists dd. rewrite Hpso; [exact Hdd | apply Hdiff; now exists dd].
      * (* Inv4, relativised to the remaining pages *)
        intros a1 p1 b1 q1 d1 Hps1 Hlpa1 Hcase.
        destruct (lp_dec b1 q1 (pa_block pa) (pa_page pa)) as [[E1 E2]|Hpne].
        -- subst b1 q1. rewrite Hpmh in Hlpa1. injection Hlpa1 as Ha Hp.
           subst a1 p1. rewrite physaddr_eta. exact Hl2ph.
        -- rewrite Hpso in Hps1 by exact Hpne. rewrite Hpmo in Hlpa1 by exact Hpne.
           assert (Hcase' : b1 <> b \/ In q1 (q :: tl))
             by (destruct Hcase as [Hc|Hc]; [now left | right; now right]).
           pose proof (I6 a1 p1 b1 q1 d1 Hps1 Hlpa1 Hcase') as Hm.
           destruct (lp_dec a1 p1 a0 p0) as [[E1 E2]|Hne1].
           ++ exfalso. subst a1 p1. rewrite H6q in Hm. injection Hm as Hb Hq.
              subst b1 q1.
              destruct Hcase as [Hc|Hc]; [now apply Hc|].
              inversion Hnd; subst. contradiction.
           ++ rewrite Hl2po by exact Hne1. exact Hm.
      * (* progress *)
        intros a1 p1 x Hm Hblk.
        destruct (lp_dec a1 p1 a0 p0) as [[E1 E2]|Hne1].
        -- exfalso. subst a1 p1. rewrite Hl2ph in Hm. injection Hm as Hx. subst x.
           exact (Hbne Hblk).
        -- rewrite Hl2po in Hm by exact Hne1.
           destruct (Hprog a1 p1 x Hm Hblk) as [Hq|Hin]; [|exact Hin].
           exfalso.
           assert (Hx : x = mkPhysAddr b q)
             by (destruct x; cbn in Hblk, Hq; congruence).
           subst x.
           destruct (I4 a1 p1 a0 p0 (mkPhysAddr b q) Hm H6q) as [Ha Hp].
           destruct Hne1 as [Hc|Hc]; auto.
      * now inversion Hnd.
      * exact (alloc_preserves_NotVictim s t ns pa s1 b (proj1 Hok) Hnv Halloc).
    + (* every backed cell survives *)
      intros a1 p1 d1 [x [Hm Hps]].
      destruct (lp_dec a1 p1 a0 p0) as [[E1 E2]|Hne1].
      * subst a1 p1. rewrite H6q in Hm. injection Hm as Hx. subst x.
        cbn in Hps. rewrite Hpsq in Hps. injection Hps as Hd. subst d1.
        exists pa. split; [exact Hl2ph | exact Hpsh].
      * exists x. split.
        -- rewrite Hl2po by exact Hne1. exact Hm.
        -- rewrite Hpso; [exact Hps | apply Hdiff; now exists d1].
Qed.

Lemma relocate_pages_loop : forall ps s b s1,
  GCLoop s b ps -> relocate_pages s b ps = Some s1 ->
  GCLoop s1 b [] /\ (forall a p d, backs s a p d -> backs s1 a p d).
Proof.
  induction ps as [|q tl IH]; intros s b s1 Hloop Hrel.
  - cbn [relocate_pages] in Hrel. injection Hrel as Hs1. subst s1.
    split; [exact Hloop | auto].
  - cbn [relocate_pages] in Hrel.
    destruct (relocate_page s b q) as [s2|] eqn:Hstep; [|discriminate].
    destruct (relocate_page_step s b q tl s2 Hloop Hstep) as [Hloop2 Hback].
    destruct (IH s2 b s1 Hloop2 Hrel) as [Hloop3 Hback3].
    split; [exact Hloop3|]. intros a p d Hb. apply Hback3, Hback, Hb.
Qed.

Lemma erase_preserves_backs : forall s b a p d,
  Progress s b [] -> backs s a p d -> backs (erase_block s b) a p d.
Proof.
  intros s b a p d Hprog [pa [Hm Hps]].
  assert (Hne : pa_block pa <> b) by (intros Hc; exact (Hprog a p pa Hm Hc)).
  exists pa. split.
  - cbn [l2p_map erase_block]. exact Hm.
  - cbn [page_state erase_block]. apply Nat.eqb_neq in Hne. rewrite Hne. exact Hps.
Qed.

Lemma find_victim_aux_reclaimable : forall s n b,
  find_victim_aux s n = Some b -> reclaimable s b = true.
Proof.
  intros s n. induction n as [|k IH]; intros b H; cbn in H; [discriminate|].
  destruct (reclaimable s k) eqn:E.
  - injection H as Hb. subst b. exact E.
  - exact (IH b H).
Qed.

Lemma reclaimable_NotVictim : forall s b,
  ftl_invariant s -> reclaimable s b = true -> NotVictim s b.
Proof.
  intros s b Hinv Hrec. unfold reclaimable, is_open in Hrec.
  apply andb_prop in Hrec as [Hfree Hopen].
  apply negb_true_iff in Hfree. apply negb_true_iff in Hopen.
  destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I26&_).
  split; [|exact Hopen].
  intros Hin. apply (proj2 (I26 b)) in Hin. rewrite Hfree in Hin. discriminate.
Qed.

Lemma gc_loop_start : forall s b,
  ftl_invariant s -> reclaimable s b = true -> GCLoop s b all_pages.
Proof.
  intros s b Hinv Hrec.
  pose proof (alloc_ok_of_invariant s Hinv) as Hok.
  pose proof (reclaimable_NotVictim s b Hinv Hrec) as Hnv.
  assert (I3 : Inv1 s) by (destruct Hinv as (_&_&_&I&_); exact I).
  assert (I4 : Inv2 s) by (destruct Hinv as (_&_&_&_&I&_); exact I).
  assert (I6 : Inv4 s) by (destruct Hinv as (_&_&_&_&_&_&I&_); exact I).
  assert (I24 : Inv22 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&I&_); exact I).
  split; [exact Hok|]. split; [exact I4|]. split; [exact I24|].
  split; [intros a p b0 q d Hps Hlpa _; exact (I6 a p b0 q d Hps Hlpa)|].
  split.
  - intros a p pa Hm _. unfold all_pages. apply in_seq.
    destruct (I3 a p pa Hm) as (_&Hpp&_). lia.
  - split; [unfold all_pages; apply seq_NoDup | exact Hnv].
Qed.

(* Reclaiming moves live pages and erases the victim; the abstract device does
   not move at all.  Which block is reclaimed is irrelevant to the relation,
   so this is proved once for any admissible victim and the two maintenance
   operations are instances. *)
Lemma reclaim_preserves_CR : forall h s b s',
  ftl_invariant s -> CR h s ->
  reclaimable s b = true -> reclaim s b = Some s' -> CR h s'.
Proof.
  intros h s b s' Hinv HCR Hrec Hrc. unfold reclaim in Hrc.
  destruct (relocate_pages s b all_pages) as [s1|] eqn:Hrel; [|discriminate].
  injection Hrc as Hs'. subst s'.
  destruct (relocate_pages_loop all_pages s b s1
              (gc_loop_start s b Hinv Hrec) Hrel) as [Hloop1 Hback].
  destruct Hloop1 as (_&_&_&_&Hprog1&_).
  intros a p d Hread.
  apply (erase_preserves_backs s1 b a p d Hprog1).
  apply Hback. exact (HCR a p d Hread).
Qed.

Lemma reclaim_with_preserves_CR : forall pick h s s',
  victim_sound pick -> ftl_invariant s -> CR h s ->
  reclaim_with pick s = Some s' -> CR h s'.
Proof.
  intros pick h s s' Hpick Hinv HCR Hstep. unfold reclaim_with in Hstep.
  destruct (pick s) as [b|] eqn:Hv; [|discriminate].
  exact (reclaim_preserves_CR h s b s' Hinv HCR (proj2 (Hpick s b Hv)) Hstep).
Qed.

Lemma gc_preserves_CR : forall h s s',
  ftl_invariant s -> CR h s -> step s COpGC = Some s' -> CR h s'.
Proof.
  intros h s s' Hinv HCR Hstep.
  change (step s COpGC) with (reclaim_with find_victim s) in Hstep.
  exact (reclaim_with_preserves_CR find_victim h s s'
           find_victim_sound Hinv HCR Hstep).
Qed.

(* Wear levelling is the same transformer under the least-worn-block policy;
   only the chooser instantiated differs. *)
Lemma wear_level_preserves_CR : forall h s s',
  ftl_invariant s -> CR h s -> step s COpWearLevel = Some s' -> CR h s'.
Proof.
  intros h s s' Hinv HCR Hstep.
  change (step s COpWearLevel) with (reclaim_with find_least_worn_victim s)
    in Hstep.
  exact (reclaim_with_preserves_CR find_least_worn_victim h s s'
           find_least_worn_victim_sound Hinv HCR Hstep).
Qed.

(* ══════════════════════════════════════════════════════════════════
   6.  The invalidate refutation is not vacuous
   ══════════════════════════════════════════════════════════════════

   [invalidate_identity_is_not_a_simulation] is universally quantified, so on
   its own it would still be compatible with there being no state at all in
   which the abstract device holds the cell being detached.  The witness below
   closes that gap: a state satisfying all 29 conjuncts, in which the abstract
   device holds one cell, and whose detachment breaks the relation.  Blocks
   0..6 are free, block 7 holds the single live page, and no block is open, so
   every frontier clause is vacuous. *)

Definition wsel (x y : nat) : bool := andb (Nat.eqb x 7) (Nat.eqb y 0).
Definition wsel0 (x y : nat) : bool := andb (Nat.eqb x 0) (Nat.eqb y 0).

Lemma wsel_true : forall x y, wsel x y = true -> x = 7 /\ y = 0.
Proof.
  intros x y H. unfold wsel in H. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2. auto.
Qed.

Lemma wsel0_true : forall x y, wsel0 x y = true -> x = 0 /\ y = 0.
Proof.
  intros x y H. unfold wsel0 in H. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2. auto.
Qed.

Definition wl2p (a : Addr) (p : Page) : option PhysAddr :=
  if wsel0 a p then Some (mkPhysAddr 7 0) else None.
Definition wps (b : Block) (p : Page) : PageState :=
  if wsel b p then PS_Valid 0 else PS_Empty.
Definition wpr (b : Block) (p : Page) : option Role :=
  if wsel b p then Some RData else None.
Definition wpm (b : Block) (p : Page) : PageMeta :=
  if wsel b p then mkPageMeta 0 0 (Some 0) (Some (0, 0)) else empty_page_meta.
Definition wbt (b : Block) : option TenantId := if Nat.eqb b 7 then Some 0 else None.
Definition wbn (b : Block) : option NamespaceId := if Nat.eqb b 7 then Some 0 else None.

Definition wstate : FTLState :=
  mkFTLState wl2p wps wpr (fun _ => Some 0) (fun _ => Some 0) wbt wbn wpm
    (fun _ => None) (seq 0 7) (fun b => Nat.ltb b 7) (fun _ => 0) (fun _ => None)
    (fun _ _ => None) (fun _ _ => 0) (fun _ => false).

Lemma wstate_invariant : ftl_invariant wstate.
Proof.
  apply make_ftl_invariant.
  - exact pages_per_block_gt0.
  - intros b p _ _. exists (wps b p). reflexivity.
  - intros b p d H. cbn in H. unfold wps in H.
    destruct (wsel b p) eqn:E; [|discriminate].
    apply wsel_true in E as [Eb Ep]. subst b p.
    exists 0, 0. reflexivity.
  - intros a p pa H. cbn in H. unfold wl2p in H.
    destruct (wsel0 a p) eqn:E; [|discriminate].
    apply wsel0_true in E as [Ea Ep]. subst a p.
    injection H as Hpa. subst pa. cbn.
    unfold total_blocks, pages_per_block, addr_space. lia.
  - intros a1 p1 a2 p2 pa H1 H2. cbn in H1, H2. unfold wl2p in H1, H2.
    destruct (wsel0 a1 p1) eqn:E1; [|discriminate].
    destruct (wsel0 a2 p2) eqn:E2; [|discriminate].
    apply wsel0_true in E1 as [? ?]; apply wsel0_true in E2 as [? ?]. subst. auto.
  - intros a p pa d H _. cbn in H |- *. unfold wl2p in H.
    destruct (wsel0 a p) eqn:E; [|discriminate].
    apply wsel0_true in E as [Ea Ep]. subst a p.
    injection H as Hpa. subst pa. reflexivity.
  - intros a p b q d Hps Hlpa. cbn in Hps, Hlpa |- *.
    unfold wps in Hps. destruct (wsel b q) eqn:E; [|discriminate].
    apply wsel_true in E as [Eb Eq]. subst b q.
    unfold wpm in Hlpa. cbn in Hlpa. injection Hlpa as Ha Hp. subst a p.
    reflexivity.
  - intros a p pa H. cbn in H |- *. unfold wl2p in H.
    destruct (wsel0 a p) eqn:E; [|discriminate].
    apply wsel0_true in E as [Ea Ep]. subst a p.
    injection H as Hpa. subst pa.
    change (~ In 7 (seq 0 7)). intros Hin. apply in_seq in Hin. lia.
  - intros b Hin p _. change (In b (seq 0 7)) in Hin. apply in_seq in Hin.
    assert (Hne : Nat.eqb b 7 = false) by (apply Nat.eqb_neq; lia).
    change (wps b p = PS_Empty /\ wpm b p = empty_page_meta).
    unfold wps, wpm, wsel. rewrite Hne. cbn. auto.
  - intros a p pa d t ns Hm _ Ht Hns. cbn in Hm, Ht, Hns |- *.
    injection Ht as Ht; injection Hns as Hns; subst t ns.
    unfold wl2p in Hm. destruct (wsel0 a p) eqn:E; [|discriminate].
    injection Hm as Hpa. subst pa. cbn. auto.
  - intros b Hin. change (In b (seq 0 7)) in Hin. apply in_seq in Hin.
    unfold total_blocks. lia.
  - intros b p d H. cbn in H |- *. unfold wps in H.
    destruct (wsel b p) eqn:E; [|discriminate].
    apply wsel_true in E as [Eb Ep]. subst b p. exists 0. reflexivity.
  - intros b Hb. unfold total_blocks in Hb.
    destruct (Nat.eq_dec b 7) as [E|E].
    + subst b. right. right. left. exists 0, 0, (mkPhysAddr 7 0).
      split; reflexivity.
    + left. change (In b (seq 0 7)). apply in_seq. lia.
  - change (NoDup (seq 0 7)). apply seq_NoDup.
  - intros b Hb [p Hp]. cbn in Hp. unfold wpr in Hp.
    destruct (wsel b p); discriminate.
  - intros b p d H. cbn in H |- *. unfold wps in H. unfold wpr.
    destruct (wsel b p); [reflexivity | discriminate].
  - intros b p H. cbn in H |- *. unfold wpr in H. unfold wps.
    destruct (wsel b p); [exists 0; reflexivity | discriminate].
  - intros b p H. cbn in H. unfold wpr in H.
    destruct (wsel b p); discriminate.
  - intros b p H. cbn in H |- *. unfold wps in H. unfold wpr.
    destruct (wsel b p); [discriminate | reflexivity].
  - intros b H. change ((b <? 7) = true) in H. apply Nat.ltb_lt in H.
    assert (Hne : Nat.eqb b 7 = false) by (apply Nat.eqb_neq; lia).
    change (wbt b = None /\ wbn b = None).
    unfold wbt, wbn. rewrite Hne. auto.
  - intros a p pa H. cbn in H |- *. unfold wl2p in H.
    destruct (wsel0 a p) eqn:E; [|discriminate].
    injection H as Hpa. subst pa. cbn. auto.
  - intros i r H. discriminate H.
  - intros t ns b H. discriminate H.
  - intros t ns b q H. discriminate H.
  - intros a p pa H. cbn in H |- *. unfold wl2p in H.
    destruct (wsel0 a p) eqn:E; [|discriminate].
    injection H as Hpa. subst pa. exists 0. reflexivity.
  - intros b H. discriminate H.
  - intros b. change ((b <? 7) = true <-> In b (seq 0 7)). split.
    + intros H. apply Nat.ltb_lt in H. apply in_seq. lia.
    + intros H. apply in_seq in H. apply Nat.ltb_lt. lia.
  - intros t ns b q H. discriminate H.
  - intros a p pa _. split; [exists 0 | exists 0]; reflexivity.
Qed.

Lemma wstate_CR : CR (abs_write empty_abs 0 0 0) wstate.
Proof.
  intros a p d Hread.
  destruct (lp_dec a p 0 0) as [[E1 E2]|Hne].
  - subst a p. rewrite abs_write_here in Hread. injection Hread as Hd. subst d.
    exists (mkPhysAddr 7 0). split; reflexivity.
  - rewrite abs_write_other in Hread by tauto. discriminate Hread.
Qed.

Theorem invalidate_identity_refutation_is_not_vacuous :
  exists h s s',
    ftl_invariant s /\ CR h s /\ h 0 0 = Some 0 /\
    step s (COpInvalidate 0 0) = Some s' /\ ~ CR h s'.
Proof.
  exists (abs_write empty_abs 0 0 0), wstate, (exec_invalidate wstate 0 0).
  split; [exact wstate_invariant|].
  split; [exact wstate_CR|].
  split; [apply abs_write_here|].
  split; [reflexivity|].
  apply (invalidate_identity_is_not_a_simulation
           (abs_write empty_abs 0 0 0) wstate (exec_invalidate wstate 0 0) 0 0 0).
  - exact wstate_CR.
  - apply abs_write_here.
  - reflexivity.
Qed.

End Refinement.
