(* BoundaryAgreement.v: completing the instruction level of the
   page-granular model.

   [Primitives.v] proves that the atomic level and the instruction level
   are defined on exactly the same operations ([decompose_domains_agree]).
   Domain agreement is the weakest of the three claims the instruction level
   has to support, and this file supplies the other two, plus the
   flash/controller boundary that makes the whole exercise mean anything.

   PART 1  THE BOUNDARY.  [is_flash] marks the three ONFI commands.  A
           controller micro-operation can re-label a cell -- that is what
           [PrimInvalidate] does -- but it can neither materialise data on a
           cell nor erase one.  This is what licenses reading the filtered
           trace as "what a checker on the wire between controller and chip
           sees".  The literal reading "any change to [page_state] needs a
           flash command" is false, and [relabelling_is_not_a_flash_command]
           refutes it: staling a page is a DRAM-side bookkeeping act in this
           model, visible in [page_state] but not on the bus.

   PART 2  STATE AGREEMENT.  [decompose_correct] compares the atomic and
           the expanded result field by field.  Two features of the statement
           are worth flagging.

           (a) The theorem needs only the invariant.  Every [PrimProgram] an
               expansion emits is preceded by a [PrimMapAddr] or [PrimRemap]
               that installs the destination block's ownership from
               [addr_tenant]/[addr_namespace] -- the very fields
               [program_page] reads.  The two levels therefore agree on the
               owner by construction, with no second hypothesis tying the
               owner down.  Such a hypothesis, [owner_attributed], would in
               any case be a consequence of Inv26;
               [decompose_correct_geom] states it explicitly and
               [owner_attribution_is_redundant] records that it is free.

           (b) The agreement is exact, not merely in-geometry.  Page-granular
               relocation moves one page at a time and erase is the only
               unbounded write, and [PrimErase] and [erase_block] clear the
               same unbounded range.  So [decompose_correct] compares
               every cell at every index, and the geometry-restricted
               statement is a corollary of it.

           The invariant hypothesis itself is genuinely needed, and
           [agreement_needs_the_invariant] exhibits a state on which
           agreement fails: the expansion of an invalidate finds the logical
           page to unmap by reading the victim's OOB stamp, which is only the
           right logical page because Inv3 says so.

   PART 3  REALIZABILITY.  Agreement is a relative check: a fault present in
           both levels satisfies it.  [trace_realizable] never mentions
           [step].  It constrains the emitted instruction stream against the
           flash state alone, by the one law NAND imposes: a page is
           programmable only while erased.  Every operation's expansion is
           realizable from an invariant-satisfying state.

           The one place where the order of the emitted instructions matters
           is the write: the destination of the write's allocation is erased
           *after* the old page has been staled, which is true because a live
           page is never the page the frontier is about to hand out
           (Inv21/Inv6 give the destination erased, and the staled page was
           live, so they are different cells).

   No admitted lemmas, no [admit], no axiom, parameter, variable or hypothesis
   is introduced. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import core.Primitives.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.
Require Import Invariants.GCPreservation.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the flash / controller boundary.
   ══════════════════════════════════════════════════════════════════════ *)

(* Physical NAND accepts three commands: read a page, program a page, erase
   a block.  Everything else in [FlashPrimitive] is controller bookkeeping:
   DRAM updates to the mapping structures and the page metadata, and pure
   transaction markers. *)
Definition is_flash (pr : FlashPrimitive) : bool :=
  match pr with
  | PrimRead _ => true
  | PrimProgram _ _ _ _ => true
  | PrimErase _ => true
  | _ => false
  end.

Lemma is_flash_onfi :
  forall pr,
    is_flash pr = true <->
    ((exists pa, pr = PrimRead pa) \/
     (exists pa d tag lpa, pr = PrimProgram pa d tag lpa) \/
     (exists b, pr = PrimErase b)).
Proof.
  intros pr. split.
  - intros H. destruct pr; cbn in H; try discriminate.
    + left. eexists. reflexivity.
    + right; left. do 4 eexists. reflexivity.
    + right; right. eexists. reflexivity.
  - intros [[pa Hp] | [[pa [d [tag [lpa Hp]]]] | [b Hp]]];
      subst pr; reflexivity.
Qed.

(* The sub-trace a bus-level monitor observes. *)
Definition flash_trace (l : list FlashPrimitive) : list FlashPrimitive :=
  filter is_flash l.

Lemma flash_trace_sound :
  forall l pr,
    In pr (flash_trace l) ->
    (exists pa, pr = PrimRead pa) \/
    (exists pa d tag lpa, pr = PrimProgram pa d tag lpa) \/
    (exists b, pr = PrimErase b).
Proof.
  intros l pr Hin. apply filter_In in Hin. destruct Hin as [_ Hf].
  apply is_flash_onfi. exact Hf.
Qed.

(* ── what a controller micro-operation can do to a cell ──────────────── *)

(* The whole content of the boundary: off the flash bus, a cell can only be
   re-labelled stale.  It cannot come to hold data and it cannot be
   erased. *)
Lemma nonflash_relabels_only :
  forall s pr b p,
    is_flash pr = false ->
    page_state (apply_primitive s pr) b p = page_state s b p \/
    page_state (apply_primitive s pr) b p = PS_Invalid.
Proof.
  intros s pr b p Hnf.
  destruct pr; cbn in Hnf; try discriminate; cbn.
  - (* PrimInvalidate *)
    destruct (page_lpa (page_meta s (pa_block pa) (pa_page pa))) as [[a q]|];
      cbn; unfold set_page_state;
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
      auto.
  - (* PrimSetTag *)
    destruct (page_state s (pa_block pa) (pa_page pa)); cbn; auto.
  - (* PrimMapAddr *) left; reflexivity.
  - (* PrimRemap *) left; reflexivity.
  - (* PrimBarrierEnter *) left; reflexivity.
  - (* PrimBarrierExit *) left; reflexivity.
  - (* PrimFreePush: touches only the free list, not the page state *)
    left; reflexivity.
Qed.

Theorem data_appears_only_via_flash :
  forall s pr b p d,
    is_flash pr = false ->
    page_state (apply_primitive s pr) b p = PS_Valid d ->
    page_state s b p = PS_Valid d.
Proof.
  intros s pr b p d Hnf Hafter.
  destruct (nonflash_relabels_only s pr b p Hnf) as [He | He];
    rewrite He in Hafter; [exact Hafter | discriminate Hafter].
Qed.

Theorem empties_only_via_flash :
  forall s pr b p,
    is_flash pr = false ->
    page_state (apply_primitive s pr) b p = PS_Empty ->
    page_state s b p = PS_Empty.
Proof.
  intros s pr b p Hnf Hafter.
  destruct (nonflash_relabels_only s pr b p Hnf) as [He | He];
    rewrite He in Hafter; [exact Hafter | discriminate Hafter].
Qed.

(* The boundary theorem.  A cell that comes to hold data, or that becomes
   erased, was driven there by a command that crossed the flash bus. *)
Theorem page_state_change_needs_flash :
  forall s pr b p,
    page_state (apply_primitive s pr) b p <> page_state s b p ->
    page_state (apply_primitive s pr) b p <> PS_Invalid ->
    is_flash pr = true.
Proof.
  intros s pr b p Hchange Hnotstale.
  destruct (is_flash pr) eqn:E; [reflexivity|].
  exfalso.
  destruct (nonflash_relabels_only s pr b p E) as [He | He];
    [exact (Hchange He) | exact (Hnotstale He)].
Qed.

(* The side condition on the theorem above is not an artefact.  Staling a
   page is a mapping-table act in this model: it changes [page_state] and
   emits nothing on the wire.  So "every change to [page_state] is a flash
   command" is false as stated, and only the two-sided form above is
   available. *)
Theorem relabelling_is_not_a_flash_command :
  exists s pr b p,
    is_flash pr = false /\
    page_state (apply_primitive s pr) b p <> page_state s b p.
Proof.
  exists empty_state, (PrimInvalidate (mkPhysAddr 0 0)), 0, 0.
  split; [reflexivity|]. cbn. discriminate.
Qed.

(* Lifted to a whole stretch of controller-only work. *)
Theorem trace_data_only_via_flash :
  forall l s b p d,
    (forall pr, In pr l -> is_flash pr = false) ->
    page_state (exec_primitives s l) b p = PS_Valid d ->
    page_state s b p = PS_Valid d.
Proof.
  induction l as [|pr l' IH]; intros s b p d Hnf Hafter.
  - cbn in Hafter. exact Hafter.
  - cbn in Hafter.
    apply (data_appears_only_via_flash s pr b p d (Hnf pr (or_introl eq_refl))).
    apply IH; [intros x Hx; apply Hnf; right; exact Hx | exact Hafter].
Qed.

Theorem trace_empties_only_via_flash :
  forall l s b p,
    (forall pr, In pr l -> is_flash pr = false) ->
    page_state (exec_primitives s l) b p = PS_Empty ->
    page_state s b p = PS_Empty.
Proof.
  induction l as [|pr l' IH]; intros s b p Hnf Hafter.
  - cbn in Hafter. exact Hafter.
  - cbn in Hafter.
    apply (empties_only_via_flash s pr b p (Hnf pr (or_introl eq_refl))).
    apply IH; [intros x Hx; apply Hnf; right; exact Hx | exact Hafter].
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- state agreement.
   ══════════════════════════════════════════════════════════════════════ *)

(* Extensional equality of two states, all sixteen fields, at every index.
   Out-of-band metadata ([page_meta], carrying the owner, the integrity tag
   and the reverse-map stamp) is compared like everything else. *)
Record state_eqv (s1 s2 : FTLState) : Prop := mk_state_eqv {
  eqv_l2p : forall a p, l2p_map s1 a p = l2p_map s2 a p;
  eqv_ps  : forall b p, page_state s1 b p = page_state s2 b p;
  eqv_pr  : forall b p, page_role s1 b p = page_role s2 b p;
  eqv_at  : forall a, addr_tenant s1 a = addr_tenant s2 a;
  eqv_an  : forall a, addr_namespace s1 a = addr_namespace s2 a;
  eqv_bt  : forall b, block_tenant s1 b = block_tenant s2 b;
  eqv_bn  : forall b, block_namespace s1 b = block_namespace s2 b;
  eqv_pm  : forall b p, page_meta s1 b p = page_meta s2 b p;
  eqv_rt  : forall i, region_table s1 i = region_table s2 i;
  eqv_fbl : free_block_list s1 = free_block_list s2;
  eqv_fb  : forall b, free_block s1 b = free_block s2 b;
  eqv_wc  : forall b, wear_count s1 b = wear_count s2 b;
  eqv_kt  : forall k, key_table s1 k = key_table s2 k;
  eqv_ob  : forall t ns, open_block s1 t ns = open_block s2 t ns;
  eqv_wp  : forall t ns, write_ptr s1 t ns = write_ptr s2 t ns;
  eqv_bo  : forall b, block_open s1 b = block_open s2 b
}.

Lemma state_eqv_refl : forall s, state_eqv s s.
Proof. intros s. constructor; intros; reflexivity. Qed.

Lemma state_eqv_sym : forall s1 s2, state_eqv s1 s2 -> state_eqv s2 s1.
Proof.
  intros s1 s2 H.
  destruct H as [A B C D E F G I J K L M N O P Q].
  constructor; intros; symmetry;
    solve [apply A | apply B | apply C | apply D | apply E | apply F
          | apply G | apply I | apply J | exact K | apply L | apply M
          | apply N | apply O | apply P | apply Q].
Qed.

Lemma state_eqv_trans :
  forall s1 s2 s3, state_eqv s1 s2 -> state_eqv s2 s3 -> state_eqv s1 s3.
Proof.
  intros s1 s2 s3 H1 H2.
  destruct H1 as [A1 B1 C1 D1 E1 F1 G1 I1 J1 K1 L1 M1 N1 O1 P1 Q1].
  destruct H2 as [A2 B2 C2 D2 E2 F2 G2 I2 J2 K2 L2 M2 N2 O2 P2 Q2].
  constructor; intros.
  - rewrite A1. apply A2.
  - rewrite B1. apply B2.
  - rewrite C1. apply C2.
  - rewrite D1. apply D2.
  - rewrite E1. apply E2.
  - rewrite F1. apply F2.
  - rewrite G1. apply G2.
  - rewrite I1. apply I2.
  - rewrite J1. apply J2.
  - rewrite K1. apply K2.
  - rewrite L1. apply L2.
  - rewrite M1. apply M2.
  - rewrite N1. apply N2.
  - rewrite O1. apply O2.
  - rewrite P1. apply P2.
  - rewrite Q1. apply Q2.
Qed.

(* The same comparison restricted to the geometry: page-indexed fields are
   compared only at indices below [pages_per_block]. *)
Record state_eqv_geom (s1 s2 : FTLState) : Prop := mk_state_eqv_geom {
  geqv_l2p : forall a p, l2p_map s1 a p = l2p_map s2 a p;
  geqv_ps  : forall b p, p < pages_per_block -> page_state s1 b p = page_state s2 b p;
  geqv_pr  : forall b p, p < pages_per_block -> page_role s1 b p = page_role s2 b p;
  geqv_at  : forall a, addr_tenant s1 a = addr_tenant s2 a;
  geqv_an  : forall a, addr_namespace s1 a = addr_namespace s2 a;
  geqv_bt  : forall b, block_tenant s1 b = block_tenant s2 b;
  geqv_bn  : forall b, block_namespace s1 b = block_namespace s2 b;
  geqv_pm  : forall b p, p < pages_per_block -> page_meta s1 b p = page_meta s2 b p;
  geqv_rt  : forall i, region_table s1 i = region_table s2 i;
  geqv_fbl : free_block_list s1 = free_block_list s2;
  geqv_fb  : forall b, free_block s1 b = free_block s2 b;
  geqv_wc  : forall b, wear_count s1 b = wear_count s2 b;
  geqv_kt  : forall k, key_table s1 k = key_table s2 k;
  geqv_ob  : forall t ns, open_block s1 t ns = open_block s2 t ns;
  geqv_wp  : forall t ns, write_ptr s1 t ns = write_ptr s2 t ns;
  geqv_bo  : forall b, block_open s1 b = block_open s2 b
}.

Lemma state_eqv_weaken : forall s1 s2, state_eqv s1 s2 -> state_eqv_geom s1 s2.
Proof.
  intros s1 s2 H.
  destruct H as [A B C D E F G I J K L M N O P Q].
  constructor; intros; auto.
Qed.

(* ── congruence: the instruction level respects extensional equality ──── *)

Lemma close_open_congr :
  forall v w t ns b,
    (forall t' ns', open_block v t' ns' = open_block w t' ns') ->
    (forall b', block_open v b' = block_open w b') ->
    close_open v t ns b = close_open w t ns b.
Proof.
  intros v w t ns b Hob Hbo. unfold close_open. rewrite Hob.
  destruct (open_block w t ns) as [ob|]; [|apply Hbo].
  unfold set_block_open. destruct (Nat.eqb b ob); [reflexivity | apply Hbo].
Qed.

Lemma apply_primitive_congr :
  forall pr v w, state_eqv v w -> state_eqv (apply_primitive v pr) (apply_primitive w pr).
Proof.
  intros pr v w H.
  pose proof (eqv_l2p _ _ H) as Hl.
  pose proof (eqv_ps  _ _ H) as Hps.
  pose proof (eqv_pr  _ _ H) as Hpr.
  pose proof (eqv_at  _ _ H) as Hat.
  pose proof (eqv_an  _ _ H) as Han.
  pose proof (eqv_bt  _ _ H) as Hbt.
  pose proof (eqv_bn  _ _ H) as Hbn.
  pose proof (eqv_pm  _ _ H) as Hpm.
  pose proof (eqv_rt  _ _ H) as Hrt.
  pose proof (eqv_fbl _ _ H) as Hfbl.
  pose proof (eqv_fb  _ _ H) as Hfb.
  pose proof (eqv_wc  _ _ H) as Hwc.
  pose proof (eqv_kt  _ _ H) as Hkt.
  pose proof (eqv_ob  _ _ H) as Hob.
  pose proof (eqv_wp  _ _ H) as Hwp.
  pose proof (eqv_bo  _ _ H) as Hbo.
  destruct pr.
  - (* PrimRead *) cbn [apply_primitive]. exact H.
  - (* PrimProgram *)
    cbn [apply_primitive]. unfold is_open.
    rewrite (Hbt (pa_block pa)), (Hbn (pa_block pa)), (Hbo (pa_block pa)), Hfbl.
    destruct (block_open w (pa_block pa));
      constructor; cbn; intros; try (apply Hl || apply Hrt || apply Hwc
                                     || apply Hkt || apply Hat || apply Han
                                     || apply Hbt || apply Hbn);
      try reflexivity.
    + unfold set_page_state.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hps].
    + unfold set_page_role.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpr].
    + unfold set_page_meta.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpm].
    + apply Hfb.
    + unfold set_open_block. destruct (Nat.eqb t _ && Nat.eqb ns _);
        [reflexivity | apply Hob].
    + unfold set_write_ptr. destruct (Nat.eqb t _ && Nat.eqb ns _);
        [reflexivity | apply Hwp].
    + apply Hbo.
    + unfold set_page_state.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hps].
    + unfold set_page_role.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpr].
    + unfold set_page_meta.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpm].
    + unfold set_free_block. destruct (Nat.eqb b (pa_block pa));
        [reflexivity | apply Hfb].
    + unfold set_open_block. destruct (Nat.eqb t _ && Nat.eqb ns _);
        [reflexivity | apply Hob].
    + unfold set_write_ptr. destruct (Nat.eqb t _ && Nat.eqb ns _);
        [reflexivity | apply Hwp].
    + unfold set_block_open. destruct (Nat.eqb b (pa_block pa));
        [reflexivity | apply close_open_congr; assumption].
  - (* PrimInvalidate *)
    cbn [apply_primitive]. rewrite (Hpm (pa_block pa) (pa_page pa)).
    destruct (page_lpa (page_meta w (pa_block pa) (pa_page pa))) as [[a0 p0]|];
      constructor; cbn; intros;
      try (apply Hrt || apply Hwc || apply Hkt || apply Hat || apply Han
           || apply Hbt || apply Hbn || apply Hob || apply Hwp || apply Hbo
           || apply Hfb);
      try (exact Hfbl).
    + unfold set_l2p_map. destruct (Nat.eqb a a0 && Nat.eqb p p0);
        [reflexivity | apply Hl].
    + unfold set_page_state.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hps].
    + unfold set_page_role.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpr].
    + unfold set_page_meta.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpm].
    + apply Hl.
    + unfold set_page_state.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hps].
    + unfold set_page_role.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpr].
    + unfold set_page_meta.
      destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
        [reflexivity | apply Hpm].
  - (* PrimSetTag *)
    cbn [apply_primitive]. rewrite (Hps (pa_block pa) (pa_page pa)).
    destruct (page_state w (pa_block pa) (pa_page pa)); try exact H.
    unfold set_page_tag_at. rewrite (Hpm (pa_block pa) (pa_page pa)).
    constructor; cbn; intros;
      try (apply Hl || apply Hps || apply Hpr || apply Hat || apply Han
           || apply Hbt || apply Hbn || apply Hrt || apply Hfb || apply Hwc
           || apply Hkt || apply Hob || apply Hwp || apply Hbo);
      try (exact Hfbl).
    unfold set_page_meta.
    destruct (Nat.eqb b (pa_block pa) && Nat.eqb p (pa_page pa));
      [reflexivity | apply Hpm].
  - (* PrimMapAddr *)
    cbn [apply_primitive]. unfold install_mapping. rewrite (Hat a).
    constructor; cbn; intros;
      try (apply Hps || apply Hpr || apply Hat || apply Han || apply Hrt
           || apply Hfb || apply Hwc || apply Hkt || apply Hob || apply Hwp
           || apply Hbo);
      try (exact Hfbl).
    + unfold set_l2p_map. destruct (Nat.eqb a0 a && Nat.eqb p0 p);
        [reflexivity | apply Hl].
    + unfold set_block_tenant. destruct (Nat.eqb b (pa_block pa));
        [reflexivity | apply Hbt].
    + unfold set_block_namespace. destruct (Nat.eqb b (pa_block pa));
        [rewrite (Han a); reflexivity | apply Hbn].
    + apply Hpm.
  - (* PrimRemap *)
    cbn [apply_primitive]. unfold install_mapping. rewrite (Hat a).
    constructor; cbn; intros;
      try (apply Hps || apply Hpr || apply Hat || apply Han || apply Hrt
           || apply Hfb || apply Hwc || apply Hkt || apply Hob || apply Hwp
           || apply Hbo);
      try (exact Hfbl).
    + unfold set_l2p_map. destruct (Nat.eqb a0 a && Nat.eqb p0 p);
        [reflexivity | apply Hl].
    + unfold set_block_tenant. destruct (Nat.eqb b (pa_block dst));
        [reflexivity | apply Hbt].
    + unfold set_block_namespace. destruct (Nat.eqb b (pa_block dst));
        [rewrite (Han a); reflexivity | apply Hbn].
    + apply Hpm.
  - (* PrimErase *)
    cbn [apply_primitive]. rewrite Hfbl.
    constructor; cbn; intros;
      try (apply Hl || apply Hat || apply Han || apply Hrt || apply Hkt
           || apply Hob || apply Hwp);
      try reflexivity.
    + unfold clear_block_state. destruct (Nat.eqb b0 b); [reflexivity | apply Hps].
    + unfold clear_block_role. destruct (Nat.eqb b0 b); [reflexivity | apply Hpr].
    + unfold set_block_tenant. destruct (Nat.eqb b0 b); [reflexivity | apply Hbt].
    + unfold set_block_namespace. destruct (Nat.eqb b0 b); [reflexivity | apply Hbn].
    + unfold clear_block_meta. destruct (Nat.eqb b0 b); [reflexivity | apply Hpm].
    + unfold set_free_block. destruct (Nat.eqb b0 b); [reflexivity | apply Hfb].
    + unfold set_wear_count. destruct (Nat.eqb b0 b);
        [rewrite (Hwc b); reflexivity | apply Hwc].
    + unfold set_block_open. destruct (Nat.eqb b0 b); [reflexivity | apply Hbo].
  - (* PrimBarrierEnter *) cbn [apply_primitive]. exact H.
  - (* PrimBarrierExit *) cbn [apply_primitive]. exact H.
  - (* PrimFreePush: only the free list and free bit move *)
    cbn [apply_primitive]. rewrite Hfbl.
    constructor; cbn; intros;
      try (apply Hl || apply Hps || apply Hpr || apply Hat || apply Han
           || apply Hbt || apply Hbn || apply Hpm || apply Hrt || apply Hwc
           || apply Hkt || apply Hob || apply Hwp || apply Hbo);
      try reflexivity.
    unfold set_free_block. destruct (Nat.eqb b0 b); [reflexivity | apply Hfb].
Qed.

Lemma exec_primitives_congr :
  forall l v w, state_eqv v w -> state_eqv (exec_primitives v l) (exec_primitives w l).
Proof.
  induction l as [|pr l' IH]; intros v w H; cbn [exec_primitives].
  - exact H.
  - apply IH. apply apply_primitive_congr. exact H.
Qed.

Lemma exec_primitives_app :
  forall l1 l2 s,
    exec_primitives s (l1 ++ l2) = exec_primitives (exec_primitives s l1) l2.
Proof.
  induction l1 as [|pr l1' IH]; intros l2 s; cbn [app exec_primitives];
    [reflexivity | apply IH].
Qed.

(* Stepping an explicit instruction list without unfolding the instructions
   themselves. *)
Lemma exec_nil : forall s, exec_primitives s [] = s.
Proof. reflexivity. Qed.

Lemma exec_cons :
  forall s pr l, exec_primitives s (pr :: l) = exec_primitives (apply_primitive s pr) l.
Proof. reflexivity. Qed.

Lemma prim_read_id : forall s pa, apply_primitive s (PrimRead pa) = s.
Proof. reflexivity. Qed.

Lemma prim_enter_id : forall s tg, apply_primitive s (PrimBarrierEnter tg) = s.
Proof. reflexivity. Qed.

Lemma prim_exit_id : forall s tg, apply_primitive s (PrimBarrierExit tg) = s.
Proof. reflexivity. Qed.

Lemma prim_mapaddr_eq :
  forall s a p pa, apply_primitive s (PrimMapAddr a p pa) = install_mapping s a p pa.
Proof. reflexivity. Qed.

Lemma prim_remap_eq :
  forall s a p dst, apply_primitive s (PrimRemap a p dst) = install_mapping s a p dst.
Proof. reflexivity. Qed.

(* ── the shape of a program instruction ──────────────────────────────── *)

Lemma prim_program_shape :
  forall s pa d tag lpa t ns,
    block_tenant s (pa_block pa) = Some t ->
    block_namespace s (pa_block pa) = Some ns ->
    apply_primitive s (PrimProgram pa d tag lpa) =
      mkFTLState
        (l2p_map s)
        (set_page_state (page_state s) (pa_block pa) (pa_page pa) (PS_Valid d))
        (set_page_role (page_role s) (pa_block pa) (pa_page pa) (Some RData))
        (addr_tenant s) (addr_namespace s)
        (block_tenant s) (block_namespace s)
        (set_page_meta (page_meta s) (pa_block pa) (pa_page pa)
                       (mkPageMeta t ns tag lpa))
        (region_table s)
        (if is_open s (pa_block pa) then free_block_list s
         else remove_block_once (pa_block pa) (free_block_list s))
        (if is_open s (pa_block pa) then free_block s
         else set_free_block (free_block s) (pa_block pa) false)
        (wear_count s) (key_table s)
        (set_open_block (open_block s) t ns (Some (pa_block pa)))
        (set_write_ptr (write_ptr s) t ns (S (pa_page pa)))
        (if is_open s (pa_block pa) then block_open s
         else set_block_open (close_open s t ns) (pa_block pa) true).
Proof.
  intros s pa d tag lpa t ns Ht Hns.
  cbn [apply_primitive]. rewrite Ht, Hns. reflexivity.
Qed.

(* ── auxiliary facts about allocation ────────────────────────────────── *)

Lemma alloc_page_fields2 :
  forall s t ns pa s1,
    alloc_page s t ns = Some (pa, s1) ->
    wear_count s1 = wear_count s /\ key_table s1 = key_table s.
Proof.
  intros s t ns pa s1 H. unfold alloc_page in H.
  destruct (open_block s t ns) as [b0|] eqn:Hob.
  - destruct (Nat.ltb (write_ptr s t ns) pages_per_block) eqn:Hlt.
    + injection H as _ H. subst s1. split; reflexivity.
    + unfold open_fresh in H.
      destruct (free_block_list s) as [|b1 [|b2 rest]] eqn:Hfl; try discriminate.
      injection H as _ H. subst s1. split; reflexivity.
  - unfold open_fresh in H.
    destruct (free_block_list s) as [|b1 [|b2 rest]] eqn:Hfl; try discriminate.
    injection H as _ H. subst s1. split; reflexivity.
Qed.

(* A block on the free list is not open: Inv23 would hand it a frontier and
   Inv20 then keeps it off the list. *)
Lemma free_block_not_open :
  forall s b, Inv20 s -> Inv23 s -> In b (free_block_list s) -> block_open s b = false.
Proof.
  intros s b I22 I25 Hin. destruct (block_open s b) eqn:E; [|reflexivity].
  destruct (I25 b E) as [t [ns Hob]].
  destruct (I22 t ns b Hob) as (_ & Hnin & _). contradiction.
Qed.

(* ── the core agreement step: install the mapping, then program ───────── *)

(* One [PrimMapAddr]/[PrimRemap] followed by one [PrimProgram] does exactly
   what [alloc_page] followed by [program_page] does.  This single lemma
   covers the destination of a write and the destination of a relocation:
   the two expansions differ only in the primitive that installs the
   mapping, and [install_mapping] is what both of them run. *)
Lemma install_mapping_bt :
  forall s a p pa,
    block_tenant (install_mapping s a p pa) (pa_block pa) = addr_tenant s a.
Proof. intros. unfold install_mapping. apply set_bt_here. Qed.

Lemma install_mapping_bn :
  forall s a p pa,
    block_namespace (install_mapping s a p pa) (pa_block pa) = addr_namespace s a.
Proof. intros. unfold install_mapping. apply set_bn_here. Qed.

Lemma program_step_eqv :
  forall s0 a p d t ns pa s1,
    Inv20 s0 -> Inv23 s0 ->
    addr_tenant s0 a = Some t ->
    addr_namespace s0 a = Some ns ->
    alloc_page s0 t ns = Some (pa, s1) ->
    state_eqv (program_page s1 a p d pa)
              (apply_primitive (install_mapping s0 a p pa)
                               (PrimProgram pa d (Some d) (Some (a, p)))).
Proof.
  intros s0 a p d t ns pa s1 I22 I25 Hat Han Halloc.
  destruct (alloc_page_fields s0 t ns pa s1 Halloc)
    as (Fl & Fps & Fpr & Fat & Fan & Fbt & Fbn & Fpm & Frt).
  destruct (alloc_page_fields2 s0 t ns pa s1 Halloc) as (Fwc & Fkt).
  assert (Hbt : block_tenant (install_mapping s0 a p pa) (pa_block pa) = Some t)
    by (rewrite install_mapping_bt; exact Hat).
  assert (Hbn : block_namespace (install_mapping s0 a p pa) (pa_block pa) = Some ns)
    by (rewrite install_mapping_bn; exact Han).
  rewrite (prim_program_shape (install_mapping s0 a p pa) pa d (Some d) (Some (a, p)) t ns Hbt Hbn).
  unfold is_open.
  assert (Hbo0 : block_open (install_mapping s0 a p pa) = block_open s0) by reflexivity.
  rewrite Hbo0.
  unfold program_page.
  destruct (alloc_page_shape s0 t ns pa s1 Halloc)
    as [[b (Hob & Hlt & Hpa & Hfbl1 & Hfb1 & Hbo1 & Hob1 & Hwp1)] | [Hof _]].
  - (* the open block still has room: the frontier moves, nothing else *)
    subst pa.
    assert (Hopen : block_open s0 (pa_block (mkPhysAddr b (write_ptr s0 t ns))) = true).
    { destruct (I22 t ns b Hob) as (_ & _ & _ & Hbo & _). exact Hbo. }
    rewrite Hopen.
    constructor; cbn; intros;
      rewrite ?Fl, ?Fps, ?Fpr, ?Fat, ?Fan, ?Hat, ?Han, ?Fbt, ?Fbn, ?Fpm, ?Frt,
              ?Fwc, ?Fkt, ?Hfbl1, ?Hfb1, ?Hbo1, ?Hob1, ?Hwp1;
      reflexivity.
  - (* a fresh block is opened, and the tenant's outgoing one retired *)
    destruct (open_fresh_shape s0 t ns pa s1 Hof)
      as [fbh [rest (Hfbl0 & Hpa & Hfbl1 & Hfb1 & Hob1 & Hwp1 & Hbo1)]].
    subst pa.
    assert (Hopen : block_open s0 (pa_block (mkPhysAddr fbh 0)) = false).
    { cbn. apply (free_block_not_open s0 fbh I22 I25).
      rewrite Hfbl0. left. reflexivity. }
    rewrite Hopen.
    constructor; cbn; intros;
      rewrite ?Fl, ?Fps, ?Fpr, ?Fat, ?Fan, ?Hat, ?Han, ?Fbt, ?Fbn, ?Fpm, ?Frt,
              ?Fwc, ?Fkt, ?Hfbl1, ?Hfbl0, ?Hfb1, ?Hbo1, ?Hob1, ?Hwp1;
      first [ reflexivity
            | (cbn [remove_block_once]; rewrite Nat.eqb_refl; reflexivity) ].
Qed.

(* Dropping a mapping and re-installing it at the same logical page is the
   same as installing it: this is what makes the write's expansion, which
   unmaps via the victim page's OOB stamp before it remaps, agree with the
   atomic write, which never unmaps at all. *)
Lemma install_mapping_unmap :
  forall X a p pa,
    state_eqv (install_mapping (unmap X a p) a p pa) (install_mapping X a p pa).
Proof.
  intros X a p pa. constructor; cbn; intros; try reflexivity.
  unfold set_l2p_map. destruct (Nat.eqb a0 a && Nat.eqb p0 p); reflexivity.
Qed.

(* ── erase ───────────────────────────────────────────────────────────── *)

Lemma erase_eqv :
  forall s b, state_eqv (erase_block s b) (apply_primitive s (PrimErase b)).
Proof.
  intros s b. constructor; cbn; intros;
    first [ reflexivity
          | (unfold set_wear_count; destruct (Nat.eqb b0 b) eqn:E;
             [ apply Nat.eqb_eq in E; subst b0 | idtac ]; reflexivity)
          | (destruct (Nat.eqb b0 b) eqn:E;
             [ apply Nat.eqb_eq in E; subst b0 | idtac ]; reflexivity) ].
Qed.

(* ── read, invalidate, set-tag ───────────────────────────────────────── *)

Lemma prim_invalidate_shape :
  forall s pa a p,
    page_lpa (page_meta s (pa_block pa) (pa_page pa)) = Some (a, p) ->
    apply_primitive s (PrimInvalidate pa) = unmap (invalidate_at s pa) a p.
Proof.
  intros s pa a p H. cbn [apply_primitive]. rewrite H. reflexivity.
Qed.

(* The expansion of an invalidate finds the logical page to detach by reading
   the victim's OOB stamp.  Inv3 and Inv22 are what make that the right
   logical page. *)
Lemma mapped_page_stamp :
  forall s a p pa,
    Inv3 s -> Inv22 s ->
    l2p_map s a p = Some pa ->
    page_lpa (page_meta s (pa_block pa) (pa_page pa)) = Some (a, p).
Proof.
  intros s a p pa I5 I24 Hm.
  destruct (I24 a p pa Hm) as [d Hd].
  exact (I5 a p pa d Hm Hd).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- realizability of the emitted instruction stream.
   ══════════════════════════════════════════════════════════════════════ *)

(* NAND programs one way only, so a page is programmable only while erased.
   Every other instruction is unconstrained by this law. *)
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
  induction l1 as [|pr l1' IH]; intros l2 s; cbn [app trace_realizable exec_primitives].
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - split.
    + intros [Hp Hrest]. apply IH in Hrest. destruct Hrest as [H1 H2].
      split; [split; assumption | exact H2].
    + intros [[Hp H1] H2]. split; [exact Hp|]. apply IH. split; assumption.
Qed.

Lemma trace_realizable_congr :
  forall l v w, state_eqv v w -> trace_realizable w l -> trace_realizable v l.
Proof.
  induction l as [|pr l' IH]; intros v w H Hr; cbn [trace_realizable] in *.
  - exact I.
  - destruct Hr as [Hp Hrest]. split.
    + destruct pr; try exact I; cbn in Hp |- *;
        rewrite (eqv_ps _ _ H); exact Hp.
    + apply (IH _ (apply_primitive w pr));
        [apply apply_primitive_congr; exact H | exact Hrest].
Qed.

(* An executable form of the same check, so that a checker can run it. *)
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
  induction l as [|pr l' IH]; intros s; cbn [trace_realizableb trace_realizable].
  - split; [intros _; exact I | intros _; reflexivity].
  - rewrite andb_true_iff. rewrite IH. split.
    + intros [Hp Hrest]. split; [|exact Hrest].
      destruct pr; cbn in Hp |- *; try exact I;
        destruct (page_state s (pa_block pa) (pa_page pa)); try discriminate;
        reflexivity.
    + intros [Hp Hrest]. split; [|exact Hrest].
      destruct pr; cbn in Hp |- *; try reflexivity; rewrite Hp; reflexivity.
Qed.

(* ── the destination of an allocation is erased ──────────────────────── *)

Lemma alloc_dest_empty :
  forall s t ns pa s1,
    Inv6 s -> Inv21 s ->
    alloc_page s t ns = Some (pa, s1) ->
    page_state s (pa_block pa) (pa_page pa) = PS_Empty.
Proof.
  intros s t ns pa s1 I8 I23 H.
  destruct (alloc_page_shape s t ns pa s1 H)
    as [[b (Hob & Hlt & Hpa & _)] | [Hof _]].
  - (* below the frontier's ceiling: Inv21 *)
    subst pa. cbn.
    destruct (I23 t ns b (write_ptr s t ns) Hob (le_n _) Hlt) as [He _]. exact He.
  - (* a fresh block off the free list: Inv6 *)
    destruct (open_fresh_shape s t ns pa s1 Hof)
      as [fbh [rest (Hfbl & Hpa & _)]].
    subst pa. cbn.
    assert (Hin : In fbh (free_block_list s)) by (rewrite Hfbl; left; reflexivity).
    destruct (I8 fbh Hin 0 pages_per_block_pos) as [He _]. exact He.
Qed.

(* Staling the page a write replaces cannot clobber the page the frontier is
   about to hand out: the staled page was live and the destination erased. *)
Lemma empty_survives_invalidate :
  forall s old b q,
    (exists dd, page_state s (pa_block old) (pa_page old) = PS_Valid dd) ->
    page_state s b q = PS_Empty ->
    page_state (invalidate_at s old) b q = PS_Empty.
Proof.
  intros s old b q [dd Hv] He. cbn. unfold set_page_state.
  destruct (Nat.eqb b (pa_block old)) eqn:Eb;
    destruct (Nat.eqb q (pa_page old)) eqn:Eq; cbn; try exact He.
  apply Nat.eqb_eq in Eb; apply Nat.eqb_eq in Eq; subst b q.
  rewrite Hv in He. discriminate He.
Qed.

Lemma write_dest_empty :
  forall s old t ns pa s2,
    Inv6 s -> Inv21 s ->
    (exists dd, page_state s (pa_block old) (pa_page old) = PS_Valid dd) ->
    alloc_page (invalidate_at s old) t ns = Some (pa, s2) ->
    page_state (invalidate_at s old) (pa_block pa) (pa_page pa) = PS_Empty.
Proof.
  intros s old t ns pa s2 I8 I23 Hlive Halloc.
  apply empty_survives_invalidate; [exact Hlive|].
  destruct (alloc_page_shape (invalidate_at s old) t ns pa s2 Halloc)
    as [[b (Hob & Hlt & Hpa & _)] | [Hof _]].
  - subst pa. cbn.
    (* the frontier of [invalidate_at s old] is the frontier of [s] *)
    destruct (I23 t ns b (write_ptr s t ns) Hob (le_n _) Hlt) as [He _]. exact He.
  - destruct (open_fresh_shape (invalidate_at s old) t ns pa s2 Hof)
      as [fbh [rest (Hfbl & Hpa & _)]].
    subst pa. cbn.
    assert (Hfl0 : free_block_list (invalidate_at s old) = free_block_list s)
      by reflexivity.
    rewrite Hfl0 in Hfbl.
    assert (Hin : In fbh (free_block_list s)) by (rewrite Hfbl; left; reflexivity).
    destruct (I8 fbh Hin 0 pages_per_block_pos) as [He _]. exact He.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- per-operation agreement and realizability.
   ══════════════════════════════════════════════════════════════════════ *)

Definition faithful_at (s : FTLState) (op : COp) : Prop :=
  match step s op, step_mqsim s op with
  | Some s1, Some s2 => state_eqv s1 s2
  | None, None => True
  | _, _ => False
  end.

Definition faithful_at_geom (s : FTLState) (op : COp) : Prop :=
  match step s op, step_mqsim s op with
  | Some s1, Some s2 => state_eqv_geom s1 s2
  | None, None => True
  | _, _ => False
  end.

Lemma faithful_weaken : forall s op, faithful_at s op -> faithful_at_geom s op.
Proof.
  intros s op. unfold faithful_at, faithful_at_geom.
  destruct (step s op); destruct (step_mqsim s op); try (intros H; exact H).
  apply state_eqv_weaken.
Qed.

(* Domain agreement disposes of the mixed cases, so an agreement proof only
   ever has to compare two states that both exist. *)
Lemma some_inj : forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H. injection H as H. exact H. Qed.

Lemma faithful_intro :
  forall s op,
    (forall s1 s2, step s op = Some s1 -> step_mqsim s op = Some s2 -> state_eqv s1 s2) ->
    faithful_at s op.
Proof.
  intros s op H. unfold faithful_at.
  destruct (step s op) as [s1|] eqn:E1; destruct (step_mqsim s op) as [s2|] eqn:E2.
  - exact (H s1 s2 eq_refl eq_refl).
  - pose proof (proj2 (decompose_domains_agree s op) E2) as Hc.
    rewrite E1 in Hc. discriminate Hc.
  - pose proof (proj1 (decompose_domains_agree s op) E1) as Hc.
    rewrite E2 in Hc. discriminate Hc.
  - exact I.
Qed.

(* ── read ────────────────────────────────────────────────────────────── *)

Lemma read_faithful : forall s a p, faithful_at s (COpRead a p).
Proof.
  intros s a p. apply faithful_intro. intros s1 s2 H1 H2.
  cbn [step] in H1. apply some_inj in H1. subst s1.
  unfold step_mqsim, op_primitives in H2.
  destruct (l2p_map s a p) as [pa|]; apply some_inj in H2; subst s2;
    rewrite ?exec_cons, ?exec_nil; try rewrite prim_read_id;
    apply state_eqv_refl.
Qed.

(* ── set-tag ─────────────────────────────────────────────────────────── *)

Lemma settag_faithful : forall s a p tag, faithful_at s (COpSetTag a p tag).
Proof.
  intros s a p tag. apply faithful_intro. intros s1 s2 H1 H2.
  cbn [step] in H1. apply some_inj in H1. subst s1.
  unfold step_mqsim, op_primitives in H2.
  unfold exec_set_tag.
  destruct (l2p_map s a p) as [pa|]; apply some_inj in H2; subst s2;
    rewrite ?exec_cons, ?exec_nil; apply state_eqv_refl.
Qed.

(* ── invalidate ──────────────────────────────────────────────────────── *)

Lemma invalidate_faithful :
  forall s a p, Inv3 s -> Inv22 s -> faithful_at s (COpInvalidate a p).
Proof.
  intros s a p I5 I24. apply faithful_intro. intros s1 s2 H1 H2.
  cbn [step] in H1. apply some_inj in H1. subst s1.
  unfold step_mqsim, op_primitives in H2.
  unfold exec_invalidate.
  destruct (l2p_map s a p) as [pa|] eqn:Hm; apply some_inj in H2; subst s2;
    rewrite ?exec_cons, ?exec_nil.
  - rewrite (prim_invalidate_shape s pa a p (mapped_page_stamp s a p pa I5 I24 Hm)).
    apply state_eqv_refl.
  - apply state_eqv_refl.
Qed.

(* ── write ───────────────────────────────────────────────────────────── *)

Lemma write_faithful :
  forall s a p d,
    Inv3 s -> Inv20 s -> Inv22 s -> Inv23 s ->
    faithful_at s (COpWrite a p d).
Proof.
  intros s a p d I5 I22 I24 I25. apply faithful_intro. intros s1 s2 H1 H2.
  cbn [step] in H1. unfold step_mqsim, op_primitives in H2.
  destruct (Nat.ltb a addr_space && Nat.ltb p pages_per_block &&
            (match addr_tenant s a, addr_namespace s a with
             | Some _, Some _ => true | _, _ => false end)) eqn:HG;
    [| discriminate H1].
  unfold exec_write in H1. unfold write_primitives in H2.
  destruct (addr_tenant s a) as [t|] eqn:Hat; [|discriminate H1].
  destruct (addr_namespace s a) as [ns|] eqn:Han; [|discriminate H1].
  destruct (l2p_map s a p) as [old|] eqn:Hm.
  - (* the logical page had a physical page: stale it, then program *)
    destruct (alloc_page (invalidate_at s old) t ns) as [[pa s3]|] eqn:Ha;
      [|discriminate H1].
    apply some_inj in H1. subst s1. apply some_inj in H2. subst s2.
    cbn [app]. rewrite ?exec_cons, ?exec_nil.
    rewrite prim_enter_id, prim_exit_id, prim_mapaddr_eq.
    rewrite (prim_invalidate_shape s old a p (mapped_page_stamp s a p old I5 I24 Hm)).
    (* the atomic level programs onto [invalidate_at s old]; the expansion
       programs onto the same state with (a,p) momentarily unmapped *)
    apply (state_eqv_trans _
             (apply_primitive (install_mapping (invalidate_at s old) a p pa)
                              (PrimProgram pa d (Some d) (Some (a, p))))).
    + apply (program_step_eqv (invalidate_at s old) a p d t ns pa s3);
        try assumption; try exact Hat; try exact Han; try exact Ha.
    + apply state_eqv_sym. apply apply_primitive_congr.
      apply install_mapping_unmap.
  - (* the logical page was unmapped *)
    destruct (alloc_page s t ns) as [[pa s3]|] eqn:Ha; [|discriminate H1].
    apply some_inj in H1. subst s1. apply some_inj in H2. subst s2.
    cbn [app]. rewrite ?exec_cons, ?exec_nil.
    rewrite prim_enter_id, prim_exit_id, prim_mapaddr_eq.
    apply (program_step_eqv s a p d t ns pa s3); assumption.
Qed.

(* ── relocation, one page at a time ──────────────────────────────────── *)

Lemma reloc_step_ok :
  forall s vb q tl pr s',
    INVX vb (q :: tl) s ->
    page_reloc_primitives s vb q = Some pr ->
    relocate_page s vb q = Some s' ->
    trace_realizable s pr /\ state_eqv s' (exec_primitives s pr).
Proof.
  intros s vb q tl pr s' HX Hpr Hrel.
  pose proof (xI8 _ _ _ HX) as I8.
  pose proof (xI22 _ _ _ HX) as I22.
  pose proof (xI23 _ _ _ HX) as I23.
  pose proof (xI25 _ _ _ HX) as I25.
  unfold page_reloc_primitives in Hpr. unfold relocate_page in Hrel.
  destruct (page_state s vb q) as [| |dd] eqn:Hps.
  - injection Hpr as Hpr; injection Hrel as Hrel; subst pr s'.
    split; [exact I | cbn [exec_primitives]; apply state_eqv_refl].
  - injection Hpr as Hpr; injection Hrel as Hrel; subst pr s'.
    split; [exact I | cbn [exec_primitives]; apply state_eqv_refl].
  - destruct (page_lpa (page_meta s vb q)) as [[a0 p0]|]; [|discriminate Hpr].
    destruct (addr_tenant s a0) as [t|] eqn:Hat; [|discriminate Hpr].
    destruct (addr_namespace s a0) as [ns|] eqn:Han; [|discriminate Hpr].
    destruct (alloc_page s t ns) as [[pa s3]|] eqn:Ha; [|discriminate Hpr].
    injection Hpr as Hpr. subst pr. injection Hrel as Hrel. subst s'.
    split.
    + cbn [trace_realizable prim_realizable apply_primitive install_mapping].
      repeat split; try exact I.
      exact (alloc_dest_empty s t ns pa s3 I8 I23 Ha).
    + cbn [exec_primitives apply_primitive].
      apply (program_step_eqv s a0 p0 dd t ns pa s3); assumption.
Qed.

Lemma reloc_loop_ok :
  forall qs s vb l s',
    INVX vb qs s ->
    reloc_primitives s vb qs = Some l ->
    relocate_pages s vb qs = Some s' ->
    trace_realizable s l /\ state_eqv s' (exec_primitives s l).
Proof.
  induction qs as [|q tl IH]; intros s vb l s' HX Hl Hs'.
  - cbn [reloc_primitives] in Hl. injection Hl as Hl. subst l.
    cbn [relocate_pages] in Hs'. injection Hs' as Hs'. subst s'.
    split; [exact I | cbn [exec_primitives]; apply state_eqv_refl].
  - cbn [reloc_primitives] in Hl. cbn [relocate_pages] in Hs'.
    destruct (page_reloc_primitives s vb q) as [pr|] eqn:Hpr; [|discriminate Hl].
    destruct (relocate_page s vb q) as [s1|] eqn:Hrel; [|discriminate Hl].
    destruct (reloc_primitives s1 vb tl) as [rest|] eqn:Hrest; [|discriminate Hl].
    injection Hl as Hl. subst l.
    destruct (reloc_step_ok s vb q tl pr s1 HX Hpr Hrel) as [Hr1 He1].
    destruct (IH s1 vb rest s' (relocate_page_INVX s vb q tl s1 HX Hrel) Hrest Hs')
      as [Hr2 He2].
    split.
    + apply trace_realizable_app. split; [exact Hr1|].
      apply (trace_realizable_congr rest _ s1); [apply state_eqv_sym; exact He1 | exact Hr2].
    + rewrite exec_primitives_app.
      apply (state_eqv_trans _ (exec_primitives s1 rest)); [exact He2|].
      apply exec_primitives_congr. exact He1.
Qed.

Lemma reclaim_ok :
  forall bt s vb l s',
    INVX vb all_pages s ->
    reclaim_primitives bt s vb = Some l ->
    reclaim s vb = Some s' ->
    trace_realizable s l /\ state_eqv s' (exec_primitives s l).
Proof.
  intros bt s vb l s' HX Hl Hs'.
  unfold reclaim_primitives in Hl. unfold reclaim in Hs'.
  destruct (reloc_primitives s vb all_pages) as [rs|] eqn:Hrs; [|discriminate Hl].
  destruct (relocate_pages s vb all_pages) as [s1|] eqn:Hrel; [|discriminate Hs'].
  injection Hl as Hl. subst l. injection Hs' as Hs'. subst s'.
  destruct (reloc_loop_ok all_pages s vb rs s1 HX Hrs Hrel) as [Hr He].
  split.
  - cbn [app]. split; [exact I|]. rewrite prim_enter_id.
    apply trace_realizable_app. split; [exact Hr|].
    repeat split; try exact I.
  - cbn [app]. rewrite exec_cons, prim_enter_id, exec_primitives_app.
    rewrite ?exec_cons, ?exec_nil, prim_exit_id.
    apply (state_eqv_trans _ (apply_primitive s1 (PrimErase vb))).
    + apply erase_eqv.
    + apply apply_primitive_congr. exact He.
Qed.

(* The victim of a reclaim satisfies the relativised bundle the fold needs.
   This is the entry condition [GCPreservation] establishes for its own
   induction, restated here because the agreement fold runs over the same
   list of pages.  It is stated over an arbitrary chooser meeting the
   [victim_sound] contract, so garbage collection and wear levelling use the
   one lemma. *)
Lemma victim_INVX :
  forall pick s vb, victim_sound pick ->
    ftl_invariant s -> pick s = Some vb -> INVX vb all_pages s.
Proof.
  intros pick s vb Hpick Hinv Hv.
  destruct (Hpick s vb Hv) as [Hblt Hrec].
  exact (reclaimable_victim_INVX s vb Hinv Hblt Hrec).
Qed.

Lemma gc_faithful : forall s, ftl_invariant s -> faithful_at s COpGC.
Proof.
  intros s Hinv. apply faithful_intro. intros s1 s2 H1 H2.
  change (step s COpGC) with (gc s) in H1. unfold gc, reclaim_with in H1.
  unfold step_mqsim, op_primitives in H2.
  destruct (find_victim s) as [vb|] eqn:Hv; [|discriminate H1].
  destruct (reclaim_primitives 0 s vb) as [l|] eqn:Hl; [|discriminate H2].
  apply some_inj in H2. subst s2.
  destruct (reclaim_ok 0 s vb l s1
              (victim_INVX find_victim s vb find_victim_sound Hinv Hv) Hl H1)
    as [_ He].
  exact He.
Qed.

(* Wear levelling reclaims a different block -- its own policy's -- but the
   expansion is faithful for the same reason, so the proof differs only in
   the chooser it names. *)
Lemma wearlevel_faithful : forall s, ftl_invariant s -> faithful_at s COpWearLevel.
Proof.
  intros s Hinv. apply faithful_intro. intros s1 s2 H1 H2.
  change (step s COpWearLevel) with (wear_level s) in H1.
  unfold wear_level, reclaim_with in H1.
  unfold step_mqsim, op_primitives in H2.
  destruct (find_least_worn_victim s) as [vb|] eqn:Hv; [|discriminate H1].
  destruct (reclaim_primitives 1 s vb) as [l|] eqn:Hl; [|discriminate H2].
  apply some_inj in H2. subst s2.
  destruct (reclaim_ok 1 s vb l s1
              (victim_INVX find_least_worn_victim s vb
                 find_least_worn_victim_sound Hinv Hv) Hl H1) as [_ He].
  exact He.
Qed.

(* ── the agreement theorem ───────────────────────────────────────────── *)

(* Every mapped address carries the ownership the vendor installed.  This is
   exactly Inv26. *)
Definition owner_attributed (s : FTLState) : Prop :=
  forall a p pa,
    l2p_map s a p = Some pa ->
    (exists t, addr_tenant s a = Some t) /\
    (exists n, addr_namespace s a = Some n).

Lemma owner_attribution_is_redundant :
  forall s, ftl_invariant s -> owner_attributed s.
Proof.
  intros s Hinv. destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_
                                  &_&_&_&_&_&_&I28).
  exact I28.
Qed.

(* Executing an operation's instruction expansion from an invariant-satisfying
   state yields the same state as the operation itself: every field, every
   index, out-of-band metadata included. *)
Theorem decompose_correct :
  forall s op, ftl_invariant s -> faithful_at s op.
Proof.
  intros s op Hinv.
  assert (I5 : Inv3 s) by (destruct Hinv as (_&_&_&_&_&H&_); exact H).
  assert (I22 : Inv20 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (I24 : Inv22 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (I25 : Inv23 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H&_);
     exact H).
  destruct op as [a p | a p d | a p | a p tag | |].
  - apply read_faithful.
  - apply write_faithful; assumption.
  - apply invalidate_faithful; assumption.
  - apply settag_faithful.
  - apply gc_faithful; exact Hinv.
  - apply wearlevel_faithful; exact Hinv.
Qed.

(* The geometry-restricted form of the agreement.  Both of its weakenings are
   unnecessary: the geometry restriction because page-granular relocation and
   erase touch the same ranges on both levels, and [owner_attributed] because
   the expansion installs the destination block's ownership from the very
   fields [program_page] reads. *)
Theorem decompose_correct_geom :
  forall s op,
    ftl_invariant s ->
    owner_attributed s ->
    faithful_at_geom s op.
Proof.
  intros s op Hinv _. apply faithful_weaken. apply decompose_correct. exact Hinv.
Qed.

(* ── the invariant hypothesis is not removable ───────────────────────── *)

(* A state whose reverse map lies.  Page (0,0) is live and mapped from
   logical page (0,0), but its OOB stamp names (1,0) instead, which Inv3
   forbids.  The atomic invalidate detaches (0,0); the expansion, which reads
   the stamp, detaches (1,0) and leaves (0,0) pointing at a stale page.  So
   agreement without the invariant is false. *)
Definition state_lying_stamp : FTLState :=
  mkFTLState
    (fun a p => if andb (Nat.eqb a 0) (Nat.eqb p 0)
                then Some (mkPhysAddr 0 0) else None)
    (fun b p => if andb (Nat.eqb b 0) (Nat.eqb p 0) then PS_Valid 7 else PS_Empty)
    (fun b p => if andb (Nat.eqb b 0) (Nat.eqb p 0) then Some RData else None)
    (fun _ => Some 0) (fun _ => Some 0)
    (fun b => if Nat.eqb b 0 then Some 0 else None)
    (fun b => if Nat.eqb b 0 then Some 0 else None)
    (fun b p => if andb (Nat.eqb b 0) (Nat.eqb p 0)
                then mkPageMeta 0 0 (Some 0) (Some (1, 0))
                else empty_page_meta)
    (fun _ => None)
    []
    (fun _ => false)
    (fun _ => 0)
    (fun _ => None)
    (fun _ _ => None)
    (fun _ _ => 0)
    (fun _ => false).

(* The clause it breaks is Inv3, the forward direction of the reverse map:
   a live page of a mapped address is stamped with that address. *)
Lemma state_lying_stamp_breaks_Inv3 : ~ Inv3 state_lying_stamp.
Proof.
  intros H5. specialize (H5 0 0 (mkPhysAddr 0 0) 7).
  cbn in H5. discriminate (H5 eq_refl eq_refl).
Qed.

Theorem agreement_needs_the_invariant :
  ~ faithful_at state_lying_stamp (COpInvalidate 0 0).
Proof.
  intros Hf. unfold faithful_at in Hf.
  cbn [step step_mqsim op_primitives] in Hf.
  (* both levels succeed; compare the forward map at (0,0) *)
  cbn in Hf.
  pose proof (eqv_l2p _ _ Hf 0 0) as Hc.
  cbn in Hc. discriminate Hc.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- the realizability theorem.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma read_realizable :
  forall s a p l, op_primitives s (COpRead a p) = Some l -> trace_realizable s l.
Proof.
  intros s a p l H. cbn [op_primitives] in H.
  destruct (l2p_map s a p) as [pa|]; injection H as H; subst l;
    cbn [trace_realizable prim_realizable]; repeat split; exact I.
Qed.

Lemma invalidate_realizable :
  forall s a p l, op_primitives s (COpInvalidate a p) = Some l -> trace_realizable s l.
Proof.
  intros s a p l H. cbn [op_primitives] in H.
  destruct (l2p_map s a p) as [pa|]; injection H as H; subst l;
    cbn [trace_realizable prim_realizable]; repeat split; exact I.
Qed.

Lemma settag_realizable :
  forall s a p tag l, op_primitives s (COpSetTag a p tag) = Some l -> trace_realizable s l.
Proof.
  intros s a p tag l H. cbn [op_primitives] in H.
  destruct (l2p_map s a p) as [pa|]; injection H as H; subst l;
    cbn [trace_realizable prim_realizable]; repeat split; exact I.
Qed.

Lemma write_realizable :
  forall s a p d l,
    Inv6 s -> Inv21 s -> Inv22 s ->
    op_primitives s (COpWrite a p d) = Some l ->
    trace_realizable s l.
Proof.
  intros s a p d l I8 I23 I24 H. cbn [op_primitives] in H.
  destruct (Nat.ltb a addr_space && Nat.ltb p pages_per_block &&
            (match addr_tenant s a, addr_namespace s a with
             | Some _, Some _ => true | _, _ => false end)); [|discriminate H].
  unfold write_primitives in H.
  destruct (addr_tenant s a) as [t|]; [|discriminate H].
  destruct (addr_namespace s a) as [ns|]; [|discriminate H].
  destruct (l2p_map s a p) as [old|] eqn:Hm.
  - destruct (alloc_page (invalidate_at s old) t ns) as [[pa s3]|] eqn:Ha;
      [|discriminate H].
    injection H as H. subst l.
    cbn [app trace_realizable prim_realizable exec_primitives].
    repeat split; try exact I.
    (* the state the program sees: barrier, stale, install mapping *)
    cbn [apply_primitive install_mapping].
    change (page_state
              (match page_lpa (page_meta s (pa_block old) (pa_page old)) with
               | Some (a1, p1) => unmap (invalidate_at s old) a1 p1
               | None => invalidate_at s old
               end) (pa_block pa) (pa_page pa) = PS_Empty).
    assert (Hlive : exists dd, page_state s (pa_block old) (pa_page old) = PS_Valid dd)
      by exact (I24 a p old Hm).
    destruct (page_lpa (page_meta s (pa_block old) (pa_page old))) as [[a1 p1]|];
      cbn [unmap page_state];
      exact (write_dest_empty s old t ns pa s3 I8 I23 Hlive Ha).
  - destruct (alloc_page s t ns) as [[pa s3]|] eqn:Ha; [|discriminate H].
    injection H as H. subst l.
    cbn [app trace_realizable prim_realizable exec_primitives apply_primitive
         install_mapping page_state].
    repeat split; try exact I.
    exact (alloc_dest_empty s t ns pa s3 I8 I23 Ha).
Qed.

Lemma gc_realizable :
  forall s l, ftl_invariant s -> op_primitives s COpGC = Some l -> trace_realizable s l.
Proof.
  intros s l Hinv H. cbn [op_primitives] in H.
  destruct (find_victim s) as [vb|] eqn:Hv; [|discriminate H].
  assert (Hrec : exists s', reclaim s vb = Some s').
  { destruct (reclaim s vb) as [s'|] eqn:E; [exists s'; reflexivity|].
    exfalso. apply (proj2 (reclaim_primitives_domain 0 s vb)) in E.
    rewrite H in E. discriminate E. }
  destruct Hrec as [s' Hs'].
  destruct (reclaim_ok 0 s vb l s'
              (victim_INVX find_victim s vb find_victim_sound Hinv Hv) H Hs')
    as [Hr _].
  exact Hr.
Qed.

Lemma wearlevel_realizable :
  forall s l, ftl_invariant s -> op_primitives s COpWearLevel = Some l ->
    trace_realizable s l.
Proof.
  intros s l Hinv H. cbn [op_primitives] in H.
  destruct (find_least_worn_victim s) as [vb|] eqn:Hv; [|discriminate H].
  assert (Hrec : exists s', reclaim s vb = Some s').
  { destruct (reclaim s vb) as [s'|] eqn:E; [exists s'; reflexivity|].
    exfalso. apply (proj2 (reclaim_primitives_domain 1 s vb)) in E.
    rewrite H in E. discriminate E. }
  destruct Hrec as [s' Hs'].
  destruct (reclaim_ok 1 s vb l s'
              (victim_INVX find_least_worn_victim s vb
                 find_least_worn_victim_sound Hinv Hv) H Hs') as [Hr _].
  exact Hr.
Qed.

(* Every program instruction an expansion emits targets a page that is erased
   at the moment the instruction is issued.  This is checked against the
   instruction stream and the flash state alone; [step] is never mentioned. *)
Theorem decompose_realizable :
  forall s op l,
    ftl_invariant s ->
    op_primitives s op = Some l ->
    trace_realizable s l.
Proof.
  intros s op l Hinv H.
  assert (I8 : Inv6 s) by (destruct Hinv as (_&_&_&_&_&_&_&_&H8&_); exact H8).
  assert (I23 : Inv21 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H23&_); exact H23).
  assert (I24 : Inv22 s) by
    (destruct Hinv as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&H24&_);
     exact H24).
  destruct op as [a p | a p d | a p | a p tag | |].
  - exact (read_realizable s a p l H).
  - exact (write_realizable s a p d l I8 I23 I24 H).
  - exact (invalidate_realizable s a p l H).
  - exact (settag_realizable s a p tag l H).
  - exact (gc_realizable s l Hinv H).
  - exact (wearlevel_realizable s l Hinv H).
Qed.

(* An executable corollary: the checker's realizability test passes on every
   expansion a reachable state emits. *)
Corollary decompose_realizableb :
  forall s op l,
    ftl_invariant s ->
    op_primitives s op = Some l ->
    trace_realizableb s l = true.
Proof.
  intros s op l Hinv H. apply trace_realizableb_correct.
  exact (decompose_realizable s op l Hinv H).
Qed.
