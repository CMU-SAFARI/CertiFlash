(* MicroOpPreconditions.v: a proved precondition bundle for the mapping-update
   micro-operations [PrimMapAddr] and [PrimRemap], extending the
   Precondition-Soundness result of [PrimitivePreconditions.v] from the three
   ONFI flash commands to the controller's mapping-table update.

   ── WHY THIS FILE EXISTS ────────────────────────────────────────────────

   [PrimitivePreconditions.v] gives, for each flash command a checker can see
   on the wire ([PrimRead], [PrimProgram], [PrimErase]), a decidable bundle
   that carries the 27-clause invariant across that one command.  The mapping
   update [PrimMapAddr] (and its relocation twin [PrimRemap]) had no such
   bundle: the model could rely only on the operation-level preservation
   theorem for verified FTLs, and the DaisyPlus firmware check for a remap --
   "refuse a remap onto a physical target already owned by a different logical
   page" -- was hand-derived and unproved.  This file closes that gap.

   Both micro-operations reduce to [install_mapping] (see [Primitives.v]):
   [apply_primitive s (PrimMapAddr a p pa) = install_mapping s a p pa] and
   [apply_primitive s (PrimRemap a p dst) = install_mapping s a p dst], so one
   soundness argument serves both.  [install_mapping] touches exactly three
   fields -- [l2p_map] (it points (a,p) at pa) and the block-ownership
   bookkeeping [block_tenant] / [block_namespace] at [pa_block pa] -- and
   leaves [page_state], [page_meta], [page_role] and every [addr_*] field
   fixed.

   ── THE BOARD CHECK AND WHAT IT PRESERVES ───────────────────────────────

   The board's actual check is an injectivity guard:

     [dst_owned_only_by s a p pa]
       : pa is the forward-map target of no logical page other than (a,p).

   This is a decidable scan over the geometry.  On its own -- with no further
   condition -- it is exactly what preserves the injectivity clause Inv2:
   installing (a,p) -> pa can only create a *second* owner of pa, and the board
   check rules that out.  [board_check_preserves_Inv2] states this standalone.

   ── THE GAP: WHAT FULL PRESERVATION NEEDS BEYOND THE BOARD CHECK ─────────

   Full [ftl_invariant] preservation needs one more conjunct: pa must be
   *live* in s.  This is forced by Inv22 (the forward map points only at live
   pages): after the update (a,p) -> pa, Inv22 demands pa be [PS_Valid], and
   [install_mapping] does not change [page_state], so pa must already be live.

   These two conjuncts together have a sharp consequence under the full
   invariant.  If pa is live, Inv0 hands us a logical page that maps to it; the
   board check forces that page to be (a,p) itself; so l2p_map s a p = Some pa
   *already*.  The reachable instances of the mapping update, under the whole
   invariant, are therefore in-place identity remaps -- the update is a no-op
   up to [state_eqv].  This is the exact analogue of the crux in
   [pre_sound_program]: a state that satisfies both the whole invariant and
   "the destination is already mapped/live" cannot be mid-write.  The two live
   on opposite sides of the transient window; neither is weakened to make the
   other go through.  (At the *real* [PrimMapAddr] call site inside a write
   expansion pa is erased, not live, so the full bundle is not satisfied there
   and the invariant is legitimately transiently false -- this is the same
   window [PrimitivePreconditions.v] documents for [PrimProgram].)

   No admitted lemmas, no [admit], no axiom, parameter, variable or hypothesis is
   introduced; no existing file is modified. *)

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
Require Import core.BoundaryAgreement.
Require Import Invariants.PrimitivePreconditions.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 0 -- the bundle, as a decidable predicate.
   ══════════════════════════════════════════════════════════════════════ *)

(* The board's check: pa is owned -- as a forward-map target -- by no logical
   page other than (a,p).  Bounded to the geometry exactly as [pre_erase]'s
   no-live-map conjunct is; a mapped logical page is in range by Inv1, so the
   bound loses nothing under the invariant. *)
Definition dst_owned_only_by (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr)
  : Prop :=
  forall a' p', a' < addr_space -> p' < pages_per_block ->
    l2p_map s a' p' = Some pa -> a' = a /\ p' = p.

Definition dst_owned_only_byb (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr)
  : bool :=
  forall_addrs (fun a' => forall_pages (fun p' =>
    match l2p_map s a' p' with
    | Some pa' => if pa_eqb pa' pa then Nat.eqb a' a && Nat.eqb p' p else true
    | None => true
    end)).

Lemma dst_owned_only_byb_correct :
  forall s a p pa, dst_owned_only_byb s a p pa = true <-> dst_owned_only_by s a p pa.
Proof.
  intros s a p pa. unfold dst_owned_only_byb, dst_owned_only_by. split.
  - intros H a' p' Ha' Hp' Hm.
    pose proof (forall_addrs_elim _ a' H Ha') as Ha4. cbn beta in Ha4.
    pose proof (forall_pages_elim _ p' Ha4 Hp') as Hp4. cbn beta in Hp4.
    rewrite Hm in Hp4. rewrite (proj2 (pa_eqb_correct pa pa) eq_refl) in Hp4.
    apply andb_true_iff in Hp4; destruct Hp4 as [Ea Ep].
    split; [apply Nat.eqb_eq; exact Ea | apply Nat.eqb_eq; exact Ep].
  - intros H. apply forall_addrs_intro. intros a' Ha'. cbn beta.
    apply forall_pages_intro. intros p' Hp'. cbn beta.
    destruct (l2p_map s a' p') as [pa'|] eqn:E; [|reflexivity].
    destruct (pa_eqb pa' pa) eqn:Epa; [|reflexivity].
    apply (proj1 (pa_eqb_correct pa' pa)) in Epa. subst pa'.
    destruct (H a' p' Ha' Hp' E) as [Ea Ep]. subst a' p'.
    rewrite !Nat.eqb_refl. reflexivity.
Qed.

(* pa is live: the extra conjunct full preservation needs beyond the board
   check (Inv22 demands the new forward target be [PS_Valid]). *)
Definition dst_live (s : FTLState) (pa : PhysAddr) : Prop :=
  exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d.

Definition dst_liveb (s : FTLState) (pa : PhysAddr) : bool :=
  match page_state s (pa_block pa) (pa_page pa) with PS_Valid _ => true | _ => false end.

Lemma dst_liveb_correct :
  forall s pa, dst_liveb s pa = true <-> dst_live s pa.
Proof.
  intros s pa. unfold dst_liveb, dst_live. split.
  - intros H. destruct (page_state s (pa_block pa) (pa_page pa)) eqn:E;
      try discriminate H. exists d. reflexivity.
  - intros [d Hd]. rewrite Hd. reflexivity.
Qed.

(* The bundle for the mapping update, shared by [PrimMapAddr] and [PrimRemap]. *)
Definition pre_install (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr) : Prop :=
  dst_owned_only_by s a p pa /\ dst_live s pa.

Definition pre_installb (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr) : bool :=
  dst_owned_only_byb s a p pa && dst_liveb s pa.

Lemma pre_installb_correct :
  forall s a p pa, pre_installb s a p pa = true <-> pre_install s a p pa.
Proof.
  intros s a p pa. unfold pre_installb, pre_install. split.
  - intros H. apply andb_true_iff in H; destruct H as [Hb Hl].
    split; [apply (proj1 (dst_owned_only_byb_correct s a p pa)); exact Hb
           | apply (proj1 (dst_liveb_correct s pa)); exact Hl].
  - intros [Hb Hl]. apply andb_true_iff; split;
      [apply (proj2 (dst_owned_only_byb_correct s a p pa)); exact Hb
      | apply (proj2 (dst_liveb_correct s pa)); exact Hl].
Qed.

(* Names carrying the per-primitive reading of the shared bundle. *)
Definition pre_PrimMapAddr := pre_install.
Definition pre_PrimMapAddrb := pre_installb.
Definition pre_PrimRemap := pre_install.
Definition pre_PrimRemapb := pre_installb.

Lemma pre_PrimMapAddrb_correct :
  forall s a p pa, pre_PrimMapAddrb s a p pa = true <-> pre_PrimMapAddr s a p pa.
Proof. exact pre_installb_correct. Qed.

Lemma pre_PrimRemapb_correct :
  forall s a p dst, pre_PrimRemapb s a p dst = true <-> pre_PrimRemap s a p dst.
Proof. exact pre_installb_correct. Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the standalone injectivity result (the board's actual check).

   The board check alone -- no liveness assumed -- preserves Inv2.  Inv1 of s
   supplies the range bound the bounded board check needs on the competing
   logical page.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma install_l2p :
  forall s a p pa,
    l2p_map (install_mapping s a p pa) = set_l2p_map (l2p_map s) a p (Some pa).
Proof. reflexivity. Qed.

Theorem board_check_preserves_Inv2 :
  forall s a p pa,
    ftl_invariant s ->
    dst_owned_only_by s a p pa ->
    Inv2 (install_mapping s a p pa).
Proof.
  intros s a p pa Hinv Hboard.
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  unfold Inv2. intros a1 p1 a2 p2 pa' H1 H2.
  rewrite install_l2p in H1, H2.
  destruct (nat_pair_dec a1 a p1 p) as [[Ea1 Ep1]|N1].
  - (* (a1,p1) = (a,p) *)
    subst a1 p1. rewrite set_l2p_here in H1. injection H1 as H1. subst pa'.
    destruct (nat_pair_dec a2 a p2 p) as [[Ea2 Ep2]|N2].
    + subst a2 p2. split; reflexivity.
    + rewrite (set_l2p_other _ _ _ _ _ _ N2) in H2.
      (* H2 : l2p_map s a2 p2 = Some pa; the board forbids a second owner *)
      destruct (I3 a2 p2 pa H2) as (_ & _ & Ha2 & Hp2).
      destruct (Hboard a2 p2 Ha2 Hp2 H2) as [Ea2 Ep2].
      subst a2 p2. split; reflexivity.
  - (* (a1,p1) <> (a,p) *)
    rewrite (set_l2p_other _ _ _ _ _ _ N1) in H1.
    destruct (nat_pair_dec a2 a p2 p) as [[Ea2 Ep2]|N2].
    + subst a2 p2. rewrite set_l2p_here in H2. injection H2 as H2. subst pa'.
      destruct (I3 a1 p1 pa H1) as (_ & _ & Ha1 & Hp1).
      destruct (Hboard a1 p1 Ha1 Hp1 H1) as [Ea1 Ep1].
      subst a1 p1. split; reflexivity.
    + rewrite (set_l2p_other _ _ _ _ _ _ N2) in H2.
      exact (I4 a1 p1 a2 p2 pa' H1 H2).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- under the full invariant, the board check plus liveness force the
   remap to be in-place, hence a no-op up to [state_eqv].
   ══════════════════════════════════════════════════════════════════════ *)

Lemma dst_owned_live_inplace :
  forall s a p pa,
    ftl_invariant s ->
    dst_owned_only_by s a p pa ->
    dst_live s pa ->
    l2p_map s a p = Some pa.
Proof.
  intros s a p pa Hinv Hboard [d Hlive].
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  (* Inv0: the live page pa is the target of some logical page *)
  destruct (I2 (pa_block pa) (pa_page pa) d Hlive) as [a' [p' Hm]].
  rewrite physaddr_eta in Hm.
  (* Inv1: that logical page is in range, so the board check applies *)
  destruct (I3 a' p' pa Hm) as (_ & _ & Ha' & Hp').
  destruct (Hboard a' p' Ha' Hp' Hm) as [Ea Ep]. subst a' p'. exact Hm.
Qed.

Lemma install_mapping_eqv_inplace :
  forall s a p pa,
    ftl_invariant s ->
    l2p_map s a p = Some pa ->
    state_eqv s (install_mapping s a p pa).
Proof.
  intros s a p pa Hinv Hinplace.
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  (* Inv18 on the in-place mapping: block ownership already matches (a,p)'s *)
  destruct (I20 a p pa Hinplace) as [Hbt Hbn].
  constructor; unfold install_mapping;
    cbn [l2p_map page_state page_role addr_tenant addr_namespace
         block_tenant block_namespace page_meta region_table
         free_block_list free_block wear_count key_table
         open_block write_ptr block_open].
  - (* l2p *) intros a' p'.
    destruct (nat_pair_dec a' a p' p) as [[E1 E2]|E].
    + subst a' p'. rewrite set_l2p_here. exact Hinplace.
    + rewrite (set_l2p_other _ _ _ _ _ _ E). reflexivity.
  - (* page_state *) intros b' p'; reflexivity.
  - (* page_role *) intros b' p'; reflexivity.
  - (* addr_tenant *) intros a'; reflexivity.
  - (* addr_namespace *) intros a'; reflexivity.
  - (* block_tenant *) intros b'.
    destruct (Nat.eq_dec b' (pa_block pa)) as [E|E].
    + subst b'. rewrite set_bt_here. exact Hbt.
    + rewrite (set_bt_other _ _ _ _ E). reflexivity.
  - (* block_namespace *) intros b'.
    destruct (Nat.eq_dec b' (pa_block pa)) as [E|E].
    + subst b'. rewrite set_bn_here. exact Hbn.
    + rewrite (set_bn_other _ _ _ _ E). reflexivity.
  - (* page_meta *) intros b' p'; reflexivity.
  - (* region_table *) intros i; reflexivity.
  - (* free_block_list *) reflexivity.
  - (* free_block *) intros b'; reflexivity.
  - (* wear_count *) intros b'; reflexivity.
  - (* key_table *) intros k; reflexivity.
  - (* open_block *) intros t ns; reflexivity.
  - (* write_ptr *) intros t ns; reflexivity.
  - (* block_open *) intros b'; reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- precondition soundness for the mapping update.
   ══════════════════════════════════════════════════════════════════════ *)

Theorem pre_sound_install :
  forall s a p pa,
    ftl_invariant s ->
    pre_install s a p pa ->
    ftl_invariant (install_mapping s a p pa).
Proof.
  intros s a p pa Hinv [Hboard Hlive].
  assert (Hinplace : l2p_map s a p = Some pa)
    by exact (dst_owned_live_inplace s a p pa Hinv Hboard Hlive).
  apply (state_eqv_invariant s (install_mapping s a p pa)).
  - exact (install_mapping_eqv_inplace s a p pa Hinv Hinplace).
  - exact Hinv.
Qed.

Theorem pre_sound_PrimMapAddr :
  forall s a p pa,
    ftl_invariant s ->
    pre_PrimMapAddr s a p pa ->
    ftl_invariant (apply_primitive s (PrimMapAddr a p pa)).
Proof.
  intros s a p pa Hinv Hpre.
  exact (pre_sound_install s a p pa Hinv Hpre).
Qed.

Theorem pre_sound_PrimRemap :
  forall s a p dst,
    ftl_invariant s ->
    pre_PrimRemap s a p dst ->
    ftl_invariant (apply_primitive s (PrimRemap a p dst)).
Proof.
  intros s a p dst Hinv Hpre.
  exact (pre_sound_install s a p dst Hinv Hpre).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- PrimInvalidate: staling a live page (and dropping its mapping).

   [apply_primitive s (PrimInvalidate pa)] sets [pa] to [PS_Invalid], clears
   its role and OOB, and -- when [pa] still carries a reverse-map stamp
   (a, p) -- drops the forward mapping [l2p_map a p] as well.  The danger is
   Inv0 (every live page is mapped): dropping a mapping can orphan a live page
   if that mapping did not point at [pa].  It cannot when [pa] is live: Inv0
   gives [pa] a mapper, Inv3 stamps [pa] with it, and Inv4 makes the stamp the
   forward map's own witness, so the only mapping dropped is the one that
   pointed at the page we just staled.  The bundle is therefore exactly

     [pre_invalidate s pa]  :  [pa] is live ([dst_live]),

   the same liveness signal the mapping update needs, read off the destination
   the checker can already see.  Invalidating the last mapped page of a block
   turns it into a garbage block (Inv10/Inv12's fourth/second disjunct), which
   is the resting state a deferred erase leaves behind.  At the *real* call
   site inside a write expansion, [old = l2p_map s a p] is precisely this live
   mapped page, so the bundle holds there.
   ══════════════════════════════════════════════════════════════════════ *)

Definition pre_invalidate (s : FTLState) (pa : PhysAddr) : Prop := dst_live s pa.

Definition pre_invalidateb (s : FTLState) (pa : PhysAddr) : bool := dst_liveb s pa.

Lemma pre_invalidateb_correct :
  forall s pa, pre_invalidateb s pa = true <-> pre_invalidate s pa.
Proof. exact dst_liveb_correct. Qed.

Theorem pre_sound_invalidate :
  forall s pa,
    ftl_invariant s ->
    pre_invalidate s pa ->
    ftl_invariant (apply_primitive s (PrimInvalidate pa)).
Proof.
  intros s pa Hinv Hpre.
  destruct pa as [b q].
  destruct Hpre as [d0 Hlive]. cbn [pa_block pa_page] in Hlive.
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  (* the live page is mapped (Inv0), and its stamp names that mapper (Inv3) *)
  destruct (I2 b q d0 Hlive) as [a0 [q0 Hm0]].
  pose proof (I5 a0 q0 (mkPhysAddr b q) d0 Hm0 Hlive) as Hstamp.
  cbn [pa_block pa_page] in Hstamp.
  (* the invalidated block is not free (its live page is mapped, Inv5) *)
  pose proof (I7 a0 q0 (mkPhysAddr b q) Hm0) as Hbfree. cbn [pa_block] in Hbfree.
  (* select the Some branch of [apply_primitive] and name the result state *)
  assert (Happ : apply_primitive s (PrimInvalidate (mkPhysAddr b q))
                 = unmap (invalidate_at s (mkPhysAddr b q)) a0 q0).
  { cbn [apply_primitive pa_block pa_page]. rewrite Hstamp. reflexivity. }
  rewrite Happ.
  match goal with |- ftl_invariant ?st => remember st as s' eqn:Es' end.
  assert (El2p : l2p_map s' = set_l2p_map (l2p_map s) a0 q0 None)
    by (rewrite Es'; reflexivity).
  assert (Eps : page_state s' = set_page_state (page_state s) b q PS_Invalid)
    by (rewrite Es'; reflexivity).
  assert (Epr : page_role s' = set_page_role (page_role s) b q None)
    by (rewrite Es'; reflexivity).
  assert (Epm : page_meta s' = set_page_meta (page_meta s) b q empty_page_meta)
    by (rewrite Es'; reflexivity).
  assert (Eat : addr_tenant s' = addr_tenant s) by (rewrite Es'; reflexivity).
  assert (Ean : addr_namespace s' = addr_namespace s) by (rewrite Es'; reflexivity).
  assert (Ebt : block_tenant s' = block_tenant s) by (rewrite Es'; reflexivity).
  assert (Ebn : block_namespace s' = block_namespace s) by (rewrite Es'; reflexivity).
  assert (Ert : region_table s' = region_table s) by (rewrite Es'; reflexivity).
  assert (Efbl : free_block_list s' = free_block_list s) by (rewrite Es'; reflexivity).
  assert (Efb : free_block s' = free_block s) by (rewrite Es'; reflexivity).
  assert (Eob : open_block s' = open_block s) by (rewrite Es'; reflexivity).
  assert (Ewp : write_ptr s' = write_ptr s) by (rewrite Es'; reflexivity).
  assert (Ebo : block_open s' = block_open s) by (rewrite Es'; reflexivity).
  clear Es'.
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros bx qx _ _. eexists. reflexivity.
  - (* Inv0 *) intros bx qx dx Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_ps_here in Hv. discriminate Hv.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      destruct (I2 bx qx dx Hv) as [ax [qx' Hmap]].
      exists ax, qx'. rewrite El2p.
      destruct (nat_pair_dec ax a0 qx' q0) as [[F1 F2]|F].
      * subst ax qx'. exfalso. rewrite Hm0 in Hmap. injection Hmap as Hb Hq.
        destruct E as [E|E]; [apply E; exact (eq_sym Hb) | apply E; exact (eq_sym Hq)].
      * rewrite (set_l2p_other _ _ _ _ _ _ F). exact Hmap.
  - (* Inv1 *) intros ax px pax Hm. rewrite El2p in Hm.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm. exact (I3 ax px pax Hm).
  - (* Inv2 *) intros a1 p1 a2 p2 pax H1 H2. rewrite El2p in H1, H2.
    destruct (nat_pair_dec a1 a0 p1 q0) as [[E1a E1b]|N1];
      [subst a1 p1; rewrite set_l2p_here in H1; discriminate H1|].
    rewrite (set_l2p_other _ _ _ _ _ _ N1) in H1.
    destruct (nat_pair_dec a2 a0 p2 q0) as [[E2a E2b]|N2];
      [subst a2 p2; rewrite set_l2p_here in H2; discriminate H2|].
    rewrite (set_l2p_other _ _ _ _ _ _ N2) in H2.
    exact (I4 a1 p1 a2 p2 pax H1 H2).
  - (* Inv3 *) intros ax px pax dx Hm Hv. rewrite El2p in Hm. rewrite Eps in Hv.
    rewrite Epm.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + rewrite E1, E2 in Hv. rewrite set_ps_here in Hv. discriminate Hv.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ E). exact (I5 ax px pax dx Hm Hv).
  - (* Inv4 *) intros ax px bx qx dx Hv Hl. rewrite Eps in Hv. rewrite Epm in Hl.
    rewrite El2p.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_ps_here in Hv. discriminate Hv.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ E) in Hl.
      pose proof (I6 ax px bx qx dx Hv Hl) as Hmap.
      destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F].
      * subst ax px. exfalso. rewrite Hm0 in Hmap. injection Hmap as Hb Hq.
        destruct E as [E|E]; [apply E; exact (eq_sym Hb) | apply E; exact (eq_sym Hq)].
      * rewrite (set_l2p_other _ _ _ _ _ _ F). exact Hmap.
  - (* Inv5 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Efbl.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm. exact (I7 ax px pax Hm).
  - (* Inv6 *) intros bx Hin px Hp. rewrite Efbl in Hin.
    assert (Hne : bx <> b) by (intros Hc; subst bx; exact (Hbfree Hin)).
    rewrite Eps, Epm.
    rewrite (set_ps_other _ _ _ _ _ _ (or_introl Hne)).
    rewrite (set_pm_other _ _ _ _ _ _ (or_introl Hne)).
    exact (I8 bx Hin px Hp).
  - (* Inv7 *) intros ax px pax dx tx nx Hm Hv Hatx Hanx.
    rewrite El2p in Hm. rewrite Eps in Hv. rewrite Eat in Hatx. rewrite Ean in Hanx.
    rewrite Epm.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + rewrite E1, E2 in Hv. rewrite set_ps_here in Hv. discriminate Hv.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ E). exact (I9 ax px pax dx tx nx Hm Hv Hatx Hanx).
  - (* Inv8 *) intros bx Hin. rewrite Efbl in Hin. exact (I10 bx Hin).
  - (* Inv9 *) intros bx qx dx Hv. rewrite Eps in Hv. rewrite Epm.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_ps_here in Hv. discriminate Hv.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ E). exact (I11 bx qx dx Hv).
  - (* Inv10 *) intros bx Hbx.
    destruct (I12 bx Hbx) as [Hf|[[t' [ns' Ho]]|[[ax [px [pax [Hmp Hbk]]]]|[qx Hq]]]].
    + left. rewrite Efbl. exact Hf.
    + right; left. exists t', ns'. rewrite Eob. exact Ho.
    + destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F].
      * subst ax px. rewrite Hm0 in Hmp. injection Hmp as Hpax. subst pax.
        cbn [pa_block] in Hbk. subst bx.
        right; right; right. exists q. rewrite Eps. rewrite set_ps_here. reflexivity.
      * right; right; left. exists ax, px, pax. split.
        -- rewrite El2p. rewrite (set_l2p_other _ _ _ _ _ _ F). exact Hmp.
        -- exact Hbk.
    + right; right; right. exists qx. rewrite Eps.
      destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
      * subst bx qx. rewrite set_ps_here. reflexivity.
      * rewrite (set_ps_other _ _ _ _ _ _ E). exact Hq.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) intros bx Hbx [px Hrole]. rewrite Epr in Hrole.
    destruct (nat_pair_dec bx b px q) as [[E1 E2]|E].
    + subst bx px. rewrite set_pr_here in Hrole. discriminate Hrole.
    + rewrite (set_pr_other _ _ _ _ _ _ E) in Hrole.
      destruct (I14 bx Hbx (ex_intro _ px Hrole)) as [[ax [px' [pax [Hmp Hbk]]]]|[qx Hq]].
      * destruct (nat_pair_dec ax a0 px' q0) as [[F1 F2]|F].
        -- subst ax px'. rewrite Hm0 in Hmp. injection Hmp as Hpax. subst pax.
           cbn [pa_block] in Hbk. subst bx.
           right. exists q. rewrite Eps. rewrite set_ps_here. reflexivity.
        -- left. exists ax, px', pax. split.
           ++ rewrite El2p. rewrite (set_l2p_other _ _ _ _ _ _ F). exact Hmp.
           ++ exact Hbk.
      * right. exists qx. rewrite Eps.
        destruct (nat_pair_dec bx b qx q) as [[G1 G2]|G].
        -- subst bx qx. rewrite set_ps_here. reflexivity.
        -- rewrite (set_ps_other _ _ _ _ _ _ G). exact Hq.
  - (* Inv13 *) intros bx qx dx Hv. rewrite Eps in Hv. rewrite Epr.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_ps_here in Hv. discriminate Hv.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      rewrite (set_pr_other _ _ _ _ _ _ E). exact (I15 bx qx dx Hv).
  - (* Inv14 *) intros bx qx Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pr_here in Hr. discriminate Hr.
    + rewrite (set_pr_other _ _ _ _ _ _ E) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ E). exact (I16 bx qx Hr).
  - (* Inv15 *) intros bx qx Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pr_here in Hr. discriminate Hr.
    + rewrite (set_pr_other _ _ _ _ _ _ E) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ E). exact (I17 bx qx Hr).
  - (* Inv16 *) intros bx qx Hv. rewrite Eps in Hv. rewrite Epr.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pr_here. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ E) in Hv.
      rewrite (set_pr_other _ _ _ _ _ _ E). exact (I18 bx qx Hv).
  - (* Inv17 *) intros bx Hf. rewrite Efb in Hf. rewrite Ebt, Ebn. exact (I19 bx Hf).
  - (* Inv18 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Ebt, Ebn, Eat, Ean.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm. exact (I20 ax px pax Hm).
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t' ns' bx Ho. rewrite Eob in Ho.
    destruct (I22 t' ns' bx Ho) as (A1&A2&A3&A4&A5&A6&A7&A8).
    split; [exact A1|]. split; [rewrite Efbl; exact A2|]. split; [rewrite Efb; exact A3|].
    split; [rewrite Ebo; exact A4|]. split; [rewrite Ewp; exact A5|].
    split; [rewrite Ebt; exact A6|]. split; [rewrite Ebn; exact A7|].
    intros t'' ns'' Ho'. rewrite Eob in Ho'. exact (A8 t'' ns'' Ho').
  - (* Inv21 *) intros t' ns' bx qx Ho Hle Hq. rewrite Eob in Ho. rewrite Ewp in Hle.
    rewrite Eps, Epm.
    destruct (I23 t' ns' bx qx Ho Hle Hq) as [Hpe Hme].
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. exfalso. rewrite Hlive in Hpe. discriminate Hpe.
    + rewrite (set_ps_other _ _ _ _ _ _ E). rewrite (set_pm_other _ _ _ _ _ _ E).
      split; [exact Hpe | exact Hme].
  - (* Inv22 *) intros ax px pax Hm. rewrite El2p in Hm.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm.
    rewrite Eps.
    destruct (I24 ax px pax Hm) as [dx Hdx].
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + exfalso.
      assert (Hpaxpa : pax = mkPhysAddr b q).
      { rewrite <- E1, <- E2. symmetry. apply physaddr_eta. }
      subst pax. destruct (I4 ax px a0 q0 (mkPhysAddr b q) Hm Hm0) as [Ea Eb].
      subst ax px. destruct F as [F|F]; [apply F; reflexivity | apply F; reflexivity].
    + rewrite (set_ps_other _ _ _ _ _ _ E). exists dx. exact Hdx.
  - (* Inv23 *) intros bx Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 bx Hbo).
  - (* Inv24 *) intros bx. rewrite Efb, Efbl. exact (I26 bx).
  - (* Inv25 *) intros t' ns' bx qx Ho Hlt. rewrite Eob in Ho. rewrite Ewp in Hlt.
    rewrite Eps.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_ps_here. intros Hc; discriminate Hc.
    + rewrite (set_ps_other _ _ _ _ _ _ E). exact (I27 t' ns' bx qx Ho Hlt).
  - (* Inv26 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Eat, Ean.
    destruct (nat_pair_dec ax a0 px q0) as [[F1 F2]|F];
      [subst ax px; rewrite set_l2p_here in Hm; discriminate Hm|].
    rewrite (set_l2p_other _ _ _ _ _ _ F) in Hm. exact (I28 ax px pax Hm).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- PrimSetTag: writing an integrity tag onto a live page.

   [apply_primitive s (PrimSetTag pa tag)] rewrites only the [page_tag] field
   of [pa]'s OOB, and only when [pa] is [PS_Valid]; on any other page state it
   is the identity.  The guard is the whole story: the only clauses that read
   the OOB are Inv3/Inv4 (the reverse-map stamp -- untouched), Inv7 (the
   owner -- untouched), Inv9 (a live page carries *some* tag -- made truer),
   and Inv6/Inv21 (an erased or above-frontier page carries the *empty* OOB --
   and the guard forbids touching such a page).  So the invariant is preserved
   with no side condition at all: the bundle is [True].
   ══════════════════════════════════════════════════════════════════════ *)

Theorem pre_sound_settag :
  forall s pa tag,
    ftl_invariant s ->
    ftl_invariant (apply_primitive s (PrimSetTag pa tag)).
Proof.
  intros s pa tag Hinv. destruct pa as [b q].
  cbn [apply_primitive pa_block pa_page].
  destruct (page_state s b q) as [| |d] eqn:Hpst; try exact Hinv.
  (* PS_Valid d: the page is live, so no free/above-frontier clause applies *)
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  remember (set_page_tag_at s (mkPhysAddr b q) tag) as s' eqn:Es'.
  assert (El2p : l2p_map s' = l2p_map s) by (rewrite Es'; reflexivity).
  assert (Eps : page_state s' = page_state s) by (rewrite Es'; reflexivity).
  assert (Epr : page_role s' = page_role s) by (rewrite Es'; reflexivity).
  assert (Eat : addr_tenant s' = addr_tenant s) by (rewrite Es'; reflexivity).
  assert (Ean : addr_namespace s' = addr_namespace s) by (rewrite Es'; reflexivity).
  assert (Ebt : block_tenant s' = block_tenant s) by (rewrite Es'; reflexivity).
  assert (Ebn : block_namespace s' = block_namespace s) by (rewrite Es'; reflexivity).
  assert (Ert : region_table s' = region_table s) by (rewrite Es'; reflexivity).
  assert (Efbl : free_block_list s' = free_block_list s) by (rewrite Es'; reflexivity).
  assert (Efb : free_block s' = free_block s) by (rewrite Es'; reflexivity).
  assert (Eob : open_block s' = open_block s) by (rewrite Es'; reflexivity).
  assert (Ewp : write_ptr s' = write_ptr s) by (rewrite Es'; reflexivity).
  assert (Ebo : block_open s' = block_open s) by (rewrite Es'; reflexivity).
  assert (Epm : page_meta s' = set_page_meta (page_meta s) b q
                  (mkPageMeta (page_owner_tenant (page_meta s b q))
                              (page_owner_namespace (page_meta s b q))
                              (Some tag) (page_lpa (page_meta s b q))))
    by (rewrite Es'; reflexivity).
  clear Es'.
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros bx qx _ _. eexists. reflexivity.
  - (* Inv0 *) intros bx qx dx Hv. rewrite Eps in Hv. rewrite El2p. exact (I2 bx qx dx Hv).
  - (* Inv1 *) intros ax px pax Hm. rewrite El2p in Hm. exact (I3 ax px pax Hm).
  - (* Inv2 *) intros a1 p1 a2 p2 pax H1 H2. rewrite El2p in H1, H2.
    exact (I4 a1 p1 a2 p2 pax H1 H2).
  - (* Inv3 *) intros ax px pax dx Hm Hv. rewrite El2p in Hm. rewrite Eps in Hv.
    rewrite Epm.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + rewrite E1, E2. rewrite set_pm_here. cbn [page_lpa].
      pose proof (I5 ax px pax dx Hm Hv) as Hlp. rewrite E1, E2 in Hlp. exact Hlp.
    + rewrite (set_pm_other _ _ _ _ _ _ E). exact (I5 ax px pax dx Hm Hv).
  - (* Inv4 *) intros ax px bx qx dx Hv Hl. rewrite Eps in Hv. rewrite Epm in Hl.
    rewrite El2p.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pm_here in Hl. cbn [page_lpa] in Hl.
      exact (I6 ax px b q dx Hv Hl).
    + rewrite (set_pm_other _ _ _ _ _ _ E) in Hl. exact (I6 ax px bx qx dx Hv Hl).
  - (* Inv5 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Efbl. exact (I7 ax px pax Hm).
  - (* Inv6 *) intros bx Hin px Hp. rewrite Efbl in Hin. rewrite Eps, Epm.
    destruct (I8 bx Hin px Hp) as [Hpe Hme].
    destruct (nat_pair_dec bx b px q) as [[E1 E2]|E].
    + subst bx px. exfalso. rewrite Hpst in Hpe. discriminate Hpe.
    + rewrite (set_pm_other _ _ _ _ _ _ E). split; [exact Hpe | exact Hme].
  - (* Inv7 *) intros ax px pax dx tx nx Hm Hv Hatx Hanx.
    rewrite El2p in Hm. rewrite Eps in Hv. rewrite Eat in Hatx. rewrite Ean in Hanx.
    rewrite Epm.
    destruct (nat_pair_dec (pa_block pax) b (pa_page pax) q) as [[E1 E2]|E].
    + rewrite E1, E2. rewrite set_pm_here. cbn [page_owner_tenant page_owner_namespace].
      destruct (I9 ax px pax dx tx nx Hm Hv Hatx Hanx) as [Ho Hn].
      rewrite E1, E2 in Ho, Hn. split; [exact Ho | exact Hn].
    + rewrite (set_pm_other _ _ _ _ _ _ E). exact (I9 ax px pax dx tx nx Hm Hv Hatx Hanx).
  - (* Inv8 *) intros bx Hin. rewrite Efbl in Hin. exact (I10 bx Hin).
  - (* Inv9 *) intros bx qx dx Hv. rewrite Eps in Hv. rewrite Epm.
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. rewrite set_pm_here. cbn [page_tag]. exists tag. reflexivity.
    + rewrite (set_pm_other _ _ _ _ _ _ E). exact (I11 bx qx dx Hv).
  - (* Inv10 *) intros bx Hbx. rewrite Efbl, Eob, El2p, Eps. exact (I12 bx Hbx).
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) intros bx Hbx [px Hrole]. rewrite Epr in Hrole. rewrite El2p, Eps.
    exact (I14 bx Hbx (ex_intro _ px Hrole)).
  - (* Inv13 *) intros bx qx dx Hv. rewrite Eps in Hv. rewrite Epr. exact (I15 bx qx dx Hv).
  - (* Inv14 *) intros bx qx Hr. rewrite Epr in Hr. rewrite Eps. exact (I16 bx qx Hr).
  - (* Inv15 *) intros bx qx Hr. rewrite Epr in Hr. rewrite Eps. exact (I17 bx qx Hr).
  - (* Inv16 *) intros bx qx Hv. rewrite Eps in Hv. rewrite Epr. exact (I18 bx qx Hv).
  - (* Inv17 *) intros bx Hf. rewrite Efb in Hf. rewrite Ebt, Ebn. exact (I19 bx Hf).
  - (* Inv18 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Ebt, Ebn, Eat, Ean.
    exact (I20 ax px pax Hm).
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t' ns' bx Ho. rewrite Eob in Ho.
    destruct (I22 t' ns' bx Ho) as (A1&A2&A3&A4&A5&A6&A7&A8).
    split; [exact A1|]. split; [rewrite Efbl; exact A2|]. split; [rewrite Efb; exact A3|].
    split; [rewrite Ebo; exact A4|]. split; [rewrite Ewp; exact A5|].
    split; [rewrite Ebt; exact A6|]. split; [rewrite Ebn; exact A7|].
    intros t'' ns'' Ho'. rewrite Eob in Ho'. exact (A8 t'' ns'' Ho').
  - (* Inv21 *) intros t' ns' bx qx Ho Hle Hq. rewrite Eob in Ho. rewrite Ewp in Hle.
    rewrite Eps, Epm.
    destruct (I23 t' ns' bx qx Ho Hle Hq) as [Hpe Hme].
    destruct (nat_pair_dec bx b qx q) as [[E1 E2]|E].
    + subst bx qx. exfalso. rewrite Hpst in Hpe. discriminate Hpe.
    + rewrite (set_pm_other _ _ _ _ _ _ E). split; [exact Hpe | exact Hme].
  - (* Inv22 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Eps. exact (I24 ax px pax Hm).
  - (* Inv23 *) intros bx Hbo. rewrite Ebo in Hbo. rewrite Eob. exact (I25 bx Hbo).
  - (* Inv24 *) intros bx. rewrite Efb, Efbl. exact (I26 bx).
  - (* Inv25 *) intros t' ns' bx qx Ho Hlt. rewrite Eob in Ho. rewrite Ewp in Hlt.
    rewrite Eps. exact (I27 t' ns' bx qx Ho Hlt).
  - (* Inv26 *) intros ax px pax Hm. rewrite El2p in Hm. rewrite Eat, Ean.
    exact (I28 ax px pax Hm).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 6 -- barriers: transaction markers with no state effect.
   ══════════════════════════════════════════════════════════════════════ *)

Theorem pre_sound_barrier_enter :
  forall s tag,
    ftl_invariant s ->
    ftl_invariant (apply_primitive s (PrimBarrierEnter tag)).
Proof. intros s tag Hinv. exact Hinv. Qed.

Theorem pre_sound_barrier_exit :
  forall s tag,
    ftl_invariant s ->
    ftl_invariant (apply_primitive s (PrimBarrierExit tag)).
Proof. intros s tag Hinv. exact Hinv. Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 6b -- the full [PrimProgram] bundle: a program whose OOB is explicit.

   [apply_primitive s (PrimProgram pa d tag lpa)] programs [pa] with data [d],
   stamps the block's owner, and writes the supplied [tag] into the OOB.  An
   honest expansion always passes [tag = Some d] (a tag stamped from the data);
   an untrusted controller is free to pass [tag = None] and leave a live page
   carrying no integrity tag -- the FS#4 surface, which falsifies Inv9.

   The full bundle [pre_program_raw] reuses the honest-expansion bundle
   [pre_program] verbatim and adds the single conjunct that the supplied tag be
   [Some _].  That conjunct is the whole difference: the honest program burns
   [Some d] and so keeps Inv9 for free ([pre_sound_program]), whereas the
   general program keeps Inv9 only when the caller supplies a real tag.  Every
   other clause is preserved for exactly the reasons [pre_sound_program] gives,
   because the two results differ only in the tag field of the one programmed
   page, and no clause but Inv9 reads that field.  [retag_invariant] transports
   the invariant across that one-field difference, and [pre_sound_program_raw]
   chains it after [pre_sound_program].
   ══════════════════════════════════════════════════════════════════════ *)

(* Transport: two states agreeing on every field, and on [page_meta]
   everywhere except one page [(b,q)] whose owner/namespace/reverse-map stamp
   agree and whose integrity tag is [Some _] on both sides, satisfy the same
   invariant.  Only Inv9 reads the tag, and it reads only whether it is [Some];
   Inv6/Inv21 read the whole OOB but only of free / above-frontier pages, and
   the old tag being [Some] keeps [(b,q)] out of both. *)
Lemma retag_invariant :
  forall s1 s2 b q,
    ftl_invariant s1 ->
    (forall a p, l2p_map s2 a p = l2p_map s1 a p) ->
    (forall x y, page_state s2 x y = page_state s1 x y) ->
    (forall x y, page_role s2 x y = page_role s1 x y) ->
    (forall a, addr_tenant s2 a = addr_tenant s1 a) ->
    (forall a, addr_namespace s2 a = addr_namespace s1 a) ->
    (forall x, block_tenant s2 x = block_tenant s1 x) ->
    (forall x, block_namespace s2 x = block_namespace s1 x) ->
    (forall x y, (x <> b \/ y <> q) -> page_meta s2 x y = page_meta s1 x y) ->
    (forall i, region_table s2 i = region_table s1 i) ->
    free_block_list s2 = free_block_list s1 ->
    (forall x, free_block s2 x = free_block s1 x) ->
    (forall k, key_table s2 k = key_table s1 k) ->
    (forall t ns, open_block s2 t ns = open_block s1 t ns) ->
    (forall t ns, write_ptr s2 t ns = write_ptr s1 t ns) ->
    (forall x, block_open s2 x = block_open s1 x) ->
    page_owner_tenant (page_meta s2 b q) = page_owner_tenant (page_meta s1 b q) ->
    page_owner_namespace (page_meta s2 b q) = page_owner_namespace (page_meta s1 b q) ->
    page_lpa (page_meta s2 b q) = page_lpa (page_meta s1 b q) ->
    (exists d0, page_tag (page_meta s1 b q) = Some d0) ->
    (exists tg, page_tag (page_meta s2 b q) = Some tg) ->
    ftl_invariant s2.
Proof.
  intros s1 s2 b q Hinv El Eps Epr Eat Ean Ebt Ebn Epm Ert Efbl Efb Ekt Eob Ewp Ebo
         Hot Hon Hlp [d0 Hd0] [tg Htg].
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros x y _ _. eexists. reflexivity.
  - (* Inv0 *) intros x y d Hv. rewrite Eps in Hv.
    destruct (I2 x y d Hv) as [a [qq Hm]]. exists a, qq. rewrite El. exact Hm.
  - (* Inv1 *) intros a p pa Hm. rewrite El in Hm. exact (I3 a p pa Hm).
  - (* Inv2 *) intros a1 p1 a2 p2 pa H1 H2. rewrite El in H1, H2.
    exact (I4 a1 p1 a2 p2 pa H1 H2).
  - (* Inv3 *) intros a p pa d Hm Hv. rewrite El in Hm. rewrite Eps in Hv.
    destruct (nat_pair_dec (pa_block pa) b (pa_page pa) q) as [[E1 E2]|E].
    + rewrite E1, E2. rewrite Hlp.
      pose proof (I5 a p pa d Hm Hv) as HL. rewrite E1, E2 in HL. exact HL.
    + rewrite (Epm _ _ E). exact (I5 a p pa d Hm Hv).
  - (* Inv4 *) intros a p x y d Hv Hl. rewrite Eps in Hv.
    destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    + subst x y. rewrite Hlp in Hl. rewrite El. exact (I6 a p b q d Hv Hl).
    + rewrite (Epm _ _ E) in Hl. rewrite El. exact (I6 a p x y d Hv Hl).
  - (* Inv5 *) intros a p pa Hm. rewrite El in Hm. rewrite Efbl. exact (I7 a p pa Hm).
  - (* Inv6 *) intros x Hin y Hy. rewrite Efbl in Hin.
    destruct (I8 x Hin y Hy) as [Hpe Hme]. rewrite Eps. split; [exact Hpe|].
    destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    + subst x y. exfalso. rewrite Hme in Hd0. cbn in Hd0. discriminate Hd0.
    + rewrite (Epm _ _ E). exact Hme.
  - (* Inv7 *) intros a p pa d t ns Hm Hv Hat Han.
    rewrite El in Hm. rewrite Eps in Hv. rewrite Eat in Hat. rewrite Ean in Han.
    destruct (nat_pair_dec (pa_block pa) b (pa_page pa) q) as [[E1 E2]|E].
    + rewrite E1, E2. rewrite Hot, Hon.
      destruct (I9 a p pa d t ns Hm Hv Hat Han) as [Ho Hn].
      rewrite E1, E2 in Ho, Hn. split; [exact Ho | exact Hn].
    + rewrite (Epm _ _ E). exact (I9 a p pa d t ns Hm Hv Hat Han).
  - (* Inv8 *) intros x Hin. rewrite Efbl in Hin. exact (I10 x Hin).
  - (* Inv9 *) intros x y d Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    + subst x y. exists tg. exact Htg.
    + rewrite (Epm _ _ E). exact (I11 x y d Hv).
  - (* Inv10 *) intros x Hx.
    destruct (I12 x Hx) as [H|[[t [ns H]]|[[a [p [pa [Hm Hbk]]]]|[y Hy]]]].
    + left. rewrite Efbl. exact H.
    + right; left. exists t, ns. rewrite Eob. exact H.
    + right; right; left. exists a, p, pa. rewrite El. split; assumption.
    + right; right; right. exists y. rewrite Eps. exact Hy.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) intros x Hx [y Hr]. rewrite Epr in Hr.
    destruct (I14 x Hx (ex_intro _ y Hr)) as [[a [p [pa [Hm Hbk]]]]|[y' Hy]].
    + left. exists a, p, pa. rewrite El. split; assumption.
    + right. exists y'. rewrite Eps. exact Hy.
  - (* Inv13 *) intros x y d Hv. rewrite Eps in Hv. rewrite Epr. exact (I15 x y d Hv).
  - (* Inv14 *) intros x y Hr. rewrite Epr in Hr. destruct (I16 x y Hr) as [d Hd].
    exists d. rewrite Eps. exact Hd.
  - (* Inv15 *) intros x y Hr. rewrite Epr in Hr. rewrite Eps. exact (I17 x y Hr).
  - (* Inv16 *) intros x y Hv. rewrite Eps in Hv. rewrite Epr. exact (I18 x y Hv).
  - (* Inv17 *) intros x Hf. rewrite Efb in Hf. rewrite Ebt, Ebn. exact (I19 x Hf).
  - (* Inv18 *) intros a p pa Hm. rewrite El in Hm. rewrite Ebt, Ebn, Eat, Ean.
    exact (I20 a p pa Hm).
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t ns x Ho. rewrite Eob in Ho.
    destruct (I22 t ns x Ho) as (A1&A2&A3&A4&A5&A6&A7&A8).
    split; [exact A1|]. split; [rewrite Efbl; exact A2|]. split; [rewrite Efb; exact A3|].
    split; [rewrite Ebo; exact A4|]. split; [rewrite Ewp; exact A5|].
    split; [rewrite Ebt; exact A6|]. split; [rewrite Ebn; exact A7|].
    intros t' ns' Ho'. rewrite Eob in Ho'. exact (A8 t' ns' Ho').
  - (* Inv21 *) intros t ns x y Ho Hle Hy. rewrite Eob in Ho. rewrite Ewp in Hle.
    rewrite Eps. destruct (I23 t ns x y Ho Hle Hy) as [Hpe Hme]. split; [exact Hpe|].
    destruct (nat_pair_dec x b y q) as [[E1 E2]|E].
    + subst x y. exfalso. rewrite Hme in Hd0. cbn in Hd0. discriminate Hd0.
    + rewrite (Epm _ _ E). exact Hme.
  - (* Inv22 *) intros a p pa Hm. rewrite El in Hm. rewrite Eps. exact (I24 a p pa Hm).
  - (* Inv23 *) intros x Hbo. rewrite Ebo in Hbo. destruct (I25 x Hbo) as [t [ns Ho]].
    exists t, ns. rewrite Eob. exact Ho.
  - (* Inv24 *) intros x. rewrite Efb, Efbl. exact (I26 x).
  - (* Inv25 *) intros t ns x y Ho Hlt. rewrite Eob in Ho. rewrite Ewp in Hlt.
    rewrite Eps. exact (I27 t ns x y Ho Hlt).
  - (* Inv26 *) intros a p pa Hm. rewrite El in Hm. rewrite Eat, Ean.
    exact (I28 a p pa Hm).
Qed.

(* The bundle: the [PrimProgram] bundle, plus "the supplied tag is real". *)
Definition pre_program_raw (s : FTLState) (pa : PhysAddr) (d : Data)
                           (tag : option CryptoTag) (lpa : option LPA) : Prop :=
  pre_program s pa d lpa /\ (exists tg, tag = Some tg).

Definition pre_program_rawb (s : FTLState) (pa : PhysAddr) (d : Data)
                            (tag : option CryptoTag) (lpa : option LPA) : bool :=
  pre_programb s pa d lpa &&
  (match tag with Some _ => true | None => false end).

Lemma pre_program_rawb_correct :
  forall s pa d tag lpa,
    pre_program_rawb s pa d tag lpa = true <-> pre_program_raw s pa d tag lpa.
Proof.
  intros s pa d tag lpa. unfold pre_program_rawb, pre_program_raw. split.
  - intros H. apply andb_true_iff in H as [Hp Ht]. split.
    + apply (proj1 (pre_programb_correct s pa d lpa)); exact Hp.
    + destruct tag as [tg|]; [exists tg; reflexivity | discriminate Ht].
  - intros [Hp [tg Ht]]. apply andb_true_iff; split.
    + apply (proj2 (pre_programb_correct s pa d lpa)); exact Hp.
    + subst tag; reflexivity.
Qed.

Theorem pre_sound_program_raw :
  forall s pa d tag lpa,
    ftl_invariant s ->
    pre_program_raw s pa d tag lpa ->
    ftl_invariant (apply_primitive s (PrimProgram pa d tag lpa)).
Proof.
  intros s pa d tag lpa Hinv [Hpre [tg Htag]]. subst tag.
  (* the tag-stamping program (tag [Some d]) preserves the invariant; the
     program with an arbitrary real tag [Some tg] is that state with only the
     one page's tag field changed, which [retag_invariant] transports across *)
  pose proof (pre_sound_program s pa d lpa Hinv Hpre) as HP.
  apply (retag_invariant
           (apply_primitive s (PrimProgram pa d (Some d) lpa))
           (apply_primitive s (PrimProgram pa d (Some tg) lpa))
           (pa_block pa) (pa_page pa) HP).
  - intros a0 p0; reflexivity.
  - intros x y; reflexivity.
  - intros x y; reflexivity.
  - intros a0; reflexivity.
  - intros a0; reflexivity.
  - intros x; reflexivity.
  - intros x; reflexivity.
  - intros x y Hne. cbn [apply_primitive page_meta].
    rewrite !(set_pm_other _ _ _ _ _ _ Hne). reflexivity.
  - intros i; reflexivity.
  - reflexivity.
  - intros x; reflexivity.
  - intros k; reflexivity.
  - intros t ns; reflexivity.
  - intros t ns; reflexivity.
  - intros x; reflexivity.
  - cbn [apply_primitive page_meta]. rewrite !set_pm_here. reflexivity.
  - cbn [apply_primitive page_meta]. rewrite !set_pm_here. reflexivity.
  - cbn [apply_primitive page_meta]. rewrite !set_pm_here. reflexivity.
  - cbn [apply_primitive page_meta]. rewrite set_pm_here. cbn [page_tag]. exists d. reflexivity.
  - cbn [apply_primitive page_meta]. rewrite set_pm_here. cbn [page_tag]. exists tg. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 6c -- PrimFreePush: returning a block to the free pool.

   [apply_primitive s (PrimFreePush b)] prepends [b] to [free_block_list] and
   sets its free bit; no other field moves.  [PrimErase] does the same push,
   but only after clearing the block and only for a block whose free bit is
   clear.  A bare push exposes both freedoms: pushing a block that is already
   free duplicates it (FS#5), and pushing a block that still holds data /
   ownership / a mapping would break the free-block clauses.

   The bundle names exactly what a sound push needs, and each conjunct guards a
   specific clause:
     - [b] not already free, both as a bit and on the list -- Inv11 (the list
       stays duplicate-free) and Inv24 (the bit and the list stay in step).
       This is the conjunct FS#5 turns off.
     - [b] closed (not open for any owner)               -- Inv20.
     - [b] unowned ([block_tenant]/[block_namespace] None) -- Inv17.
     - no forward mapping lands in [b]                   -- Inv5.
     - every in-range page of [b] erased with empty OOB  -- Inv6.
   These are the resting shape of a block the clearing half of an erase has
   already produced; a push issued with the bundle omitted is the attack.
   ══════════════════════════════════════════════════════════════════════ *)

Definition pre_freepush (s : FTLState) (b : Block) : Prop :=
  b < total_blocks /\
  free_block s b = false /\
  ~ In b (free_block_list s) /\
  block_open s b = false /\
  block_tenant s b = None /\
  block_namespace s b = None /\
  (forall a p pa, a < addr_space -> p < pages_per_block ->
     l2p_map s a p = Some pa -> pa_block pa <> b) /\
  (forall p, p < pages_per_block ->
     page_state s b p = PS_Empty /\ page_meta s b p = empty_page_meta).

Definition inb (b : Block) (l : list Block) : bool := existsb (Nat.eqb b) l.

Lemma inb_correct : forall b l, inb b l = true <-> In b l.
Proof.
  intros b l. unfold inb. rewrite existsb_exists. split.
  - intros [x [Hin Hx]]. apply Nat.eqb_eq in Hx. subst x. exact Hin.
  - intros Hin. exists b. split; [exact Hin | apply Nat.eqb_refl].
Qed.

Definition pre_freepushb (s : FTLState) (b : Block) : bool :=
  Nat.ltb b total_blocks &&
  negb (free_block s b) &&
  negb (inb b (free_block_list s)) &&
  negb (block_open s b) &&
  (match block_tenant s b with None => true | Some _ => false end) &&
  (match block_namespace s b with None => true | Some _ => false end) &&
  forall_addrs (fun a => forall_pages (fun p =>
     match l2p_map s a p with
     | Some pa => negb (Nat.eqb (pa_block pa) b)
     | None => true
     end)) &&
  forall_pages (fun p => ps_emptyb (page_state s b p) && meta_emptyb (page_meta s b p)).

Lemma pre_freepushb_correct :
  forall s b, pre_freepushb s b = true <-> pre_freepush s b.
Proof.
  intros s b. unfold pre_freepushb, pre_freepush. split.
  - intros H.
    apply andb_true_iff in H; destruct H as [H H8].
    apply andb_true_iff in H; destruct H as [H H7].
    apply andb_true_iff in H; destruct H as [H H6].
    apply andb_true_iff in H; destruct H as [H H5].
    apply andb_true_iff in H; destruct H as [H H4].
    apply andb_true_iff in H; destruct H as [H H3].
    apply andb_true_iff in H; destruct H as [H1 H2].
    apply Nat.ltb_lt in H1. apply negb_true_iff in H2.
    apply negb_true_iff in H3. apply negb_true_iff in H4.
    split; [exact H1|].
    split; [exact H2|].
    split; [intro Hc; apply (proj2 (inb_correct b (free_block_list s))) in Hc;
            rewrite Hc in H3; discriminate H3|].
    split; [exact H4|].
    split; [destruct (block_tenant s b); [discriminate H5 | reflexivity]|].
    split; [destruct (block_namespace s b); [discriminate H6 | reflexivity]|].
    split.
    { intros a p pa Ha Hp Hm.
      pose proof (forall_addrs_elim _ a H7 Ha) as Ha7. cbn beta in Ha7.
      pose proof (forall_pages_elim _ p Ha7 Hp) as Hp7. cbn beta in Hp7.
      rewrite Hm in Hp7. apply negb_true_iff in Hp7. apply Nat.eqb_neq in Hp7. exact Hp7. }
    { intros p Hp.
      pose proof (forall_pages_elim _ p H8 Hp) as Hp8. cbn beta in Hp8.
      apply andb_true_iff in Hp8; destruct Hp8 as [Hps Hpm].
      split; [exact (proj1 (ps_emptyb_true _) Hps)
             | exact (proj1 (meta_emptyb_correct _) Hpm)]. }
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    apply andb_true_iff; split; [apply andb_true_iff; split;
      [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split; [apply andb_true_iff; split;
          [apply andb_true_iff; split | ] | ] | ] | ] | ] | ].
    + apply Nat.ltb_lt; exact H1.
    + apply negb_true_iff; exact H2.
    + apply negb_true_iff. destruct (inb b (free_block_list s)) eqn:E;
        [exfalso; apply H3; apply (proj1 (inb_correct b (free_block_list s))); exact E
        | reflexivity].
    + apply negb_true_iff; exact H4.
    + rewrite H5; reflexivity.
    + rewrite H6; reflexivity.
    + apply forall_addrs_intro. intros a Ha. cbn beta.
      apply forall_pages_intro. intros p Hp. cbn beta.
      destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
      apply negb_true_iff. apply Nat.eqb_neq. exact (H7 a p pa Ha Hp E).
    + apply forall_pages_intro. intros p Hp. cbn beta.
      destruct (H8 p Hp) as [Hps Hpm].
      apply andb_true_iff; split;
        [exact (proj2 (ps_emptyb_true _) Hps) | exact (proj2 (meta_emptyb_correct _) Hpm)].
Qed.

Theorem pre_sound_freepush :
  forall s b,
    ftl_invariant s ->
    pre_freepush s b ->
    ftl_invariant (apply_primitive s (PrimFreePush b)).
Proof.
  intros s b Hinv Hpre.
  destruct Hpre as (Hrange & Hfb0 & Hnin & Hclosed & Hbt0 & Hbn0 & Hunmap & Hempty).
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  (* the resulting state's fields *)
  remember (apply_primitive s (PrimFreePush b)) as s' eqn:Es'.
  assert (El2p : l2p_map s' = l2p_map s) by (rewrite Es'; reflexivity).
  assert (Eps : page_state s' = page_state s) by (rewrite Es'; reflexivity).
  assert (Epr : page_role s' = page_role s) by (rewrite Es'; reflexivity).
  assert (Eat : addr_tenant s' = addr_tenant s) by (rewrite Es'; reflexivity).
  assert (Ean : addr_namespace s' = addr_namespace s) by (rewrite Es'; reflexivity).
  assert (Ebt : block_tenant s' = block_tenant s) by (rewrite Es'; reflexivity).
  assert (Ebn : block_namespace s' = block_namespace s) by (rewrite Es'; reflexivity).
  assert (Epm : page_meta s' = page_meta s) by (rewrite Es'; reflexivity).
  assert (Ert : region_table s' = region_table s) by (rewrite Es'; reflexivity).
  assert (Efbl : free_block_list s' = b :: free_block_list s) by (rewrite Es'; reflexivity).
  assert (Efb : free_block s' = set_free_block (free_block s) b true)
    by (rewrite Es'; reflexivity).
  assert (Eob : open_block s' = open_block s) by (rewrite Es'; reflexivity).
  assert (Ewp : write_ptr s' = write_ptr s) by (rewrite Es'; reflexivity).
  assert (Ebo : block_open s' = block_open s) by (rewrite Es'; reflexivity).
  clear Es'.
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros x y _ _. eexists. reflexivity.
  - (* Inv0 *) intros x y d Hv. rewrite Eps in Hv. rewrite El2p. exact (I2 x y d Hv).
  - (* Inv1 *) intros a p pa Hm. rewrite El2p in Hm. exact (I3 a p pa Hm).
  - (* Inv2 *) intros a1 p1 a2 p2 pa H1 H2. rewrite El2p in H1, H2.
    exact (I4 a1 p1 a2 p2 pa H1 H2).
  - (* Inv3 *) intros a p pa d Hm Hv. rewrite El2p in Hm. rewrite Eps in Hv. rewrite Epm.
    exact (I5 a p pa d Hm Hv).
  - (* Inv4 *) intros a p x y d Hv Hl. rewrite Eps in Hv. rewrite Epm in Hl. rewrite El2p.
    exact (I6 a p x y d Hv Hl).
  - (* Inv5 *) intros a p pa Hm. rewrite El2p in Hm. rewrite Efbl.
    destruct (I3 a p pa Hm) as (_ & _ & Ha & Hp).
    intros [Hc|Hc].
    + exact (Hunmap a p pa Ha Hp Hm (eq_sym Hc)).
    + exact (I7 a p pa Hm Hc).
  - (* Inv6 *) intros x Hin y Hy. rewrite Efbl in Hin. rewrite Eps, Epm.
    destruct Hin as [Hxb|Hx].
    + subst x. exact (Hempty y Hy).
    + exact (I8 x Hx y Hy).
  - (* Inv7 *) intros a p pa d t ns Hm Hv Hat Han.
    rewrite El2p in Hm. rewrite Eps in Hv. rewrite Eat in Hat. rewrite Ean in Han.
    rewrite Epm. exact (I9 a p pa d t ns Hm Hv Hat Han).
  - (* Inv8 *) intros x Hin. rewrite Efbl in Hin. destruct Hin as [Hxb|Hx].
    + subst x. exact Hrange.
    + exact (I10 x Hx).
  - (* Inv9 *) intros x y d Hv. rewrite Eps in Hv. rewrite Epm. exact (I11 x y d Hv).
  - (* Inv10 *) intros x Hx. rewrite Efbl, El2p, Eps.
    destruct (Nat.eq_dec x b) as [Exb|Exb].
    + subst x. left. left. reflexivity.
    + destruct (I12 x Hx) as [H|[[t [ns H]]|[[a [p [pa [Hm Hbk]]]]|[y Hy]]]].
      * left. right. exact H.
      * right; left. exists t, ns. rewrite Eob. exact H.
      * right; right; left. exists a, p, pa. split; assumption.
      * right; right; right. exists y. exact Hy.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. constructor; [exact Hnin | exact I13].
  - (* Inv12 *) intros x Hx [y Hr]. rewrite Epr in Hr. rewrite El2p, Eps.
    exact (I14 x Hx (ex_intro _ y Hr)).
  - (* Inv13 *) intros x y d Hv. rewrite Eps in Hv. rewrite Epr. exact (I15 x y d Hv).
  - (* Inv14 *) intros x y Hr. rewrite Epr in Hr. destruct (I16 x y Hr) as [d Hd].
    exists d. rewrite Eps. exact Hd.
  - (* Inv15 *) intros x y Hr. rewrite Epr in Hr. rewrite Eps. exact (I17 x y Hr).
  - (* Inv16 *) intros x y Hv. rewrite Eps in Hv. rewrite Epr. exact (I18 x y Hv).
  - (* Inv17 *) intros x Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    destruct (Nat.eq_dec x b) as [Exb|Exb].
    + subst x. split; [exact Hbt0 | exact Hbn0].
    + rewrite (set_fb_other _ _ _ _ Exb) in Hf. exact (I19 x Hf).
  - (* Inv18 *) intros a p pa Hm. rewrite El2p in Hm. rewrite Ebt, Ebn, Eat, Ean.
    exact (I20 a p pa Hm).
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t ns x Ho. rewrite Eob in Ho.
    destruct (I22 t ns x Ho) as (A1&A2&A3&A4&A5&A6&A7&A8).
    assert (Hxb : x <> b).
    { intro Hc. subst x. rewrite Hclosed in A4. discriminate A4. }
    split; [exact A1|].
    split; [rewrite Efbl; intros [Hc|Hc]; [exact (Hxb (eq_sym Hc)) | exact (A2 Hc)]|].
    split; [rewrite Efb; rewrite (set_fb_other _ _ _ _ Hxb); exact A3|].
    split; [rewrite Ebo; exact A4|]. split; [rewrite Ewp; exact A5|].
    split; [rewrite Ebt; exact A6|]. split; [rewrite Ebn; exact A7|].
    intros t' ns' Ho'. rewrite Eob in Ho'. exact (A8 t' ns' Ho').
  - (* Inv21 *) intros t ns x y Ho Hle Hy. rewrite Eob in Ho. rewrite Ewp in Hle.
    rewrite Eps, Epm. exact (I23 t ns x y Ho Hle Hy).
  - (* Inv22 *) intros a p pa Hm. rewrite El2p in Hm. rewrite Eps. exact (I24 a p pa Hm).
  - (* Inv23 *) intros x Hbo. rewrite Ebo in Hbo. rewrite Eob. exact (I25 x Hbo).
  - (* Inv24 *) intros x. rewrite Efb, Efbl.
    destruct (Nat.eq_dec x b) as [Exb|Exb].
    + subst x. rewrite set_fb_here. split; [intros _; left; reflexivity | intros _; reflexivity].
    + rewrite (set_fb_other _ _ _ _ Exb). split.
      * intros Hc. right. apply (proj1 (I26 x)). exact Hc.
      * intros [Hc|Hc]; [exfalso; apply Exb; exact (eq_sym Hc)
                        | apply (proj2 (I26 x)); exact Hc].
  - (* Inv25 *) intros t ns x y Ho Hlt. rewrite Eob in Ho. rewrite Ewp in Hlt.
    rewrite Eps. exact (I27 t ns x y Ho Hlt).
  - (* Inv26 *) intros a p pa Hm. rewrite El2p in Hm. rewrite Eat, Ean.
    exact (I28 a p pa Hm).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 7 -- the uniform statement.

   [pre_instr] dispatches every instruction -- flash primitive or controller
   micro-operation -- to its bundle, reusing the flash-command bundles from
   [PrimitivePreconditions.v] and the mapping bundle above.  Instructions
   that preserve the invariant unconditionally (both barriers and the guarded
   [PrimSetTag]) get the bundle [True].  [precondition_sound] is then one
   theorem covering all nine instructions, and [pre_instrb] gives its decidable
   checker so the whole bundle can be evaluated on the wire.
   ══════════════════════════════════════════════════════════════════════ *)

Definition pre_instr (i : FlashPrimitive) (s : FTLState) : Prop :=
  match i with
  | PrimRead pa => pre_read s pa
  (* the unified program carries its OOB explicitly, so the full checker demands
     a real integrity tag: this is the conjunct FS#4 turns off *)
  | PrimProgram pa d tag lpa => pre_program_raw s pa d tag lpa
  | PrimInvalidate pa => pre_invalidate s pa
  | PrimSetTag pa tag => True
  | PrimMapAddr a p pa => pre_PrimMapAddr s a p pa
  | PrimRemap a p dst => pre_PrimRemap s a p dst
  | PrimErase b => pre_erase s b
  | PrimBarrierEnter _ => True
  | PrimBarrierExit _ => True
  | PrimFreePush b => pre_freepush s b
  end.

Definition pre_instrb (i : FlashPrimitive) (s : FTLState) : bool :=
  match i with
  | PrimRead pa => pre_readb s pa
  | PrimProgram pa d tag lpa => pre_program_rawb s pa d tag lpa
  | PrimInvalidate pa => pre_invalidateb s pa
  | PrimSetTag pa tag => true
  | PrimMapAddr a p pa => pre_PrimMapAddrb s a p pa
  | PrimRemap a p dst => pre_PrimRemapb s a p dst
  | PrimErase b => pre_eraseb s b
  | PrimBarrierEnter _ => true
  | PrimBarrierExit _ => true
  | PrimFreePush b => pre_freepushb s b
  end.

Lemma pre_instrb_correct :
  forall i s, pre_instrb i s = true <-> pre_instr i s.
Proof.
  intros i s. destruct i; cbn [pre_instrb pre_instr].
  - apply pre_readb_correct.
  - apply pre_program_rawb_correct.
  - apply pre_invalidateb_correct.
  - split; [intros _; exact I | intros _; reflexivity].
  - apply pre_PrimMapAddrb_correct.
  - apply pre_PrimRemapb_correct.
  - apply pre_eraseb_correct.
  - split; [intros _; exact I | intros _; reflexivity].
  - split; [intros _; exact I | intros _; reflexivity].
  - apply pre_freepushb_correct.
Qed.

Theorem precondition_sound :
  forall i s,
    ftl_invariant s ->
    pre_instr i s ->
    ftl_invariant (apply_primitive s i).
Proof.
  intros i s Hinv Hpre.
  destruct i as [pa | pa d tag lpa | pa | pa tag | a p pa | a p dst | b | tag | tag
                | b];
    cbn [pre_instr] in Hpre.
  - exact (pre_sound_read s pa Hinv Hpre).
  - exact (pre_sound_program_raw s pa d tag lpa Hinv Hpre).
  - exact (pre_sound_invalidate s pa Hinv Hpre).
  - exact (pre_sound_settag s pa tag Hinv).
  - exact (pre_sound_PrimMapAddr s a p pa Hinv Hpre).
  - exact (pre_sound_PrimRemap s a p dst Hinv Hpre).
  - exact (pre_sound_erase s b Hinv Hpre).
  - exact (pre_sound_barrier_enter s tag Hinv).
  - exact (pre_sound_barrier_exit s tag Hinv).
  - exact (pre_sound_freepush s b Hinv Hpre).
Qed.
