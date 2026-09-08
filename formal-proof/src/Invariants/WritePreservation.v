(* WritePreservation.v

   Proves

     write_preserves_invariant :
       forall s a p d s', ftl_invariant s ->
         step s (COpWrite a p d) = Some s' -> ftl_invariant s'.

     invalidate_preserves_invariant :
       forall s a p s', ftl_invariant s ->
         step s (COpInvalidate a p) = Some s' -> ftl_invariant s'.

   Both are proved below and closed with [Qed].  No admitted lemmas, no [admit],
   no added axiom, parameter, variable or hypothesis.

   WHY THE ALLOCATION FRONTIER IS INDEXED BY (TENANT, NAMESPACE).  The hard
   clause of the write case is the namespace half of Inv18: [program_page]
   stamps the destination block with the writing address's namespace, and a
   frontier indexed by tenant alone would pin nothing about that namespace, so
   the stamp could overwrite a co-resident page's.  The frontier is indexed
   by the (tenant, namespace) pair, and Inv20 carries the namespace disjunct
     [block_namespace s b = None \/ block_namespace s b = Some ns]
   alongside the tenant one.  The Inv18 argument is therefore symmetric in
   the two fields: a co-resident mapped address a0 has, by Inv26, both
   labels; Inv18 at [s2] identifies them with the block's; the two Inv20
   disjuncts force them to be [t] and [ns]; the re-stamp is a no-op in both
   coordinates.  Nothing else was needed.

   WHAT IS IN THIS FILE, in order:
     pointwise update lemmas for the frontier and ownership fields
     [invalidate_preserves_invariant]  invalidate preserves the invariant, Qed
     [program_ok]                      programming the fresh page
     [write_core]                      allocating it, both branches
     [write_preserves_invariant]       write preserves the invariant, Qed
   and, outside the section, both with the geometry hypothesis discharged. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.

Import ListNotations.

Section WritePreservation.

Context {pages_per_block_gt0 : pages_per_block > 0}.

(* ── pointwise update lemmas for the fields PagePreservation omits ── *)

Lemma set_ob_here : forall f t ns v, set_open_block f t ns v t ns = v.
Proof. intros. unfold set_open_block. now rewrite !Nat.eqb_refl. Qed.

Lemma set_ob_other : forall f t ns v x y,
  (x <> t \/ y <> ns) -> set_open_block f t ns v x y = f x y.
Proof.
  intros f t ns v x y H. unfold set_open_block.
  destruct (Nat.eqb x t) eqn:Ex; destruct (Nat.eqb y ns) eqn:Ey; simpl; auto.
  apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey. destruct H; congruence.
Qed.

Lemma set_wp_here : forall f t ns v, set_write_ptr f t ns v t ns = v.
Proof. intros. unfold set_write_ptr. now rewrite !Nat.eqb_refl. Qed.

Lemma set_wp_other : forall f t ns v x y,
  (x <> t \/ y <> ns) -> set_write_ptr f t ns v x y = f x y.
Proof.
  intros f t ns v x y H. unfold set_write_ptr.
  destruct (Nat.eqb x t) eqn:Ex; destruct (Nat.eqb y ns) eqn:Ey; simpl; auto.
  apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey. destruct H; congruence.
Qed.

Lemma set_bo_here : forall f b v, set_block_open f b v b = v.
Proof. intros. unfold set_block_open. now rewrite Nat.eqb_refl. Qed.

Lemma set_bo_other : forall f b v x, x <> b -> set_block_open f b v x = f x.
Proof.
  intros f b v x H. unfold set_block_open.
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma set_fb_here : forall f b v, set_free_block f b v b = v.
Proof. intros. unfold set_free_block. now rewrite Nat.eqb_refl. Qed.

Lemma set_fb_other : forall f b v x, x <> b -> set_free_block f b v x = f x.
Proof.
  intros f b v x H. unfold set_free_block.
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma set_bt_here : forall f b v, set_block_tenant f b v b = v.
Proof. intros. unfold set_block_tenant. now rewrite Nat.eqb_refl. Qed.

Lemma set_bt_other : forall f b v x, x <> b -> set_block_tenant f b v x = f x.
Proof.
  intros f b v x H. unfold set_block_tenant.
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma set_bn_here : forall f b v, set_block_namespace f b v b = v.
Proof. intros. unfold set_block_namespace. now rewrite Nat.eqb_refl. Qed.

Lemma set_bn_other : forall f b v x, x <> b -> set_block_namespace f b v x = f x.
Proof.
  intros f b v x H. unfold set_block_namespace.
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma nat_pair_dec :
  forall x y z w : nat, (x = y /\ z = w) \/ (x <> y \/ z <> w).
Proof.
  intros x y z w. destruct (Nat.eq_dec x y); destruct (Nat.eq_dec z w); auto.
Qed.

Lemma remove_block_once_head :
  forall b l, remove_block_once b (b :: l) = l.
Proof. intros b l. cbn. now rewrite Nat.eqb_refl. Qed.

(* ── COpInvalidate ────────────────────────────────────────────────── *)

Lemma invalidate_preserves_invariant :
  forall s a p s', ftl_invariant s ->
    step s (COpInvalidate a p) = Some s' -> ftl_invariant s'.
Proof.
  intros s a p s' Hinv Hstep.
  unfold step in Hstep. injection Hstep as Hstep. subst s'.
  unfold exec_invalidate.
  destruct (l2p_map s a p) as [pa|] eqn:Hm; [|exact Hinv].
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  destruct (I24 a p pa Hm) as [dold Hold].
  pose proof (I7 a p pa Hm) as Hnf.
  set (u := unmap (invalidate_at s pa) a p).
  assert (Els : l2p_map u = set_l2p_map (l2p_map s) a p None) by reflexivity.
  assert (Eps : page_state u =
                set_page_state (page_state s) (pa_block pa) (pa_page pa) PS_Invalid)
    by reflexivity.
  assert (Epr : page_role u =
                set_page_role (page_role s) (pa_block pa) (pa_page pa) None)
    by reflexivity.
  assert (Epm : page_meta u =
                set_page_meta (page_meta s) (pa_block pa) (pa_page pa) empty_page_meta)
    by reflexivity.
  assert (Eat : addr_tenant u = addr_tenant s) by reflexivity.
  assert (Ean : addr_namespace u = addr_namespace s) by reflexivity.
  assert (Ebt : block_tenant u = block_tenant s) by reflexivity.
  assert (Ebn : block_namespace u = block_namespace s) by reflexivity.
  assert (Ert : region_table u = region_table s) by reflexivity.
  assert (Efbl : free_block_list u = free_block_list s) by reflexivity.
  assert (Efb : free_block u = free_block s) by reflexivity.
  assert (Eob : open_block u = open_block s) by reflexivity.
  assert (Ewp : write_ptr u = write_ptr s) by reflexivity.
  assert (Ebo : block_open u = block_open s) by reflexivity.
  assert (Hdiff : forall x y z w : nat, (x = y /\ z = w) \/ (x <> y \/ z <> w)).
  { intros x y z w. destruct (Nat.eq_dec x y); destruct (Nat.eq_dec z w); auto. }
  (* a mapping other than (a,p) cannot land on the invalidated page *)
  assert (Hnotpa : forall a0 p0 pa0, l2p_map s a0 p0 = Some pa0 ->
                     (a0 <> a \/ p0 <> p) ->
                     (pa_block pa0 <> pa_block pa \/ pa_page pa0 <> pa_page pa)).
  { intros a0 p0 pa0 H Hne.
    destruct (Hdiff (pa_block pa0) (pa_block pa) (pa_page pa0) (pa_page pa))
      as [[E1 E2]|H']; [|exact H'].
    exfalso.
    assert (Hpa : pa0 = pa).
    { rewrite <- (physaddr_eta pa0), <- (physaddr_eta pa), E1, E2. reflexivity. }
    subst pa0. destruct (I4 a0 p0 a p pa H Hm) as [E3 E4].
    destruct Hne as [X|X]; auto. }
  (* conversely, a page other than the invalidated one is not mapped by (a,p) *)
  assert (Hmapdiff : forall a0 p0 b0 q0,
                       l2p_map s a0 p0 = Some (mkPhysAddr b0 q0) ->
                       (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
                       (a0 <> a \/ p0 <> p)).
  { intros a0 p0 b0 q0 H Hne. destruct (Hdiff a0 a p0 p) as [[E1 E2]|H']; [|exact H'].
    exfalso. subst a0 p0. rewrite Hm in H. injection H as H.
    rewrite H in Hne. cbn in Hne. destruct Hne as [X|X]; exact (X eq_refl). }
  assert (Hstale : page_state u (pa_block pa) (pa_page pa) = PS_Invalid)
    by (rewrite Eps; apply set_ps_here).
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      destruct (I2 b0 q0 d0 Hv) as (a0 & p0 & Hmap).
      exists a0, p0. rewrite Els.
      rewrite (set_l2p_other _ _ _ _ _ _ (Hmapdiff a0 p0 b0 q0 Hmap Hne)). exact Hmap.
  - (* Inv1 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap. exact (I3 a0 p0 pa0 Hmap).
  - (* Inv2 *) intros a1 p1 a2 p2 pa0 H1 H2. rewrite Els in H1, H2.
    destruct (Hdiff a1 a p1 p) as [[E1 E2]|Hne1].
    + subst a1 p1. rewrite set_l2p_here in H1. discriminate.
    + destruct (Hdiff a2 a p2 p) as [[E3 E4]|Hne2].
      * subst a2 p2. rewrite set_l2p_here in H2. discriminate.
      * rewrite (set_l2p_other _ _ _ _ _ _ Hne1) in H1.
        rewrite (set_l2p_other _ _ _ _ _ _ Hne2) in H2.
        exact (I4 a1 p1 a2 p2 pa0 H1 H2).
  - (* Inv3 *) intros a0 p0 pa0 d0 Hmap Hv. rewrite Els in Hmap.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (Hnotpa a0 p0 pa0 Hmap Hne) as Hd.
      rewrite Eps in Hv. rewrite (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm. rewrite (set_pm_other _ _ _ _ _ _ Hd).
      exact (I5 a0 p0 pa0 d0 Hmap Hv).
  - (* Inv4 *) intros a0 p0 b0 q0 d0 Hv Hlpa. rewrite Eps in Hv. rewrite Epm in Hlpa.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
      pose proof (I6 a0 p0 b0 q0 d0 Hv Hlpa) as Hmap.
      rewrite Els.
      rewrite (set_l2p_other _ _ _ _ _ _ (Hmapdiff a0 p0 b0 q0 Hmap Hne)). exact Hmap.
  - (* Inv5 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap. rewrite Efbl.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap. exact (I7 a0 p0 pa0 Hmap).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0. exfalso. exact (Hnf Hin).
    + rewrite Eps, Epm.
      rewrite (set_ps_other _ _ _ _ _ _ Hne), (set_pm_other _ _ _ _ _ _ Hne).
      exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn.
    rewrite Els in Hmap. rewrite Eat in Ht. rewrite Ean in Hn.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (Hnotpa a0 p0 pa0 Hmap Hne) as Hd.
      rewrite Eps in Hv. rewrite (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm. rewrite (set_pm_other _ _ _ _ _ _ Hd).
      exact (I9 a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite Epm. rewrite (set_pm_other _ _ _ _ _ _ Hne).
      exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) intros b0 Hb0.
    destruct (I12 b0 Hb0)
      as [Hin | [[t0 [ns0 Hob]] | [(a0&p0&pa0&Hmap&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob.
    + destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
      * subst a0 p0. right; right; right.
        rewrite Hm in Hmap. injection Hmap as Hmap. subst pa0.
        exists (pa_page pa). rewrite <- Hblk. exact Hstale.
      * right; right; left. exists a0, p0, pa0. split; [|exact Hblk].
        rewrite Els. rewrite (set_l2p_other _ _ _ _ _ _ Hne). exact Hmap.
    + right; right; right. exists q0. rewrite Eps.
      destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
      * subst b0 q0. apply set_ps_here.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne). exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) intros b0 Hb0 [q0 Hrole]. rewrite Epr in Hrole.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
      destruct (I14 b0 Hb0 (ex_intro _ q0 Hrole))
        as [(a0&p0&pa0&Hmap&Hblk) | [q1 Hq1]].
      * destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne2].
        -- subst a0 p0. right.
           rewrite Hm in Hmap. injection Hmap as Hmap. subst pa0.
           exists (pa_page pa). rewrite <- Hblk. exact Hstale.
        -- left. exists a0, p0, pa0. split; [|exact Hblk].
           rewrite Els. rewrite (set_l2p_other _ _ _ _ _ _ Hne2). exact Hmap.
      * right. exists q1. rewrite Eps.
        destruct (Hdiff b0 (pa_block pa) q1 (pa_page pa)) as [[E3 E4]|Hne3].
        -- subst b0 q1. apply set_ps_here.
        -- rewrite (set_ps_other _ _ _ _ _ _ Hne3). exact Hq1.
  - (* Inv13 *) intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I15 b0 q0 d0 Hv).
  - (* Inv14 *) intros b0 q0 Hrole. rewrite Epr in Hrole. rewrite Eps.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I16 b0 q0 Hrole).
  - (* Inv15 *) intros b0 q0 Hrole. rewrite Epr in Hrole. rewrite Eps.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I17 b0 q0 Hrole).
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in He. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in He.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    exact (I19 b0 Hf).
  - (* Inv18 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    rewrite Ebt, Ebn, Eat, Ean.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap. exact (I20 a0 p0 pa0 Hmap).
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t0 ns0 b0 Hob. rewrite Eob in Hob.
    rewrite Efbl, Efb, Ebo, Ewp, Ebt, Ebn, Eob. exact (I22 t0 ns0 b0 Hob).
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob Hwp Hq0.
    rewrite Eob in Hob. rewrite Ewp in Hwp.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + exfalso. subst b0 q0.
      pose proof (live_below_frontier s t0 ns0 (pa_block pa) (pa_page pa) dold
                    I23 Hob Hq0 Hold) as Hlt.
      lia.
    + rewrite Eps, Epm.
      rewrite (set_ps_other _ _ _ _ _ _ Hne), (set_pm_other _ _ _ _ _ _ Hne).
      exact (I23 t0 ns0 b0 q0 Hob Hwp Hq0).
  - (* Inv22 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (Hnotpa a0 p0 pa0 Hmap Hne) as Hd.
      rewrite Eps. rewrite (set_ps_other _ _ _ _ _ _ Hd).
      exact (I24 a0 p0 pa0 Hmap).
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob. exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob Hlt.
    rewrite Eob in Hob. rewrite Ewp in Hlt. rewrite Eps.
    destruct (Hdiff b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I27 t0 ns0 b0 q0 Hob Hlt).
  - (* Inv26 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap. rewrite Eat, Ean.
    destruct (Hdiff a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. discriminate.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap. exact (I28 a0 p0 pa0 Hmap).
Qed.

(* ── the programming half of a write ──────────────────────────────── *)

(* [pa] is the fresh page just handed out by [alloc_page]: it sits at the top
   of the open block of the pair (t, ns), one below that pair's frontier, and
   is still erased.  Two clauses hold of the allocated state only in a
   restricted form, because the frontier has already moved past [pa] while
   [pa] is not yet programmed (Inv25), and because the old page of the logical
   address being rewritten has already been staled while the map still points
   at it (Inv22). *)
Lemma program_ok :
  forall (s2 : FTLState) (a : Addr) (p : Page) (d : Data)
         (t : TenantId) (ns : NamespaceId) (pa : PhysAddr),
    WF0 s2 -> WF1 s2 -> Inv0 s2 -> Inv1 s2 -> Inv2 s2 -> Inv3 s2 -> Inv4 s2 ->
    Inv5 s2 -> Inv6 s2 -> Inv7 s2 -> Inv8 s2 -> Inv9 s2 -> Inv10 s2 ->
    Inv11 s2 -> Inv12 s2 -> Inv13 s2 -> Inv14 s2 -> Inv15 s2 -> Inv16 s2 ->
    Inv17 s2 -> Inv18 s2 -> Inv19 s2 -> Inv20 s2 -> Inv21 s2 -> Inv23 s2 ->
    Inv24 s2 -> Inv26 s2 ->
    (forall a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 -> (a0 <> a \/ p0 <> p) ->
       exists dd, page_state s2 (pa_block pa0) (pa_page pa0) = PS_Valid dd) ->
    (forall t0 ns0 b0 q0, open_block s2 t0 ns0 = Some b0 ->
       q0 < write_ptr s2 t0 ns0 ->
       (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
       page_state s2 b0 q0 <> PS_Empty) ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s2 a = Some t ->
    addr_namespace s2 a = Some ns ->
    open_block s2 t ns = Some (pa_block pa) ->
    write_ptr s2 t ns = S (pa_page pa) ->
    pa_page pa < pages_per_block ->
    page_state s2 (pa_block pa) (pa_page pa) = PS_Empty ->
    (forall pa0, l2p_map s2 a p = Some pa0 ->
       page_state s2 (pa_block pa0) (pa_page pa0) = PS_Invalid) ->
    ftl_invariant (program_page s2 a p d pa).
Proof.
  intros s2 a p d t ns pa I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15
         I16 I17 I18 I19 I20 I21 I22 I23 I25 I26 I28 I24r I27r Ha Hp Hat Han
         Hob Hwp Hpp Hempty Hstale.
  destruct (I22 t ns (pa_block pa) Hob)
    as (Hbtb & Hnfl & Hfbf & Hbof & Hwple & Hbtd & Hbnd & Huniq).
  set (s' := program_page s2 a p d pa).
  assert (Els : l2p_map s' = set_l2p_map (l2p_map s2) a p (Some pa))
    by reflexivity.
  assert (Eps : page_state s' =
                set_page_state (page_state s2) (pa_block pa) (pa_page pa)
                               (PS_Valid d)) by reflexivity.
  assert (Epr : page_role s' =
                set_page_role (page_role s2) (pa_block pa) (pa_page pa)
                              (Some RData)) by reflexivity.
  assert (Epm : page_meta s' =
                set_page_meta (page_meta s2) (pa_block pa) (pa_page pa)
                  (mkPageMeta
                     (match addr_tenant s2 a with Some x => x | None => 0 end)
                     (match addr_namespace s2 a with Some x => x | None => 0 end)
                     (Some d) (Some (a, p)))) by reflexivity.
  assert (Eat : addr_tenant s' = addr_tenant s2) by reflexivity.
  assert (Ean : addr_namespace s' = addr_namespace s2) by reflexivity.
  assert (Ebt : block_tenant s' =
                set_block_tenant (block_tenant s2) (pa_block pa)
                                 (addr_tenant s2 a)) by reflexivity.
  assert (Ebn : block_namespace s' =
                set_block_namespace (block_namespace s2) (pa_block pa)
                                    (addr_namespace s2 a)) by reflexivity.
  assert (Ert : region_table s' = region_table s2) by reflexivity.
  assert (Efbl : free_block_list s' = free_block_list s2) by reflexivity.
  assert (Efb : free_block s' = free_block s2) by reflexivity.
  assert (Eob : open_block s' = open_block s2) by reflexivity.
  assert (Ewp : write_ptr s' = write_ptr s2) by reflexivity.
  assert (Ebo : block_open s' = block_open s2) by reflexivity.
  (* no other mapping points at the fresh page: it is still erased *)
  assert (HnotPa : forall a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 ->
                     (a0 <> a \/ p0 <> p) ->
                     (pa_block pa0 <> pa_block pa \/
                      pa_page pa0 <> pa_page pa)).
  { intros a0 p0 pa0 Hmap Hne.
    destruct (nat_pair_dec (pa_block pa0) (pa_block pa)
                           (pa_page pa0) (pa_page pa)) as [[E1 E2]|H'];
      [|exact H'].
    exfalso. destruct (I24r a0 p0 pa0 Hmap Hne) as [dd Hdd].
    rewrite E1, E2, Hempty in Hdd. discriminate. }
  (* the page the map still points at, if any, is stale, not live *)
  assert (Hnotold : forall a0 p0 b0 q0,
                      l2p_map s2 a0 p0 = Some (mkPhysAddr b0 q0) ->
                      page_state s2 b0 q0 <> PS_Invalid ->
                      (a0 <> a \/ p0 <> p)).
  { intros a0 p0 b0 q0 Hmap Hne.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|H']; [|exact H'].
    exfalso. subst a0 p0. pose proof (Hstale _ Hmap) as HI. cbn in HI.
    exact (Hne HI). }
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. exists a, p. rewrite Els, set_l2p_here, physaddr_eta.
      reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      destruct (I2 b0 q0 d0 Hv) as (a0 & p0 & Hmap).
      assert (Hne2 : a0 <> a \/ p0 <> p).
      { apply (Hnotold a0 p0 b0 q0 Hmap). rewrite Hv. discriminate. }
      exists a0, p0. rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne2). exact Hmap.
  - (* Inv1 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. split; [exact Hbtb|]. split; [exact Hpp|].
      split; [exact Ha|exact Hp].
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap. exact (I3 a0 p0 pa0 Hmap).
  - (* Inv2 *) intros a1 p1 a2 p2 pa0 H1 H2. rewrite Els in H1, H2.
    destruct (nat_pair_dec a1 a p1 p) as [[E1 E2]|Hne1];
      destruct (nat_pair_dec a2 a p2 p) as [[E3 E4]|Hne2].
    + subst. split; reflexivity.
    + exfalso. subst a1 p1. rewrite set_l2p_here in H1. injection H1 as H1.
      subst pa0. rewrite (set_l2p_other _ _ _ _ _ _ Hne2) in H2.
      destruct (HnotPa a2 p2 pa H2 Hne2) as [X|X]; exact (X eq_refl).
    + exfalso. subst a2 p2. rewrite set_l2p_here in H2. injection H2 as H2.
      subst pa0. rewrite (set_l2p_other _ _ _ _ _ _ Hne1) in H1.
      destruct (HnotPa a1 p1 pa H1 Hne1) as [X|X]; exact (X eq_refl).
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne1) in H1.
      rewrite (set_l2p_other _ _ _ _ _ _ Hne2) in H2.
      exact (I4 a1 p1 a2 p2 pa0 H1 H2).
  - (* Inv3 *) intros a0 p0 pa0 d0 Hmap Hv. rewrite Els in Hmap.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. rewrite Epm, set_pm_here. reflexivity.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (HnotPa a0 p0 pa0 Hmap Hne) as Hd.
      rewrite Eps in Hv. rewrite (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd).
      exact (I5 a0 p0 pa0 d0 Hmap Hv).
  - (* Inv4 *) intros a0 p0 b0 q0 d0 Hv Hlpa. rewrite Eps in Hv.
    rewrite Epm in Hlpa.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pm_here in Hlpa. cbn in Hlpa.
      injection Hlpa as F1 F2. subst a0 p0.
      rewrite Els, set_l2p_here, physaddr_eta. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
      pose proof (I6 a0 p0 b0 q0 d0 Hv Hlpa) as Hmap.
      assert (Hne2 : a0 <> a \/ p0 <> p).
      { apply (Hnotold a0 p0 b0 q0 Hmap). rewrite Hv. discriminate. }
      rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne2). exact Hmap.
  - (* Inv5 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap. rewrite Efbl.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. exact Hnfl.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap. exact (I7 a0 p0 pa0 Hmap).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa).
    { left. intro E. subst b0. exact (Hnfl Hin). }
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hd),
            (set_pm_other _ _ _ _ _ _ Hd).
    exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn.
    rewrite Els in Hmap. rewrite Eat in Ht. rewrite Ean in Hn.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. rewrite Epm, set_pm_here, Ht, Hn. cbn. split; reflexivity.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (HnotPa a0 p0 pa0 Hmap Hne) as Hd.
      rewrite Eps in Hv. rewrite (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd).
      exact (I9 a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite Epm, set_pm_here. cbn. exists d. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hne). exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) intros b0 Hb0.
    destruct (I12 b0 Hb0)
      as [Hin | [[t0 [ns0 Hob0]] | [(a0&p0&pa0&Hmap&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob0.
    + destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
      * subst a0 p0. right; right; right. exists (pa_page pa0).
        pose proof (Hstale _ Hmap) as HI.
        assert (Hd : pa_block pa0 <> pa_block pa \/
                     pa_page pa0 <> pa_page pa).
        { destruct (nat_pair_dec (pa_block pa0) (pa_block pa)
                                 (pa_page pa0) (pa_page pa)) as [[F1 F2]|H'];
            [|exact H'].
          exfalso. rewrite F1, F2, Hempty in HI. discriminate. }
        rewrite <- Hblk, Eps, (set_ps_other _ _ _ _ _ _ Hd). exact HI.
      * right; right; left. exists a0, p0, pa0. split; [|exact Hblk].
        rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne). exact Hmap.
    + right; right; right. exists q0. rewrite Eps.
      assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa).
      { destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa))
          as [[F1 F2]|H']; [|exact H'].
        exfalso. subst b0 q0. rewrite Hempty in Hq0. discriminate. }
      rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) intros b0 Hb0 [q0 Hrole]. rewrite Epr in Hrole.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
      destruct (I14 b0 Hb0 (ex_intro _ q0 Hrole))
        as [(a0&p0&pa0&Hmap&Hblk) | [q1 Hq1]].
      * destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne2].
        -- subst a0 p0. right. exists (pa_page pa0).
           pose proof (Hstale _ Hmap) as HI.
           assert (Hd : pa_block pa0 <> pa_block pa \/
                        pa_page pa0 <> pa_page pa).
           { destruct (nat_pair_dec (pa_block pa0) (pa_block pa)
                                    (pa_page pa0) (pa_page pa)) as [[F1 F2]|H'];
               [|exact H'].
             exfalso. rewrite F1, F2, Hempty in HI. discriminate. }
           rewrite <- Hblk, Eps, (set_ps_other _ _ _ _ _ _ Hd). exact HI.
        -- left. exists a0, p0, pa0. split; [|exact Hblk].
           rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne2). exact Hmap.
      * right. exists q1. rewrite Eps.
        assert (Hd : b0 <> pa_block pa \/ q1 <> pa_page pa).
        { destruct (nat_pair_dec b0 (pa_block pa) q1 (pa_page pa))
            as [[F1 F2]|H']; [|exact H'].
          exfalso. subst b0 q1. rewrite Hempty in Hq1. discriminate. }
        rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hq1.
  - (* Inv13 *) intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. apply set_pr_here.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I15 b0 q0 d0 Hv).
  - (* Inv14 *) intros b0 q0 Hrole. rewrite Epr in Hrole. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. exists d. apply set_ps_here.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I16 b0 q0 Hrole).
  - (* Inv15 *) intros b0 q0 Hrole. rewrite Epr in Hrole. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I17 b0 q0 Hrole).
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in He. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in He.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    assert (Hbne : b0 <> pa_block pa).
    { intro E. subst b0. rewrite Hfbf in Hf. discriminate. }
    rewrite (set_bt_other _ _ _ _ Hbne), (set_bn_other _ _ _ _ Hbne).
    exact (I19 b0 Hf).
  - (* Inv18 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    rewrite Ebt, Ebn, Eat, Ean.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. rewrite set_bt_here, set_bn_here. split; reflexivity.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      destruct (I20 a0 p0 pa0 Hmap) as [Gt Gn].
      destruct (Nat.eq_dec (pa_block pa0) (pa_block pa)) as [E|E].
      * (* a0 already has a page in the open block.  Inv26 gives it both
           labels, Inv18 identifies them with the block's, and the two Inv20
           disjuncts pin them to (t, ns): the re-stamp is a no-op. *)
        rewrite E, set_bt_here, set_bn_here.
        destruct (I28 a0 p0 pa0 Hmap) as [[t0 Ht0] [ns0 Hns0]].
        rewrite E in Gt, Gn. rewrite Ht0 in Gt. rewrite Hns0 in Gn.
        destruct Hbtd as [Hbtd|Hbtd]; rewrite Hbtd in Gt; [discriminate|].
        injection Gt as Gt. subst t0.
        destruct Hbnd as [Hbnd|Hbnd]; rewrite Hbnd in Gn; [discriminate|].
        injection Gn as Gn. subst ns0.
        split.
        -- rewrite Hat, Ht0. reflexivity.
        -- rewrite Han, Hns0. reflexivity.
      * rewrite (set_bt_other _ _ _ _ E), (set_bn_other _ _ _ _ E).
        split; [exact Gt|exact Gn].
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t0 ns0 b0 Hob0. rewrite Eob in Hob0.
    destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
    rewrite Efbl, Efb, Ebo, Ewp, Eob, Ebt, Ebn.
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    split; [exact G4|]. split; [exact G5|].
    destruct (Nat.eq_dec b0 (pa_block pa)) as [E|E].
    + subst b0. destruct (Huniq t0 ns0 Hob0) as [Et Ens]. subst t0 ns0.
      rewrite set_bt_here, set_bn_here.
      split; [right; exact Hat|]. split; [right; exact Han|]. exact G8.
    + rewrite (set_bt_other _ _ _ _ E), (set_bn_other _ _ _ _ E).
      split; [exact G6|]. split; [exact G7|]. exact G8.
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob in Hob0.
    rewrite Ewp in Hwp0.
    assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa).
    { destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa))
        as [[F1 F2]|H']; [|exact H'].
      exfalso. subst b0 q0. destruct (Huniq t0 ns0 Hob0) as [Et Ens].
      subst t0 ns0. rewrite Hwp in Hwp0. lia. }
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hd),
            (set_pm_other _ _ _ _ _ _ Hd).
    exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0).
  - (* Inv22 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. exists d. rewrite Eps. apply set_ps_here.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (HnotPa a0 p0 pa0 Hmap Hne) as Hd.
      destruct (I24r a0 p0 pa0 Hmap Hne) as [dd Hdd].
      exists dd. rewrite Eps, (set_ps_other _ _ _ _ _ _ Hd). exact Hdd.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob0 Hlt. rewrite Eob in Hob0.
    rewrite Ewp in Hlt. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne).
      exact (I27r t0 ns0 b0 q0 Hob0 Hlt Hne).
  - (* Inv26 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap. rewrite Eat, Ean.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. split; [exists t; exact Hat|exists ns; exact Han].
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      exact (I28 a0 p0 pa0 Hmap).
Qed.

(* ── the allocating half of a write ───────────────────────────────── *)

(* [s1] is the state after the old page has been staled, so Inv22 holds of it
   only away from (a,p).  [alloc_page] either advances the frontier inside the
   pair's open block or retires that block and opens the head of the free
   list; the second branch is where Inv25 earns its keep, since the retired
   block has to keep a claim on Inv10 without being open. *)
Lemma write_core :
  forall (s1 : FTLState) (a : Addr) (p : Page) (d : Data)
         (t : TenantId) (ns : NamespaceId) (pa : PhysAddr) (s2 : FTLState),
    WF0 s1 -> WF1 s1 -> Inv0 s1 -> Inv1 s1 -> Inv2 s1 -> Inv3 s1 -> Inv4 s1 ->
    Inv5 s1 -> Inv6 s1 -> Inv7 s1 -> Inv8 s1 -> Inv9 s1 -> Inv10 s1 ->
    Inv11 s1 -> Inv12 s1 -> Inv13 s1 -> Inv14 s1 -> Inv15 s1 -> Inv16 s1 ->
    Inv17 s1 -> Inv18 s1 -> Inv19 s1 -> Inv20 s1 -> Inv21 s1 -> Inv23 s1 ->
    Inv24 s1 -> Inv25 s1 -> Inv26 s1 ->
    (forall a0 p0 pa0, l2p_map s1 a0 p0 = Some pa0 -> (a0 <> a \/ p0 <> p) ->
       exists dd, page_state s1 (pa_block pa0) (pa_page pa0) = PS_Valid dd) ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s1 a = Some t ->
    addr_namespace s1 a = Some ns ->
    (forall pa0, l2p_map s1 a p = Some pa0 ->
       page_state s1 (pa_block pa0) (pa_page pa0) = PS_Invalid) ->
    alloc_page s1 t ns = Some (pa, s2) ->
    ftl_invariant (program_page s2 a p d pa).
Proof.
  intros s1 a p d t ns pa s2 I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14
         I15 I16 I17 I18 I19 I20 I21 I22 I23 I25 I26 I27 I28 I24r Ha Hp
         Hat Han Hstale Halloc.
  assert (Hppb : pages_per_block > 0) by exact I0.
  (* the [open_fresh] branch, shared by the two ways of reaching it *)
  assert (Hfresh :
            (forall ob, open_block s1 t ns = Some ob ->
                        pages_per_block <= write_ptr s1 t ns) ->
            open_fresh s1 t ns = Some (pa, s2) ->
            ftl_invariant (program_page s2 a p d pa)).
  { intros Hclosed Hof. clear Halloc.
    unfold open_fresh in Hof.
    destruct (free_block_list s1) as [|b [|c l]] eqn:Hfbl;
      try rewrite Hfbl in Hof; cbv beta iota in Hof; try discriminate.
    rewrite remove_block_once_head in Hof.
    injection Hof as E1 E2. subst pa. subst s2.
    assert (Hinb : In b (free_block_list s1)) by (rewrite Hfbl; left; reflexivity).
    assert (Hnd : NoDup (b :: c :: l)) by (rewrite <- Hfbl; exact I13).
    assert (Hbnotin : ~ In b (c :: l))
      by (inversion Hnd as [|x xs Hx Hrest]; exact Hx).
    assert (Hnd2 : NoDup (c :: l))
      by (inversion Hnd as [|x xs Hx Hrest]; exact Hrest).
    assert (Hfbb : free_block s1 b = true) by (apply (I26 b); exact Hinb).
    destruct (I19 b Hfbb) as [Hbtn Hbnn].
    assert (Hblt : b < total_blocks) by (apply I10; exact Hinb).
    pose proof (I8 b Hinb) as Hpages.
    assert (Efbl2 : free_block_list
                      (with_frontier s1 t ns (Some b) 1 (c :: l)
                         (set_free_block (free_block s1) b false)
                         (set_block_open (close_open s1 t ns) b true)) = c :: l)
      by reflexivity.
    assert (Eob : open_block
                    (with_frontier s1 t ns (Some b) 1 (c :: l)
                       (set_free_block (free_block s1) b false)
                       (set_block_open (close_open s1 t ns) b true)) =
                  set_open_block (open_block s1) t ns (Some b)) by reflexivity.
    assert (Ewp : write_ptr
                    (with_frontier s1 t ns (Some b) 1 (c :: l)
                       (set_free_block (free_block s1) b false)
                       (set_block_open (close_open s1 t ns) b true)) =
                  set_write_ptr (write_ptr s1) t ns 1) by reflexivity.
    assert (Efb : free_block
                    (with_frontier s1 t ns (Some b) 1 (c :: l)
                       (set_free_block (free_block s1) b false)
                       (set_block_open (close_open s1 t ns) b true)) =
                  set_free_block (free_block s1) b false) by reflexivity.
    assert (Ebo : block_open
                    (with_frontier s1 t ns (Some b) 1 (c :: l)
                       (set_free_block (free_block s1) b false)
                       (set_block_open (close_open s1 t ns) b true)) =
                  set_block_open (close_open s1 t ns) b true) by reflexivity.
    apply program_ok with (t := t) (ns := ns).
    - exact I0.
    - exact I1.
    - exact I2.
    - exact I3.
    - exact I4.
    - exact I5.
    - exact I6.
    - intros a0 p0 pa0 Hmap. rewrite Efbl2. intro Hin.
      apply (I7 a0 p0 pa0 Hmap). rewrite Hfbl. right. exact Hin.
    - intros b0 Hin q0 Hq0. rewrite Efbl2 in Hin.
      apply (I8 b0); [rewrite Hfbl; right; exact Hin | exact Hq0].
    - exact I9.
    - intros b0 Hin. rewrite Efbl2 in Hin. apply I10. rewrite Hfbl. right.
      exact Hin.
    - exact I11.
    - intros b0 Hb0.
      destruct (I12 b0 Hb0) as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
      + rewrite Hfbl in Hin. destruct Hin as [E|Hin].
        * subst b0. right; left. exists t, ns. rewrite Eob. apply set_ob_here.
        * left. rewrite Efbl2. exact Hin.
      + destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
        * subst t0 ns0.
          assert (Hwpt : pages_per_block <= write_ptr s1 t ns)
            by (apply (Hclosed b0); exact Hob0).
          assert (H0 : 0 < write_ptr s1 t ns) by lia.
          pose proof (I27 t ns b0 0 Hob0 H0) as Hne0.
          destruct (page_state s1 b0 0) as [| |d0] eqn:Eps0.
          -- exfalso. exact (Hne0 eq_refl).
          -- right; right; right. exists 0. exact Eps0.
          -- destruct (I2 b0 0 d0 Eps0) as (a0 & p0 & Hmap).
             right; right; left. exists a0, p0, (mkPhysAddr b0 0).
             split; [exact Hmap|reflexivity].
        * right; left. exists t0, ns0.
          rewrite Eob, (set_ob_other _ _ _ _ _ _ E). exact Hob0.
      + right; right; left. exact Hm.
      + right; right; right. exact Hq.
    - unfold Inv11. rewrite Efbl2. exact Hnd2.
    - exact I14.
    - exact I15.
    - exact I16.
    - exact I17.
    - exact I18.
    - intros b0 Hf. rewrite Efb in Hf.
      assert (Hbb : b0 <> b).
      { intro E. subst b0. rewrite set_fb_here in Hf. discriminate. }
      rewrite (set_fb_other _ _ _ _ Hbb) in Hf. exact (I19 b0 Hf).
    - exact I20.
    - exact I21.
    - intros t0 ns0 b0 Hob0. rewrite Eob in Hob0.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      + subst t0 ns0. rewrite set_ob_here in Hob0. injection Hob0 as Hob0.
        subst b0.
        split; [exact Hblt|].
        split; [rewrite Efbl2; exact Hbnotin|].
        split; [rewrite Efb; apply set_fb_here|].
        split; [rewrite Ebo; apply set_bo_here|].
        split; [rewrite Ewp, set_wp_here; lia|].
        split; [left; exact Hbtn|].
        split; [left; exact Hbnn|].
        intros t' ns' Hob'. rewrite Eob in Hob'.
        destruct (nat_pair_dec t' t ns' ns) as [[F1 F2]|E'];
          [split; assumption|].
        exfalso. rewrite (set_ob_other _ _ _ _ _ _ E') in Hob'.
        exact (proj1 (proj2 (I22 t' ns' b Hob')) Hinb).
      + rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
        assert (Hbb : b0 <> b). { intro Ez. subst b0. exact (G2 Hinb). }
        split; [exact G1|].
        split; [rewrite Efbl2; intro Hin; apply G2; rewrite Hfbl; right;
                exact Hin|].
        split; [rewrite Efb, (set_fb_other _ _ _ _ Hbb); exact G3|].
        split.
        { rewrite Ebo, (set_bo_other _ _ _ _ Hbb). unfold close_open.
          destruct (open_block s1 t ns) as [ob|] eqn:Hobt; [|exact G4].
          assert (Hobne : b0 <> ob).
          { intro Ez. subst ob. destruct (G8 t ns Hobt) as [Ea1 Ea2].
            destruct E as [X|X];
              [exact (X (eq_sym Ea1))|exact (X (eq_sym Ea2))]. }
          rewrite (set_bo_other _ _ _ _ Hobne). exact G4. }
        split; [rewrite Ewp, (set_wp_other _ _ _ _ _ _ E); exact G5|].
        split; [exact G6|].
        split; [exact G7|].
        intros t' ns' Hob'. rewrite Eob in Hob'.
        destruct (nat_pair_dec t' t ns' ns) as [[F1 F2]|E'].
        * exfalso. subst t' ns'. rewrite set_ob_here in Hob'.
          injection Hob' as Hob'. exact (Hbb (eq_sym Hob')).
        * rewrite (set_ob_other _ _ _ _ _ _ E') in Hob'. exact (G8 t' ns' Hob').
    - intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob in Hob0. rewrite Ewp in Hwp0.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      + subst t0 ns0. rewrite set_ob_here in Hob0. injection Hob0 as Hob0.
        subst b0. exact (Hpages q0 Hq0).
      + rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        rewrite (set_wp_other _ _ _ _ _ _ E) in Hwp0.
        exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0).
    - intros b0 Hbo. rewrite Ebo in Hbo.
      destruct (Nat.eq_dec b0 b) as [E|E].
      + subst b0. exists t, ns. rewrite Eob. apply set_ob_here.
      + rewrite (set_bo_other _ _ _ _ E) in Hbo. unfold close_open in Hbo.
        destruct (open_block s1 t ns) as [ob|] eqn:Hobt.
        * destruct (Nat.eq_dec b0 ob) as [E2|E2].
          -- subst b0. rewrite set_bo_here in Hbo. discriminate.
          -- rewrite (set_bo_other _ _ _ _ E2) in Hbo.
             destruct (I25 b0 Hbo) as [t' [ns' Hob']].
             exists t', ns'. rewrite Eob.
             assert (E3 : t' <> t \/ ns' <> ns).
             { destruct (nat_pair_dec t' t ns' ns) as [[F1 F2]|H']; [|exact H'].
               exfalso. subst t' ns'. rewrite Hobt in Hob'.
               injection Hob' as Hob'. exact (E2 (eq_sym Hob')). }
             rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'.
        * destruct (I25 b0 Hbo) as [t' [ns' Hob']].
          exists t', ns'. rewrite Eob.
          assert (E3 : t' <> t \/ ns' <> ns).
          { destruct (nat_pair_dec t' t ns' ns) as [[F1 F2]|H']; [|exact H'].
            exfalso. subst t' ns'. rewrite Hobt in Hob'. discriminate. }
          rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'.
    - intros b0. rewrite Efb, Efbl2. split.
      + intro Hf.
        assert (Hbb : b0 <> b).
        { intro Ez. subst b0. rewrite set_fb_here in Hf. discriminate. }
        rewrite (set_fb_other _ _ _ _ Hbb) in Hf.
        pose proof (proj1 (I26 b0) Hf) as Hin. rewrite Hfbl in Hin.
        destruct Hin as [Ez|Hin]; [exfalso; exact (Hbb (eq_sym Ez))|exact Hin].
      + intro Hin.
        assert (Hbb : b0 <> b).
        { intro Ez. subst b0. exact (Hbnotin Hin). }
        rewrite (set_fb_other _ _ _ _ Hbb). apply (proj2 (I26 b0)).
        rewrite Hfbl. right. exact Hin.
    - exact I28.
    - exact I24r.
    - intros t0 ns0 b0 q0 Hob0 Hlt0 Hne. rewrite Eob in Hob0. rewrite Ewp in Hlt0.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      + exfalso. subst t0 ns0. rewrite set_ob_here in Hob0.
        injection Hob0 as Hob0. subst b0. rewrite set_wp_here in Hlt0.
        assert (q0 = 0) by lia. subst q0. cbn in Hne.
        destruct Hne as [X|X]; exact (X eq_refl).
      + rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt0.
        exact (I27 t0 ns0 b0 q0 Hob0 Hlt0).
    - exact Ha.
    - exact Hp.
    - exact Hat.
    - exact Han.
    - cbn [pa_block]. rewrite Eob. apply set_ob_here.
    - cbn [pa_page]. rewrite Ewp, set_wp_here. reflexivity.
    - cbn [pa_page]. exact Hppb.
    - cbn [pa_block pa_page]. exact (proj1 (Hpages 0 Hppb)).
    - exact Hstale. }
  (* now the allocation itself *)
  unfold alloc_page in Halloc.
  destruct (open_block s1 t ns) as [b|] eqn:Hob1; try rewrite Hob1 in Halloc;
    cbv beta iota in Halloc.
  - destruct (Nat.ltb (write_ptr s1 t ns) pages_per_block) eqn:Hlt;
      try rewrite Hlt in Halloc; cbv beta iota in Halloc.
    + injection Halloc as E1 E2. subst pa. subst s2.
      assert (Hlt' : write_ptr s1 t ns < pages_per_block)
        by (apply Nat.ltb_lt; exact Hlt).
      assert (Eob : open_block
                      (with_frontier s1 t ns (Some b) (S (write_ptr s1 t ns))
                         (free_block_list s1) (free_block s1) (block_open s1)) =
                    set_open_block (open_block s1) t ns (Some b)) by reflexivity.
      assert (Ewp : write_ptr
                      (with_frontier s1 t ns (Some b) (S (write_ptr s1 t ns))
                         (free_block_list s1) (free_block s1) (block_open s1)) =
                    set_write_ptr (write_ptr s1) t ns (S (write_ptr s1 t ns)))
        by reflexivity.
      assert (Eob2 : forall x y,
                 open_block
                   (with_frontier s1 t ns (Some b) (S (write_ptr s1 t ns))
                      (free_block_list s1) (free_block s1) (block_open s1)) x y =
                 open_block s1 x y).
      { intros x y. rewrite Eob. destruct (nat_pair_dec x t y ns) as [[E1 E2]|E].
        - subst x y. rewrite set_ob_here. symmetry. exact Hob1.
        - apply set_ob_other. exact E. }
      apply program_ok with (t := t) (ns := ns).
      * exact I0.
      * exact I1.
      * exact I2.
      * exact I3.
      * exact I4.
      * exact I5.
      * exact I6.
      * exact I7.
      * exact I8.
      * exact I9.
      * exact I10.
      * exact I11.
      * intros b0 Hb0. destruct (I12 b0 Hb0) as [H|[[t0 [ns0 H]]|[H|H]]].
        -- left. exact H.
        -- right; left. exists t0, ns0. rewrite Eob2. exact H.
        -- right; right; left. exact H.
        -- right; right; right. exact H.
      * exact I13.
      * exact I14.
      * exact I15.
      * exact I16.
      * exact I17.
      * exact I18.
      * exact I19.
      * exact I20.
      * exact I21.
      * intros t0 ns0 b0 Hob0. rewrite Eob2 in Hob0.
        destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
        split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
        split; [exact G4|].
        split.
        { rewrite Ewp. destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
          - subst t0 ns0. rewrite set_wp_here. lia.
          - rewrite (set_wp_other _ _ _ _ _ _ E). exact G5. }
        split; [exact G6|]. split; [exact G7|].
        intros t' ns' Hob'. rewrite Eob2 in Hob'. exact (G8 t' ns' Hob').
      * intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob2 in Hob0.
        rewrite Ewp in Hwp0.
        destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
        -- subst t0 ns0. rewrite set_wp_here in Hwp0.
           apply (I23 t ns b0 q0 Hob0); [lia|exact Hq0].
        -- rewrite (set_wp_other _ _ _ _ _ _ E) in Hwp0.
           exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0).
      * intros b0 Hbo. destruct (I25 b0 Hbo) as [t0 [ns0 H]]. exists t0, ns0.
        rewrite Eob2. exact H.
      * exact I26.
      * exact I28.
      * exact I24r.
      * intros t0 ns0 b0 q0 Hob0 Hlt0 Hne. rewrite Eob2 in Hob0.
        rewrite Ewp in Hlt0. cbn in Hne.
        destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
        -- subst t0 ns0. rewrite set_wp_here in Hlt0. rewrite Hob1 in Hob0.
           injection Hob0 as Hob0. subst b0.
           assert (Hq : q0 < write_ptr s1 t ns).
           { destruct Hne as [X|X]; [exfalso; exact (X eq_refl)|lia]. }
           exact (I27 t ns b q0 Hob1 Hq).
        -- rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt0.
           exact (I27 t0 ns0 b0 q0 Hob0 Hlt0).
      * exact Ha.
      * exact Hp.
      * exact Hat.
      * exact Han.
      * cbn [pa_block]. rewrite Eob2. exact Hob1.
      * cbn [pa_page]. rewrite Ewp. apply set_wp_here.
      * cbn [pa_page]. exact Hlt'.
      * cbn [pa_block pa_page].
        exact (proj1 (I23 t ns b (write_ptr s1 t ns) Hob1 (Nat.le_refl _) Hlt')).
      * exact Hstale.
    + apply Hfresh; [|exact Halloc].
      intros ob _. apply Nat.ltb_ge in Hlt. lia.
  - apply Hfresh; [|exact Halloc].
    intros ob Hob'. try rewrite Hob1 in Hob'. discriminate.
Qed.

(* ── write preserves the invariant ─────────────────────────────────── *)

Theorem write_preserves_invariant :
  forall s a p d s', ftl_invariant s ->
    step s (COpWrite a p d) = Some s' -> ftl_invariant s'.
Proof.
  intros s a p d s' Hinv Hstep.
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  unfold step in Hstep.
  destruct (addr_tenant s a) as [t|] eqn:Eat;
    destruct (addr_namespace s a) as [ns|] eqn:Ean;
    destruct (Nat.ltb a addr_space) eqn:Ea;
    destruct (Nat.ltb p pages_per_block) eqn:Ep;
    try rewrite Ea in Hstep; try rewrite Ep in Hstep;
    try rewrite Eat in Hstep; try rewrite Ean in Hstep;
    cbv beta iota delta [andb] in Hstep; try discriminate.
  apply Nat.ltb_lt in Ea. apply Nat.ltb_lt in Ep.
  unfold exec_write in Hstep. cbv zeta in Hstep.
  rewrite Eat, Ean in Hstep. cbv beta iota in Hstep.
  destruct (l2p_map s a p) as [old|] eqn:Hold; try rewrite Hold in Hstep;
    cbv beta iota in Hstep.
  - (* the logical page had a previous physical home: stale it first *)
    destruct (alloc_page (invalidate_at s old) t ns) as [[pa s2]|] eqn:Halloc;
      try rewrite Halloc in Hstep; cbv beta iota in Hstep; [|discriminate].
    injection Hstep as Hstep. subst s'.
    destruct (I24 a p old Hold) as [dold Hlive].
    pose proof (I7 a p old Hold) as Hnf.
    assert (Eps : page_state (invalidate_at s old) =
                  set_page_state (page_state s) (pa_block old) (pa_page old)
                                 PS_Invalid) by reflexivity.
    assert (Epr : page_role (invalidate_at s old) =
                  set_page_role (page_role s) (pa_block old) (pa_page old) None)
      by reflexivity.
    assert (Epm : page_meta (invalidate_at s old) =
                  set_page_meta (page_meta s) (pa_block old) (pa_page old)
                                empty_page_meta) by reflexivity.
    apply (write_core (invalidate_at s old) a p d t ns pa s2).
    + exact I0.
    + intros b0 q0 _ _. eexists. reflexivity.
    + intros b0 q0 d0 Hv. rewrite Eps in Hv.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_ps_here in Hv. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv. exact (I2 b0 q0 d0 Hv).
    + exact I3.
    + exact I4.
    + intros a0 p0 pa0 d0 Hmap Hv. rewrite Eps in Hv. rewrite Epm.
      destruct (nat_pair_dec (pa_block pa0) (pa_block old)
                             (pa_page pa0) (pa_page old)) as [[E1 E2]|Hne].
      * exfalso. rewrite E1, E2, set_ps_here in Hv. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
        rewrite (set_pm_other _ _ _ _ _ _ Hne).
        exact (I5 a0 p0 pa0 d0 Hmap Hv).
    + intros a0 p0 b0 q0 d0 Hv Hlpa. rewrite Eps in Hv. rewrite Epm in Hlpa.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_ps_here in Hv. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
        rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
        exact (I6 a0 p0 b0 q0 d0 Hv Hlpa).
    + exact I7.
    + intros b0 Hin q0 Hq0.
      assert (Hne : b0 <> pa_block old \/ q0 <> pa_page old)
        by (left; intro E; subst b0; exact (Hnf Hin)).
      rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hne),
              (set_pm_other _ _ _ _ _ _ Hne).
      exact (I8 b0 Hin q0 Hq0).
    + intros a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn. rewrite Eps in Hv. rewrite Epm.
      destruct (nat_pair_dec (pa_block pa0) (pa_block old)
                             (pa_page pa0) (pa_page old)) as [[E1 E2]|Hne].
      * exfalso. rewrite E1, E2, set_ps_here in Hv. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
        rewrite (set_pm_other _ _ _ _ _ _ Hne).
        exact (I9 a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn).
    + exact I10.
    + intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epm.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_ps_here in Hv. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
        rewrite (set_pm_other _ _ _ _ _ _ Hne). exact (I11 b0 q0 d0 Hv).
    + intros b0 Hb0. destruct (I12 b0 Hb0) as [H|[H|[H|[q0 Hq0]]]].
      * left. exact H.
      * right; left. exact H.
      * right; right; left. exact H.
      * right; right; right. exists q0. rewrite Eps.
        destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
          as [[E1 E2]|Hne].
        -- subst b0 q0. apply set_ps_here.
        -- rewrite (set_ps_other _ _ _ _ _ _ Hne). exact Hq0.
    + exact I13.
    + intros b0 Hb0 [q0 Hrole]. rewrite Epr in Hrole.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
      * rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
        destruct (I14 b0 Hb0 (ex_intro _ q0 Hrole)) as [H|[q1 Hq1]].
        -- left. exact H.
        -- right. exists q1. rewrite Eps.
           destruct (nat_pair_dec b0 (pa_block old) q1 (pa_page old))
             as [[E3 E4]|Hne3].
           ++ subst b0 q1. apply set_ps_here.
           ++ rewrite (set_ps_other _ _ _ _ _ _ Hne3). exact Hq1.
    + intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_ps_here in Hv. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
        rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I15 b0 q0 d0 Hv).
    + intros b0 q0 Hrole. rewrite Epr in Hrole. rewrite Eps.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
      * rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
        rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I16 b0 q0 Hrole).
    + intros b0 q0 Hrole. rewrite Epr in Hrole. rewrite Eps.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_pr_here in Hrole. discriminate.
      * rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hrole.
        rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I17 b0 q0 Hrole).
    + intros b0 q0 He. rewrite Eps in He. rewrite Epr.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_ps_here in He. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne) in He.
        rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I18 b0 q0 He).
    + exact I19.
    + exact I20.
    + exact I21.
    + exact I22.
    + intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0.
      assert (Hne : b0 <> pa_block old \/ q0 <> pa_page old).
      { destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
          as [[E1 E2]|H']; [|exact H'].
        exfalso. subst b0 q0.
        pose proof (live_below_frontier s t0 ns0 (pa_block old) (pa_page old)
                      dold I23 Hob0 Hq0 Hlive) as Hltf.
        assert (Hwp1 : write_ptr s t0 ns0 <= pa_page old) by exact Hwp0.
        lia. }
      rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hne),
              (set_pm_other _ _ _ _ _ _ Hne).
      exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0).
    + exact I25.
    + exact I26.
    + intros t0 ns0 b0 q0 Hob0 Hlt0. rewrite Eps.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. rewrite set_ps_here. discriminate.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne).
        exact (I27 t0 ns0 b0 q0 Hob0 Hlt0).
    + exact I28.
    + intros a0 p0 pa0 Hmap Hne.
      destruct (I24 a0 p0 pa0 Hmap) as [dd Hdd]. exists dd. rewrite Eps.
      assert (Hd : pa_block pa0 <> pa_block old \/ pa_page pa0 <> pa_page old).
      { destruct (nat_pair_dec (pa_block pa0) (pa_block old)
                               (pa_page pa0) (pa_page old)) as [[E1 E2]|H'];
          [|exact H'].
        exfalso.
        assert (Hpa : pa0 = old).
        { rewrite <- (physaddr_eta pa0), <- (physaddr_eta old), E1, E2.
          reflexivity. }
        subst pa0. destruct (I4 a0 p0 a p old Hmap Hold) as [F1 F2].
        destruct Hne as [X|X]; auto. }
      rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hdd.
    + exact Ea.
    + exact Ep.
    + exact Eat.
    + exact Ean.
    + intros pa0 Hmap.
      assert (Hmm : l2p_map s a p = Some pa0) by exact Hmap.
      rewrite Hold in Hmm. injection Hmm as Hmm. subst pa0.
      rewrite Eps. apply set_ps_here.
    + exact Halloc.
  - (* the logical page was unmapped: nothing to stale *)
    destruct (alloc_page s t ns) as [[pa s2]|] eqn:Halloc;
      try rewrite Halloc in Hstep; cbv beta iota in Hstep; [|discriminate].
    injection Hstep as Hstep. subst s'.
    apply (write_core s a p d t ns pa s2).
    + exact I0.
    + exact I1.
    + exact I2.
    + exact I3.
    + exact I4.
    + exact I5.
    + exact I6.
    + exact I7.
    + exact I8.
    + exact I9.
    + exact I10.
    + exact I11.
    + exact I12.
    + exact I13.
    + exact I14.
    + exact I15.
    + exact I16.
    + exact I17.
    + exact I18.
    + exact I19.
    + exact I20.
    + exact I21.
    + exact I22.
    + exact I23.
    + exact I25.
    + exact I26.
    + exact I27.
    + exact I28.
    + intros a0 p0 pa0 Hmap _. exact (I24 a0 p0 pa0 Hmap).
    + exact Ea.
    + exact Ep.
    + exact Eat.
    + exact Ean.
    + intros pa0 Hmap. rewrite Hold in Hmap. discriminate.
    + exact Halloc.
Qed.

End WritePreservation.

(* Outside the section, discharging the geometry hypothesis with the
   geometry's own positivity lemma. *)

Corollary write_preserves_invariant_closed :
  forall s a p d s', ftl_invariant s ->
    step s (COpWrite a p d) = Some s' -> ftl_invariant s'.
Proof. exact (@write_preserves_invariant pages_per_block_pos). Qed.

Corollary invalidate_preserves_invariant_closed :
  forall s a p s', ftl_invariant s ->
    step s (COpInvalidate a p) = Some s' -> ftl_invariant s'.
Proof. exact (@invalidate_preserves_invariant pages_per_block_pos). Qed.
