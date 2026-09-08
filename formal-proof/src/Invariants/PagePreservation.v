(* PagePreservation.v: every operation preserves the 27-clause invariant
   under page-granular translation.

   A page-granular write touches exactly two physical pages, so the cases are
   independent and live together here. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.

Import ListNotations.

Section PagePreservation.

Context {pages_per_block_gt0 : pages_per_block > 0}.

Notation INV := (@ftl_invariant pages_per_block_gt0).

(* ── pointwise update lemmas ──────────────────────────────────────── *)

Lemma set_l2p_here : forall m a p opa,
  set_l2p_map m a p opa a p = opa.
Proof. intros. unfold set_l2p_map. now rewrite !Nat.eqb_refl. Qed.

Lemma set_l2p_other : forall m a p opa x y,
  (x <> a \/ y <> p) -> set_l2p_map m a p opa x y = m x y.
Proof.
  intros m a p opa x y H. unfold set_l2p_map.
  destruct (Nat.eqb x a) eqn:Ex; destruct (Nat.eqb y p) eqn:Ey; simpl; auto.
  apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey. destruct H; congruence.
Qed.

Lemma set_ps_here : forall f b p st, set_page_state f b p st b p = st.
Proof. intros. unfold set_page_state. now rewrite !Nat.eqb_refl. Qed.

Lemma set_ps_other : forall f b p st x y,
  (x <> b \/ y <> p) -> set_page_state f b p st x y = f x y.
Proof.
  intros f b p st x y H. unfold set_page_state.
  destruct (Nat.eqb x b) eqn:Ex; destruct (Nat.eqb y p) eqn:Ey; simpl; auto.
  apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey. destruct H; congruence.
Qed.

Lemma set_pr_here : forall f b p r, set_page_role f b p r b p = r.
Proof. intros. unfold set_page_role. now rewrite !Nat.eqb_refl. Qed.

Lemma set_pr_other : forall f b p r x y,
  (x <> b \/ y <> p) -> set_page_role f b p r x y = f x y.
Proof.
  intros f b p r x y H. unfold set_page_role.
  destruct (Nat.eqb x b) eqn:Ex; destruct (Nat.eqb y p) eqn:Ey; simpl; auto.
  apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey. destruct H; congruence.
Qed.

Lemma set_pm_here : forall f b p m, set_page_meta f b p m b p = m.
Proof. intros. unfold set_page_meta. now rewrite !Nat.eqb_refl. Qed.

Lemma set_pm_other : forall f b p m x y,
  (x <> b \/ y <> p) -> set_page_meta f b p m x y = f x y.
Proof.
  intros f b p m x y H. unfold set_page_meta.
  destruct (Nat.eqb x b) eqn:Ex; destruct (Nat.eqb y p) eqn:Ey; simpl; auto.
  apply Nat.eqb_eq in Ex; apply Nat.eqb_eq in Ey. destruct H; congruence.
Qed.

Lemma physaddr_eta : forall pa, mkPhysAddr (pa_block pa) (pa_page pa) = pa.
Proof. intros [b p]. reflexivity. Qed.

(* A live page never sits at or beyond the write frontier (Inv21). *)
Lemma live_below_frontier :
  forall s t ns b q d,
    Inv21 s ->
    open_block s t ns = Some b -> q < pages_per_block ->
    page_state s b q = PS_Valid d -> q < write_ptr s t ns.
Proof.
  intros s t ns b q d H23 Hob Hq Hps.
  destruct (Nat.ltb q (write_ptr s t ns)) eqn:E.
  - apply Nat.ltb_lt in E. exact E.
  - apply Nat.ltb_ge in E.
    destruct (H23 t ns b q Hob E Hq) as [He _]. rewrite He in Hps. discriminate.
Qed.

(* ── COpRead: the state is unchanged ──────────────────────────────── *)

Lemma read_preserves_invariant :
  forall s a p s', ftl_invariant s ->
    step s (COpRead a p) = Some s' -> ftl_invariant s'.
Proof. intros s a p s' Hinv Hstep. cbn in Hstep. now inversion Hstep; subst. Qed.

(* ── COpSetTag: only the tag field of one live page changes ───────── *)

Lemma set_tag_preserves_invariant :
  forall s a p tag s', ftl_invariant s ->
    step s (COpSetTag a p tag) = Some s' -> ftl_invariant s'.
Proof.
  intros s a p tag s' Hinv Hstep. cbn in Hstep. inversion Hstep; subst s'; clear Hstep.
  unfold exec_set_tag.
  destruct (l2p_map s a p) as [pa|] eqn:Hm; [|exact Hinv].
  destruct (page_state s (pa_block pa) (pa_page pa)) as [| |d] eqn:Hps;
    try exact Hinv.
  (* the tagged page is live and mapped *)
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15&I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  set (pb := pa_block pa). set (pp := pa_page pa).
  assert (Hmeta : forall x y, page_meta (set_page_tag_at s pa tag) x y =
                  if andb (Nat.eqb x pb) (Nat.eqb y pp)
                  then mkPageMeta (page_owner_tenant (page_meta s pb pp))
                                  (page_owner_namespace (page_meta s pb pp))
                                  (Some tag) (page_lpa (page_meta s pb pp))
                  else page_meta s x y)
    by (intros; reflexivity).
  (* the page is not in a free block (Inv5) and is below the frontier (Inv21) *)
  assert (Hnf : ~ In pb (free_block_list s)) by (exact (I7 a p pa Hm)).
  apply make_ftl_invariant.
  - exact I0.
  - exact I1.
  - exact I2.
  - exact I3.
  - exact I4.
  - intros a0 p0 pa0 d0 Hm0 Hps0. rewrite Hmeta.
    destruct (andb (Nat.eqb (pa_block pa0) pb) (Nat.eqb (pa_page pa0) pp)) eqn:E.
    + cbn. apply andb_prop in E as [E1 E2].
      apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2.
      assert (Hpa : pa0 = pa) by
        (unfold pb, pp in E1, E2; destruct pa0; destruct pa; cbn in *; congruence).
      subst pa0. exact (I5 a0 p0 pa d0 Hm0 Hps0).
    + exact (I5 a0 p0 pa0 d0 Hm0 Hps0).
  - intros a0 p0 b0 q0 d0 Hps0 Hlpa. rewrite Hmeta in Hlpa.
    destruct (andb (Nat.eqb b0 pb) (Nat.eqb q0 pp)) eqn:E.
    + cbn in Hlpa. apply andb_prop in E as [E1 E2].
      apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2. subst b0 q0.
      exact (I6 a0 p0 pb pp d0 Hps0 Hlpa).
    + exact (I6 a0 p0 b0 q0 d0 Hps0 Hlpa).
  - exact I7.
  - intros b0 Hin q0 Hq0. destruct (I8 b0 Hin q0 Hq0) as [He Hm0].
    split; [exact He|]. rewrite Hmeta.
    destruct (andb (Nat.eqb b0 pb) (Nat.eqb q0 pp)) eqn:E; [|exact Hm0].
    exfalso. apply andb_prop in E as [E1 _]. apply Nat.eqb_eq in E1. subst b0.
    exact (Hnf Hin).
  - intros a0 p0 pa0 d0 t ns Hm0 Hps0 Ht Hns. rewrite !Hmeta.
    destruct (andb (Nat.eqb (pa_block pa0) pb) (Nat.eqb (pa_page pa0) pp)) eqn:E.
    + cbn. apply andb_prop in E as [E1 E2].
      apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2.
      assert (Hpa : pa0 = pa) by
        (unfold pb, pp in E1, E2; destruct pa0; destruct pa; cbn in *; congruence).
      subst pa0. exact (I9 a0 p0 pa d0 t ns Hm0 Hps0 Ht Hns).
    + exact (I9 a0 p0 pa0 d0 t ns Hm0 Hps0 Ht Hns).
  - exact I10.
  - intros b0 q0 d0 Hps0. rewrite Hmeta.
    destruct (andb (Nat.eqb b0 pb) (Nat.eqb q0 pp)) eqn:E.
    + cbn. now exists tag.
    + exact (I11 b0 q0 d0 Hps0).
  - exact I12.
  - exact I13.
  - exact I14.
  - exact I15.
  - exact I16.
  - exact I17.
  - exact I18.
  - exact I19.
  - exact I20.
  - exact I21.
  - exact I22.
  - intros t0 ns0 b0 q0 Hob Hwp Hq0. destruct (I23 t0 ns0 b0 q0 Hob Hwp Hq0) as [He Hm0].
    split; [exact He|]. rewrite Hmeta.
    destruct (andb (Nat.eqb b0 pb) (Nat.eqb q0 pp)) eqn:E; [|exact Hm0].
    exfalso. apply andb_prop in E as [E1 E2].
    apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E2. subst b0 q0.
    pose proof (live_below_frontier s t0 ns0 pb pp d I23 Hob Hq0 Hps) as Hlt.
    replace (write_ptr (set_page_tag_at s pa tag)) with (write_ptr s) in Hwp
      by reflexivity.
    lia.
  - exact I24.
  - exact I25.
  - exact I26.
  - exact I27.
  - exact I28.
Qed.

End PagePreservation.
