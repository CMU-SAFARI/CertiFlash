(* GCPreservation.v

   Garbage collection and wear levelling preserve the 27-clause invariant,
   under the page-granular model whose allocation frontier is indexed by the
   owning (tenant, namespace) pair.

   Structure:
     PART 0  pointwise update lemmas for the frontier and block fields
     PART 1  the relativised bundle [INVX] carried through the reclaim fold
     PART 2  [program_relx]  -- programming the relocation destination
     PART 3  [relocate_core] -- allocating it, both branches
     PART 4  the fold and the erase
     PART 5  preservation once, generalized over the victim chooser, and the
             two assigned theorems as instances of it

   No admitted lemmas, no [admit], no axiom, parameter, variable or hypothesis is
   introduced; Model.v, Operational.v, Invariants.v and PagePreservation.v are
   untouched. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 0 -- pointwise update lemmas.
   ══════════════════════════════════════════════════════════════════════ *)

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
  intros f b v x H. unfold set_block_open. apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma set_fb_here : forall f b v, set_free_block f b v b = v.
Proof. intros. unfold set_free_block. now rewrite Nat.eqb_refl. Qed.

Lemma set_fb_other : forall f b v x, x <> b -> set_free_block f b v x = f x.
Proof.
  intros f b v x H. unfold set_free_block. apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma set_bt_here : forall f b v, set_block_tenant f b v b = v.
Proof. intros. unfold set_block_tenant. now rewrite Nat.eqb_refl. Qed.

Lemma set_bt_other : forall f b v x, x <> b -> set_block_tenant f b v x = f x.
Proof.
  intros f b v x H. unfold set_block_tenant. apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma set_bn_here : forall f b v, set_block_namespace f b v b = v.
Proof. intros. unfold set_block_namespace. now rewrite Nat.eqb_refl. Qed.

Lemma set_bn_other : forall f b v x, x <> b -> set_block_namespace f b v x = f x.
Proof.
  intros f b v x H. unfold set_block_namespace. apply Nat.eqb_neq in H.
  now rewrite H.
Qed.

Lemma nat_pair_dec :
  forall x y z w : nat, (x = y /\ z = w) \/ (x <> y \/ z <> w).
Proof.
  intros x y z w. destruct (Nat.eq_dec x y); destruct (Nat.eq_dec z w); auto.
Qed.

(* ── field equations for [with_frontier] ──────────────────────────── *)

Lemma wf_l2p : forall s t ns ob wp fbl fb bo,
  l2p_map (with_frontier s t ns ob wp fbl fb bo) = l2p_map s.
Proof. reflexivity. Qed.

Lemma wf_ps : forall s t ns ob wp fbl fb bo,
  page_state (with_frontier s t ns ob wp fbl fb bo) = page_state s.
Proof. reflexivity. Qed.

Lemma wf_pr : forall s t ns ob wp fbl fb bo,
  page_role (with_frontier s t ns ob wp fbl fb bo) = page_role s.
Proof. reflexivity. Qed.

Lemma wf_at : forall s t ns ob wp fbl fb bo,
  addr_tenant (with_frontier s t ns ob wp fbl fb bo) = addr_tenant s.
Proof. reflexivity. Qed.

Lemma wf_an : forall s t ns ob wp fbl fb bo,
  addr_namespace (with_frontier s t ns ob wp fbl fb bo) = addr_namespace s.
Proof. reflexivity. Qed.

Lemma wf_bt : forall s t ns ob wp fbl fb bo,
  block_tenant (with_frontier s t ns ob wp fbl fb bo) = block_tenant s.
Proof. reflexivity. Qed.

Lemma wf_bn : forall s t ns ob wp fbl fb bo,
  block_namespace (with_frontier s t ns ob wp fbl fb bo) = block_namespace s.
Proof. reflexivity. Qed.

Lemma wf_pm : forall s t ns ob wp fbl fb bo,
  page_meta (with_frontier s t ns ob wp fbl fb bo) = page_meta s.
Proof. reflexivity. Qed.

Lemma wf_rt : forall s t ns ob wp fbl fb bo,
  region_table (with_frontier s t ns ob wp fbl fb bo) = region_table s.
Proof. reflexivity. Qed.

Lemma wf_fbl : forall s t ns ob wp fbl fb bo,
  free_block_list (with_frontier s t ns ob wp fbl fb bo) = fbl.
Proof. reflexivity. Qed.

Lemma wf_fb : forall s t ns ob wp fbl fb bo,
  free_block (with_frontier s t ns ob wp fbl fb bo) = fb.
Proof. reflexivity. Qed.

Lemma wf_ob : forall s t ns ob wp fbl fb bo,
  open_block (with_frontier s t ns ob wp fbl fb bo) =
  set_open_block (open_block s) t ns ob.
Proof. reflexivity. Qed.

Lemma wf_wp : forall s t ns ob wp fbl fb bo,
  write_ptr (with_frontier s t ns ob wp fbl fb bo) =
  set_write_ptr (write_ptr s) t ns wp.
Proof. reflexivity. Qed.

Lemma wf_bo : forall s t ns ob wp fbl fb bo,
  block_open (with_frontier s t ns ob wp fbl fb bo) = bo.
Proof. reflexivity. Qed.

(* ── field equations for [erase_block] ────────────────────────────── *)

Lemma eb_l2p : forall s b, l2p_map (erase_block s b) = l2p_map s.
Proof. reflexivity. Qed.

Lemma eb_at : forall s b, addr_tenant (erase_block s b) = addr_tenant s.
Proof. reflexivity. Qed.

Lemma eb_an : forall s b, addr_namespace (erase_block s b) = addr_namespace s.
Proof. reflexivity. Qed.

Lemma eb_rt : forall s b, region_table (erase_block s b) = region_table s.
Proof. reflexivity. Qed.

Lemma eb_ob : forall s b, open_block (erase_block s b) = open_block s.
Proof. reflexivity. Qed.

Lemma eb_wp : forall s b, write_ptr (erase_block s b) = write_ptr s.
Proof. reflexivity. Qed.

Lemma eb_fbl : forall s b, free_block_list (erase_block s b) = b :: free_block_list s.
Proof. reflexivity. Qed.

Lemma eb_fb : forall s b,
  free_block (erase_block s b) = set_free_block (free_block s) b true.
Proof. reflexivity. Qed.

Lemma eb_bo : forall s b,
  block_open (erase_block s b) = set_block_open (block_open s) b false.
Proof. reflexivity. Qed.

Lemma eb_bt : forall s b,
  block_tenant (erase_block s b) = set_block_tenant (block_tenant s) b None.
Proof. reflexivity. Qed.

Lemma eb_bn : forall s b,
  block_namespace (erase_block s b) = set_block_namespace (block_namespace s) b None.
Proof. reflexivity. Qed.

Lemma eb_ps_self : forall s b p, page_state (erase_block s b) b p = PS_Empty.
Proof.
  intros s b p.
  change (page_state (erase_block s b) b p)
    with (if Nat.eqb b b then PS_Empty else page_state s b p).
  now rewrite Nat.eqb_refl.
Qed.

Lemma eb_ps_other : forall s b blk p,
  blk <> b -> page_state (erase_block s b) blk p = page_state s blk p.
Proof.
  intros s b blk p H.
  change (page_state (erase_block s b) blk p)
    with (if Nat.eqb blk b then PS_Empty else page_state s blk p).
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma eb_pr_self : forall s b p, page_role (erase_block s b) b p = None.
Proof.
  intros s b p.
  change (page_role (erase_block s b) b p)
    with (if Nat.eqb b b then (None : option Role) else page_role s b p).
  now rewrite Nat.eqb_refl.
Qed.

Lemma eb_pr_other : forall s b blk p,
  blk <> b -> page_role (erase_block s b) blk p = page_role s blk p.
Proof.
  intros s b blk p H.
  change (page_role (erase_block s b) blk p)
    with (if Nat.eqb blk b then (None : option Role) else page_role s blk p).
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma eb_pm_self : forall s b p, page_meta (erase_block s b) b p = empty_page_meta.
Proof.
  intros s b p.
  change (page_meta (erase_block s b) b p)
    with (if Nat.eqb b b then empty_page_meta else page_meta s b p).
  now rewrite Nat.eqb_refl.
Qed.

Lemma eb_pm_other : forall s b blk p,
  blk <> b -> page_meta (erase_block s b) blk p = page_meta s blk p.
Proof.
  intros s b blk p H.
  change (page_meta (erase_block s b) blk p)
    with (if Nat.eqb blk b then empty_page_meta else page_meta s blk p).
  apply Nat.eqb_neq in H. now rewrite H.
Qed.

(* ── Inv12 is derivable, so the fold need not carry it ────────────── *)

Lemma Inv12_from_Inv13_Inv15 :
  forall s, Inv13 s -> Inv15 s -> Inv12 s.
Proof.
  intros s I15 I17 b _ [p Hrole].
  right. exists p.
  destruct (page_state s b p) as [| |d] eqn:Est.
  - exfalso. exact (I17 b p Hrole Est).
  - reflexivity.
  - exfalso. pose proof (I15 b p d Est) as Hd.
    rewrite Hrole in Hd. discriminate.
Qed.

(* ── allocation carries the data fields across unchanged ──────────── *)

Lemma alloc_page_fields :
  forall s t ns pa s1,
    alloc_page s t ns = Some (pa, s1) ->
    l2p_map s1 = l2p_map s /\
    page_state s1 = page_state s /\
    page_role s1 = page_role s /\
    addr_tenant s1 = addr_tenant s /\
    addr_namespace s1 = addr_namespace s /\
    block_tenant s1 = block_tenant s /\
    block_namespace s1 = block_namespace s /\
    page_meta s1 = page_meta s /\
    region_table s1 = region_table s.
Proof.
  intros s t ns pa s1 H. unfold alloc_page in H.
  destruct (open_block s t ns) as [b0|] eqn:Hob.
  - destruct (Nat.ltb (write_ptr s t ns) pages_per_block) eqn:Hlt.
    + injection H as _ H. subst s1. repeat split; reflexivity.
    + unfold open_fresh in H.
      destruct (free_block_list s) as [|b1 [|b2 rest]] eqn:Hfl; try discriminate.
      injection H as _ H. subst s1. repeat split; reflexivity.
  - unfold open_fresh in H.
    destruct (free_block_list s) as [|b1 [|b2 rest]] eqn:Hfl; try discriminate.
    injection H as _ H. subst s1. repeat split; reflexivity.
Qed.

(* ── the destination of an allocation is never the victim ─────────── *)

Lemma alloc_dest_not_victim :
  forall s t ns b pa s1,
    Inv20 s -> Inv24 s ->
    free_block s b = false ->
    block_open s b = false ->
    alloc_page s t ns = Some (pa, s1) ->
    pa_block pa <> b.
Proof.
  intros s t ns b pa s1 I22 I26 Hfb Hbo H.
  unfold alloc_page in H.
  destruct (open_block s t ns) as [b0|] eqn:Hob.
  - destruct (Nat.ltb (write_ptr s t ns) pages_per_block) eqn:Hlt.
    + injection H as H _. subst pa. cbn. intro Heq. subst b0.
      destruct (I22 t ns b Hob) as (_ & _ & _ & Hopen & _).
      rewrite Hopen in Hbo. discriminate.
    + unfold open_fresh in H.
      destruct (free_block_list s) as [|b1 [|b2 rest]] eqn:Hfl; try discriminate.
      injection H as H _. subst pa. cbn. intro Heq. subst b1.
      assert (Hin : In b (free_block_list s)) by (rewrite Hfl; left; reflexivity).
      pose proof (proj2 (I26 b) Hin) as Hbit.
      rewrite Hbit in Hfb. discriminate.
  - unfold open_fresh in H.
    destruct (free_block_list s) as [|b1 [|b2 rest]] eqn:Hfl; try discriminate.
    injection H as H _. subst pa. cbn. intro Heq. subst b1.
    assert (Hin : In b (free_block_list s)) by (rewrite Hfl; left; reflexivity).
    pose proof (proj2 (I26 b) Hin) as Hbit.
    rewrite Hbit in Hfb. discriminate.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the relativised bundle.

   [reclaim s b] relocates every live page of the victim [b] and then erases
   it.  The intermediate states of that fold do not satisfy the invariant:
   [program_page] stamps the destination but never touches the source, so a
   page already relocated stays [PS_Valid] in the victim while nothing maps to
   it any more.  Inv0, Inv4 and Inv10 are therefore relativised at the victim
   and the not-yet-processed page list; everything else holds outright.

   The progress conjunct [xprog] is positive: every mapping into the victim
   lands on a page still to be processed.  At [ps = []] it says nothing maps
   into the victim at all, which is what [erase_block] consumes.
   ══════════════════════════════════════════════════════════════════════ *)

Record INVX (vb : Block) (ps : list Page) (s : FTLState) : Prop := mkINVX {
  xI0  : WF0 s;
  xI1  : WF1 s;
  xI3  : Inv1 s;
  xI4  : Inv2 s;
  xI5  : Inv3 s;
  xI7  : Inv5 s;
  xI8  : Inv6 s;
  xI9  : Inv7 s;
  xI10 : Inv8 s;
  xI11 : Inv9 s;
  xI13 : Inv11 s;
  xI15 : Inv13 s;
  xI16 : Inv14 s;
  xI17 : Inv15 s;
  xI18 : Inv16 s;
  xI19 : Inv17 s;
  xI20 : Inv18 s;
  xI21 : Inv19 s;
  xI22 : Inv20 s;
  xI23 : Inv21 s;
  xI24 : Inv22 s;
  xI25 : Inv23 s;
  xI26 : Inv24 s;
  xI27 : Inv25 s;
  xI28 : Inv26 s;
  xI2R : forall b0 p0 d0,
           page_state s b0 p0 = PS_Valid d0 ->
           (b0 <> vb \/ In p0 ps) ->
           exists a0 q0, l2p_map s a0 q0 = Some (mkPhysAddr b0 p0);
  xI6R : forall a0 p0 b0 q0 d0,
           page_state s b0 q0 = PS_Valid d0 ->
           page_lpa (page_meta s b0 q0) = Some (a0, p0) ->
           (b0 <> vb \/ In q0 ps) ->
           l2p_map s a0 p0 = Some (mkPhysAddr b0 q0);
  xI12R : forall b0,
            b0 < total_blocks -> b0 <> vb ->
            In b0 (free_block_list s) \/
            (exists t0 ns0, open_block s t0 ns0 = Some b0) \/
            (exists a0 p0 pa0, l2p_map s a0 p0 = Some pa0 /\ pa_block pa0 = b0) \/
            (exists q0, page_state s b0 q0 = PS_Invalid);
  xfree : free_block s vb = false;
  xopen : block_open s vb = false;
  xblt  : vb < total_blocks;
  xnd   : NoDup ps;
  xprog : forall a0 p0 pa0,
            l2p_map s a0 p0 = Some pa0 -> pa_block pa0 = vb ->
            In (pa_page pa0) ps
}.

(* A page of the victim that is not live can be dropped from the work list
   without doing anything: Inv22 already forbids a mapping onto it. *)
Lemma INVX_drop :
  forall s vb q tl,
    INVX vb (q :: tl) s ->
    (forall d, page_state s vb q <> PS_Valid d) ->
    INVX vb tl s.
Proof.
  intros s vb q tl HX Hnv.
  destruct HX as [I0 I1 I3 I4 I5 I7 I8 I9 I10 I11 I13 I15 I16 I17 I18 I19 I20
                  I21 I22 I23 I24 I25 I26 I27 I28 I2R I6R I12R Hfvb Hovb Hvblt
                  Hnd Iprog].
  assert (Hndtl : NoDup tl) by (inversion Hnd; assumption).
  apply mkINVX; try assumption.
  - intros b0 p0 d0 Hv Hc. apply (I2R b0 p0 d0 Hv).
    destruct Hc as [X|X]; [left; exact X | right; apply in_cons; exact X].
  - intros a0 p0 b0 q0 d0 Hv Hlpa Hc. apply (I6R a0 p0 b0 q0 d0 Hv Hlpa).
    destruct Hc as [X|X]; [left; exact X | right; apply in_cons; exact X].
  - intros a0 p0 pa0 Hm Hblk.
    destruct (Iprog a0 p0 pa0 Hm Hblk) as [E|Hin]; [|exact Hin].
    exfalso.
    assert (Hpa : pa0 = mkPhysAddr vb q).
    { rewrite <- Hblk, E. symmetry. apply physaddr_eta. }
    rewrite Hpa in Hm. destruct (I24 a0 p0 (mkPhysAddr vb q) Hm) as [d0 Hd0].
    cbn in Hd0. exact (Hnv d0 Hd0).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- programming the relocation destination.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma program_relx :
  forall (s2 : FTLState) (a : Addr) (p : Page) (d : Data)
         (t : TenantId) (ns : NamespaceId) (pa : PhysAddr)
         (vb : Block) (q : Page) (tl : list Page),
    WF0 s2 -> WF1 s2 -> Inv1 s2 -> Inv2 s2 -> Inv3 s2 -> Inv5 s2 ->
    Inv6 s2 -> Inv7 s2 -> Inv8 s2 -> Inv9 s2 -> Inv11 s2 -> Inv13 s2 ->
    Inv14 s2 -> Inv15 s2 -> Inv16 s2 -> Inv17 s2 -> Inv18 s2 -> Inv19 s2 ->
    Inv20 s2 -> Inv21 s2 -> Inv22 s2 -> Inv23 s2 -> Inv24 s2 -> Inv26 s2 ->
    (forall b0 p0 d0, page_state s2 b0 p0 = PS_Valid d0 ->
       (b0 <> vb \/ In p0 (q :: tl)) ->
       exists a0 q0, l2p_map s2 a0 q0 = Some (mkPhysAddr b0 p0)) ->
    (forall a0 p0 b0 q0 d0, page_state s2 b0 q0 = PS_Valid d0 ->
       page_lpa (page_meta s2 b0 q0) = Some (a0, p0) ->
       (b0 <> vb \/ In q0 (q :: tl)) ->
       l2p_map s2 a0 p0 = Some (mkPhysAddr b0 q0)) ->
    (forall b0, b0 < total_blocks -> b0 <> vb ->
       In b0 (free_block_list s2) \/
       (exists t0 ns0, open_block s2 t0 ns0 = Some b0) \/
       (exists a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 /\ pa_block pa0 = b0) \/
       (exists q0, page_state s2 b0 q0 = PS_Invalid)) ->
    (forall t0 ns0 b0 q0, open_block s2 t0 ns0 = Some b0 ->
       q0 < write_ptr s2 t0 ns0 ->
       (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
       page_state s2 b0 q0 <> PS_Empty) ->
    (forall a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 -> pa_block pa0 = vb ->
       In (pa_page pa0) (q :: tl)) ->
    NoDup (q :: tl) ->
    free_block s2 vb = false ->
    block_open s2 vb = false ->
    vb < total_blocks ->
    pa_block pa <> vb ->
    l2p_map s2 a p = Some (mkPhysAddr vb q) ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s2 a = Some t ->
    addr_namespace s2 a = Some ns ->
    open_block s2 t ns = Some (pa_block pa) ->
    write_ptr s2 t ns = S (pa_page pa) ->
    pa_page pa < pages_per_block ->
    page_state s2 (pa_block pa) (pa_page pa) = PS_Empty ->
    INVX vb tl (program_page s2 a p d pa).
Proof.
  intros s2 a p d t ns pa vb q tl I0 I1 I3 I4 I5 I7 I8 I9 I10 I11 I13 I15
         I16 I17 I18 I19 I20 I21 I22 I23 I24 I25 I26 I28
         I2R I6R I12R I27R Iprog Hnd Hfvb Hovb Hvblt Hdest Hold Ha Hp
         Hat Han Hob Hwp Hpp Hempty.
  destruct (I22 t ns (pa_block pa) Hob)
    as (Hbtb & Hnfl & Hfbf & Hbof & Hwple & Hbt & Hbn & Huniq).
  assert (Hqnt : ~ In q tl) by (inversion Hnd; assumption).
  assert (Hndtl : NoDup tl) by (inversion Hnd; assumption).
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
  (* nothing maps onto the fresh page: it is still erased *)
  assert (HnotPa : forall a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 ->
                     (pa_block pa0 <> pa_block pa \/
                      pa_page pa0 <> pa_page pa)).
  { intros a0 p0 pa0 Hmap.
    destruct (nat_pair_dec (pa_block pa0) (pa_block pa)
                           (pa_page pa0) (pa_page pa)) as [[E1 E2]|H'];
      [|exact H'].
    exfalso. destruct (I24 a0 p0 pa0 Hmap) as [dd Hdd].
    rewrite E1, E2, Hempty in Hdd. discriminate. }
  (* a mapping that survives relativisation is not the one being retargeted *)
  assert (Hnotold : forall a1 p1 b0 q0,
                      l2p_map s2 a1 p1 = Some (mkPhysAddr b0 q0) ->
                      (b0 <> vb \/ In q0 tl) ->
                      (a1 <> a \/ p1 <> p)).
  { intros a1 p1 b0 q0 Hm Hc.
    destruct (nat_pair_dec a1 a p1 p) as [[E1 E2]|H']; [|exact H'].
    exfalso. subst a1 p1. rewrite Hold in Hm.
    injection Hm as Hm1 Hm2. subst b0. subst q0.
    destruct Hc as [X|X]; [exact (X eq_refl) | exact (Hqnt X)]. }
  apply mkINVX.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
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
      destruct (HnotPa a2 p2 pa H2) as [X|X]; exact (X eq_refl).
    + exfalso. subst a2 p2. rewrite set_l2p_here in H2. injection H2 as H2.
      subst pa0. rewrite (set_l2p_other _ _ _ _ _ _ Hne1) in H1.
      destruct (HnotPa a1 p1 pa H1) as [X|X]; exact (X eq_refl).
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne1) in H1.
      rewrite (set_l2p_other _ _ _ _ _ _ Hne2) in H2.
      exact (I4 a1 p1 a2 p2 pa0 H1 H2).
  - (* Inv3 *) intros a0 p0 pa0 d0 Hmap Hv. rewrite Els in Hmap.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. rewrite Epm, set_pm_here. reflexivity.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (HnotPa a0 p0 pa0 Hmap) as Hd.
      rewrite Eps in Hv. rewrite (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd).
      exact (I5 a0 p0 pa0 d0 Hmap Hv).
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
      pose proof (HnotPa a0 p0 pa0 Hmap) as Hd.
      rewrite Eps in Hv. rewrite (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd).
      exact (I9 a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite Epm, set_pm_here. cbn. exists d. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hne). exact (I11 b0 q0 d0 Hv).
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
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
      * destruct (I28 a0 p0 pa0 Hmap) as [[t0 Ht0] [ns0 Hns0]].
        rewrite E in Gt, Gn. rewrite Ht0 in Gt. rewrite Hns0 in Gn.
        destruct Hbt as [Hbt|Hbt]; rewrite Hbt in Gt; [discriminate|].
        injection Gt as Gt. subst t0.
        destruct Hbn as [Hbn|Hbn]; rewrite Hbn in Gn; [discriminate|].
        injection Gn as Gn. subst ns0.
        rewrite E, set_bt_here, set_bn_here.
        split; [rewrite Hat, Ht0; reflexivity | rewrite Han, Hns0; reflexivity].
      * rewrite (set_bt_other _ _ _ _ E), (set_bn_other _ _ _ _ E).
        split; [exact Gt|exact Gn].
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t0 ns0 b0 Hob0. rewrite Eob in Hob0.
    destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
    rewrite Efbl, Efb, Ebo, Ewp, Eob, Ebt, Ebn.
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    split; [exact G4|]. split; [exact G5|].
    destruct (Nat.eq_dec b0 (pa_block pa)) as [E|E].
    + subst b0. rewrite set_bt_here, set_bn_here.
      destruct (Huniq t0 ns0 Hob0) as [Et Ens]. subst t0. subst ns0.
      split; [right; exact Hat|]. split; [right; exact Han|]. exact G8.
    + rewrite (set_bt_other _ _ _ _ E), (set_bn_other _ _ _ _ E).
      split; [exact G6|]. split; [exact G7|]. exact G8.
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob in Hob0.
    rewrite Ewp in Hwp0.
    assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa).
    { destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa))
        as [[F1 F2]|H']; [|exact H'].
      exfalso. subst b0. subst q0.
      destruct (Huniq t0 ns0 Hob0) as [Et Ens]. subst t0. subst ns0.
      rewrite Hwp in Hwp0. lia. }
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hd),
            (set_pm_other _ _ _ _ _ _ Hd).
    exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0).
  - (* Inv22 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. rewrite set_l2p_here in Hmap. injection Hmap as Hmap.
      subst pa0. exists d. rewrite Eps. apply set_ps_here.
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      pose proof (HnotPa a0 p0 pa0 Hmap) as Hd.
      destruct (I24 a0 p0 pa0 Hmap) as [dd Hdd].
      exists dd. rewrite Eps, (set_ps_other _ _ _ _ _ _ Hd). exact Hdd.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob0 Hlt. rewrite Eob in Hob0.
    rewrite Ewp in Hlt. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne).
      exact (I27R t0 ns0 b0 q0 Hob0 Hlt Hne).
  - (* Inv26 *) intros a0 p0 pa0 Hmap. rewrite Els in Hmap. rewrite Eat.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + subst a0 p0. split; [exists t; exact Hat | exists ns; exact Han].
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      exact (I28 a0 p0 pa0 Hmap).
  - (* Inv0, relativised at [tl] *) intros b0 p0 d0 Hv Hc. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) p0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 p0. exists a, p. rewrite Els, set_l2p_here, physaddr_eta.
      reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      assert (Hc' : b0 <> vb \/ In p0 (q :: tl)).
      { destruct Hc as [X|X]; [left; exact X | right; apply in_cons; exact X]. }
      destruct (I2R b0 p0 d0 Hv Hc') as (a0 & p1 & Hmap).
      assert (Hne2 : a0 <> a \/ p1 <> p)
        by (apply (Hnotold a0 p1 b0 p0 Hmap); exact Hc).
      exists a0, p1. rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne2). exact Hmap.
  - (* Inv4, relativised at [tl] *) intros a0 p0 b0 q0 d0 Hv Hlpa Hc.
    rewrite Eps in Hv. rewrite Epm in Hlpa.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pm_here in Hlpa. cbn in Hlpa.
      injection Hlpa as F1 F2. subst a0 p0.
      rewrite Els, set_l2p_here, physaddr_eta. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
      assert (Hc' : b0 <> vb \/ In q0 (q :: tl)).
      { destruct Hc as [X|X]; [left; exact X | right; apply in_cons; exact X]. }
      pose proof (I6R a0 p0 b0 q0 d0 Hv Hlpa Hc') as Hmap.
      assert (Hne2 : a0 <> a \/ p0 <> p)
        by (apply (Hnotold a0 p0 b0 q0 Hmap); exact Hc).
      rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne2). exact Hmap.
  - (* Inv10, relativised at the victim *) intros b0 Hb0 Hbvb.
    destruct (I12R b0 Hb0 Hbvb)
      as [Hin | [[t0 [ns0 Hob0]] | [(a0&p0&pa0&Hmap&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob0.
    + destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
      * exfalso. subst a0 p0. rewrite Hold in Hmap. injection Hmap as Hmap.
        subst pa0. cbn in Hblk. exact (Hbvb (eq_sym Hblk)).
      * right; right; left. exists a0, p0, pa0. split; [|exact Hblk].
        rewrite Els, (set_l2p_other _ _ _ _ _ _ Hne). exact Hmap.
    + right; right; right. exists q0. rewrite Eps.
      assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa).
      { destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa))
          as [[F1 F2]|H']; [|exact H'].
        exfalso. subst b0 q0. rewrite Hempty in Hq0. discriminate. }
      rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hq0.
  - (* the victim is still not free *) rewrite Efb. exact Hfvb.
  - (* the victim is still not open *) rewrite Ebo. exact Hovb.
  - (* the victim is still in range *) exact Hvblt.
  - (* the work list is still duplicate-free *) exact Hndtl.
  - (* progress *) intros a0 p0 pa0 Hmap Hblk. rewrite Els in Hmap.
    destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|Hne].
    + exfalso. subst a0 p0. rewrite set_l2p_here in Hmap.
      injection Hmap as Hmap. subst pa0. exact (Hdest Hblk).
    + rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hmap.
      destruct (Iprog a0 p0 pa0 Hmap Hblk) as [E|Hin]; [|exact Hin].
      exfalso.
      assert (Hpa : pa0 = mkPhysAddr vb q).
      { rewrite <- Hblk, E. symmetry. apply physaddr_eta. }
      rewrite Hpa in Hmap.
      destruct (I4 a0 p0 a p (mkPhysAddr vb q) Hmap Hold) as [X1 X2].
      destruct Hne as [Y|Y]; [exact (Y X1)|exact (Y X2)].
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- allocating the relocation destination.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma open_fresh_shape :
  forall s t ns pa s1,
    open_fresh s t ns = Some (pa, s1) ->
    exists fb rest,
      free_block_list s = fb :: rest /\
      pa = mkPhysAddr fb 0 /\
      free_block_list s1 = rest /\
      free_block s1 = set_free_block (free_block s) fb false /\
      open_block s1 = set_open_block (open_block s) t ns (Some fb) /\
      write_ptr s1 = set_write_ptr (write_ptr s) t ns 1 /\
      block_open s1 = set_block_open (close_open s t ns) fb true.
Proof.
  intros s t ns pa s1 H. unfold open_fresh in H.
  destruct (free_block_list s) as [|fb [|c l]] eqn:Hfbl;
    try rewrite Hfbl in H; cbv beta iota in H; try discriminate.
  injection H as E1 E2. subst pa. subst s1.
  exists fb, (c :: l).
  (* [injection] leaves the new free list as [if fb =? fb then c :: l else ...] *)
  rewrite Nat.eqb_refl. cbv beta iota.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; reflexivity.
Qed.

Lemma alloc_page_shape :
  forall s t ns pa s1,
    alloc_page s t ns = Some (pa, s1) ->
    (exists b,
       open_block s t ns = Some b /\
       write_ptr s t ns < pages_per_block /\
       pa = mkPhysAddr b (write_ptr s t ns) /\
       free_block_list s1 = free_block_list s /\
       free_block s1 = free_block s /\
       block_open s1 = block_open s /\
       open_block s1 = set_open_block (open_block s) t ns (Some b) /\
       write_ptr s1 = set_write_ptr (write_ptr s) t ns (S (write_ptr s t ns)))
    \/ (open_fresh s t ns = Some (pa, s1) /\
        (forall ob, open_block s t ns = Some ob ->
                    pages_per_block <= write_ptr s t ns)).
Proof.
  intros s t ns pa s1 H. unfold alloc_page in H.
  destruct (open_block s t ns) as [b|] eqn:Hob;
    try rewrite Hob in H; cbv beta iota in H.
  - destruct (Nat.ltb (write_ptr s t ns) pages_per_block) eqn:Hlt;
      try rewrite Hlt in H; cbv beta iota in H.
    + left. injection H as E1 E2. subst pa. subst s1. exists b.
      split; [reflexivity|].
      split; [apply Nat.ltb_lt; exact Hlt|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; reflexivity.
    + right. split; [exact H|]. intros ob _. apply Nat.ltb_ge in Hlt. lia.
  - right. split; [exact H|]. intros ob Hob'. discriminate.
Qed.

Lemma relocate_core :
  forall s vb q tl a p d t ns pa s1,
    INVX vb (q :: tl) s ->
    page_state s vb q = PS_Valid d ->
    page_lpa (page_meta s vb q) = Some (a, p) ->
    addr_tenant s a = Some t ->
    addr_namespace s a = Some ns ->
    alloc_page s t ns = Some (pa, s1) ->
    INVX vb tl (program_page s1 a p d pa).
Proof.
  intros s vb q tl a p d t ns pa s1 HX Hps Hlpa Hat Han Halloc.
  destruct HX as [I0 I1 I3 I4 I5 I7 I8 I9 I10 I11 I13 I15 I16 I17 I18 I19 I20
                  I21 I22 I23 I24 I25 I26 I27 I28 I2R I6R I12R Hfvb Hovb Hvblt
                  Hnd Iprog].
  assert (Hppb : pages_per_block > 0) by exact I0.
  assert (Hold : l2p_map s a p = Some (mkPhysAddr vb q)).
  { apply (I6R a p vb q d Hps Hlpa). right. apply in_eq. }
  destruct (I3 a p (mkPhysAddr vb q) Hold) as (_ & _ & Ha & Hp).
  assert (Hdest : pa_block pa <> vb)
    by exact (alloc_dest_not_victim s t ns vb pa s1 I22 I26 Hfvb Hovb Halloc).
  destruct (alloc_page_fields s t ns pa s1 Halloc)
    as (Els1 & Eps1 & Epr1 & Eat1 & Ean1 & Ebt1 & Ebn1 & Epm1 & Ert1).
  (* clauses that only mention the data fields carry across at once *)
  assert (J0 : WF0 s1) by exact I0.
  assert (J1 : WF1 s1) by (intros b0 p0 _ _; eexists; reflexivity).
  assert (J3 : Inv1 s1) by (unfold Inv1; rewrite Els1; exact I3).
  assert (J4 : Inv2 s1) by (unfold Inv2; rewrite Els1; exact I4).
  assert (J5 : Inv3 s1)
    by (unfold Inv3; rewrite Els1, Eps1, Epm1; exact I5).
  assert (J9 : Inv7 s1)
    by (unfold Inv7; rewrite Els1, Eps1, Eat1, Ean1, Epm1; exact I9).
  assert (J11 : Inv9 s1) by (unfold Inv9; rewrite Eps1, Epm1; exact I11).
  assert (J15 : Inv13 s1) by (unfold Inv13; rewrite Eps1, Epr1; exact I15).
  assert (J16 : Inv14 s1) by (unfold Inv14; rewrite Epr1, Eps1; exact I16).
  assert (J17 : Inv15 s1) by (unfold Inv15; rewrite Epr1, Eps1; exact I17).
  assert (J18 : Inv16 s1) by (unfold Inv16; rewrite Eps1, Epr1; exact I18).
  assert (J20 : Inv18 s1)
    by (unfold Inv18; rewrite Els1, Ebt1, Ebn1, Eat1, Ean1; exact I20).
  assert (J21 : Inv19 s1) by (unfold Inv19; rewrite Ert1; exact I21).
  assert (J24 : Inv22 s1) by (unfold Inv22; rewrite Els1, Eps1; exact I24).
  assert (J28 : Inv26 s1)
    by (unfold Inv26; rewrite Els1, Eat1, Ean1; exact I28).
  assert (J2R : forall b0 p0 d0, page_state s1 b0 p0 = PS_Valid d0 ->
                  (b0 <> vb \/ In p0 (q :: tl)) ->
                  exists a0 q0, l2p_map s1 a0 q0 = Some (mkPhysAddr b0 p0)).
  { intros b0 p0 d0 Hv Hc. rewrite Eps1 in Hv. rewrite Els1.
    exact (I2R b0 p0 d0 Hv Hc). }
  assert (J6R : forall a0 p0 b0 q0 d0, page_state s1 b0 q0 = PS_Valid d0 ->
                  page_lpa (page_meta s1 b0 q0) = Some (a0, p0) ->
                  (b0 <> vb \/ In q0 (q :: tl)) ->
                  l2p_map s1 a0 p0 = Some (mkPhysAddr b0 q0)).
  { intros a0 p0 b0 q0 d0 Hv Hl Hc. rewrite Eps1 in Hv. rewrite Epm1 in Hl.
    rewrite Els1. exact (I6R a0 p0 b0 q0 d0 Hv Hl Hc). }
  assert (Jprog : forall a0 p0 pa0, l2p_map s1 a0 p0 = Some pa0 ->
                    pa_block pa0 = vb -> In (pa_page pa0) (q :: tl)).
  { intros a0 p0 pa0 Hm Hblk. rewrite Els1 in Hm.
    exact (Iprog a0 p0 pa0 Hm Hblk). }
  assert (Hold1 : l2p_map s1 a p = Some (mkPhysAddr vb q))
    by (rewrite Els1; exact Hold).
  assert (Hat1 : addr_tenant s1 a = Some t) by (rewrite Eat1; exact Hat).
  assert (Han1 : addr_namespace s1 a = Some ns) by (rewrite Ean1; exact Han).
  destruct (alloc_page_shape s t ns pa s1 Halloc)
    as [(b & Hob & Hlt & Epa & Efbl1 & Efb1 & Ebo1 & Eob1 & Ewp1)
       | (Hof & Hclosed)].
  - (* ── the frontier branch: the open block simply advances ──────── *)
    assert (Eob1' : forall x y, open_block s1 x y = open_block s x y).
    { intros x y. rewrite Eob1. destruct (nat_pair_dec x t y ns) as [[E1 E2]|E].
      - subst x. subst y. rewrite set_ob_here. symmetry. exact Hob.
      - apply set_ob_other. exact E. }
    assert (J7 : Inv5 s1) by (unfold Inv5; rewrite Els1, Efbl1; exact I7).
    assert (J8 : Inv6 s1)
      by (unfold Inv6; rewrite Efbl1, Eps1, Epm1; exact I8).
    assert (J10 : Inv8 s1) by (unfold Inv8; rewrite Efbl1; exact I10).
    assert (J13 : Inv11 s1) by (unfold Inv11; rewrite Efbl1; exact I13).
    assert (J19 : Inv17 s1)
      by (unfold Inv17; rewrite Efb1, Ebt1, Ebn1; exact I19).
    assert (J26 : Inv24 s1) by (unfold Inv24; rewrite Efb1, Efbl1; exact I26).
    assert (J22 : Inv20 s1).
    { intros t0 ns0 b0 Hob0. rewrite Eob1' in Hob0.
      destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
      rewrite Efbl1, Efb1, Ebo1, Ebt1, Ebn1, Ewp1.
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
      split; [exact G4|].
      split.
      { destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
        - subst t0. subst ns0. rewrite set_wp_here. lia.
        - rewrite (set_wp_other _ _ _ _ _ _ E). exact G5. }
      split; [exact G6|]. split; [exact G7|].
      intros t' ns' Hob'. rewrite Eob1' in Hob'. exact (G8 t' ns' Hob'). }
    assert (J23 : Inv21 s1).
    { intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob1' in Hob0.
      rewrite Ewp1 in Hwp0. rewrite Eps1, Epm1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0. subst ns0. rewrite set_wp_here in Hwp0.
        apply (I23 t ns b0 q0 Hob0); [lia|exact Hq0].
      - rewrite (set_wp_other _ _ _ _ _ _ E) in Hwp0.
        exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0). }
    assert (J25 : Inv23 s1).
    { intros b0 Hbo. rewrite Ebo1 in Hbo.
      destruct (I25 b0 Hbo) as [t0 [ns0 H]]. exists t0, ns0.
      rewrite Eob1'. exact H. }
    assert (J12R : forall b0, b0 < total_blocks -> b0 <> vb ->
              In b0 (free_block_list s1) \/
              (exists t0 ns0, open_block s1 t0 ns0 = Some b0) \/
              (exists a0 p0 pa0, l2p_map s1 a0 p0 = Some pa0 /\
                                 pa_block pa0 = b0) \/
              (exists q0, page_state s1 b0 q0 = PS_Invalid)).
    { intros b0 Hb0 Hbvb.
      destruct (I12R b0 Hb0 Hbvb)
        as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
      - left. rewrite Efbl1. exact Hin.
      - right; left. exists t0, ns0. rewrite Eob1'. exact Hob0.
      - right; right; left. destruct Hm as (a0&p0&pa0&Hm1&Hm2).
        exists a0, p0, pa0. rewrite Els1. split; [exact Hm1|exact Hm2].
      - right; right; right. destruct Hq as [q0 Hq0]. exists q0.
        rewrite Eps1. exact Hq0. }
    assert (J27R : forall t0 ns0 b0 q0, open_block s1 t0 ns0 = Some b0 ->
              q0 < write_ptr s1 t0 ns0 ->
              (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
              page_state s1 b0 q0 <> PS_Empty).
    { intros t0 ns0 b0 q0 Hob0 Hlt0 Hne. rewrite Eob1' in Hob0.
      rewrite Ewp1 in Hlt0. rewrite Eps1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0. subst ns0. rewrite set_wp_here in Hlt0.
        rewrite Hob in Hob0. injection Hob0 as Hob0. subst b0.
        rewrite Epa in Hne. cbn in Hne.
        assert (Hq : q0 < write_ptr s t ns).
        { destruct Hne as [X|X]; [exfalso; exact (X eq_refl)|lia]. }
        exact (I27 t ns b q0 Hob Hq).
      - rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt0.
        exact (I27 t0 ns0 b0 q0 Hob0 Hlt0). }
    assert (Hfvb1 : free_block s1 vb = false) by (rewrite Efb1; exact Hfvb).
    assert (Hovb1 : block_open s1 vb = false) by (rewrite Ebo1; exact Hovb).
    assert (Hobf : open_block s1 t ns = Some (pa_block pa))
      by (rewrite Epa; cbn; rewrite Eob1'; exact Hob).
    assert (Hwpf : write_ptr s1 t ns = S (pa_page pa))
      by (rewrite Epa; cbn; rewrite Ewp1; apply set_wp_here).
    assert (Hppf : pa_page pa < pages_per_block)
      by (rewrite Epa; cbn; exact Hlt).
    assert (Hemptyf : page_state s1 (pa_block pa) (pa_page pa) = PS_Empty).
    { rewrite Epa. cbn. rewrite Eps1.
      exact (proj1 (I23 t ns b (write_ptr s t ns) Hob (Nat.le_refl _) Hlt)). }
    exact (program_relx s1 a p d t ns pa vb q tl J0 J1 J3 J4 J5 J7 J8 J9 J10
             J11 J13 J15 J16 J17 J18 J19 J20 J21 J22 J23 J24 J25 J26 J28
             J2R J6R J12R J27R Jprog Hnd Hfvb1 Hovb1 Hvblt Hdest Hold1 Ha Hp
             Hat1 Han1 Hobf Hwpf Hppf Hemptyf).
  - (* ── the open_fresh branch: retire the old block, open a new one ─ *)
    destruct (open_fresh_shape s t ns pa s1 Hof)
      as (fb & rest & Hfbl & Epa & Efbl1 & Efb1 & Eob1 & Ewp1 & Ebo1).
    assert (Hinb : In fb (free_block_list s))
      by (rewrite Hfbl; left; reflexivity).
    assert (Hnd13 : NoDup (fb :: rest)) by (rewrite <- Hfbl; exact I13).
    assert (Hbnotin : ~ In fb rest) by (inversion Hnd13; assumption).
    assert (Hndrest : NoDup rest) by (inversion Hnd13; assumption).
    assert (Hfbb : free_block s fb = true) by (apply (I26 fb); exact Hinb).
    destruct (I19 fb Hfbb) as [Hbtn Hbnn].
    assert (Hblt : fb < total_blocks) by (apply I10; exact Hinb).
    pose proof (I8 fb Hinb) as Hpages.
    assert (Hvbfb : vb <> fb)
      by (intro E; subst vb; rewrite Hfbb in Hfvb; discriminate).
    assert (J7 : Inv5 s1).
    { intros a0 p0 pa0 Hm. rewrite Els1 in Hm. rewrite Efbl1. intro Hin.
      apply (I7 a0 p0 pa0 Hm). rewrite Hfbl. right. exact Hin. }
    assert (J8 : Inv6 s1).
    { intros b0 Hin q0 Hq0. rewrite Efbl1 in Hin. rewrite Eps1, Epm1.
      apply (I8 b0); [rewrite Hfbl; right; exact Hin | exact Hq0]. }
    assert (J10 : Inv8 s1).
    { intros b0 Hin. rewrite Efbl1 in Hin. apply I10. rewrite Hfbl. right.
      exact Hin. }
    assert (J13 : Inv11 s1) by (unfold Inv11; rewrite Efbl1; exact Hndrest).
    assert (J19 : Inv17 s1).
    { intros b0 Hf. rewrite Efb1 in Hf. rewrite Ebt1, Ebn1.
      assert (Hbb : b0 <> fb)
        by (intro E; subst b0; rewrite set_fb_here in Hf; discriminate).
      rewrite (set_fb_other _ _ _ _ Hbb) in Hf. exact (I19 b0 Hf). }
    assert (J26 : Inv24 s1).
    { intros b0. rewrite Efb1, Efbl1. split.
      - intro Hf.
        assert (Hbb : b0 <> fb)
          by (intro Ez; subst b0; rewrite set_fb_here in Hf; discriminate).
        rewrite (set_fb_other _ _ _ _ Hbb) in Hf.
        pose proof (proj1 (I26 b0) Hf) as Hin. rewrite Hfbl in Hin.
        destruct Hin as [Ez|Hin]; [exfalso; exact (Hbb (eq_sym Ez))|exact Hin].
      - intro Hin.
        assert (Hbb : b0 <> fb) by (intro Ez; subst b0; exact (Hbnotin Hin)).
        rewrite (set_fb_other _ _ _ _ Hbb). apply (proj2 (I26 b0)).
        rewrite Hfbl. right. exact Hin. }
    assert (J22 : Inv20 s1).
    { intros t0 ns0 b0 Hob0. rewrite Eob1 in Hob0.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0. subst ns0. rewrite set_ob_here in Hob0.
        injection Hob0 as Hob0. subst b0.
        split; [exact Hblt|].
        split; [rewrite Efbl1; exact Hbnotin|].
        split; [rewrite Efb1; apply set_fb_here|].
        split; [rewrite Ebo1; apply set_bo_here|].
        split; [rewrite Ewp1, set_wp_here; lia|].
        split; [rewrite Ebt1; left; exact Hbtn|].
        split; [rewrite Ebn1; left; exact Hbnn|].
        intros t' ns' Hob'. rewrite Eob1 in Hob'.
        destruct (nat_pair_dec t' t ns' ns) as [[F1 F2]|F];
          [split; assumption|].
        exfalso. rewrite (set_ob_other _ _ _ _ _ _ F) in Hob'.
        exact (proj1 (proj2 (I22 t' ns' fb Hob')) Hinb).
      - rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
        assert (Hbb : b0 <> fb) by (intro Ez; subst b0; exact (G2 Hinb)).
        split; [exact G1|].
        split; [rewrite Efbl1; intro Hin; apply G2; rewrite Hfbl; right;
                exact Hin|].
        split; [rewrite Efb1, (set_fb_other _ _ _ _ Hbb); exact G3|].
        split.
        { rewrite Ebo1, (set_bo_other _ _ _ _ Hbb). unfold close_open.
          destruct (open_block s t ns) as [ob|] eqn:Hobt; [|exact G4].
          assert (Hobne : b0 <> ob).
          { intro Ez. subst ob. destruct (G8 t ns Hobt) as [X1 X2].
            destruct E as [Y|Y];
              [exact (Y (eq_sym X1)) | exact (Y (eq_sym X2))]. }
          rewrite (set_bo_other _ _ _ _ Hobne). exact G4. }
        split; [rewrite Ewp1, (set_wp_other _ _ _ _ _ _ E); exact G5|].
        split; [rewrite Ebt1; exact G6|].
        split; [rewrite Ebn1; exact G7|].
        intros t' ns' Hob'. rewrite Eob1 in Hob'.
        destruct (nat_pair_dec t' t ns' ns) as [[F1 F2]|F].
        + exfalso. subst t'. subst ns'. rewrite set_ob_here in Hob'.
          injection Hob' as Hob'. exact (Hbb (eq_sym Hob')).
        + rewrite (set_ob_other _ _ _ _ _ _ F) in Hob'.
          exact (G8 t' ns' Hob'). }
    assert (J23 : Inv21 s1).
    { intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob1 in Hob0.
      rewrite Ewp1 in Hwp0. rewrite Eps1, Epm1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0. subst ns0. rewrite set_ob_here in Hob0.
        injection Hob0 as Hob0. subst b0. exact (Hpages q0 Hq0).
      - rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        rewrite (set_wp_other _ _ _ _ _ _ E) in Hwp0.
        exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0). }
    assert (J25 : Inv23 s1).
    { intros b0 Hbo. rewrite Ebo1 in Hbo. rewrite Eob1.
      destruct (Nat.eq_dec b0 fb) as [E|E].
      - subst b0. exists t, ns. apply set_ob_here.
      - rewrite (set_bo_other _ _ _ _ E) in Hbo. unfold close_open in Hbo.
        destruct (open_block s t ns) as [ob|] eqn:Hobt.
        + destruct (Nat.eq_dec b0 ob) as [E2|E2].
          * subst b0. rewrite set_bo_here in Hbo. discriminate.
          * rewrite (set_bo_other _ _ _ _ E2) in Hbo.
            destruct (I25 b0 Hbo) as [t' [ns' Hob']]. exists t', ns'.
            assert (E3 : t' <> t \/ ns' <> ns).
            { destruct (nat_pair_dec t' t ns' ns) as [[Y1 Y2]|Y]; [|exact Y].
              exfalso. subst t'. subst ns'. rewrite Hobt in Hob'.
              injection Hob' as Hob'. exact (E2 (eq_sym Hob')). }
            rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'.
        + destruct (I25 b0 Hbo) as [t' [ns' Hob']]. exists t', ns'.
          assert (E3 : t' <> t \/ ns' <> ns).
          { destruct (nat_pair_dec t' t ns' ns) as [[Y1 Y2]|Y]; [|exact Y].
            exfalso. subst t'. subst ns'. rewrite Hobt in Hob'. discriminate. }
          rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'. }
    assert (J12R : forall b0, b0 < total_blocks -> b0 <> vb ->
              In b0 (free_block_list s1) \/
              (exists t0 ns0, open_block s1 t0 ns0 = Some b0) \/
              (exists a0 p0 pa0, l2p_map s1 a0 p0 = Some pa0 /\
                                 pa_block pa0 = b0) \/
              (exists q0, page_state s1 b0 q0 = PS_Invalid)).
    { intros b0 Hb0 Hbvb.
      destruct (I12R b0 Hb0 Hbvb) as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
      - rewrite Hfbl in Hin. destruct Hin as [Ez|Hin].
        + subst b0. right; left. exists t, ns. rewrite Eob1. apply set_ob_here.
        + left. rewrite Efbl1. exact Hin.
      - destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
        + subst t0. subst ns0.
          assert (Hwpt : pages_per_block <= write_ptr s t ns)
            by (apply (Hclosed b0); exact Hob0).
          assert (H0 : 0 < write_ptr s t ns) by lia.
          pose proof (I27 t ns b0 0 Hob0 H0) as Hne0.
          destruct (page_state s b0 0) as [| |d0] eqn:Eps0.
          * exfalso. exact (Hne0 eq_refl).
          * right; right; right. exists 0. rewrite Eps1. exact Eps0.
          * destruct (I2R b0 0 d0 Eps0 (or_introl Hbvb)) as (a0 & p0 & Hmap).
            right; right; left. exists a0, p0, (mkPhysAddr b0 0).
            rewrite Els1. split; [exact Hmap|reflexivity].
        + right; left. exists t0, ns0.
          rewrite Eob1, (set_ob_other _ _ _ _ _ _ E). exact Hob0.
      - right; right; left. destruct Hm as (a0&p0&pa0&Hm1&Hm2).
        exists a0, p0, pa0. rewrite Els1. split; [exact Hm1|exact Hm2].
      - right; right; right. destruct Hq as [q0 Hq0]. exists q0.
        rewrite Eps1. exact Hq0. }
    assert (J27R : forall t0 ns0 b0 q0, open_block s1 t0 ns0 = Some b0 ->
              q0 < write_ptr s1 t0 ns0 ->
              (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
              page_state s1 b0 q0 <> PS_Empty).
    { intros t0 ns0 b0 q0 Hob0 Hlt0 Hne. rewrite Eob1 in Hob0.
      rewrite Ewp1 in Hlt0. rewrite Eps1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - exfalso. subst t0. subst ns0. rewrite set_ob_here in Hob0.
        injection Hob0 as Hob0. subst b0. rewrite set_wp_here in Hlt0.
        assert (Hq0 : q0 = 0) by lia. subst q0.
        rewrite Epa in Hne. cbn in Hne.
        destruct Hne as [X|X]; exact (X eq_refl).
      - rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt0.
        exact (I27 t0 ns0 b0 q0 Hob0 Hlt0). }
    assert (Hfvb1 : free_block s1 vb = false)
      by (rewrite Efb1, (set_fb_other _ _ _ _ Hvbfb); exact Hfvb).
    assert (Hovb1 : block_open s1 vb = false).
    { rewrite Ebo1, (set_bo_other _ _ _ _ Hvbfb). unfold close_open.
      destruct (open_block s t ns) as [ob|] eqn:Hobt; [|exact Hovb].
      destruct (Nat.eq_dec vb ob) as [E|E].
      - rewrite E. apply set_bo_here.
      - rewrite (set_bo_other _ _ _ _ E). exact Hovb. }
    assert (Hobf : open_block s1 t ns = Some (pa_block pa))
      by (rewrite Epa; cbn; rewrite Eob1; apply set_ob_here).
    assert (Hwpf : write_ptr s1 t ns = S (pa_page pa))
      by (rewrite Epa; cbn; rewrite Ewp1; apply set_wp_here).
    assert (Hppf : pa_page pa < pages_per_block)
      by (rewrite Epa; cbn; exact Hppb).
    assert (Hemptyf : page_state s1 (pa_block pa) (pa_page pa) = PS_Empty)
      by (rewrite Epa; cbn; rewrite Eps1; exact (proj1 (Hpages 0 Hppb))).
    exact (program_relx s1 a p d t ns pa vb q tl J0 J1 J3 J4 J5 J7 J8 J9 J10
             J11 J13 J15 J16 J17 J18 J19 J20 J21 J22 J23 J24 J25 J26 J28
             J2R J6R J12R J27R Jprog Hnd Hfvb1 Hovb1 Hvblt Hdest Hold1 Ha Hp
             Hat1 Han1 Hobf Hwpf Hppf Hemptyf).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- the fold, the erase, and the two assigned statements.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma relocate_page_INVX :
  forall s vb q tl s',
    INVX vb (q :: tl) s ->
    relocate_page s vb q = Some s' ->
    INVX vb tl s'.
Proof.
  intros s vb q tl s' HX Hrel. unfold relocate_page in Hrel.
  destruct (page_state s vb q) as [| |d] eqn:Hps.
  - injection Hrel as Hrel. subst s'.
    apply (INVX_drop s vb q tl HX). intros d0 Hc.
    rewrite Hps in Hc. discriminate.
  - injection Hrel as Hrel. subst s'.
    apply (INVX_drop s vb q tl HX). intros d0 Hc.
    rewrite Hps in Hc. discriminate.
  - destruct (page_lpa (page_meta s vb q)) as [[a p]|] eqn:Hlpa;
      [|discriminate].
    destruct (addr_tenant s a) as [t|] eqn:Hat;
      destruct (addr_namespace s a) as [ns|] eqn:Han;
      cbv beta iota in Hrel; try discriminate.
    destruct (alloc_page s t ns) as [[pa s1]|] eqn:Halloc;
      cbv beta iota in Hrel; [|discriminate].
    injection Hrel as Hrel. subst s'.
    exact (relocate_core s vb q tl a p d t ns pa s1 HX Hps Hlpa Hat Han Halloc).
Qed.

Lemma relocate_pages_INVX :
  forall ps s vb s',
    INVX vb ps s -> relocate_pages s vb ps = Some s' -> INVX vb [] s'.
Proof.
  intros ps. induction ps as [|q tl IH]; intros s vb s' HX H.
  - cbn [relocate_pages] in H. injection H as H. subst s'. exact HX.
  - cbn [relocate_pages] in H.
    destruct (relocate_page s vb q) as [s1|] eqn:Hr;
      cbv beta iota in H; [|discriminate].
    exact (IH s1 vb s' (relocate_page_INVX s vb q tl s1 HX Hr) H).
Qed.

Lemma erase_ok :
  forall s vb, INVX vb [] s -> ftl_invariant (erase_block s vb).
Proof.
  intros s vb HX.
  destruct HX as [I0 I1 I3 I4 I5 I7 I8 I9 I10 I11 I13 I15 I16 I17 I18 I19 I20
                  I21 I22 I23 I24 I25 I26 I27 I28 I2R I6R I12R Hfvb Hovb Hvblt
                  Hnd Iprog].
  assert (Hnomap : forall a0 p0 pa0, l2p_map s a0 p0 = Some pa0 ->
                     pa_block pa0 <> vb).
  { intros a0 p0 pa0 Hm E. exact (Iprog a0 p0 pa0 Hm E). }
  assert (Hnotfree : ~ In vb (free_block_list s)).
  { intro Hin. pose proof (proj2 (I26 vb) Hin) as X. rewrite X in Hfvb.
    discriminate. }
  assert (Hopenne : forall t0 ns0 b0, open_block s t0 ns0 = Some b0 -> b0 <> vb).
  { intros t0 ns0 b0 H E. subst b0.
    destruct (I22 t0 ns0 vb H) as (_&_&_&G4&_).
    rewrite G4 in Hovb. discriminate. }
  assert (K15 : Inv13 (erase_block s vb)).
  { intros b0 q0 d0 Hv. destruct (Nat.eq_dec b0 vb) as [E|E].
    - subst b0. rewrite eb_ps_self in Hv. discriminate.
    - rewrite (eb_ps_other _ _ _ _ E) in Hv. rewrite (eb_pr_other _ _ _ _ E).
      exact (I15 b0 q0 d0 Hv). }
  assert (K17 : Inv15 (erase_block s vb)).
  { intros b0 q0 Hr. destruct (Nat.eq_dec b0 vb) as [E|E].
    - subst b0. rewrite eb_pr_self in Hr. discriminate.
    - rewrite (eb_pr_other _ _ _ _ E) in Hr. rewrite (eb_ps_other _ _ _ _ E).
      exact (I17 b0 q0 Hr). }
  apply make_ftl_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 p0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 p0 d0 Hv. rewrite eb_l2p.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite eb_ps_self in Hv. discriminate.
    + rewrite (eb_ps_other _ _ _ _ E) in Hv.
      exact (I2R b0 p0 d0 Hv (or_introl E)).
  - (* Inv1 *) unfold Inv1. rewrite eb_l2p. exact I3.
  - (* Inv2 *) unfold Inv2. rewrite eb_l2p. exact I4.
  - (* Inv3 *) intros a0 p0 pa0 d0 Hm Hv. rewrite eb_l2p in Hm.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne) in Hv.
    rewrite (eb_pm_other _ _ _ _ Hne). exact (I5 a0 p0 pa0 d0 Hm Hv).
  - (* Inv4 *) intros a0 p0 b0 q0 d0 Hv Hlpa. rewrite eb_l2p.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite eb_ps_self in Hv. discriminate.
    + rewrite (eb_ps_other _ _ _ _ E) in Hv.
      rewrite (eb_pm_other _ _ _ _ E) in Hlpa.
      exact (I6R a0 p0 b0 q0 d0 Hv Hlpa (or_introl E)).
  - (* Inv5 *) intros a0 p0 pa0 Hm. rewrite eb_l2p in Hm. rewrite eb_fbl.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    intro Hin. destruct Hin as [Ez|Hin];
      [exact (Hne (eq_sym Ez)) | exact (I7 a0 p0 pa0 Hm Hin)].
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite eb_fbl in Hin.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. split; [apply eb_ps_self | apply eb_pm_self].
    + rewrite (eb_ps_other _ _ _ _ E), (eb_pm_other _ _ _ _ E).
      destruct Hin as [Ez|Hin]; [exfalso; exact (E (eq_sym Ez))|].
      exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros a0 p0 pa0 d0 t0 n0 Hm Hv Ht Hn.
    rewrite eb_l2p in Hm. rewrite eb_at in Ht. rewrite eb_an in Hn.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne) in Hv.
    rewrite (eb_pm_other _ _ _ _ Hne). exact (I9 a0 p0 pa0 d0 t0 n0 Hm Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite eb_fbl in Hin.
    destruct Hin as [Ez|Hin]; [subst b0; exact Hvblt | exact (I10 b0 Hin)].
  - (* Inv9 *) intros b0 q0 d0 Hv.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite eb_ps_self in Hv. discriminate.
    + rewrite (eb_ps_other _ _ _ _ E) in Hv. rewrite (eb_pm_other _ _ _ _ E).
      exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) intros b0 Hb0. rewrite eb_fbl.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. left. apply in_eq.
    + destruct (I12R b0 Hb0 E) as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
      * left. apply in_cons. exact Hin.
      * right; left. exists t0, ns0. rewrite eb_ob. exact Hob0.
      * right; right; left. destruct Hm as (a0&p0&pa0&Hm1&Hm2).
        exists a0, p0, pa0. rewrite eb_l2p. split; [exact Hm1|exact Hm2].
      * right; right; right. destruct Hq as [q0 Hq0]. exists q0.
        rewrite (eb_ps_other _ _ _ _ E). exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite eb_fbl.
    apply NoDup_cons; [exact Hnotfree | exact I13].
  - (* Inv12 *) exact (Inv12_from_Inv13_Inv15 _ K15 K17).
  - (* Inv13 *) exact K15.
  - (* Inv14 *) intros b0 q0 Hr. destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite eb_pr_self in Hr. discriminate.
    + rewrite (eb_pr_other _ _ _ _ E) in Hr. rewrite (eb_ps_other _ _ _ _ E).
      exact (I16 b0 q0 Hr).
  - (* Inv15 *) exact K17.
  - (* Inv16 *) intros b0 q0 He. destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. apply eb_pr_self.
    + rewrite (eb_ps_other _ _ _ _ E) in He. rewrite (eb_pr_other _ _ _ _ E).
      exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite eb_fb in Hf. rewrite eb_bt, eb_bn.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite set_bt_here, set_bn_here. split; reflexivity.
    + rewrite (set_fb_other _ _ _ _ E) in Hf.
      rewrite (set_bt_other _ _ _ _ E), (set_bn_other _ _ _ _ E).
      exact (I19 b0 Hf).
  - (* Inv18 *) intros a0 p0 pa0 Hm. rewrite eb_l2p in Hm.
    rewrite eb_bt, eb_bn, eb_at, eb_an.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (set_bt_other _ _ _ _ Hne), (set_bn_other _ _ _ _ Hne).
    exact (I20 a0 p0 pa0 Hm).
  - (* Inv19 *) unfold Inv19. rewrite eb_rt. exact I21.
  - (* Inv20 *) intros t0 ns0 b0 Hob0. rewrite eb_ob in Hob0.
    pose proof (Hopenne t0 ns0 b0 Hob0) as Hne.
    destruct (I22 t0 ns0 b0 Hob0) as (G1&G2&G3&G4&G5&G6&G7&G8).
    rewrite eb_fbl, eb_fb, eb_bo, eb_wp, eb_ob, eb_bt, eb_bn.
    split; [exact G1|].
    split; [intro Hin; destruct Hin as [Ez|Hin];
            [exact (Hne (eq_sym Ez)) | exact (G2 Hin)]|].
    split; [rewrite (set_fb_other _ _ _ _ Hne); exact G3|].
    split; [rewrite (set_bo_other _ _ _ _ Hne); exact G4|].
    split; [exact G5|].
    split; [rewrite (set_bt_other _ _ _ _ Hne); exact G6|].
    split; [rewrite (set_bn_other _ _ _ _ Hne); exact G7|].
    exact G8.
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0.
    rewrite eb_ob in Hob0. rewrite eb_wp in Hwp0.
    pose proof (Hopenne t0 ns0 b0 Hob0) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne), (eb_pm_other _ _ _ _ Hne).
    exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0).
  - (* Inv22 *) intros a0 p0 pa0 Hm. rewrite eb_l2p in Hm.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne). exact (I24 a0 p0 pa0 Hm).
  - (* Inv23 *) intros b0 Hbo. rewrite eb_bo in Hbo. rewrite eb_ob.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite set_bo_here in Hbo. discriminate.
    + rewrite (set_bo_other _ _ _ _ E) in Hbo. exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite eb_fb, eb_fbl.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite set_fb_here.
      split; [intros _; apply in_eq | intros _; reflexivity].
    + rewrite (set_fb_other _ _ _ _ E). split.
      * intro Hf. apply in_cons. exact (proj1 (I26 b0) Hf).
      * intro Hin. destruct Hin as [Ez|Hin];
          [exfalso; exact (E (eq_sym Ez)) | exact (proj2 (I26 b0) Hin)].
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob0 Hlt0.
    rewrite eb_ob in Hob0. rewrite eb_wp in Hlt0.
    pose proof (Hopenne t0 ns0 b0 Hob0) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne). exact (I27 t0 ns0 b0 q0 Hob0 Hlt0).
  - (* Inv26 *) unfold Inv26. rewrite eb_l2p, eb_at, eb_an. exact I28.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- preservation, once, for every victim chooser.

   The argument above never mentions how the victim was found.  It needs
   exactly three facts about it: the block is in range, its free bit is clear,
   and it is not open.  Those are precisely [victim_sound]'s obligations, so
   the theorem is stated over [reclaim_with pick] for an arbitrary sound
   [pick] and the two host-visible maintenance operations are instances.
   ══════════════════════════════════════════════════════════════════════ *)

(* The entry condition of the fold, for any block the chooser may legally
   return.  [find_victim] appears nowhere in it. *)
Lemma reclaimable_victim_INVX :
  forall s b,
    ftl_invariant s ->
    b < total_blocks -> reclaimable s b = true ->
    INVX b all_pages s.
Proof.
  intros s b Hinv Hblt Hrec.
  destruct Hinv as (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  unfold reclaimable, is_open in Hrec.
  apply andb_prop in Hrec. destruct Hrec as [Hf1 Hf2].
  apply negb_true_iff in Hf1. apply negb_true_iff in Hf2.
  apply mkINVX; try assumption.
  - intros b0 p0 d0 Hv0 _. exact (I2 b0 p0 d0 Hv0).
  - intros a0 p0 b0 q0 d0 Hv0 Hl0 _. exact (I6 a0 p0 b0 q0 d0 Hv0 Hl0).
  - intros b0 Hb0 _. exact (I12 b0 Hb0).
  - unfold all_pages. apply seq_NoDup.
  - intros a0 p0 pa0 Hm _. unfold all_pages. apply in_seq.
    destruct (I3 a0 p0 pa0 Hm) as (_ & Hpp & _). lia.
Qed.

(* Reclaiming one admissible block preserves all 29 conjuncts. *)
Theorem reclaim_preserves_invariant :
  forall s b s',
    ftl_invariant s ->
    b < total_blocks -> reclaimable s b = true ->
    reclaim s b = Some s' ->
    ftl_invariant s'.
Proof.
  intros s b s' Hinv Hblt Hrec Hrc. unfold reclaim in Hrc.
  destruct (relocate_pages s b all_pages) as [s1|] eqn:Hrel;
    cbv beta iota in Hrc; [|discriminate].
  injection Hrc as Hrc. subst s'.
  apply erase_ok.
  apply (relocate_pages_INVX all_pages s b s1); [|exact Hrel].
  exact (reclaimable_victim_INVX s b Hinv Hblt Hrec).
Qed.

(* The generalized statement.  One proof for every reclamation policy that
   meets the chooser contract; the policy itself is not constrained further,
   and in particular the invariant says nothing about [wear_count], so a
   wear-aware chooser is admissible for free. *)
Theorem reclaim_with_preserves_invariant :
  forall pick s s',
    victim_sound pick ->
    ftl_invariant s ->
    reclaim_with pick s = Some s' ->
    ftl_invariant s'.
Proof.
  intros pick s s' Hpick Hinv Hstep. unfold reclaim_with in Hstep.
  destruct (pick s) as [b|] eqn:Hv; cbv beta iota in Hstep; [|discriminate].
  destruct (Hpick s b Hv) as [Hblt Hrec].
  exact (reclaim_preserves_invariant s b s' Hinv Hblt Hrec Hstep).
Qed.

(* ── the chooser contract is necessary, not a convenience ───────────────

   [reclaim_with_preserves_invariant] carries a hypothesis on [pick], and the
   statement "for every [pick], [reclaim_with pick] preserves the invariant"
   is simply false.  A chooser that names a *free* block is the cheapest
   refutation: nothing is live in it, so the relocation fold does nothing and
   the reclaim succeeds, and [erase_block] then pushes the block onto the free
   list a second time.  Inv11 -- the free list has no duplicates -- fails, from
   a start state that satisfies all 29 conjuncts.  So [victim_sound] is doing
   real work; it is not slack in the statement. *)
Lemma relocate_page_empty :
  forall s b q, page_state s b q = PS_Empty -> relocate_page s b q = Some s.
Proof. intros s b q He. unfold relocate_page. rewrite He. reflexivity. Qed.

Lemma relocate_pages_all_empty :
  forall ps s b,
    (forall q, page_state s b q = PS_Empty) ->
    relocate_pages s b ps = Some s.
Proof.
  induction ps as [|q tl IH]; intros s b He; [reflexivity|].
  cbn [relocate_pages]. rewrite (relocate_page_empty s b q (He q)).
  exact (IH s b He).
Qed.

Theorem unconstrained_chooser_breaks_invariant :
  exists (pick : FTLState -> option Block) (s s' : FTLState),
    ftl_invariant s /\
    reclaim_with pick s = Some s' /\
    ~ Inv11 s'.
Proof.
  exists (fun _ => Some 0), empty_state, (erase_block empty_state 0).
  split; [exact (@empty_state_invariant pages_per_block_pos)|].
  split.
  - unfold reclaim_with, reclaim.
    rewrite (relocate_pages_all_empty all_pages empty_state 0
               (fun q => eq_refl)).
    reflexivity.
  - unfold Inv11. rewrite eb_fbl.
    intro Hnd. inversion Hnd as [|x l Hnin Hrest]. apply Hnin.
    change (In 0 (seq 0 total_blocks)). apply in_seq.
    pose proof total_blocks_pos. lia.
Qed.

(* ── the two assigned statements, as instances ───────────────────────── *)

Lemma gc_preserves_invariant :
  forall s s', ftl_invariant s ->
    step s COpGC = Some s' -> ftl_invariant s'.
Proof.
  intros s s' Hinv Hstep.
  change (step s COpGC) with (reclaim_with find_victim s) in Hstep.
  exact (reclaim_with_preserves_invariant find_victim s s'
           find_victim_sound Hinv Hstep).
Qed.

(* Wear levelling is the same transformer under the least-worn-block policy.
   Nothing in the proof changes; only the chooser instantiated does. *)
Lemma wear_level_preserves_invariant :
  forall s s', ftl_invariant s ->
    step s COpWearLevel = Some s' -> ftl_invariant s'.
Proof.
  intros s s' Hinv Hstep.
  change (step s COpWearLevel) with (reclaim_with find_least_worn_victim s)
    in Hstep.
  exact (reclaim_with_preserves_invariant find_least_worn_victim s s'
           find_least_worn_victim_sound Hinv Hstep).
Qed.
