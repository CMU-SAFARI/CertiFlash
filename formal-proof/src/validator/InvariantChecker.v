(* InvariantChecker.v: an executable, geometry-bounded boolean rendering of
   the page-granular global invariant [ftl_invariant] (WF0 .. Inv26,
   Invariants/Invariants.v).

   ══════════════════════════════════════════════════════════════════════
   THE TWO DIRECTIONS, PLAINLY
   ══════════════════════════════════════════════════════════════════════

   A [false] verdict REFUTES.  The headline result is

       Theorem check_refutes :
         forall s, check_bounded_all s = false -> ~ ftl_invariant s.

   proved from [check_bounded_all_complete : ftl_invariant s ->
   check_bounded_all s = true] and, clause by clause, from
   [check_invN_complete : Inv_N s -> check_invN s = true].  Every rejection
   is a real bug; the checker never cries wolf.  This direction survives the
   unbounded quantification in the clauses because a bounded check tests
   finitely many points and the clause holds at *every* point, so it holds at
   the tested ones — a bounded search that finds a counterexample has found a
   real one.  Truncation costs completeness of the search, never soundness of
   the refutation.

   A [true] verdict does NOT CERTIFY.  It cannot: see the next section.  Only
   six clauses (WF0, WF1, Inv6, Inv8, Inv10, Inv11) are decided outright,
   and those are collected in [check_invariant] with
   [check_invariant_sound : check_invariant s = true -> WF0 s /\ ... ].  For
   the other 23 a [true] verdict certifies only the geometry-restricted
   reading of the clause, written out in full in each [check_invN_sound].

   So: the module is a debugging aid whose rejections are proofs of a bug, not
   a certifier whose acceptances are proofs of correctness.

   ══════════════════════════════════════════════════════════════════════
   WHY A BOUNDED CHECKER CANNOT CERTIFY
   ══════════════════════════════════════════════════════════════════════

   [FTLState] stores its maps as *total functions* on [nat]
   ([l2p_map : Addr -> Page -> option PhysAddr], [page_state], [page_role],
   [free_block], [block_open], [open_block], [region_table], ...).  Nothing in
   the model confines those functions to the device geometry: a state may
   perfectly well have [l2p_map s 10000 0 = Some pa] or
   [page_state s 999 0 = PS_Valid d].

   Almost every clause of [ftl_invariant] is a universally quantified
   statement over such an unbounded domain, e.g.

       Inv1 s := forall a p pa, l2p_map s a p = Some pa -> ... bounds ...

   A [bool]-valued function can only inspect finitely many points.  So for a
   clause whose *universal* quantifiers are unbounded, no boolean check can be
   sound: the check would have to certify infinitely many untested points.
   This is not a limitation of the proof effort below, it is a fact about the
   model, and pretending otherwise would be exactly the "fake decision
   procedure" this file avoids.

   Consequently the clauses split in two:

   (A) SOUNDLY DECIDABLE — every universal quantifier is already bounded by
       the clause itself (by [< total_blocks], [< pages_per_block], or by
       membership in the finite list [free_block_list s]), and every
       existential can be *witnessed* by a bounded search (finding a witness
       inside the geometry proves the existential outright; failing to find
       one merely makes the check return [false], which is sound).

         WF0   pages_per_block > 0                          (a closed fact)
         WF1   totality of page_state on the geometry       (vacuously true)
         Inv6   free-list blocks are fully erased            (b in a list,
                                                              p < ppb)
         Inv8  free-list blocks are in range                (b in a list)
         Inv10  every block is free / open / mapped / stale  (b < tb, and the
                                                              four disjuncts
                                                              are existentials
                                                              we witness)
         Inv11  NoDup (free_block_list s)                    (a finite list)

       These six, and only these six, are conjoined into [check_invariant],
       and [check_invariant_sound] below proves

           check_invariant s = true ->
             WF0 s /\ WF1 s /\ Inv6 s /\ Inv8 s /\ Inv10 s /\ Inv11 s.

   (B) NOT SOUNDLY DECIDABLE — the clause universally quantifies over an
       unbounded domain (Inv0..Inv5, Inv7, Inv9, Inv13..Inv19, Inv22, Inv24,
       Inv26 range over all [a]/[b]/[p]/[i]; Inv20, Inv21, Inv23, Inv25 range
       over all tenants and namespaces; Inv12's *hypothesis* is itself an
       unbounded existential "exists p, page_role s b p = Some RMeta", so a
       bounded search for that hypothesis can miss it and let the check pass
       vacuously on a state that violates the clause).

       These are EXCLUDED from [check_invariant].  A [check_invN] is still
       defined for each of them — the geometry-bounded test one would actually
       run on a device — and each still gets a Qed-closed soundness lemma, but
       against the *geometry-restricted* reading of its clause, stated
       explicitly in the lemma.  For instance [check_inv3_sound] concludes

           forall a p pa, a < addr_space -> p < pages_per_block ->
             l2p_map s a p = Some pa -> ... bounds ...

       which is Inv1 with its quantifiers truncated.  That is a real theorem
       and it is what the bounded test genuinely buys; it is *not* Inv1.
       They are collected in [check_bounded_all] / [check_bounded_all_sound].

   TENANTS AND NAMESPACES.  Inv20, Inv21, Inv23 and Inv25 quantify over
   [TenantId] and [NamespaceId], which are bare [nat] with no geometry
   constant to bound them.  The bounded surrogate used here enumerates only
   the (tenant, namespace) pairs that some in-range logical address is
   labelled with, i.e. the pairs satisfying [observed_owner] below.  What that
   establishes: the clause holds for every owner pair the address map
   mentions.  What it does NOT establish: anything about a frontier opened for
   an owner that labels no address in [seq 0 addr_space] — such a frontier is
   invisible to the checker.  (In the existential *conclusions* of Inv10 and
   Inv23 the same enumeration is used in the sound direction: a pair found
   there is a genuine witness, so those two searches lose completeness only,
   never soundness — which is why Inv10 stays in group (A).)

   REGION TABLE.  [region_table : nat -> option RegionMeta] has no size
   constant either; [check_inv21] bounds the index by [total_blocks] and the
   corresponding lemma restricts Inv19 to [i < total_blocks] accordingly.

   NO admitted lemmas, [admit], axiom declarations, parameters, variables or hypotheses
   is introduced anywhere in this file; every result is closed with [Qed]. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import core.Model.
Require Import Invariants.Invariants.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════
   Generic enumeration helpers
   ══════════════════════════════════════════════════════════════ *)

Lemma forallb_in_elim :
  forall (A : Type) (f : A -> bool) (l : list A) (x : A),
    forallb f l = true -> In x l -> f x = true.
Proof.
  intros A f l x H Hin.
  apply forallb_forall with (x := x) in H; assumption.
Qed.

Lemma forallb_seq_elim :
  forall (f : nat -> bool) (n x : nat),
    forallb f (seq 0 n) = true -> x < n -> f x = true.
Proof.
  intros f n x H Hx.
  apply (forallb_in_elim nat f (seq 0 n) x H).
  apply in_seq. lia.
Qed.

(* ══════════════════════════════════════════════════════════════
   Small boolean helpers, each with the elimination lemma that the
   SOUNDNESS direction needs (bool = true -> the Prop it stands for)
   ══════════════════════════════════════════════════════════════ *)

Definition inb (b : nat) (l : list nat) : bool := existsb (Nat.eqb b) l.

Lemma inb_sound : forall b l, inb b l = true -> In b l.
Proof.
  intros b l H. unfold inb in H.
  apply existsb_exists in H. destruct H as [x [Hin Heq]].
  apply Nat.eqb_eq in Heq. subst x. exact Hin.
Qed.

Lemma inb_complete : forall b l, In b l -> inb b l = true.
Proof.
  intros b l H. unfold inb. apply existsb_exists.
  exists b. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma inb_false_sound : forall b l, negb (inb b l) = true -> ~ In b l.
Proof.
  intros b l H Hin. apply negb_true_iff in H.
  rewrite (inb_complete b l Hin) in H. discriminate.
Qed.

Definition opt_nat_eqb (x y : option nat) : bool :=
  match x with
  | None => match y with None => true | Some _ => false end
  | Some u => match y with None => false | Some v => Nat.eqb u v end
  end.

Lemma opt_nat_eqb_sound : forall x y, opt_nat_eqb x y = true -> x = y.
Proof.
  intros [u|] [v|] H; simpl in H; try discriminate; try reflexivity.
  apply Nat.eqb_eq in H. subst v. reflexivity.
Qed.

Lemma opt_nat_eqb_refl : forall x, opt_nat_eqb x x = true.
Proof.
  intros [u|]; simpl; [apply Nat.eqb_refl | reflexivity].
Qed.

Definition lpa_eqb (x y : LPA) : bool :=
  andb (Nat.eqb (fst x) (fst y)) (Nat.eqb (snd x) (snd y)).

Definition opt_lpa_eqb (x y : option LPA) : bool :=
  match x with
  | None => match y with None => true | Some _ => false end
  | Some u => match y with None => false | Some v => lpa_eqb u v end
  end.

Lemma opt_lpa_eqb_sound : forall x y, opt_lpa_eqb x y = true -> x = y.
Proof.
  intros [[a p]|] [[a' p']|] H; simpl in H; try discriminate; try reflexivity.
  unfold lpa_eqb in H. simpl in H.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma opt_lpa_eqb_refl : forall x, opt_lpa_eqb x x = true.
Proof.
  intros [[a p]|]; simpl; [| reflexivity].
  unfold lpa_eqb. simpl. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Definition page_meta_eqb (m1 m2 : PageMeta) : bool :=
  andb (andb (andb (Nat.eqb (page_owner_tenant m1) (page_owner_tenant m2))
                   (Nat.eqb (page_owner_namespace m1) (page_owner_namespace m2)))
             (opt_nat_eqb (page_tag m1) (page_tag m2)))
       (opt_lpa_eqb (page_lpa m1) (page_lpa m2)).

Lemma page_meta_eqb_sound : forall m1 m2, page_meta_eqb m1 m2 = true -> m1 = m2.
Proof.
  intros [t1 n1 g1 l1] [t2 n2 g2 l2] H.
  unfold page_meta_eqb in H. simpl in H.
  apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
  apply opt_nat_eqb_sound in H3. apply opt_lpa_eqb_sound in H4.
  subst. reflexivity.
Qed.

Lemma page_meta_eqb_refl : forall m, page_meta_eqb m m = true.
Proof.
  intros [t n g l]. unfold page_meta_eqb. simpl.
  rewrite !Nat.eqb_refl, opt_nat_eqb_refl, opt_lpa_eqb_refl. reflexivity.
Qed.

Definition phys_eqb (x y : PhysAddr) : bool :=
  andb (Nat.eqb (pa_block x) (pa_block y)) (Nat.eqb (pa_page x) (pa_page y)).

Lemma phys_eqb_refl : forall x, phys_eqb x x = true.
Proof.
  intros [b p]. unfold phys_eqb. simpl. rewrite !Nat.eqb_refl. reflexivity.
Qed.

(* "l2p_map s a q points exactly at (b, p)" *)
Definition l2p_isb (s : FTLState) (b : Block) (p : Page) (a : Addr) (q : Page) : bool :=
  match l2p_map s a q with
  | Some pa => andb (Nat.eqb (pa_block pa) b) (Nat.eqb (pa_page pa) p)
  | None => false
  end.

Lemma l2p_isb_sound :
  forall s b p a q, l2p_isb s b p a q = true -> l2p_map s a q = Some (mkPhysAddr b p).
Proof.
  intros s b p a q H. unfold l2p_isb in H.
  destruct (l2p_map s a q) as [pa|] eqn:E; [|discriminate].
  destruct pa as [bb pp]. simpl in H.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════
   Owner (tenant, namespace) enumeration

   [TenantId] and [NamespaceId] are unbounded.  The only finite handle the
   model offers is the labelling of the address space, so the checker
   enumerates the owners that some in-range address carries.  A pair found
   this way is a genuine pair ([exists_over_owners_sound]); a pair *not*
   found this way is simply invisible to the checker, which is why the
   clauses that quantify universally over owners are restricted to
   [observed_owner] in their soundness lemmas.
   ══════════════════════════════════════════════════════════════ *)

Definition observed_owner (s : FTLState) (t : TenantId) (ns : NamespaceId) : Prop :=
  exists a, a < addr_space /\ addr_tenant s a = Some t /\ addr_namespace s a = Some ns.

Definition check_over_owners (s : FTLState) (f : TenantId -> NamespaceId -> bool) : bool :=
  forallb (fun a =>
    match addr_tenant s a with
    | Some t => match addr_namespace s a with
                | Some ns => f t ns
                | None => true
                end
    | None => true
    end) (seq 0 addr_space).

Lemma check_over_owners_sound :
  forall s f t ns,
    check_over_owners s f = true -> observed_owner s t ns -> f t ns = true.
Proof.
  intros s f t ns H [a [Ha [Ht Hn]]]. unfold check_over_owners in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H'. cbn beta in H'.
  rewrite Ht in H'. rewrite Hn in H'. exact H'.
Qed.

Definition exists_over_owners (s : FTLState) (f : TenantId -> NamespaceId -> bool) : bool :=
  existsb (fun a =>
    match addr_tenant s a with
    | Some t => match addr_namespace s a with
                | Some ns => f t ns
                | None => false
                end
    | None => false
    end) (seq 0 addr_space).

Lemma exists_over_owners_sound :
  forall s f, exists_over_owners s f = true -> exists t ns, f t ns = true.
Proof.
  intros s f H. unfold exists_over_owners in H.
  apply existsb_exists in H. destruct H as [a [_ H]]. cbn beta in H.
  destruct (addr_tenant s a) as [t|]; [|discriminate].
  destruct (addr_namespace s a) as [ns|]; [|discriminate].
  exists t, ns. exact H.
Qed.

(* ══════════════════════════════════════════════════════════════
   GROUP (A): clauses whose bounded check is sound for the clause itself
   ══════════════════════════════════════════════════════════════ *)

(* ---- WF0: pages_per_block > 0.  A closed arithmetic fact. ---- *)
Definition check_inv0 (_ : FTLState) : bool := 0 <? pages_per_block.

Lemma check_inv0_sound : forall s, check_inv0 s = true -> WF0 s.
Proof.
  intros s H. unfold WF0. unfold check_inv0 in H.
  apply Nat.ltb_lt in H. exact H.
Qed.

(* ---- WF1: page_state is total on the geometry.  [page_state s b p] is a
   function application, so the witness always exists; the check is a
   formality that also demonstrates the enumeration shape. ---- *)
Definition check_inv1 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p => match page_state s b p with _ => true end)
      (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv1_sound : forall s, check_inv1 s = true -> WF1 s.
Proof.
  intros s _. unfold WF1. intros b p _ _.
  exists (page_state s b p). reflexivity.
Qed.

(* ---- Inv6: free-list blocks are fully erased.  [b] ranges over the finite
   [free_block_list s], [p] over [pages_per_block]: fully decidable. ---- *)
Definition check_inv8 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      andb (match page_state s b p with PS_Empty => true | _ => false end)
           (page_meta_eqb (page_meta s b p) empty_page_meta))
      (seq 0 pages_per_block))
    (free_block_list s).

Lemma check_inv8_sound : forall s, check_inv8 s = true -> Inv6 s.
Proof.
  intros s H. unfold Inv6. intros b Hin p Hp. unfold check_inv8 in H.
  pose proof (forallb_in_elim _ _ _ b H Hin) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  apply andb_true_iff in H2 as [Hst Hmeta].
  split.
  - destruct (page_state s b p); try discriminate. reflexivity.
  - apply page_meta_eqb_sound. exact Hmeta.
Qed.

(* ---- Inv8: free-list blocks are in range.  Finite list: decidable. ---- *)
Definition check_inv10 (s : FTLState) : bool :=
  forallb (fun b => b <? total_blocks) (free_block_list s).

Lemma check_inv10_sound : forall s, check_inv10 s = true -> Inv8 s.
Proof.
  intros s H. unfold Inv8. intros b Hin. unfold check_inv10 in H.
  pose proof (forallb_in_elim _ _ _ b H Hin) as H1. cbn beta in H1.
  apply Nat.ltb_lt in H1. exact H1.
Qed.

(* ---- Inv10: every geometry block is free, open, mapped, or stale.
   The universal is bounded by [total_blocks]; all four disjuncts are
   existentials, and a witness found by a bounded search is a real witness,
   so this check is sound (it is merely incomplete: an open block whose owner
   labels no in-range address, or a mapping from an out-of-range address, is
   not found and the check returns [false]). ---- *)
Definition check_inv12 (s : FTLState) : bool :=
  forallb (fun b =>
    orb (orb (orb
      (inb b (free_block_list s))
      (exists_over_owners s (fun t ns =>
         match open_block s t ns with
         | Some b' => Nat.eqb b' b
         | None => false
         end)))
      (existsb (fun a =>
         existsb (fun p =>
           match l2p_map s a p with
           | Some pa => Nat.eqb (pa_block pa) b
           | None => false
           end) (seq 0 pages_per_block))
         (seq 0 addr_space)))
      (existsb (fun q =>
         match page_state s b q with PS_Invalid => true | _ => false end)
         (seq 0 pages_per_block)))
    (seq 0 total_blocks).

Lemma check_inv12_sound : forall s, check_inv12 s = true -> Inv10 s.
Proof.
  intros s H. unfold Inv10. intros b Hb. unfold check_inv12 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  apply orb_true_iff in H1 as [H1 | Hstale].
  apply orb_true_iff in H1 as [H1 | Hmap].
  apply orb_true_iff in H1 as [Hfree | Hopen].
  - (* free *)
    left. apply inb_sound. exact Hfree.
  - (* open for some observed owner *)
    right. left.
    apply exists_over_owners_sound in Hopen.
    destruct Hopen as [t [ns Hob]].
    destruct (open_block s t ns) as [b'|] eqn:E; [|discriminate].
    apply Nat.eqb_eq in Hob. subst b'.
    exists t, ns. exact E.
  - (* some in-range logical page maps into b *)
    right. right. left.
    apply existsb_exists in Hmap. destruct Hmap as [a [_ Ha]]. cbn beta in Ha.
    apply existsb_exists in Ha. destruct Ha as [p [_ Hp]]. cbn beta in Hp.
    destruct (l2p_map s a p) as [pa|] eqn:E; [|discriminate].
    apply Nat.eqb_eq in Hp.
    exists a, p, pa. split; [exact E | exact Hp].
  - (* holds a stale page *)
    right. right. right.
    apply existsb_exists in Hstale. destruct Hstale as [q [_ Hq]]. cbn beta in Hq.
    exists q. destruct (page_state s b q) eqn:E; try discriminate. reflexivity.
Qed.

(* ---- Inv11: the free list is duplicate-free.  Finite list: decidable. ---- *)
Fixpoint nodupb (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: t => andb (negb (existsb (Nat.eqb x) t)) (nodupb t)
  end.

Lemma nodupb_sound : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|x t IH]; intros H.
  - constructor.
  - simpl in H. apply andb_true_iff in H as [H1 H2].
    constructor.
    + intro Hin. apply negb_true_iff in H1.
      pose proof (inb_complete x t Hin) as Hc. unfold inb in Hc.
      rewrite Hc in H1. discriminate.
    + apply IH. exact H2.
Qed.

Definition check_inv13 (s : FTLState) : bool := nodupb (free_block_list s).

Lemma check_inv13_sound : forall s, check_inv13 s = true -> Inv11 s.
Proof.
  intros s H. unfold Inv11. apply nodupb_sound. exact H.
Qed.

(* ══════════════════════════════════════════════════════════════
   THE SOUND GLOBAL CHECK

   Exactly the six clauses of group (A).  The clauses of group (B) are
   deliberately absent: including them would make [check_invariant s = true]
   a claim the checker cannot back up.
   ══════════════════════════════════════════════════════════════ *)

Definition check_invariant (s : FTLState) : bool :=
  check_inv0 s && check_inv1 s && check_inv8 s &&
  check_inv10 s && check_inv12 s && check_inv13 s.

Theorem check_invariant_sound :
  forall s, check_invariant s = true ->
    WF0 s /\ WF1 s /\ Inv6 s /\ Inv8 s /\ Inv10 s /\ Inv11 s.
Proof.
  intros s H. unfold check_invariant in H.
  apply andb_true_iff in H as [H H13].
  apply andb_true_iff in H as [H H12].
  apply andb_true_iff in H as [H H10].
  apply andb_true_iff in H as [H H8].
  apply andb_true_iff in H as [H0 H1].
  split; [| split; [| split; [| split; [| split]]]].
  - apply check_inv0_sound. exact H0.
  - apply check_inv1_sound. exact H1.
  - apply check_inv8_sound. exact H8.
  - apply check_inv10_sound. exact H10.
  - apply check_inv12_sound. exact H12.
  - apply check_inv13_sound. exact H13.
Qed.

(* ══════════════════════════════════════════════════════════════
   GROUP (B): the remaining 23 conjuncts.

   Each gets the geometry-bounded test one would run on a device, plus a
   Qed-closed soundness lemma against the GEOMETRY-RESTRICTED reading of the
   clause.  The restriction is written out in full in every statement, so
   what is and is not established is visible at the point of use.  None of
   these appears in [check_invariant].
   ══════════════════════════════════════════════════════════════ *)

(* ---- Inv0.  Restricted: only pages inside the geometry are inspected.
   (The existential conclusion is the real one — the witnesses found are
   genuine.) ---- *)
Definition check_inv2 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      match page_state s b p with
      | PS_Valid _ =>
          existsb (fun a =>
            existsb (fun q => l2p_isb s b p a q) (seq 0 pages_per_block))
            (seq 0 addr_space)
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv2_sound :
  forall s, check_inv2 s = true ->
    forall b p d, b < total_blocks -> p < pages_per_block ->
      page_state s b p = PS_Valid d ->
      exists a q, l2p_map s a q = Some (mkPhysAddr b p).
Proof.
  intros s H b p d Hb Hp Hps. unfold check_inv2 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hps in H2.
  apply existsb_exists in H2. destruct H2 as [a [_ Ha]]. cbn beta in Ha.
  apply existsb_exists in Ha. destruct Ha as [q [_ Hq]]. cbn beta in Hq.
  exists a, q. apply l2p_isb_sound. exact Hq.
Qed.

(* ---- Inv1.  Restricted: only in-range (a, p) are inspected, so an
   out-of-geometry entry of [l2p_map] is not ruled out. ---- *)
Definition check_inv3 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some pa =>
          andb (andb (andb (pa_block pa <? total_blocks)
                           (pa_page pa <? pages_per_block))
                     (a <? addr_space))
               (p <? pages_per_block)
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv3_sound :
  forall s, check_inv3 s = true ->
    forall a p pa, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa ->
      pa_block pa < total_blocks /\ pa_page pa < pages_per_block /\
      a < addr_space /\ p < pages_per_block.
Proof.
  intros s H a p pa Ha Hp Hm. unfold check_inv3 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm in H2.
  apply andb_true_iff in H2 as [H2 Hd].
  apply andb_true_iff in H2 as [H2 Hc].
  apply andb_true_iff in H2 as [Hx Hy].
  apply Nat.ltb_lt in Hx. apply Nat.ltb_lt in Hy.
  apply Nat.ltb_lt in Hc. apply Nat.ltb_lt in Hd.
  repeat split; assumption.
Qed.

(* ---- Inv2.  Restricted: injectivity is verified only among in-range
   logical pages. ---- *)
Definition check_inv4 (s : FTLState) : bool :=
  forallb (fun a1 =>
    forallb (fun p1 =>
      forallb (fun a2 =>
        forallb (fun p2 =>
          match l2p_map s a1 p1 with
          | Some pa1 =>
              match l2p_map s a2 p2 with
              | Some pa2 =>
                  if phys_eqb pa1 pa2
                  then andb (Nat.eqb a1 a2) (Nat.eqb p1 p2)
                  else true
              | None => true
              end
          | None => true
          end) (seq 0 pages_per_block))
        (seq 0 addr_space))
      (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv4_sound :
  forall s, check_inv4 s = true ->
    forall a1 p1 a2 p2 pa,
      a1 < addr_space -> p1 < pages_per_block ->
      a2 < addr_space -> p2 < pages_per_block ->
      l2p_map s a1 p1 = Some pa -> l2p_map s a2 p2 = Some pa ->
      a1 = a2 /\ p1 = p2.
Proof.
  intros s H a1 p1 a2 p2 pa Ha1 Hp1 Ha2 Hp2 Hm1 Hm2. unfold check_inv4 in H.
  pose proof (forallb_seq_elim _ _ a1 H Ha1) as A. cbn beta in A.
  pose proof (forallb_seq_elim _ _ p1 A Hp1) as B. cbn beta in B.
  pose proof (forallb_seq_elim _ _ a2 B Ha2) as C. cbn beta in C.
  pose proof (forallb_seq_elim _ _ p2 C Hp2) as D. cbn beta in D.
  rewrite Hm1 in D. rewrite Hm2 in D.
  rewrite phys_eqb_refl in D.
  apply andb_true_iff in D as [D1 D2].
  apply Nat.eqb_eq in D1. apply Nat.eqb_eq in D2.
  split; assumption.
Qed.

(* ---- Inv3 (forward OOB agreement).  Restricted to in-range (a, p). ---- *)
Definition check_inv5 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some pa =>
          match page_state s (pa_block pa) (pa_page pa) with
          | PS_Valid _ =>
              match page_lpa (page_meta s (pa_block pa) (pa_page pa)) with
              | Some (a', p') => andb (Nat.eqb a' a) (Nat.eqb p' p)
              | None => false
              end
          | _ => true
          end
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv5_sound :
  forall s, check_inv5 s = true ->
    forall a p pa d, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa ->
      page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
      page_lpa (page_meta s (pa_block pa) (pa_page pa)) = Some (a, p).
Proof.
  intros s H a p pa d Ha Hp Hm Hst. unfold check_inv5 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm in H2. rewrite Hst in H2.
  destruct (page_lpa (page_meta s (pa_block pa) (pa_page pa)))
    as [[a' p']|] eqn:E; [|discriminate].
  apply andb_true_iff in H2 as [E1 E2].
  apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. subst. reflexivity.
Qed.

(* ---- Inv4 (reverse OOB agreement).  Restricted to in-range (b, q). ---- *)
Definition check_inv6 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun q =>
      match page_state s b q with
      | PS_Valid _ =>
          match page_lpa (page_meta s b q) with
          | Some (a, p) =>
              match l2p_map s a p with
              | Some pa => andb (Nat.eqb (pa_block pa) b) (Nat.eqb (pa_page pa) q)
              | None => false
              end
          | None => true
          end
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv6_sound :
  forall s, check_inv6 s = true ->
    forall a p b q d, b < total_blocks -> q < pages_per_block ->
      page_state s b q = PS_Valid d ->
      page_lpa (page_meta s b q) = Some (a, p) ->
      l2p_map s a p = Some (mkPhysAddr b q).
Proof.
  intros s H a p b q d Hb Hq Hst Hlpa. unfold check_inv6 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ q H1 Hq) as H2. cbn beta in H2.
  rewrite Hst in H2. rewrite Hlpa in H2.
  apply l2p_isb_sound. unfold l2p_isb. exact H2.
Qed.

(* ---- Inv5.  Restricted to in-range (a, p). ---- *)
Definition check_inv7 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some pa => negb (inb (pa_block pa) (free_block_list s))
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv7_sound :
  forall s, check_inv7 s = true ->
    forall a p pa, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa -> ~ In (pa_block pa) (free_block_list s).
Proof.
  intros s H a p pa Ha Hp Hm. unfold check_inv7 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm in H2. apply inb_false_sound. exact H2.
Qed.

(* ---- Inv7.  Restricted to in-range (a, p). ---- *)
Definition check_inv9 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some pa =>
          match page_state s (pa_block pa) (pa_page pa) with
          | PS_Valid _ =>
              match addr_tenant s a with
              | Some t =>
                  match addr_namespace s a with
                  | Some ns =>
                      andb (Nat.eqb (page_owner_tenant
                                       (page_meta s (pa_block pa) (pa_page pa))) t)
                           (Nat.eqb (page_owner_namespace
                                       (page_meta s (pa_block pa) (pa_page pa))) ns)
                  | None => true
                  end
              | None => true
              end
          | _ => true
          end
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv9_sound :
  forall s, check_inv9 s = true ->
    forall a p pa d t ns, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa ->
      page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
      addr_tenant s a = Some t ->
      addr_namespace s a = Some ns ->
      page_owner_tenant (page_meta s (pa_block pa) (pa_page pa)) = t /\
      page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)) = ns.
Proof.
  intros s H a p pa d t ns Ha Hp Hm Hst Ht Hn. unfold check_inv9 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm, Hst, Ht, Hn in H2.
  apply andb_true_iff in H2 as [E1 E2].
  apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. split; assumption.
Qed.

(* ---- Inv9.  Restricted to in-range (b, p). ---- *)
Definition check_inv11 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      match page_state s b p with
      | PS_Valid _ =>
          match page_tag (page_meta s b p) with Some _ => true | None => false end
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv11_sound :
  forall s, check_inv11 s = true ->
    forall b p d, b < total_blocks -> p < pages_per_block ->
      page_state s b p = PS_Valid d ->
      exists tag, page_tag (page_meta s b p) = Some tag.
Proof.
  intros s H b p d Hb Hp Hst. unfold check_inv11 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hst in H2.
  destruct (page_tag (page_meta s b p)) as [tag|] eqn:E; [|discriminate].
  exists tag. reflexivity.
Qed.

(* ---- Inv12.  NOT soundly decidable even in a restricted form that keeps
   the hypothesis as stated: the hypothesis "exists p, page_role s b p =
   Some RMeta" ranges over all page offsets, and a bounded search for it can
   miss a witness above [pages_per_block], letting the implication pass
   vacuously.  The lemma therefore restricts the HYPOTHESIS to an in-range
   witness; the conclusion is the real (unrestricted) one. ---- *)
Definition check_inv14 (s : FTLState) : bool :=
  forallb (fun b =>
    if existsb (fun p =>
         match page_role s b p with Some RMeta => true | _ => false end)
         (seq 0 pages_per_block)
    then orb
      (existsb (fun a =>
         existsb (fun p =>
           match l2p_map s a p with
           | Some pa => Nat.eqb (pa_block pa) b
           | None => false
           end) (seq 0 pages_per_block))
         (seq 0 addr_space))
      (existsb (fun q =>
         match page_state s b q with PS_Invalid => true | _ => false end)
         (seq 0 pages_per_block))
    else true)
    (seq 0 total_blocks).

Lemma check_inv14_sound :
  forall s, check_inv14 s = true ->
    forall b, b < total_blocks ->
      (exists p, p < pages_per_block /\ page_role s b p = Some RMeta) ->
      (exists a p pa, l2p_map s a p = Some pa /\ pa_block pa = b) \/
      (exists q, page_state s b q = PS_Invalid).
Proof.
  intros s H b Hb [p [Hp Hrole]]. unfold check_inv14 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  assert (Hex : existsb (fun p0 =>
                  match page_role s b p0 with Some RMeta => true | _ => false end)
                  (seq 0 pages_per_block) = true).
  { apply existsb_exists. exists p. split.
    - apply in_seq. lia.
    - cbn beta. rewrite Hrole. reflexivity. }
  rewrite Hex in H1.
  apply orb_true_iff in H1 as [Hmap | Hstale].
  - left.
    apply existsb_exists in Hmap. destruct Hmap as [a [_ Ha]]. cbn beta in Ha.
    apply existsb_exists in Ha. destruct Ha as [q [_ Hq]]. cbn beta in Hq.
    destruct (l2p_map s a q) as [pa|] eqn:E; [|discriminate].
    apply Nat.eqb_eq in Hq.
    exists a, q, pa. split; [exact E | exact Hq].
  - right.
    apply existsb_exists in Hstale. destruct Hstale as [q [_ Hq]]. cbn beta in Hq.
    exists q. destruct (page_state s b q) eqn:E; try discriminate. reflexivity.
Qed.

(* ---- Inv13.  Restricted to in-range (b, p). ---- *)
Definition check_inv15 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      match page_state s b p with
      | PS_Valid _ =>
          match page_role s b p with Some RData => true | _ => false end
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv15_sound :
  forall s, check_inv15 s = true ->
    forall b p d, b < total_blocks -> p < pages_per_block ->
      page_state s b p = PS_Valid d -> page_role s b p = Some RData.
Proof.
  intros s H b p d Hb Hp Hst. unfold check_inv15 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hst in H2.
  destruct (page_role s b p) as [[|]|] eqn:E; try discriminate. reflexivity.
Qed.

(* ---- Inv14.  Restricted to in-range (b, p). ---- *)
Definition check_inv16 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      match page_role s b p with
      | Some RData =>
          match page_state s b p with PS_Valid _ => true | _ => false end
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv16_sound :
  forall s, check_inv16 s = true ->
    forall b p, b < total_blocks -> p < pages_per_block ->
      page_role s b p = Some RData -> exists d, page_state s b p = PS_Valid d.
Proof.
  intros s H b p Hb Hp Hrole. unfold check_inv16 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hrole in H2.
  destruct (page_state s b p) as [| |d] eqn:E; try discriminate.
  exists d. reflexivity.
Qed.

(* ---- Inv15.  Restricted to in-range (b, p). ---- *)
Definition check_inv17 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      match page_role s b p with
      | Some RMeta =>
          match page_state s b p with PS_Empty => false | _ => true end
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv17_sound :
  forall s, check_inv17 s = true ->
    forall b p, b < total_blocks -> p < pages_per_block ->
      page_role s b p = Some RMeta -> page_state s b p <> PS_Empty.
Proof.
  intros s H b p Hb Hp Hrole. unfold check_inv17 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hrole in H2.
  intro Hst. rewrite Hst in H2. discriminate.
Qed.

(* ---- Inv16.  Restricted to in-range (b, p). ---- *)
Definition check_inv18 (s : FTLState) : bool :=
  forallb (fun b =>
    forallb (fun p =>
      match page_state s b p with
      | PS_Empty =>
          match page_role s b p with None => true | Some _ => false end
      | _ => true
      end) (seq 0 pages_per_block))
    (seq 0 total_blocks).

Lemma check_inv18_sound :
  forall s, check_inv18 s = true ->
    forall b p, b < total_blocks -> p < pages_per_block ->
      page_state s b p = PS_Empty -> page_role s b p = None.
Proof.
  intros s H b p Hb Hp Hst. unfold check_inv18 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hst in H2.
  destruct (page_role s b p) as [r|] eqn:E; [discriminate | reflexivity].
Qed.

(* ---- Inv17.  Restricted to b < total_blocks. ---- *)
Definition check_inv19 (s : FTLState) : bool :=
  forallb (fun b =>
    if free_block s b
    then andb (match block_tenant s b with None => true | Some _ => false end)
              (match block_namespace s b with None => true | Some _ => false end)
    else true)
    (seq 0 total_blocks).

Lemma check_inv19_sound :
  forall s, check_inv19 s = true ->
    forall b, b < total_blocks -> free_block s b = true ->
      block_tenant s b = None /\ block_namespace s b = None.
Proof.
  intros s H b Hb Hf. unfold check_inv19 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  rewrite Hf in H1.
  apply andb_true_iff in H1 as [E1 E2].
  split.
  - destruct (block_tenant s b); [discriminate | reflexivity].
  - destruct (block_namespace s b); [discriminate | reflexivity].
Qed.

(* ---- Inv18.  Restricted to in-range (a, p). ---- *)
Definition check_inv20 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some pa =>
          andb (opt_nat_eqb (block_tenant s (pa_block pa)) (addr_tenant s a))
               (opt_nat_eqb (block_namespace s (pa_block pa)) (addr_namespace s a))
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv20_sound :
  forall s, check_inv20 s = true ->
    forall a p pa, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa ->
      block_tenant s (pa_block pa) = addr_tenant s a /\
      block_namespace s (pa_block pa) = addr_namespace s a.
Proof.
  intros s H a p pa Ha Hp Hm. unfold check_inv20 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm in H2.
  apply andb_true_iff in H2 as [E1 E2].
  split; apply opt_nat_eqb_sound; assumption.
Qed.

(* ---- Inv19.  The region table is indexed by a bare [nat] with no size
   constant in the model; the index is bounded by [total_blocks], the natural
   hardware-side region granularity, and the lemma restricts Inv19 to
   i < total_blocks accordingly. ---- *)
Definition check_inv21 (s : FTLState) : bool :=
  forallb (fun i =>
    match region_table s i with
    | Some r => region_start r + region_len r <=? addr_space
    | None => true
    end) (seq 0 total_blocks).

Lemma check_inv21_sound :
  forall s, check_inv21 s = true ->
    forall i r, i < total_blocks -> region_table s i = Some r ->
      region_start r + region_len r <= addr_space.
Proof.
  intros s H i r Hi Hr. unfold check_inv21 in H.
  pose proof (forallb_seq_elim _ _ i H Hi) as H1. cbn beta in H1.
  rewrite Hr in H1. apply Nat.leb_le. exact H1.
Qed.

(* ---- Inv20.  Restricted to owner pairs that some in-range address is
   labelled with ([observed_owner]); the inner uniqueness quantifier is
   restricted the same way.  A frontier opened for an owner that labels no
   in-range address is invisible to this check. ---- *)
Definition check_inv22 (s : FTLState) : bool :=
  check_over_owners s (fun t ns =>
    match open_block s t ns with
    | Some b =>
        andb (andb (andb (andb (andb (andb (andb
          (b <? total_blocks)
          (negb (inb b (free_block_list s))))
          (negb (free_block s b)))
          (block_open s b))
          (write_ptr s t ns <=? pages_per_block))
          (match block_tenant s b with
           | None => true | Some t' => Nat.eqb t' t end))
          (match block_namespace s b with
           | None => true | Some n' => Nat.eqb n' ns end))
          (check_over_owners s (fun t' ns' =>
             match open_block s t' ns' with
             | Some b' =>
                 if Nat.eqb b' b
                 then andb (Nat.eqb t' t) (Nat.eqb ns' ns)
                 else true
             | None => true
             end))
    | None => true
    end).

Lemma check_inv22_sound :
  forall s, check_inv22 s = true ->
    forall t ns b, observed_owner s t ns -> open_block s t ns = Some b ->
      b < total_blocks /\ ~ In b (free_block_list s) /\
      free_block s b = false /\ block_open s b = true /\
      write_ptr s t ns <= pages_per_block /\
      (block_tenant s b = None \/ block_tenant s b = Some t) /\
      (block_namespace s b = None \/ block_namespace s b = Some ns) /\
      (forall t' ns', observed_owner s t' ns' ->
                      open_block s t' ns' = Some b -> t' = t /\ ns' = ns).
Proof.
  intros s H t ns b Hobs Hob. unfold check_inv22 in H.
  pose proof (check_over_owners_sound s _ t ns H Hobs) as H1. cbn beta in H1.
  rewrite Hob in H1.
  apply andb_true_iff in H1 as [H1 C8].
  apply andb_true_iff in H1 as [H1 C7].
  apply andb_true_iff in H1 as [H1 C6].
  apply andb_true_iff in H1 as [H1 C5].
  apply andb_true_iff in H1 as [H1 C4].
  apply andb_true_iff in H1 as [H1 C3].
  apply andb_true_iff in H1 as [C1 C2].
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - apply Nat.ltb_lt. exact C1.
  - apply inb_false_sound. exact C2.
  - apply negb_true_iff in C3. exact C3.
  - exact C4.
  - apply Nat.leb_le. exact C5.
  - destruct (block_tenant s b) as [t'|] eqn:E.
    + right. apply Nat.eqb_eq in C6. subst t'. reflexivity.
    + left. reflexivity.
  - destruct (block_namespace s b) as [n'|] eqn:E.
    + right. apply Nat.eqb_eq in C7. subst n'. reflexivity.
    + left. reflexivity.
  - intros t' ns' Hobs' Hob'.
    pose proof (check_over_owners_sound s _ t' ns' C8 Hobs') as H2. cbn beta in H2.
    rewrite Hob' in H2. rewrite Nat.eqb_refl in H2.
    apply andb_true_iff in H2 as [E1 E2].
    apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. split; assumption.
Qed.

(* ---- Inv21.  Restricted to observed owners and in-range page offsets. ---- *)
Definition check_inv23 (s : FTLState) : bool :=
  check_over_owners s (fun t ns =>
    match open_block s t ns with
    | Some b =>
        forallb (fun q =>
          if write_ptr s t ns <=? q
          then andb (match page_state s b q with PS_Empty => true | _ => false end)
                    (page_meta_eqb (page_meta s b q) empty_page_meta)
          else true) (seq 0 pages_per_block)
    | None => true
    end).

Lemma check_inv23_sound :
  forall s, check_inv23 s = true ->
    forall t ns b q, observed_owner s t ns -> open_block s t ns = Some b ->
      write_ptr s t ns <= q -> q < pages_per_block ->
      page_state s b q = PS_Empty /\ page_meta s b q = empty_page_meta.
Proof.
  intros s H t ns b q Hobs Hob Hwp Hq. unfold check_inv23 in H.
  pose proof (check_over_owners_sound s _ t ns H Hobs) as H1. cbn beta in H1.
  rewrite Hob in H1.
  pose proof (forallb_seq_elim _ _ q H1 Hq) as H2. cbn beta in H2.
  assert (Hleb : (write_ptr s t ns <=? q) = true) by (apply Nat.leb_le; exact Hwp).
  rewrite Hleb in H2.
  apply andb_true_iff in H2 as [E1 E2].
  split.
  - destruct (page_state s b q); try discriminate. reflexivity.
  - apply page_meta_eqb_sound. exact E2.
Qed.

(* ---- Inv22.  Restricted to in-range (a, p). ---- *)
Definition check_inv24 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some pa =>
          match page_state s (pa_block pa) (pa_page pa) with
          | PS_Valid _ => true
          | _ => false
          end
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv24_sound :
  forall s, check_inv24 s = true ->
    forall a p pa, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa ->
      exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d.
Proof.
  intros s H a p pa Ha Hp Hm. unfold check_inv24 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm in H2.
  destruct (page_state s (pa_block pa) (pa_page pa)) as [| |d] eqn:E;
    try discriminate.
  exists d. reflexivity.
Qed.

(* ---- Inv23.  Restricted to b < total_blocks.  The existential conclusion
   is genuine: a pair found by [exists_over_owners] is a real witness. ---- *)
Definition check_inv25 (s : FTLState) : bool :=
  forallb (fun b =>
    if block_open s b
    then exists_over_owners s (fun t ns =>
           match open_block s t ns with
           | Some b' => Nat.eqb b' b
           | None => false
           end)
    else true)
    (seq 0 total_blocks).

Lemma check_inv25_sound :
  forall s, check_inv25 s = true ->
    forall b, b < total_blocks -> block_open s b = true ->
      exists t ns, open_block s t ns = Some b.
Proof.
  intros s H b Hb Hbo. unfold check_inv25 in H.
  pose proof (forallb_seq_elim _ _ b H Hb) as H1. cbn beta in H1.
  rewrite Hbo in H1.
  apply exists_over_owners_sound in H1. destruct H1 as [t [ns Hf]].
  destruct (open_block s t ns) as [b'|] eqn:E; [|discriminate].
  apply Nat.eqb_eq in Hf. subst b'.
  exists t, ns. exact E.
Qed.

(* ---- Inv24.  The "list -> bitmap" half is checked in full (the free list
   is finite, so that direction is genuinely decided); the "bitmap -> list"
   half is restricted to b < total_blocks, since [free_block] is a function
   on all of [nat]. ---- *)
Definition check_inv26 (s : FTLState) : bool :=
  andb
    (forallb (fun b => implb (free_block s b) (inb b (free_block_list s)))
       (seq 0 total_blocks))
    (forallb (fun b => free_block s b) (free_block_list s)).

Lemma check_inv26_sound :
  forall s, check_inv26 s = true ->
    (forall b, b < total_blocks -> free_block s b = true -> In b (free_block_list s)) /\
    (forall b, In b (free_block_list s) -> free_block s b = true).
Proof.
  intros s H. unfold check_inv26 in H.
  apply andb_true_iff in H as [HA HB].
  split.
  - intros b Hb Hf.
    pose proof (forallb_seq_elim _ _ b HA Hb) as H1. cbn beta in H1.
    rewrite Hf in H1. apply inb_sound. exact H1.
  - intros b Hin.
    pose proof (forallb_in_elim _ _ _ b HB Hin) as H1. cbn beta in H1. exact H1.
Qed.

(* ---- Inv25.  Restricted to observed owners and in-range page offsets. ---- *)
Definition check_inv27 (s : FTLState) : bool :=
  check_over_owners s (fun t ns =>
    match open_block s t ns with
    | Some b =>
        forallb (fun q =>
          if q <? write_ptr s t ns
          then negb (match page_state s b q with PS_Empty => true | _ => false end)
          else true) (seq 0 pages_per_block)
    | None => true
    end).

Lemma check_inv27_sound :
  forall s, check_inv27 s = true ->
    forall t ns b q, observed_owner s t ns -> open_block s t ns = Some b ->
      q < write_ptr s t ns -> q < pages_per_block ->
      page_state s b q <> PS_Empty.
Proof.
  intros s H t ns b q Hobs Hob Hwp Hq. unfold check_inv27 in H.
  pose proof (check_over_owners_sound s _ t ns H Hobs) as H1. cbn beta in H1.
  rewrite Hob in H1.
  pose proof (forallb_seq_elim _ _ q H1 Hq) as H2. cbn beta in H2.
  assert (Hltb : (q <? write_ptr s t ns) = true) by (apply Nat.ltb_lt; exact Hwp).
  rewrite Hltb in H2.
  intro Hst. rewrite Hst in H2. simpl in H2. discriminate.
Qed.

(* ---- Inv26.  Restricted to in-range (a, p). ---- *)
Definition check_inv28 (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match l2p_map s a p with
      | Some _ =>
          andb (match addr_tenant s a with Some _ => true | None => false end)
               (match addr_namespace s a with Some _ => true | None => false end)
      | None => true
      end) (seq 0 pages_per_block))
    (seq 0 addr_space).

Lemma check_inv28_sound :
  forall s, check_inv28 s = true ->
    forall a p pa, a < addr_space -> p < pages_per_block ->
      l2p_map s a p = Some pa ->
      (exists t, addr_tenant s a = Some t) /\
      (exists ns, addr_namespace s a = Some ns).
Proof.
  intros s H a p pa Ha Hp Hm. unfold check_inv28 in H.
  pose proof (forallb_seq_elim _ _ a H Ha) as H1. cbn beta in H1.
  pose proof (forallb_seq_elim _ _ p H1 Hp) as H2. cbn beta in H2.
  rewrite Hm in H2.
  apply andb_true_iff in H2 as [E1 E2].
  split.
  - destruct (addr_tenant s a) as [t|] eqn:E; [exists t; reflexivity | discriminate].
  - destruct (addr_namespace s a) as [ns|] eqn:E; [exists ns; reflexivity | discriminate].
Qed.

(* ══════════════════════════════════════════════════════════════
   COMPLETENESS: the direction that makes a [false] verdict a refutation

   Everything above answers "what does [true] certify?".  This section
   answers the question the module actually exists to answer: "what does
   [false] mean?".  For each clause we prove

       check_invN s = true   is IMPLIED BY   Inv_N s,

   whose contrapositive is [check_invN s = false -> ~ Inv_N s]: a rejection
   is a genuine refutation, never a false alarm.

   Why this direction survives unbounded quantification while soundness did
   not: a bounded check tests finitely many points, and the clause holds at
   *every* point, so it holds at the tested ones.  Where a check performs a
   bounded existential SEARCH, completeness needs the real witness to lie in
   the searched range, which the rest of the invariant supplies:
     - Inv1 bounds every witness coming out of [l2p_map] ([l2p_in_geometry]),
       which is what the searches in [check_inv2], [check_inv12_c] and
       [check_inv14] need;
     - Inv13 and Inv15 place [check_inv14]'s stale-page witness inside the
       geometry (a page with role [RMeta] is not empty by Inv15 and not valid
       by Inv13, hence invalid, and its offset is the in-range one the guard
       just found);
     - Inv20 turns "b is open for some owner" into the bounded test
       [block_open s b], which is what [check_inv12_c] and [check_inv25_c]
       need.

   TWO CLAUSES NEED A DIFFERENT TEST FOR THIS DIRECTION.  [check_inv12] and
   [check_inv25] as written above locate the frontier by enumerating owner
   pairs reachable from [addr_tenant]/[addr_namespace], which is what makes
   them SOUND.  They are not complete: a block opened for a tenant that
   labels no in-range address — a legitimate state, e.g. [empty_state] with
   one block opened and nothing yet written — makes the enumeration come up
   empty and the check return [false] on a state that satisfies the
   invariant.  That would be a false alarm, so those two checks must not go
   into the refutation instrument.  [check_inv12_c] and [check_inv25_c]
   below replace the owner enumeration by [block_open], which Inv20
   guarantees mirrors [open_block]; they are complete, and they are the
   variants [check_bounded_all] uses.  ([check_inv12_c] additionally carries
   a fifth disjunct, "every in-range page of b is empty", which closes the
   one remaining gap: Inv10's stale-page witness [exists q, page_state s b q
   = PS_Invalid] has no bound on [q], so a stale page at an offset beyond
   [pages_per_block] is invisible; whenever it is invisible every in-range
   page is empty or is covered by one of the earlier disjuncts.)
   ══════════════════════════════════════════════════════════════ *)

Lemma forallb_seq_intro :
  forall (f : nat -> bool) (n : nat),
    (forall x, x < n -> f x = true) -> forallb f (seq 0 n) = true.
Proof.
  intros f n H. apply forallb_forall. intros x Hx.
  apply in_seq in Hx. apply H. lia.
Qed.

Lemma existsb_seq_intro :
  forall (f : nat -> bool) (n x : nat),
    x < n -> f x = true -> existsb f (seq 0 n) = true.
Proof.
  intros f n x Hx Hf. apply existsb_exists.
  exists x. split; [apply in_seq; lia | exact Hf].
Qed.

Lemma forallb_false_elim :
  forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros A f l. induction l as [|y t IH]; simpl; intros H.
  - discriminate.
  - destruct (f y) eqn:Ey.
    + simpl in H. destruct (IH H) as [x [Hin Hf]].
      exists x. split; [right; exact Hin | exact Hf].
    + exists y. split; [left; reflexivity | exact Ey].
Qed.

Lemma not_in_inb : forall b l, ~ In b l -> inb b l = false.
Proof.
  intros b l H. destruct (inb b l) eqn:E; [|reflexivity].
  exfalso. apply H. apply inb_sound. exact E.
Qed.

Lemma nodupb_complete : forall l, NoDup l -> nodupb l = true.
Proof.
  induction l as [|x t IH]; intros H; [reflexivity|].
  inversion H as [|y ys Hnin Hnd]; subst.
  simpl. rewrite IH by exact Hnd. rewrite andb_true_r.
  apply negb_true_iff.
  pose proof (not_in_inb x t Hnin) as Hc. unfold inb in Hc. exact Hc.
Qed.

Lemma phys_eqb_sound : forall x y, phys_eqb x y = true -> x = y.
Proof.
  intros [b1 p1] [b2 p2] H. unfold phys_eqb in H. simpl in H.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma l2p_isb_complete :
  forall s b p a q,
    l2p_map s a q = Some (mkPhysAddr b p) -> l2p_isb s b p a q = true.
Proof.
  intros s b p a q H. unfold l2p_isb. rewrite H. simpl.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

(* Inv1 is what puts every witness produced by [l2p_map] inside the range
   the bounded searches actually scan. *)
Lemma l2p_in_geometry :
  forall s a p pa, Inv1 s -> l2p_map s a p = Some pa ->
    a < addr_space /\ p < pages_per_block.
Proof.
  intros s a p pa H3 Hm. destruct (H3 a p pa Hm) as [_ [_ [Ha Hp]]].
  split; assumption.
Qed.

Lemma check_over_owners_intro :
  forall s f, (forall t ns, f t ns = true) -> check_over_owners s f = true.
Proof.
  intros s f H. unfold check_over_owners.
  apply forallb_seq_intro. intros a _. cbn beta.
  destruct (addr_tenant s a); [|reflexivity].
  destruct (addr_namespace s a); [|reflexivity].
  apply H.
Qed.

(* ---- Per-clause completeness ---- *)

Lemma check_inv0_complete : forall s, WF0 s -> check_inv0 s = true.
Proof.
  intros s H. unfold check_inv0. apply Nat.ltb_lt. exact H.
Qed.

Lemma check_inv1_complete : forall s, WF1 s -> check_inv1 s = true.
Proof.
  intros s _. unfold check_inv1.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_state s b p); reflexivity.
Qed.

Lemma check_inv2_complete :
  forall s, Inv0 s -> Inv1 s -> check_inv2 s = true.
Proof.
  intros s H2 H3. unfold check_inv2.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_state s b p) as [| |d] eqn:E; try reflexivity.
  destruct (H2 b p d E) as [a [q Hm]].
  destruct (l2p_in_geometry s a q (mkPhysAddr b p) H3 Hm) as [Ha Hq].
  apply (existsb_seq_intro _ _ a Ha). cbn beta.
  apply (existsb_seq_intro _ _ q Hq). cbn beta.
  apply l2p_isb_complete. exact Hm.
Qed.

Lemma check_inv3_complete : forall s, Inv1 s -> check_inv3 s = true.
Proof.
  intros s H3. unfold check_inv3.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  destruct (H3 a p pa E) as [Hb [Hpg [Ha' Hp']]].
  apply Nat.ltb_lt in Hb. apply Nat.ltb_lt in Hpg.
  apply Nat.ltb_lt in Ha'. apply Nat.ltb_lt in Hp'.
  rewrite Hb, Hpg, Ha', Hp'. reflexivity.
Qed.

Lemma check_inv4_complete : forall s, Inv2 s -> check_inv4 s = true.
Proof.
  intros s H4. unfold check_inv4.
  apply forallb_seq_intro. intros a1 _. cbn beta.
  apply forallb_seq_intro. intros p1 _. cbn beta.
  apply forallb_seq_intro. intros a2 _. cbn beta.
  apply forallb_seq_intro. intros p2 _. cbn beta.
  destruct (l2p_map s a1 p1) as [pa1|] eqn:E1; [|reflexivity].
  destruct (l2p_map s a2 p2) as [pa2|] eqn:E2; [|reflexivity].
  destruct (phys_eqb pa1 pa2) eqn:Eq; [|reflexivity].
  apply phys_eqb_sound in Eq. subst pa2.
  destruct (H4 a1 p1 a2 p2 pa1 E1 E2) as [Ha Hp]. subst.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma check_inv5_complete : forall s, Inv3 s -> check_inv5 s = true.
Proof.
  intros s H5. unfold check_inv5.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  destruct (page_state s (pa_block pa) (pa_page pa)) as [| |d] eqn:Est;
    try reflexivity.
  pose proof (H5 a p pa d E Est) as Hl.
  destruct (page_lpa (page_meta s (pa_block pa) (pa_page pa)))
    as [[a' p']|] eqn:El; [|discriminate].
  inversion Hl. subst. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma check_inv6_complete : forall s, Inv4 s -> check_inv6 s = true.
Proof.
  intros s H6. unfold check_inv6.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros q _. cbn beta.
  destruct (page_state s b q) as [| |d] eqn:Est; try reflexivity.
  destruct (page_lpa (page_meta s b q)) as [[a p]|] eqn:El; [|reflexivity].
  pose proof (H6 a p b q d Est El) as Hm.
  destruct (l2p_map s a p) as [pa|] eqn:E2; [|discriminate].
  inversion Hm. subst. simpl. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma check_inv7_complete : forall s, Inv5 s -> check_inv7 s = true.
Proof.
  intros s H7. unfold check_inv7.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  rewrite (not_in_inb _ _ (H7 a p pa E)). reflexivity.
Qed.

Lemma check_inv8_complete : forall s, Inv6 s -> check_inv8 s = true.
Proof.
  intros s H8. unfold check_inv8.
  apply forallb_forall. intros b Hin. cbn beta.
  apply forallb_seq_intro. intros p Hp. cbn beta.
  destruct (H8 b Hin p Hp) as [Hst Hmeta].
  rewrite Hst, Hmeta, page_meta_eqb_refl. reflexivity.
Qed.

Lemma check_inv9_complete : forall s, Inv7 s -> check_inv9 s = true.
Proof.
  intros s H9. unfold check_inv9.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  destruct (page_state s (pa_block pa) (pa_page pa)) as [| |d] eqn:Est;
    try reflexivity.
  destruct (addr_tenant s a) as [t|] eqn:Et; [|reflexivity].
  destruct (addr_namespace s a) as [ns|] eqn:En; [|reflexivity].
  destruct (H9 a p pa d t ns E Est Et En) as [Ho1 Ho2].
  rewrite Ho1, Ho2, !Nat.eqb_refl. reflexivity.
Qed.

Lemma check_inv10_complete : forall s, Inv8 s -> check_inv10 s = true.
Proof.
  intros s H10. unfold check_inv10.
  apply forallb_forall. intros b Hin. cbn beta.
  apply Nat.ltb_lt. apply H10. exact Hin.
Qed.

Lemma check_inv11_complete : forall s, Inv9 s -> check_inv11 s = true.
Proof.
  intros s H11. unfold check_inv11.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_state s b p) as [| |d] eqn:E; try reflexivity.
  destruct (H11 b p d E) as [tag Ht]. rewrite Ht. reflexivity.
Qed.

(* The complete rendering of Inv10: [block_open] in place of the owner
   enumeration (Inv20 makes it a faithful stand-in), and a fifth disjunct
   "every in-range page of b is empty" that absorbs the case in which the
   stale-page witness sits beyond [pages_per_block].  Not sound for Inv10 on
   its own — that is what [check_inv12] above is for. *)
Definition check_inv12_c (s : FTLState) : bool :=
  forallb (fun b =>
    orb (orb (orb (orb
      (inb b (free_block_list s))
      (block_open s b))
      (existsb (fun a =>
         existsb (fun p =>
           match l2p_map s a p with
           | Some pa => Nat.eqb (pa_block pa) b
           | None => false
           end) (seq 0 pages_per_block))
         (seq 0 addr_space)))
      (existsb (fun q =>
         match page_state s b q with PS_Invalid => true | _ => false end)
         (seq 0 pages_per_block)))
      (forallb (fun q =>
         match page_state s b q with PS_Empty => true | _ => false end)
         (seq 0 pages_per_block)))
    (seq 0 total_blocks).

Lemma check_inv12_c_complete :
  forall s, Inv0 s -> Inv1 s -> check_inv12_c s = true.
Proof.
  intros s H2 H3. unfold check_inv12_c.
  apply forallb_seq_intro. intros b _. cbn beta.
  destruct (forallb (fun q =>
              match page_state s b q with PS_Empty => true | _ => false end)
              (seq 0 pages_per_block)) eqn:Eall.
  - apply orb_true_r.
  - rewrite orb_false_r.
    apply forallb_false_elim in Eall. destruct Eall as [q [Hqin Hfq]].
    cbn beta in Hfq. apply in_seq in Hqin.
    destruct (page_state s b q) as [| |d] eqn:Est; [discriminate Hfq | |].
    + (* stale, and its offset is in range *)
      apply orb_true_iff. right.
      apply (existsb_seq_intro _ _ q); [lia|]. cbn beta.
      rewrite Est. reflexivity.
    + (* live: Inv0 gives a mapping, Inv1 puts it in range *)
      apply orb_true_iff. left. apply orb_true_iff. right.
      destruct (H2 b q d Est) as [a [q' Hm]].
      destruct (l2p_in_geometry s a q' (mkPhysAddr b q) H3 Hm) as [Ha Hq'].
      apply (existsb_seq_intro _ _ a Ha). cbn beta.
      apply (existsb_seq_intro _ _ q' Hq'). cbn beta.
      rewrite Hm. simpl. apply Nat.eqb_refl.
Qed.

Lemma check_inv13_complete : forall s, Inv11 s -> check_inv13 s = true.
Proof.
  intros s H13. unfold check_inv13. apply nodupb_complete. exact H13.
Qed.

(* Inv12's own conclusion is not needed: whenever the bounded guard fires,
   Inv15 says the page is not empty and Inv13 says it is not valid, so it is
   stale — at an offset the guard already certified to be in range. *)
Lemma check_inv14_complete :
  forall s, Inv13 s -> Inv15 s -> check_inv14 s = true.
Proof.
  intros s H15 H17. unfold check_inv14.
  apply forallb_seq_intro. intros b _. cbn beta.
  destruct (existsb (fun p =>
              match page_role s b p with Some RMeta => true | _ => false end)
              (seq 0 pages_per_block)) eqn:Eg; [|reflexivity].
  apply existsb_exists in Eg. destruct Eg as [p [Hpin Hr]]. cbn beta in Hr.
  apply in_seq in Hpin.
  destruct (page_role s b p) as [[|]|] eqn:Er; try discriminate.
  pose proof (H17 b p Er) as Hne.
  apply orb_true_iff. right.
  apply (existsb_seq_intro _ _ p); [lia|]. cbn beta.
  destruct (page_state s b p) as [| |d] eqn:Est.
  - exfalso. apply Hne. reflexivity.
  - reflexivity.
  - exfalso. pose proof (H15 b p d Est) as Hrd.
    rewrite Er in Hrd. discriminate.
Qed.

Lemma check_inv15_complete : forall s, Inv13 s -> check_inv15 s = true.
Proof.
  intros s H15. unfold check_inv15.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_state s b p) as [| |d] eqn:E; try reflexivity.
  rewrite (H15 b p d E). reflexivity.
Qed.

Lemma check_inv16_complete : forall s, Inv14 s -> check_inv16 s = true.
Proof.
  intros s H16. unfold check_inv16.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_role s b p) as [[|]|] eqn:E; try reflexivity.
  destruct (H16 b p E) as [d Hd]. rewrite Hd. reflexivity.
Qed.

Lemma check_inv17_complete : forall s, Inv15 s -> check_inv17 s = true.
Proof.
  intros s H17. unfold check_inv17.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_role s b p) as [[|]|] eqn:E; try reflexivity.
  pose proof (H17 b p E) as Hne.
  destruct (page_state s b p) eqn:Est; try reflexivity.
  exfalso. apply Hne. reflexivity.
Qed.

Lemma check_inv18_complete : forall s, Inv16 s -> check_inv18 s = true.
Proof.
  intros s H18. unfold check_inv18.
  apply forallb_seq_intro. intros b _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (page_state s b p) eqn:E; try reflexivity.
  rewrite (H18 b p E). reflexivity.
Qed.

Lemma check_inv19_complete : forall s, Inv17 s -> check_inv19 s = true.
Proof.
  intros s H19. unfold check_inv19.
  apply forallb_seq_intro. intros b _. cbn beta.
  destruct (free_block s b) eqn:E; [|reflexivity].
  destruct (H19 b E) as [Ht Hn]. rewrite Ht, Hn. reflexivity.
Qed.

Lemma check_inv20_complete : forall s, Inv18 s -> check_inv20 s = true.
Proof.
  intros s H20. unfold check_inv20.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  destruct (H20 a p pa E) as [Ht Hn].
  rewrite Ht, Hn, !opt_nat_eqb_refl. reflexivity.
Qed.

Lemma check_inv21_complete : forall s, Inv19 s -> check_inv21 s = true.
Proof.
  intros s H21. unfold check_inv21.
  apply forallb_seq_intro. intros i _. cbn beta.
  destruct (region_table s i) as [r|] eqn:E; [|reflexivity].
  apply Nat.leb_le. exact (H21 i r E).
Qed.

(* [check_inv22] enumerates only observed owners, and Inv20 holds of every
   owner, so the truncation costs nothing in this direction. *)
Lemma check_inv22_complete : forall s, Inv20 s -> check_inv22 s = true.
Proof.
  intros s H22. unfold check_inv22.
  apply check_over_owners_intro. intros t ns.
  destruct (open_block s t ns) as [b|] eqn:E; [|reflexivity].
  destruct (H22 t ns b E)
    as [Hb [Hfree [Hfb [Hbo [Hwp [Hbt [Hbn Huniq]]]]]]].
  (* Explicit, not [repeat]: the geometry constants are concrete, so
     [check_over_owners] itself reduces to a conjunction and [repeat] would
     tear it apart. *)
  apply andb_true_iff; split;
  [ apply andb_true_iff; split;
    [ apply andb_true_iff; split;
      [ apply andb_true_iff; split;
        [ apply andb_true_iff; split;
          [ apply andb_true_iff; split;
            [ apply andb_true_iff; split | ] | ] | ] | ] | ] | ].
  - apply Nat.ltb_lt. exact Hb.
  - rewrite (not_in_inb _ _ Hfree). reflexivity.
  - rewrite Hfb. reflexivity.
  - exact Hbo.
  - apply Nat.leb_le. exact Hwp.
  - destruct Hbt as [Hbt|Hbt]; rewrite Hbt;
      [reflexivity | apply Nat.eqb_refl].
  - destruct Hbn as [Hbn|Hbn]; rewrite Hbn;
      [reflexivity | apply Nat.eqb_refl].
  - apply check_over_owners_intro. intros t' ns'.
    destruct (open_block s t' ns') as [b'|] eqn:E'; [|reflexivity].
    destruct (Nat.eqb b' b) eqn:Eb; [|reflexivity].
    apply Nat.eqb_eq in Eb. subst b'.
    destruct (Huniq t' ns' E') as [Ht' Hns']. subst.
    rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma check_inv23_complete : forall s, Inv21 s -> check_inv23 s = true.
Proof.
  intros s H23. unfold check_inv23.
  apply check_over_owners_intro. intros t ns.
  destruct (open_block s t ns) as [b|] eqn:E; [|reflexivity].
  apply forallb_seq_intro. intros q Hq. cbn beta.
  destruct (write_ptr s t ns <=? q) eqn:Ew; [|reflexivity].
  apply Nat.leb_le in Ew.
  destruct (H23 t ns b q E Ew Hq) as [Hst Hmeta].
  rewrite Hst, Hmeta, page_meta_eqb_refl. reflexivity.
Qed.

Lemma check_inv24_complete : forall s, Inv22 s -> check_inv24 s = true.
Proof.
  intros s H24. unfold check_inv24.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  destruct (H24 a p pa E) as [d Hd]. rewrite Hd. reflexivity.
Qed.

(* The complete rendering of Inv23.  The existential "exists t ns,
   open_block s t ns = Some b" cannot be searched completely (the owner may
   label no in-range address), so the test is the checkable consequence that
   Inv23 and Inv20 together force: a block flagged open is neither on the
   free list nor free in the bitmap.  A [false] here refutes Inv23 /\ Inv20,
   which is all [check_refutes] needs. *)
Definition check_inv25_c (s : FTLState) : bool :=
  forallb (fun b =>
    if block_open s b
    then andb (negb (free_block s b)) (negb (inb b (free_block_list s)))
    else true)
    (seq 0 total_blocks).

Lemma check_inv25_c_complete :
  forall s, Inv23 s -> Inv20 s -> check_inv25_c s = true.
Proof.
  intros s H25 H22. unfold check_inv25_c.
  apply forallb_seq_intro. intros b _. cbn beta.
  destruct (block_open s b) eqn:Ebo; [|reflexivity].
  destruct (H25 b Ebo) as [t [ns Hob]].
  destruct (H22 t ns b Hob) as [_ [Hfree [Hfb _]]].
  rewrite Hfb, (not_in_inb _ _ Hfree). reflexivity.
Qed.

Lemma check_inv26_complete : forall s, Inv24 s -> check_inv26 s = true.
Proof.
  intros s H26. unfold check_inv26.
  apply andb_true_iff. split.
  - apply forallb_seq_intro. intros b _. cbn beta.
    destruct (free_block s b) eqn:E; [|reflexivity].
    exact (inb_complete b (free_block_list s) (proj1 (H26 b) E)).
  - apply forallb_forall. intros b Hin. cbn beta.
    exact (proj2 (H26 b) Hin).
Qed.

Lemma check_inv27_complete : forall s, Inv25 s -> check_inv27 s = true.
Proof.
  intros s H27. unfold check_inv27.
  apply check_over_owners_intro. intros t ns.
  destruct (open_block s t ns) as [b|] eqn:E; [|reflexivity].
  apply forallb_seq_intro. intros q Hq. cbn beta.
  destruct (q <? write_ptr s t ns) eqn:Ew; [|reflexivity].
  apply Nat.ltb_lt in Ew.
  pose proof (H27 t ns b q E Ew) as Hne.
  destruct (page_state s b q) eqn:Est; try reflexivity.
  exfalso. apply Hne. reflexivity.
Qed.

Lemma check_inv28_complete : forall s, Inv26 s -> check_inv28 s = true.
Proof.
  intros s H28. unfold check_inv28.
  apply forallb_seq_intro. intros a _. cbn beta.
  apply forallb_seq_intro. intros p _. cbn beta.
  destruct (l2p_map s a p) as [pa|] eqn:E; [|reflexivity].
  destruct (H28 a p pa E) as [[t Ht] [ns Hn]].
  rewrite Ht, Hn. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════
   The full 29-conjunct bounded check: the refutation instrument

   This conjoins one bounded test per clause, using the complete variants
   [check_inv12_c] and [check_inv25_c] for the two clauses whose sound and
   complete renderings differ.  Every conjunct is implied by its clause, so:

     - [check_bounded_all s = false] is a REFUTATION: the state provably
       violates [ftl_invariant] ([check_refutes]).  The checker never
       cries wolf.
     - [check_bounded_all s = true] is NOT a certificate of
       [ftl_invariant]: the 23 conjuncts of group (B) quantify over
       unbounded domains that no finite test can cover, so a [true] verdict
       certifies only the geometry-restricted readings proved above, plus
       the five real clauses recorded in [check_bounded_all_sound].
   ══════════════════════════════════════════════════════════════ *)

Definition check_bounded_all (s : FTLState) : bool :=
  check_inv0 s && check_inv1 s && check_inv2 s && check_inv3 s &&
  check_inv4 s && check_inv5 s && check_inv6 s && check_inv7 s &&
  check_inv8 s && check_inv9 s && check_inv10 s && check_inv11 s &&
  check_inv12_c s && check_inv13 s && check_inv14 s && check_inv15 s &&
  check_inv16 s && check_inv17 s && check_inv18 s && check_inv19 s &&
  check_inv20 s && check_inv21 s && check_inv22 s && check_inv23 s &&
  check_inv24 s && check_inv25_c s && check_inv26 s && check_inv27 s &&
  check_inv28 s.

(* THE HEADLINE: a [false] verdict is a genuine refutation. *)
Theorem check_bounded_all_complete :
  forall s, ftl_invariant s -> check_bounded_all s = true.
Proof.
  intros s Hinv.
  destruct Hinv as
    (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 &
     H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 &
     H22 & H23 & H24 & H25 & H26 & H27 & H28).
  unfold check_bounded_all.
  rewrite (check_inv0_complete s H0).
  rewrite (check_inv1_complete s H1).
  rewrite (check_inv2_complete s H2 H3).
  rewrite (check_inv3_complete s H3).
  rewrite (check_inv4_complete s H4).
  rewrite (check_inv5_complete s H5).
  rewrite (check_inv6_complete s H6).
  rewrite (check_inv7_complete s H7).
  rewrite (check_inv8_complete s H8).
  rewrite (check_inv9_complete s H9).
  rewrite (check_inv10_complete s H10).
  rewrite (check_inv11_complete s H11).
  rewrite (check_inv12_c_complete s H2 H3).
  rewrite (check_inv13_complete s H13).
  rewrite (check_inv14_complete s H15 H17).
  rewrite (check_inv15_complete s H15).
  rewrite (check_inv16_complete s H16).
  rewrite (check_inv17_complete s H17).
  rewrite (check_inv18_complete s H18).
  rewrite (check_inv19_complete s H19).
  rewrite (check_inv20_complete s H20).
  rewrite (check_inv21_complete s H21).
  rewrite (check_inv22_complete s H22).
  rewrite (check_inv23_complete s H23).
  rewrite (check_inv24_complete s H24).
  rewrite (check_inv25_c_complete s H25 H22).
  rewrite (check_inv26_complete s H26).
  rewrite (check_inv27_complete s H27).
  rewrite (check_inv28_complete s H28).
  reflexivity.
Qed.

Theorem check_refutes :
  forall s, check_bounded_all s = false -> ~ ftl_invariant s.
Proof.
  intros s Hf Hinv.
  rewrite (check_bounded_all_complete s Hinv) in Hf. discriminate.
Qed.

(* A [true] verdict from the refutation instrument still yields the real
   clauses whose bounded test happens to be sound as well.  Inv10 is absent
   here (unlike in [check_invariant]) precisely because the complete
   rendering [check_inv12_c] is not the sound one. *)
Theorem check_bounded_all_sound :
  forall s, check_bounded_all s = true ->
    WF0 s /\ WF1 s /\ Inv6 s /\ Inv8 s /\ Inv11 s.
Proof.
  intros s H.
  unfold check_bounded_all in H.
  apply andb_true_iff in H as [H C28].
  apply andb_true_iff in H as [H C27].
  apply andb_true_iff in H as [H C26].
  apply andb_true_iff in H as [H C25].
  apply andb_true_iff in H as [H C24].
  apply andb_true_iff in H as [H C23].
  apply andb_true_iff in H as [H C22].
  apply andb_true_iff in H as [H C21].
  apply andb_true_iff in H as [H C20].
  apply andb_true_iff in H as [H C19].
  apply andb_true_iff in H as [H C18].
  apply andb_true_iff in H as [H C17].
  apply andb_true_iff in H as [H C16].
  apply andb_true_iff in H as [H C15].
  apply andb_true_iff in H as [H C14].
  apply andb_true_iff in H as [H C13].
  apply andb_true_iff in H as [H C12].
  apply andb_true_iff in H as [H C11].
  apply andb_true_iff in H as [H C10].
  apply andb_true_iff in H as [H C9].
  apply andb_true_iff in H as [H C8].
  apply andb_true_iff in H as [H C7].
  apply andb_true_iff in H as [H C6].
  apply andb_true_iff in H as [H C5].
  apply andb_true_iff in H as [H C4].
  apply andb_true_iff in H as [H C3].
  apply andb_true_iff in H as [H C2].
  apply andb_true_iff in H as [C0 C1].
  split; [| split; [| split; [| split]]].
  - apply check_inv0_sound. exact C0.
  - apply check_inv1_sound. exact C1.
  - apply check_inv8_sound. exact C8.
  - apply check_inv10_sound. exact C10.
  - apply check_inv13_sound. exact C13.
Qed.

(* Contrapositive of the group-(A) soundness: a state failing any of the six
   real clauses cannot be accepted. *)
Corollary check_invariant_rejects :
  forall s,
    ~ (WF0 s /\ WF1 s /\ Inv6 s /\ Inv8 s /\ Inv10 s /\ Inv11 s) ->
    check_invariant s = false.
Proof.
  intros s Hno.
  destruct (check_invariant s) eqn:E; [|reflexivity].
  exfalso. apply Hno. apply check_invariant_sound. exact E.
Qed.

(* ══════════════════════════════════════════════════════════════
   Worked demonstration: the checker computes.

   Geometry is concrete (pages_per_block = 4, addr_space = 4,
   total_blocks = 8), so both checks reduce to a closed boolean.
   ══════════════════════════════════════════════════════════════ *)

Compute check_invariant empty_state.
Compute check_bounded_all empty_state.

Lemma check_invariant_empty_state : check_invariant empty_state = true.
Proof. reflexivity. Qed.

Lemma check_bounded_all_empty_state : check_bounded_all empty_state = true.
Proof. reflexivity. Qed.

(* And the verdict is a real guarantee: the six clauses hold of the initial
   state, obtained here from the checker rather than from a hand proof. *)
Corollary empty_state_clauses :
  WF0 empty_state /\ WF1 empty_state /\ Inv6 empty_state /\
  Inv8 empty_state /\ Inv10 empty_state /\ Inv11 empty_state.
Proof.
  apply check_invariant_sound. exact check_invariant_empty_state.
Qed.

(* ══════════════════════════════════════════════════════════════
   Worked demonstration of both directions on concrete states
   ══════════════════════════════════════════════════════════════ *)

(* [broken_state] is [empty_state] with block 0 pushed onto the free list a
   second time, violating Inv11.  The checker rejects it, and the rejection
   is by itself a proof that the state breaks the global invariant: the
   refutation below is discharged by [reflexivity] through [check_refutes]. *)
Definition broken_state : FTLState :=
  mkFTLState
    (l2p_map empty_state) (page_state empty_state) (page_role empty_state)
    (addr_tenant empty_state) (addr_namespace empty_state)
    (block_tenant empty_state) (block_namespace empty_state)
    (page_meta empty_state) (region_table empty_state)
    (0 :: free_block_list empty_state) (free_block empty_state)
    (wear_count empty_state) (key_table empty_state)
    (open_block empty_state) (write_ptr empty_state) (block_open empty_state).

Compute check_bounded_all broken_state.

Lemma check_rejects_broken_state : check_bounded_all broken_state = false.
Proof. reflexivity. Qed.

Corollary broken_state_violates : ~ ftl_invariant broken_state.
Proof. apply check_refutes. exact check_rejects_broken_state. Qed.

(* The converse, made concrete.  [invisible_state] maps logical address 100
   — outside [addr_space] — onto physical page (0,0), which violates Inv1 and
   Inv22.  Every quantifier the checker can range over misses it, so the
   checker accepts.  This is the counterexample behind "a [true] verdict does
   not certify"; it is why the top-level soundness result is stated for the
   six clauses of [check_invariant] and not for [ftl_invariant]. *)
Definition invisible_state : FTLState :=
  mkFTLState
    (fun a _ => if Nat.eqb a 100 then Some (mkPhysAddr 0 0) else None)
    (page_state empty_state) (page_role empty_state)
    (addr_tenant empty_state) (addr_namespace empty_state)
    (block_tenant empty_state) (block_namespace empty_state)
    (page_meta empty_state) (region_table empty_state)
    (free_block_list empty_state) (free_block empty_state)
    (wear_count empty_state) (key_table empty_state)
    (open_block empty_state) (write_ptr empty_state) (block_open empty_state).

Lemma check_accepts_invisible_state : check_bounded_all invisible_state = true.
Proof. reflexivity. Qed.

Lemma invisible_state_violates_Inv1 : ~ Inv1 invisible_state.
Proof.
  intro H3.
  destruct (H3 100 0 (mkPhysAddr 0 0) eq_refl) as [_ [_ [Ha _]]].
  unfold addr_space in Ha. cbn in Ha. lia.
Qed.
