(* Dedup.v -- a deduplicating FTL over the page-granular model, and a
   measurement of what changing a shared invariant clause actually costs.

   Deduplication lets two logical pages that hold identical data share one
   physical page.  That contradicts Inv2, which says the forward map is
   injective.  The paper's claim about this case is that "the affected
   clause is weakened or replaced and the hypotheses depending on it
   re-proved, and the rest carries over".  This file is the test.  Nothing
   outside src/dedup/ is edited; the framework is used as a library.

   Build:   coqc -Q src "" src/dedup/Dedup.v
   Result:  compiles with no output, no warnings.  53 [Qed]s, no
            admitted lemmas, no [admit], no axiom declarations/parameters/variables/
            hypotheses introduced here.  [Print Assumptions] on
            dedup_write_preserves_invariant, dedup_gc_preserves_invariant,
            dedup_wear_level_preserves_invariant,
            dedup_reclaim_with_preserves_invariant,
            dedup_unconstrained_chooser_breaks_invariant,
            dedup_step_preserves_invariant, release_ok, Inv3_forbids_sharing,
            Inv2_dedup_is_derivable, dedup_cannot_cross_tenants,
            framework_relocation_strands_sharers and
            empty_state_dedup_invariant all report
            "Closed under the global context".
   Size:    3232 lines, of which 288 are this header.

   ═══════════════════════════════════════════════════════════════════════
   FINDING 0.  REPLACING Inv2 ALONE IS A NO-OP, AND THE REAL COST IS Inv3.
   ═══════════════════════════════════════════════════════════════════════

   Two facts, both proved below, bracket the whole exercise.

   [Inv3_forbids_sharing] : Inv3 s -> Inv22 s -> Inv2 s.
       Inv3 says a live mapped page is stamped with *the* logical address
       that maps to it, and Inv22 says every mapped page is live.  Together
       they re-derive injectivity.  A 29-conjunct bundle that swaps Inv2 for
       any weaker clause but keeps Inv3 is therefore *equivalent to the
       original bundle*: no state in it can share a page, and the dedup
       write can never fire.  The design does not change one clause.  It
       changes two, and the second one is not the one you set out to change.

   [Inv2_dedup_is_derivable] : Inv18 s -> Inv22 s -> Inv2_dedup s.
       The natural dedup weakening of Inv2 -- sharing is allowed only of a
       live page, only when both sharers read the same datum, and only
       inside one (tenant, namespace) pair -- is already a consequence of
       clauses the bundle keeps.  Inv22 supplies the liveness and the data
       agreement (a mapped page has one state, so both readers necessarily
       see the same datum), and Inv18 identifies the two sharers' tenants
       through the block they share.  So Inv2 is not traded for a weaker
       clause.  It is deleted, and [Inv2_dedup] is discharged mechanically
       at all 5 sites where the bundle asks for it.  What is left of the
       old reverse-mapping discipline is carried entirely by [Inv3_dedup]:
       the page is stamped, and the stamp names one of its readers.

   Not machine-checked, stated as an observation: Inv3_dedup is not
   derivable from the other 28 conjuncts, because Inv3 is the only clause
   that constrains [page_lpa] in the direction "a live mapped page has a
   stamp"; Inv4 constrains only stamps that already exist, and no other
   clause mentions [page_lpa] at all.

   ═══════════════════════════════════════════════════════════════════════
   FINDING 1.  SURVIVAL TABLE.
   ═══════════════════════════════════════════════════════════════════════

   Every framework result this development needed, and what happened to it.
   "verbatim" = imported and applied with no restatement and no re-proof.
   "re-proved" = the statement mentions the invariant bundle, so it had to
   be restated against [dedup_invariant] / [INVXD] and proved again;
   the last two columns are its size and how many of those lines are
   textually identical to the framework proof (measured with diff).
   "false" = the result is not merely unavailable, its negation is proved.

   --------------------------------------------------------------------
   RESULT                                   FATE      LINES  OF WHICH
                                                      MINE   IDENTICAL
   --------------------------------------------------------------------
   Model.v / PagePreservation.v
     set_l2p_here, set_l2p_other            verbatim      0        -
     set_ps_here, set_ps_other              verbatim      0        -
     set_pr_here, set_pr_other              verbatim      0        -
     set_pm_here, set_pm_other              verbatim      0        -
     physaddr_eta                           verbatim      0        -
     read_preserves_invariant               re-proved     8        0
     set_tag_preserves_invariant            re-proved   103        5
   Invariants.v
     WF0..Inv1, Inv4..Inv26 (27 conjuncts)   verbatim      0        -
     Inv2                                   FALSE         -        -
     Inv3                                   FALSE         -        -
     ftl_invariant                      re-proved     7        -
     make_ftl_invariant                 re-proved    13        -
     empty_state_invariant                  re-proved     5        -
   GCPreservation.v -- infrastructure
     set_ob_*, set_wp_*, set_bo_*,
       set_fb_*, set_bt_*, set_bn_*         verbatim      0        -
     nat_pair_dec                           verbatim      0        -
     eb_* (17 erase field equations)        verbatim      0        -
     alloc_page_fields                      verbatim      0        -
     alloc_dest_not_victim                  verbatim      0        -
     open_fresh_shape                       verbatim      0        -
     alloc_page_shape                       verbatim      0        -
     victim_sound (chooser contract)        verbatim      0        -
     find_victim_sound                      verbatim      0        -
     find_least_worn_victim_sound           verbatim      0        -
     Inv12_from_Inv13_Inv15                 verbatim      0        -
   WritePreservation.v
     program_ok                             re-proved   249      133
     write_core                             re-proved   272      233*
     write_preserves_invariant              re-proved    50       10
     invalidate_preserves_invariant         FALSE         -        -
   GCPreservation.v -- the reclaim fold
     INVX (relativised bundle)              re-proved    48       15
     INVX_drop                              re-proved    24       19
     program_relx                           re-proved   295      163
     relocate_core                          re-proved   320      291
     relocate_page_INVX                     re-proved    25       16
     relocate_pages_INVX                    re-proved    11        5
     erase_ok                               re-proved   149      128
   GCPreservation.v -- the chooser interface
     reclaimable_victim_INVX                re-proved    20       15
     reclaim_preserves_invariant            re-proved    15        6
     reclaim_with_preserves_invariant       re-proved    12        6
     relocate_page_empty                    re-proved     4        0
     relocate_pages_all_empty               re-proved    10        6
     unconstrained_chooser_breaks_invariant re-proved    19       12
     gc_preserves_invariant                 re-proved     8        4
     wear_level_preserves_invariant         re-proved    10        4
     (step dispatcher, no analogue)         re-proved    10        -
   Operational.v -- operations, not results
     exec_write                             FALSE         -        -
     exec_invalidate                        FALSE         -        -
     relocate_page / reclaim / reclaim_with
       / gc / wear_level                    FALSE         -        -
   --------------------------------------------------------------------

   * [alloc_ok_d] plays [write_core]'s role but was built by adapting
     [relocate_core], whose allocation argument is factored through
     [alloc_page_shape].  233 of its 272 lines are identical to
     [relocate_core]; only 14 are identical to [write_core] itself.

   How the two rightmost columns are measured.  A result's extent is the
   lines from its [Lemma]/[Theorem]/[Definition]/[Record] keyword through
   its terminating [Qed.] (or terminating [.]), inclusive; preceding
   comments are not counted.  IDENTICAL is the number of those lines that
   GNU [diff] reports as common between the framework extent and the dedup
   extent, i.e. (dedup lines) minus (lines diff marks '>').  MINE and
   IDENTICAL therefore always sum with the "changed" column below.  Four
   rows carry "-" because the dedup side is not a restatement of one
   framework result: the three bundle-plumbing rows enumerate a different
   clause list, so a diff of them measures the enumeration and nothing
   else, and the step dispatcher has no framework counterpart at all.  The
   [write_preserves_invariant] row covers the two adjacent dedup theorems
   [dedup_write_preserves_invariant] and
   [dedup_step_write_preserves_invariant] as one contiguous extent, which
   is why its MINE is 50 rather than 33+16.

   Totals.
     47 framework lemmas survived verbatim -- [find_victim_aux_sound] is no
     longer used and [find_victim_sound] and [find_least_worn_victim_sound]
     take its place -- together with the [victim_sound] definition and 27
     of the 29 invariant clauses.
     24 framework results were re-proved, for 1687 lines of Coq.
     The corresponding framework text is 2021 lines.
     Of the 1652 re-proved lines in the 20 pairs measured with diff,
     1071 (64.8%) are textually identical to the framework proof they
     replace and 581 differ.
     2 invariant clauses and 7 operations became false.

   Where the 581 changed lines are.  They are not spread evenly.  Ranked:
     program_relx -> reloc_program_ok
                                  132 of 295 changed
     program_ok -> program_ok_d   116 of 249 changed
     set_tag_preserves_invariant   98 of 103 changed  (restructured; the
                                   framework threads a single [Hmeta]
                                   rewrite, the dedup version needs the
                                   page_lpa-preservation fact separately)
     write_preserves_invariant     40 of  50 changed  (the operation itself
                                   is different, see Finding 2)
     alloc_ok_d                    39 of 272 changed (vs relocate_core)
     INVX -> INVXD                 33 of  48 changed  (one field deleted,
                                   one replaced, all field names renamed)
     relocate_core                 29 of 320 changed
     erase_ok                      21 of 149 changed
     the eight chooser results     45 of  98 changed  (Finding 2e)
     the three small fold lemmas   20 of  60 changed
     read_preserves_invariant       8 of   8 changed

   Read the other way: the two biggest proofs in the framework
   ([relocate_core] at 291 of 320, [erase_ok] at 128 of 149) came across at
   91% and 86% textual identity.  The claim "the rest carries over" is
   accurate about the *bulk* of the proof text.  What it hides is that
   carrying it over is not free: every one of those 1687 lines had to be
   restated, re-run and re-closed, because the conclusion of each lemma
   names the bundle.  A framework that abstracted its preservation lemmas
   over the bundle would have made 1071 of these lines genuinely reusable;
   this one does not, so they were copied.

   ═══════════════════════════════════════════════════════════════════════
   FINDING 2.  WHAT DEDUPLICATION GENUINELY COSTS.
   ═══════════════════════════════════════════════════════════════════════

   (a) Two of the framework's *operations* become unsound, and no
       weakening of any clause rescues them; the code has to change.

       [framework_relocation_strands_sharers] (proved below).
       [relocate_page] follows the OOB stamp to the single logical address
       that reads the page and repoints only that one.  If the page has
       another reader, that reader is left pointing into the victim block,
       and [reclaim] then erases the block underneath it: Inv22 fails
       after the erase.  The GC relocation argument in [GCPreservation.v]
       uses Inv2 to know a relocated page's mapping is unique, and that
       is exactly what sharing takes away.  The fix is [redirect], which
       retargets *every* reader of the source page at
       once; the progress conjunct of the fold then follows without any
       injectivity argument at all, and that clause got *shorter*.

       [exec_write] and [exec_invalidate] stale the old physical page
       unconditionally.  That is sound only because Inv2 makes (a, p) its
       sole reader.  Under sharing they destroy other readers' data.  The
       fix is [release_old], which detaches (a, p), searches for a
       surviving reader, and stales the page only if there is none.

   (b) The reverse map stops being sufficient, and a search takes its
       place.  [find_mapper] scans the logical address space and
       [find_dup] scans the physical one.  Both are total because the
       geometry is finite, but the FTL now pays a table scan where it used
       to follow one pointer.

   (c) A shared page's OOB stamp has to be *rewritten* when its stamped
       reader is overwritten while other readers remain ([restamp], used
       in [release_shared_ok]).  Inv3 made this situation impossible.  On
       real NAND the OOB area is part of the page and cannot be rewritten
       in place, so a faithful implementation would have to relocate the
       page instead.  The model records the obligation; it does not charge
       for it.

   (d) Cross-tenant deduplication is not available.
       [dedup_cannot_cross_tenants] (proved below): if two logical
       addresses share a live page, Inv7 forces their tenants and
       namespaces to be equal.  The obstruction is Inv7, the framework's
       isolation clause, and the only way to share across tenants is to
       give that clause up.  Nothing else was weakened to rescue it:
       instead the dedup write's candidate test [dup_ok]
       refuses any page whose owner fields do not match the writer's, and
       Inv7 and Inv18 come through unchanged.  The practical reading is
       that the headline benefit of deduplication -- one copy of a common
       block shared across the whole device -- is unavailable to a
       multi-tenant FTL that keeps this isolation property.  Dedup is
       confined to within a single (tenant, namespace).

   (e) What deduplication does *not* cost: the reclamation policy
       interface.  The framework separates the reclaim transformer from the
       choice of victim ([reclaim_with pick], [victim_sound], and the two
       instances [gc] and [wear_level]), and deduplication leaves that
       separation intact.  The reason is measurable: [victim_sound] is a
       statement about the geometry and the free/open bits only, and no
       clause of the bundle -- neither the framework's 29 nor the 28 that
       survive here -- constrains [wear_count], so the weakening cannot
       reach the chooser.  So [dedup_reclaim_with] is parameterized exactly
       as [reclaim_with] is, [dedup_gc] and [dedup_wear_level] are its two
       instances, and one proof
       ([dedup_reclaim_with_preserves_invariant]) covers every policy
       meeting the contract, just as in the framework.  The contract is
       still necessary and not slack:
       [dedup_unconstrained_chooser_breaks_invariant] refutes the
       unconstrained statement here as well, from [empty_state], via Inv11.
       This is the one place in this file where the framework's *structure*
       transferred and not merely its proof text -- and it is also where
       the transfer was least free in proportional terms: 98 lines for 8
       results, 45 of them changed, almost all of the change being the
       bundle name.

   ═══════════════════════════════════════════════════════════════════════
   WHAT IS IN THIS FILE
   ═══════════════════════════════════════════════════════════════════════
     PART 0  physical-address equality; the two finite searches
     PART 1  Inv2_dedup, Inv3_dedup, dedup_invariant, and Findings 0 and 2d
     PART 2  the deduplicating operations, and Finding 2a
     PART 3  release_old preserves the bundle (both branches), Qed
     PART 4  the dedup hit: attach a logical page to an existing physical
             one.  No framework analogue; this is the step Inv2 forbade
     PART 5  the dedup miss: the ordinary out-of-place path, and
             [dedup_write_preserves_invariant], Qed
     PART 6  reclamation: INVXD, redirect-based relocation, the fold, the
             erase, then the chooser interface -- one generalized
             preservation proof, its refutation, and the two instances
             [dedup_gc_preserves_invariant] and
             [dedup_wear_level_preserves_invariant] (Finding 2e), Qed
     PART 7  the remaining operations and [dedup_step_preserves_invariant]
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import Invariants.PagePreservation.
Require Import Invariants.GCPreservation.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 0 -- physical-address equality and the enumeration of the
   logical and physical address spaces.

   Deduplication makes [l2p_map] non-injective, so the single reverse
   pointer a page carries in its OOB area ([page_lpa]) no longer
   determines the set of logical pages that read that page.  Two
   operations therefore need to *search* for a mapper where the plain FTL
   could simply follow the stamp: overwriting a shared page, and reclaiming
   one.  Both address spaces are finite, so the searches are total functions.
   ══════════════════════════════════════════════════════════════════════ *)

Definition phys_eqb (x y : PhysAddr) : bool :=
  andb (Nat.eqb (pa_block x) (pa_block y)) (Nat.eqb (pa_page x) (pa_page y)).

Lemma phys_eqb_eq : forall x y, phys_eqb x y = true -> x = y.
Proof.
  intros [b1 p1] [b2 p2] H. unfold phys_eqb in H. cbn in H.
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma phys_eqb_neq : forall x y, phys_eqb x y = false -> x <> y.
Proof.
  intros x y H E. subst y. unfold phys_eqb in H.
  rewrite !Nat.eqb_refl in H. discriminate.
Qed.

Lemma phys_eqb_refl : forall x, phys_eqb x x = true.
Proof. intros x. unfold phys_eqb. now rewrite !Nat.eqb_refl. Qed.

Lemma phys_dec : forall x y : PhysAddr, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (phys_eqb x y) eqn:E.
  - left. exact (phys_eqb_eq x y E).
  - right. exact (phys_eqb_neq x y E).
Qed.

(* ── the logical address space, enumerated ─────────────────────────── *)

Definition lpa_pairs : list (Addr * Page) :=
  list_prod (seq 0 addr_space) (seq 0 pages_per_block).

Lemma in_lpa_pairs :
  forall a p, In (a, p) lpa_pairs <-> a < addr_space /\ p < pages_per_block.
Proof.
  intros a p. unfold lpa_pairs. rewrite in_prod_iff, !in_seq. lia.
Qed.

Definition maps_to (s : FTLState) (pa : PhysAddr) (ap : Addr * Page) : bool :=
  match l2p_map s (fst ap) (snd ap) with
  | Some pa0 => phys_eqb pa0 pa
  | None => false
  end.

Lemma maps_to_true :
  forall s pa a p, maps_to s pa (a, p) = true -> l2p_map s a p = Some pa.
Proof.
  intros s pa a p H. unfold maps_to in H. cbn in H.
  destruct (l2p_map s a p) as [pa0|] eqn:E; [|discriminate].
  apply phys_eqb_eq in H. subst pa0. reflexivity.
Qed.

Lemma maps_to_false :
  forall s pa a p, maps_to s pa (a, p) = false -> l2p_map s a p <> Some pa.
Proof.
  intros s pa a p H E. unfold maps_to in H. cbn in H. rewrite E in H.
  rewrite phys_eqb_refl in H. discriminate.
Qed.

(* [find_mapper] returns some logical page that reads [pa], if there is
   one inside the address space.  Under Inv1 every mapper is inside the
   address space, so [None] means there is no mapper at all. *)
Definition find_mapper (s : FTLState) (pa : PhysAddr) : option (Addr * Page) :=
  find (maps_to s pa) lpa_pairs.

Lemma find_mapper_some :
  forall s pa a0 p0,
    find_mapper s pa = Some (a0, p0) -> l2p_map s a0 p0 = Some pa.
Proof.
  intros s pa a0 p0 H. unfold find_mapper in H.
  apply find_some in H as [_ H]. exact (maps_to_true s pa a0 p0 H).
Qed.

Lemma find_mapper_none :
  forall s pa,
    Inv1 s ->
    find_mapper s pa = None ->
    forall a0 p0, l2p_map s a0 p0 <> Some pa.
Proof.
  intros s pa I3 H a0 p0 E.
  destruct (I3 a0 p0 pa E) as (_ & _ & Ha & Hp).
  assert (Hin : In (a0, p0) lpa_pairs) by (apply in_lpa_pairs; split; assumption).
  unfold find_mapper in H.
  pose proof (find_none (maps_to s pa) lpa_pairs H (a0, p0) Hin) as Hf.
  exact (maps_to_false s pa a0 p0 Hf E).
Qed.

(* ── the physical address space, enumerated ────────────────────────── *)

Definition phys_all : list PhysAddr :=
  flat_map (fun b => map (mkPhysAddr b) (seq 0 pages_per_block))
           (seq 0 total_blocks).

Lemma in_phys_all :
  forall pa,
    In pa phys_all ->
    pa_block pa < total_blocks /\ pa_page pa < pages_per_block.
Proof.
  intros pa H. unfold phys_all in H. apply in_flat_map in H as (b & Hb & H).
  apply in_map_iff in H as (q & Hq & Hin).
  apply in_seq in Hb. apply in_seq in Hin. subst pa. cbn. lia.
Qed.

(* A candidate for reuse: a live page holding exactly the data being
   written, owned by exactly the (tenant, namespace) pair doing the write.
   The ownership test is not an optimisation.  Inv7 and Inv18 tie a live
   page's owner fields to the tenant of *every* logical address that maps
   to it, so a physical page shared across two tenants falsifies them; see
   [dedup_cannot_cross_tenants] below. *)
Definition dup_ok (s : FTLState) (t : TenantId) (ns : NamespaceId)
                  (d : Data) (pa : PhysAddr) : bool :=
  match page_state s (pa_block pa) (pa_page pa) with
  | PS_Valid d' =>
      andb (Nat.eqb d' d)
        (andb (Nat.eqb (page_owner_tenant (page_meta s (pa_block pa) (pa_page pa))) t)
              (Nat.eqb (page_owner_namespace (page_meta s (pa_block pa) (pa_page pa))) ns))
  | _ => false
  end.

Definition find_dup (s : FTLState) (t : TenantId) (ns : NamespaceId)
                    (d : Data) : option PhysAddr :=
  find (dup_ok s t ns d) phys_all.

Lemma find_dup_spec :
  forall s t ns d pa,
    find_dup s t ns d = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d /\
    page_owner_tenant (page_meta s (pa_block pa) (pa_page pa)) = t /\
    page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)) = ns /\
    pa_block pa < total_blocks /\ pa_page pa < pages_per_block.
Proof.
  intros s t ns d pa H. unfold find_dup in H.
  apply find_some in H as [Hin Hok].
  destruct (in_phys_all pa Hin) as [Hb Hp].
  unfold dup_ok in Hok.
  destruct (page_state s (pa_block pa) (pa_page pa)) as [| |d'] eqn:Eps;
    try discriminate.
  apply andb_prop in Hok as [Hd Hok]. apply andb_prop in Hok as [Ht Hn].
  apply Nat.eqb_eq in Hd. apply Nat.eqb_eq in Ht. apply Nat.eqb_eq in Hn.
  subst d'. repeat split; assumption.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the weakened clauses and the dedup bundle.
   ══════════════════════════════════════════════════════════════════════ *)

(* Inv2 said the forward map is injective: no physical page is named by two
   logical pages.  Deduplication contradicts it directly.  [Inv2_dedup] is
   the weakening the design asks for: sharing is permitted, but only of a
   *live* page, only when both sharers read the same datum out of it, and
   only inside one (tenant, namespace) pair. *)
Definition Inv2_dedup (s : FTLState) : Prop :=
  forall a1 p1 a2 p2 pa,
    l2p_map s a1 p1 = Some pa -> l2p_map s a2 p2 = Some pa ->
    (a1 = a2 /\ p1 = p2) \/
    ((exists d, page_state s (pa_block pa) (pa_page pa) = PS_Valid d /\
                read_page s a1 p1 = Some d /\ read_page s a2 p2 = Some d) /\
     addr_tenant s a1 = addr_tenant s a2 /\
     addr_namespace s a1 = addr_namespace s a2).

(* Inv3 said a live mapped page is stamped with *the* logical address that
   maps to it.  Under sharing there is more than one such address and only
   one stamp, so Inv3 is false of every deduplicated state --- see
   [Inv3_forbids_sharing].  [Inv3_dedup] keeps what survives: the page is
   stamped, and the stamp names one of its readers, its owner. *)
Definition Inv3_dedup (s : FTLState) : Prop :=
  forall a p pa d,
    l2p_map s a p = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    exists a0 p0,
      page_lpa (page_meta s (pa_block pa) (pa_page pa)) = Some (a0, p0) /\
      l2p_map s a0 p0 = Some pa.

Definition dedup_invariant (s : FTLState) : Prop :=
  WF0 s /\ WF1 s /\ Inv0 s /\ Inv1 s /\
  Inv2_dedup s /\ Inv3_dedup s /\
  Inv4 s /\ Inv5 s /\ Inv6 s /\ Inv7 s /\ Inv8 s /\ Inv9 s /\ Inv10 s /\
  Inv11 s /\ Inv12 s /\ Inv13 s /\ Inv14 s /\ Inv15 s /\ Inv16 s /\
  Inv17 s /\ Inv18 s /\ Inv19 s /\ Inv20 s /\ Inv21 s /\ Inv22 s /\
  Inv23 s /\ Inv24 s /\ Inv25 s /\ Inv26 s.

Lemma make_dedup_invariant :
  forall s,
    WF0 s -> WF1 s -> Inv0 s -> Inv1 s -> Inv2_dedup s -> Inv3_dedup s ->
    Inv4 s -> Inv5 s -> Inv6 s -> Inv7 s -> Inv8 s -> Inv9 s -> Inv10 s ->
    Inv11 s -> Inv12 s -> Inv13 s -> Inv14 s -> Inv15 s -> Inv16 s ->
    Inv17 s -> Inv18 s -> Inv19 s -> Inv20 s -> Inv21 s -> Inv22 s ->
    Inv23 s -> Inv24 s -> Inv25 s -> Inv26 s ->
    dedup_invariant s.
Proof.
  intros s H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18
         H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
  unfold dedup_invariant. do 28 (split; [assumption|]). assumption.
Qed.

(* ── measurement 1: the bundle really is weaker ────────────────────── *)

Lemma Inv3_implies_Inv3_dedup : forall s, Inv3 s -> Inv3_dedup s.
Proof.
  intros s I5 a p pa d Hm Hv. exists a, p. split; [exact (I5 a p pa d Hm Hv)|exact Hm].
Qed.

Lemma Inv2_implies_Inv2_dedup : forall s, Inv2 s -> Inv2_dedup s.
Proof.
  intros s I4 a1 p1 a2 p2 pa H1 H2. left. exact (I4 a1 p1 a2 p2 pa H1 H2).
Qed.

Theorem ftl_implies_dedup_invariant :
  forall s, ftl_invariant s -> dedup_invariant s.
Proof.
  intros s (I0&I1&I2&I3&I4&I5&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15&I16&I17&I18
           &I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  apply make_dedup_invariant; try assumption.
  - exact (Inv2_implies_Inv2_dedup s I4).
  - exact (Inv3_implies_Inv3_dedup s I5).
Qed.

(* ── measurement 2: replacing Inv2 *alone* changes nothing ─────────── *)

(* Inv3 forces the forward map to be injective on live pages, and Inv22
   says every mapped page is live.  So a bundle that replaces Inv2 by
   Inv2_dedup and keeps Inv3 still entails Inv2: no state in it can share
   a page.  Deduplication is impossible until Inv3 is weakened too.  This
   is the single most expensive fact in this development: the design
   changes the meaning of one clause and drags a second one with it. *)
Theorem Inv3_forbids_sharing :
  forall s, Inv3 s -> Inv22 s -> Inv2 s.
Proof.
  intros s I5 I24 a1 p1 a2 p2 pa H1 H2.
  destruct (I24 a1 p1 pa H1) as [d Hd].
  pose proof (I5 a1 p1 pa d H1 Hd) as E1.
  pose proof (I5 a2 p2 pa d H2 Hd) as E2.
  rewrite E1 in E2. injection E2 as F1 F2. split; [exact F1|exact F2].
Qed.

(* ── measurement 3: the weakened Inv2 carries no information ───────── *)

(* Inv2_dedup is *derivable* from clauses the bundle already has: Inv22
   makes a mapped page live, which supplies the data conjuncts outright,
   and Inv18 identifies the tenants of any two sharers through the block.
   Replacing Inv2 by the natural dedup clause therefore does not trade a
   strong clause for a weaker one.  It deletes Inv2.  What is left of the
   old reverse-mapping discipline lives entirely in Inv3_dedup. *)
Theorem Inv2_dedup_is_derivable :
  forall s, Inv18 s -> Inv22 s -> Inv2_dedup s.
Proof.
  intros s I20 I24 a1 p1 a2 p2 pa H1 H2. right.
  destruct (I24 a1 p1 pa H1) as [d Hd].
  destruct (I20 a1 p1 pa H1) as [Gt1 Gn1].
  destruct (I20 a2 p2 pa H2) as [Gt2 Gn2].
  split.
  - exists d. split; [exact Hd|]. unfold read_page.
    rewrite H1, H2, Hd. split; reflexivity.
  - rewrite <- Gt1, <- Gt2, <- Gn1, <- Gn2. split; reflexivity.
Qed.

(* ── measurement 4: what deduplication genuinely costs ─────────────── *)

(* Cross-tenant sharing is not available.  Inv7 pins a live page's owner
   fields to the tenant and namespace of every logical address that reads
   it, so two addresses of different tenants cannot share a page without
   falsifying Inv7.  No weakening of Inv2 recovers this: the obstruction
   is Inv7, which is the framework's isolation clause, and weakening it is
   exactly giving up multi-tenant isolation.  The dedup write below
   therefore refuses a candidate whose owner fields do not match. *)
Theorem dedup_cannot_cross_tenants :
  forall s a1 p1 a2 p2 pa d t1 t2 ns1 ns2,
    Inv7 s ->
    l2p_map s a1 p1 = Some pa ->
    l2p_map s a2 p2 = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    addr_tenant s a1 = Some t1 -> addr_namespace s a1 = Some ns1 ->
    addr_tenant s a2 = Some t2 -> addr_namespace s a2 = Some ns2 ->
    t1 = t2 /\ ns1 = ns2.
Proof.
  intros s a1 p1 a2 p2 pa d t1 t2 ns1 ns2 I9 H1 H2 Hd Ht1 Hn1 Ht2 Hn2.
  destruct (I9 a1 p1 pa d t1 ns1 H1 Hd Ht1 Hn1) as [E1 F1].
  destruct (I9 a2 p2 pa d t2 ns2 H2 Hd Ht2 Hn2) as [E2 F2].
  split; [rewrite <- E1, <- E2; reflexivity | rewrite <- F1, <- F2; reflexivity].
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- the deduplicating operations.
   ══════════════════════════════════════════════════════════════════════ *)

(* Re-stamping a page's OOB reverse pointer.  Under Inv3 this operation
   never arises: a page has one reader and the stamp names it for the
   page's whole lifetime.  Under sharing the stamped reader can be
   overwritten while other readers remain, and Inv3_dedup then demands the
   stamp be moved to a surviving reader.  On real NAND the OOB area is
   part of the page and cannot be rewritten in place, so this is a cost
   the model records but does not charge for. *)
Definition restamp (s : FTLState) (pa : PhysAddr) (a0 : Addr) (p0 : Page)
  : FTLState :=
  let m := page_meta s (pa_block pa) (pa_page pa) in
  mkFTLState (l2p_map s) (page_state s) (page_role s) (addr_tenant s)
    (addr_namespace s) (block_tenant s) (block_namespace s)
    (set_page_meta (page_meta s) (pa_block pa) (pa_page pa)
       (mkPageMeta (page_owner_tenant m) (page_owner_namespace m)
                   (page_tag m) (Some (a0, p0))))
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s) (open_block s) (write_ptr s) (block_open s).

(* Detaching (a, p) from its physical page.  The framework's [exec_write]
   and [exec_invalidate] stale the old page unconditionally; that is sound
   only because Inv2 makes (a, p) its sole reader.  Under sharing the page
   must survive if anyone else still reads it, and its stamp must be moved
   to one of them. *)
Definition release_old (s : FTLState) (a : Addr) (p : Page) : FTLState :=
  match l2p_map s a p with
  | Some old =>
      let s1 := unmap s a p in
      match find_mapper s1 old with
      | Some (a0, p0) => restamp s1 old a0 p0
      | None => invalidate_at s1 old
      end
  | None => s
  end.

(* Attaching (a, p) to an existing physical page.  No page is programmed:
   this is the whole point of deduplication. *)
Definition map_to (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr)
  : FTLState :=
  mkFTLState (set_l2p_map (l2p_map s) a p (Some pa))
    (page_state s) (page_role s) (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s) (page_meta s) (region_table s)
    (free_block_list s) (free_block s) (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

Definition dedup_write (s : FTLState) (a : Addr) (p : Page) (d : Data)
  : option FTLState :=
  match addr_tenant s a, addr_namespace s a with
  | Some t, Some ns =>
      let s1 := release_old s a p in
      match find_dup s1 t ns d with
      | Some pa => Some (map_to s1 a p pa)
      | None =>
          match alloc_page s1 t ns with
          | Some (pa, s2) => Some (program_page s2 a p d pa)
          | None => None
          end
      end
  | _, _ => None
  end.

Definition dedup_invalidate (s : FTLState) (a : Addr) (p : Page) : FTLState :=
  release_old s a p.

(* ── relocation ────────────────────────────────────────────────────── *)

(* The framework relocates a page by following its OOB stamp to the one
   logical address that reads it and repointing that address.  With
   sharing the stamp names one reader out of several, and the others are
   left pointing into the block about to be erased --- see
   [framework_relocation_strands_sharers].  A deduplicating FTL has to
   repoint every reader of the source page at once. *)
Definition redirect (m : Addr -> Page -> option PhysAddr) (src dst : PhysAddr)
  : Addr -> Page -> option PhysAddr :=
  fun x y => match m x y with
             | Some pa0 => if phys_eqb pa0 src then Some dst else Some pa0
             | None => None
             end.

Lemma redirect_hit :
  forall m src dst x y, m x y = Some src -> redirect m src dst x y = Some dst.
Proof.
  intros m src dst x y H. unfold redirect. rewrite H, phys_eqb_refl. reflexivity.
Qed.

Lemma redirect_miss :
  forall m src dst x y pa0,
    m x y = Some pa0 -> pa0 <> src -> redirect m src dst x y = Some pa0.
Proof.
  intros m src dst x y pa0 H Hne. unfold redirect. rewrite H.
  destruct (phys_eqb pa0 src) eqn:E; [|reflexivity].
  exfalso. exact (Hne (phys_eqb_eq _ _ E)).
Qed.

Lemma redirect_case :
  forall m src dst x y pa0,
    redirect m src dst x y = Some pa0 ->
    (pa0 = dst /\ m x y = Some src) \/ (m x y = Some pa0 /\ pa0 <> src).
Proof.
  intros m src dst x y pa0 H.
  assert (Hd : forall o, m x y = o ->
                 (pa0 = dst /\ o = Some src) \/ (o = Some pa0 /\ pa0 <> src)).
  { intros o Ho. unfold redirect in H. rewrite Ho in H.
    destruct o as [pa1|]; [|discriminate].
    destruct (phys_eqb pa1 src) eqn:Eq.
    - left. injection H as H. subst pa0. split; [reflexivity|].
      rewrite (phys_eqb_eq _ _ Eq). reflexivity.
    - right. injection H as H. subst pa1. split; [reflexivity|].
      exact (phys_eqb_neq _ _ Eq). }
  destruct (Hd (m x y) eq_refl) as [[E1 E2]|[E1 E2]].
  - left. split; assumption.
  - right. split; assumption.
Qed.

Definition reloc_program (s : FTLState) (a : Addr) (p : Page) (d : Data)
                         (src pa : PhysAddr) : FTLState :=
  let t := match addr_tenant s a with Some t => t | None => 0 end in
  let n := match addr_namespace s a with Some n => n | None => 0 end in
  mkFTLState
    (redirect (l2p_map s) src pa)
    (set_page_state (page_state s) (pa_block pa) (pa_page pa) (PS_Valid d))
    (set_page_role  (page_role s)  (pa_block pa) (pa_page pa) (Some RData))
    (addr_tenant s)
    (addr_namespace s)
    (set_block_tenant (block_tenant s) (pa_block pa) (addr_tenant s a))
    (set_block_namespace (block_namespace s) (pa_block pa) (addr_namespace s a))
    (set_page_meta (page_meta s) (pa_block pa) (pa_page pa)
                   (mkPageMeta t n (Some d) (Some (a, p))))
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s) (open_block s) (write_ptr s)
    (block_open s).

Definition dedup_relocate_page (s : FTLState) (b : Block) (q : Page)
  : option FTLState :=
  match page_state s b q with
  | PS_Valid d =>
      match page_lpa (page_meta s b q) with
      | Some (a, p) =>
          match addr_tenant s a, addr_namespace s a with
          | Some t, Some ns =>
              match alloc_page s t ns with
              | Some (pa, s1) =>
                  Some (reloc_program s1 a p d (mkPhysAddr b q) pa)
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _ => Some s
  end.

Fixpoint dedup_relocate_pages (s : FTLState) (b : Block) (ps : list Page)
  : option FTLState :=
  match ps with
  | [] => Some s
  | q :: tl =>
      match dedup_relocate_page s b q with
      | Some s1 => dedup_relocate_pages s1 b tl
      | None => None
      end
  end.

Definition dedup_reclaim (s : FTLState) (b : Block) : option FTLState :=
  match dedup_relocate_pages s b all_pages with
  | Some s1 => Some (erase_block s1 b)
  | None => None
  end.

(* ── reclamation, parameterized over the victim chooser ─────────────────

   The framework separates *what* a reclaim does from *which* block it
   reclaims: [reclaim_with pick] is the transformer, [victim_sound] is the
   contract on the policy, and the two host-visible maintenance operations
   are the two instances [gc] and [wear_level].  Deduplication changes the
   transformer -- [dedup_relocate_page] redirects every reader of the
   relocated page rather than only the stamped one (Finding 2a) -- but it
   changes nothing about the policy interface.  [victim_sound] speaks only
   about the geometry and the free/open bits; it does not mention the
   invariant bundle, so it is one of the framework definitions that
   survives the weakening verbatim, and the separation applies here
   unchanged. *)
Definition dedup_reclaim_with (pick : FTLState -> option Block)
                              (s : FTLState) : option FTLState :=
  match pick s with
  | Some b => dedup_reclaim s b
  | None => None
  end.

Definition dedup_gc (s : FTLState) : option FTLState :=
  dedup_reclaim_with find_victim s.

(* Static wear levelling: the same reclaim under the least-worn-block
   policy.  Deduplication does not change this either.  No clause of the
   bundle constrains [wear_count] -- not one of the framework's 29, hence
   not one of the 28 that survive here -- so the wear-aware chooser is
   admissible for exactly the reason the framework's is, and the one
   generalized proof below covers both. *)
Definition dedup_wear_level (s : FTLState) : option FTLState :=
  dedup_reclaim_with find_least_worn_victim s.

Definition dedup_step (s : FTLState) (op : COp) : option FTLState :=
  match op with
  | COpRead _ _ => Some s
  | COpWrite a p d =>
      if andb (andb (Nat.ltb a addr_space) (Nat.ltb p pages_per_block))
              (match addr_tenant s a, addr_namespace s a with
               | Some _, Some _ => true | _, _ => false end)
      then dedup_write s a p d
      else None
  | COpInvalidate a p => Some (dedup_invalidate s a p)
  | COpSetTag a p tag => Some (exec_set_tag s a p tag)
  | COpGC => dedup_gc s
  | COpWearLevel => dedup_wear_level s
  end.

(* ── measurement 5: the framework's relocation is unsound here ─────── *)

(* [relocate_page] repoints only the logical address in the OOB stamp.
   Any other reader of the same physical page is left pointing at it, and
   [reclaim] then erases the block underneath that pointer.  Neither Inv2
   nor Inv2_dedup can rescue this; the operation itself has to change. *)
Theorem framework_relocation_strands_sharers :
  forall s vb q s' a1 p1 a2 p2,
    page_lpa (page_meta s vb q) = Some (a1, p1) ->
    l2p_map s a2 p2 = Some (mkPhysAddr vb q) ->
    (a2 <> a1 \/ p2 <> p1) ->
    relocate_page s vb q = Some s' ->
    l2p_map s' a2 p2 = Some (mkPhysAddr vb q) /\
    page_state (erase_block s' vb) vb q = PS_Empty /\
    ~ Inv22 (erase_block s' vb).
Proof.
  intros s vb q s' a1 p1 a2 p2 Hstamp Hmap Hne Hrel.
  unfold relocate_page in Hrel. rewrite Hstamp in Hrel.
  destruct (page_state s vb q) as [| |d] eqn:Hps.
  - injection Hrel as Hrel. subst s'.
    (* the page is not live, so nothing was relocated; but then Inv22 is
       already broken at [s] and stays broken after the erase *)
    split; [exact Hmap|]. split; [apply eb_ps_self|].
    intro I24. destruct (I24 a2 p2 (mkPhysAddr vb q) Hmap) as [dd Hdd].
    cbn [pa_block pa_page] in Hdd. rewrite eb_ps_self in Hdd. discriminate.
  - injection Hrel as Hrel. subst s'.
    split; [exact Hmap|]. split; [apply eb_ps_self|].
    intro I24. destruct (I24 a2 p2 (mkPhysAddr vb q) Hmap) as [dd Hdd].
    cbn [pa_block pa_page] in Hdd. rewrite eb_ps_self in Hdd. discriminate.
  - destruct (addr_tenant s a1) as [t|] eqn:Hat;
      destruct (addr_namespace s a1) as [ns|] eqn:Han;
      cbv beta iota in Hrel; try discriminate.
    destruct (alloc_page s t ns) as [[pa s1]|] eqn:Halloc;
      cbv beta iota in Hrel; [|discriminate].
    injection Hrel as Hrel. subst s'.
    destruct (alloc_page_fields s t ns pa s1 Halloc) as (Els1 & _).
    assert (Hmap1 : l2p_map s1 a2 p2 = Some (mkPhysAddr vb q))
      by (rewrite Els1; exact Hmap).
    assert (Hkeep : l2p_map (program_page s1 a1 p1 d pa) a2 p2 =
                    Some (mkPhysAddr vb q)).
    { change (l2p_map (program_page s1 a1 p1 d pa))
        with (set_l2p_map (l2p_map s1) a1 p1 (Some pa)).
      rewrite (set_l2p_other _ _ _ _ _ _ Hne). exact Hmap1. }
    split; [exact Hkeep|]. split; [apply eb_ps_self|].
    intro I24.
    assert (Hmap2 : l2p_map (erase_block (program_page s1 a1 p1 d pa) vb) a2 p2
                    = Some (mkPhysAddr vb q)) by (rewrite eb_l2p; exact Hkeep).
    destruct (I24 a2 p2 (mkPhysAddr vb q) Hmap2) as [dd Hdd].
    cbn [pa_block pa_page] in Hdd. rewrite eb_ps_self in Hdd. discriminate.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- detaching a logical page from a possibly shared physical one.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma phys_neq_split :
  forall x y : PhysAddr,
    x <> y -> (pa_block x <> pa_block y \/ pa_page x <> pa_page y).
Proof.
  intros [b1 q1] [b2 q2] Hne.
  destruct (nat_pair_dec b1 b2 q1 q2) as [[E1 E2]|H'];
    [subst; exfalso; exact (Hne eq_refl) | exact H'].
Qed.

Lemma unmap_here : forall s a p, l2p_map (unmap s a p) a p = None.
Proof. intros s a p. exact (set_l2p_here (l2p_map s) a p None). Qed.

Lemma unmap_other :
  forall s a p x y,
    (x <> a \/ y <> p) -> l2p_map (unmap s a p) x y = l2p_map s x y.
Proof.
  intros s a p x y H. exact (set_l2p_other (l2p_map s) a p None x y H).
Qed.

(* ── the shared branch: the stamped reader goes, another one stays ── *)

Lemma release_shared_ok :
  forall s a p old a0 p0,
    dedup_invariant s ->
    l2p_map s a p = Some old ->
    l2p_map (unmap s a p) a0 p0 = Some old ->
    dedup_invariant (restamp (unmap s a p) old a0 p0).
Proof.
  intros s a p old a0 p0 Hinv Hold Hm0.
  destruct Hinv as (I0&I1&I2&I3&I4d&I5d&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  destruct (I24 a p old Hold) as [dold Hlive].
  pose proof (I7 a p old Hold) as Hnf.
  assert (Hsub : forall x y pa0, l2p_map (unmap s a p) x y = Some pa0 ->
                   l2p_map s x y = Some pa0 /\ (x <> a \/ y <> p)).
  { intros x y pa0 H. destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
    - subst x y. rewrite unmap_here in H. discriminate.
    - rewrite (unmap_other s a p x y Hne) in H. split; [exact H|exact Hne]. }
  assert (Hup : forall x y pa0, l2p_map s x y = Some pa0 ->
                  (x <> a \/ y <> p) -> l2p_map (unmap s a p) x y = Some pa0).
  { intros x y pa0 H Hne. rewrite (unmap_other s a p x y Hne). exact H. }
  set (s' := restamp (unmap s a p) old a0 p0).
  assert (Els : l2p_map s' = l2p_map (unmap s a p)) by reflexivity.
  assert (Eps : page_state s' = page_state s) by reflexivity.
  assert (Epr : page_role s' = page_role s) by reflexivity.
  assert (Eat : addr_tenant s' = addr_tenant s) by reflexivity.
  assert (Ean : addr_namespace s' = addr_namespace s) by reflexivity.
  assert (Ebt : block_tenant s' = block_tenant s) by reflexivity.
  assert (Ebn : block_namespace s' = block_namespace s) by reflexivity.
  assert (Ert : region_table s' = region_table s) by reflexivity.
  assert (Efbl : free_block_list s' = free_block_list s) by reflexivity.
  assert (Efb : free_block s' = free_block s) by reflexivity.
  assert (Eob : open_block s' = open_block s) by reflexivity.
  assert (Ewp : write_ptr s' = write_ptr s) by reflexivity.
  assert (Ebo : block_open s' = block_open s) by reflexivity.
  assert (Epm_here : page_meta s' (pa_block old) (pa_page old) =
            mkPageMeta
              (page_owner_tenant (page_meta s (pa_block old) (pa_page old)))
              (page_owner_namespace (page_meta s (pa_block old) (pa_page old)))
              (page_tag (page_meta s (pa_block old) (pa_page old)))
              (Some (a0, p0))).
  { unfold s', restamp. cbn [page_meta]. apply set_pm_here. }
  assert (Epm_other : forall x y,
            (x <> pa_block old \/ y <> pa_page old) ->
            page_meta s' x y = page_meta s x y).
  { intros x y H. unfold s', restamp. cbn [page_meta].
    apply (set_pm_other (page_meta s) (pa_block old) (pa_page old) _ x y H). }
  assert (Epm_own : forall x y,
            page_owner_tenant (page_meta s' x y) =
            page_owner_tenant (page_meta s x y) /\
            page_owner_namespace (page_meta s' x y) =
            page_owner_namespace (page_meta s x y) /\
            page_tag (page_meta s' x y) = page_tag (page_meta s x y)).
  { intros x y. destruct (nat_pair_dec x (pa_block old) y (pa_page old))
      as [[E1 E2]|Hne].
    - subst x y. rewrite Epm_here. cbn. repeat split; reflexivity.
    - rewrite (Epm_other x y Hne). repeat split; reflexivity. }
  assert (K15 : Inv13 s').
  { intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr. exact (I15 b0 q0 d0 Hv). }
  assert (K17 : Inv15 s').
  { intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps. exact (I17 b0 q0 Hr). }
  assert (K20 : Inv18 s').
  { intros x y pa1 Hm. rewrite Els in Hm. destruct (Hsub x y pa1 Hm) as [Hms _].
    rewrite Ebt, Ebn, Eat, Ean. exact (I20 x y pa1 Hms). }
  assert (K24 : Inv22 s').
  { intros x y pa1 Hm. rewrite Els in Hm. destruct (Hsub x y pa1 Hm) as [Hms _].
    rewrite Eps. exact (I24 x y pa1 Hms). }
  apply make_dedup_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (I2 b0 q0 d0 Hv) as (x & y & Hmx).
    destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
    + subst x y. rewrite Hold in Hmx. injection Hmx as Hmx.
      exists a0, p0. rewrite Els, <- Hmx. exact Hm0.
    + exists x, y. rewrite Els. exact (Hup x y _ Hmx Hne).
  - (* Inv1 *) intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. exact (I3 x y pa1 Hms).
  - (* Inv2_dedup *) exact (Inv2_dedup_is_derivable s' K20 K24).
  - (* Inv3_dedup *) intros x y pa1 d0 Hm Hv. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Eps in Hv.
    destruct (phys_dec pa1 old) as [E|E].
    + subst pa1. exists a0, p0. split.
      * rewrite Epm_here. reflexivity.
      * rewrite Els. exact Hm0.
    + pose proof (phys_neq_split pa1 old E) as Hd.
      destruct (I5d x y pa1 d0 Hms Hv) as (b1 & q1 & Hst & Hmb).
      exists b1, q1. split.
      * rewrite (Epm_other _ _ Hd). exact Hst.
      * rewrite Els. apply (Hup b1 q1 pa1 Hmb).
        destruct (nat_pair_dec b1 a q1 p) as [[G1 G2]|G]; [|exact G].
        exfalso. subst b1 q1. rewrite Hold in Hmb. injection Hmb as Hmb.
        exact (E (eq_sym Hmb)).
  - (* Inv4 *) intros x y b0 q0 d0 Hv Hlpa. rewrite Eps in Hv. rewrite Els.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite Epm_here in Hlpa. cbn in Hlpa.
      injection Hlpa as F1 F2. subst x y. rewrite physaddr_eta. exact Hm0.
    + rewrite (Epm_other b0 q0 Hne) in Hlpa.
      pose proof (I6 x y b0 q0 d0 Hv Hlpa) as Hmx.
      apply (Hup x y _ Hmx).
      destruct (nat_pair_dec x a y p) as [[G1 G2]|G]; [|exact G].
      exfalso. subst x y. rewrite Hold in Hmx. injection Hmx as Hmx.
      subst old. cbn in Hne. destruct Hne as [Z|Z]; exact (Z eq_refl).
  - (* Inv5 *) intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Efbl. exact (I7 x y pa1 Hms).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    assert (Hne : b0 <> pa_block old \/ q0 <> pa_page old)
      by (left; intro E; subst b0; exact (Hnf Hin)).
    rewrite Eps, (Epm_other b0 q0 Hne). exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros x y pa1 d0 t0 n0 Hm Hv Ht Hn. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Eps in Hv.
    rewrite Eat in Ht. rewrite Ean in Hn.
    destruct (Epm_own (pa_block pa1) (pa_page pa1)) as [G1 [G2 _]].
    rewrite G1, G2. exact (I9 x y pa1 d0 t0 n0 Hms Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (I11 b0 q0 d0 Hv) as [tag Htag]. exists tag.
    destruct (Epm_own b0 q0) as [_ [_ G3]]. rewrite G3. exact Htag.
  - (* Inv10 *) intros b0 Hb0.
    destruct (I12 b0 Hb0)
      as [Hin | [[t0 [ns0 Hob]] | [(x&y&pa1&Hmx&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob.
    + destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
      * subst x y. rewrite Hold in Hmx. injection Hmx as Hmx. subst pa1.
        right; right; left. exists a0, p0, old.
        split; [rewrite Els; exact Hm0 | exact Hblk].
      * right; right; left. exists x, y, pa1.
        split; [rewrite Els; exact (Hup x y _ Hmx Hne) | exact Hblk].
    + right; right; right. exists q0. rewrite Eps. exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) exact (Inv12_from_Inv13_Inv15 s' K15 K17).
  - (* Inv13 *) exact K15.
  - (* Inv14 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    exact (I16 b0 q0 Hr).
  - (* Inv15 *) exact K17.
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    exact (I19 b0 Hf).
  - (* Inv18 *) exact K20.
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t0 ns0 b0 Hob. rewrite Eob in Hob.
    rewrite Efbl, Efb, Ebo, Ewp, Ebt, Ebn, Eob. exact (I22 t0 ns0 b0 Hob).
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob Hwp Hq0. rewrite Eob in Hob.
    rewrite Ewp in Hwp.
    destruct (I23 t0 ns0 b0 q0 Hob Hwp Hq0) as [He Hm1].
    assert (Hne : b0 <> pa_block old \/ q0 <> pa_page old).
    { destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|H']; [|exact H'].
      exfalso. subst b0 q0. rewrite He in Hlive. discriminate. }
    rewrite Eps, (Epm_other b0 q0 Hne). split; [exact He|exact Hm1].
  - (* Inv22 *) exact K24.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob Hlt. rewrite Eob in Hob.
    rewrite Ewp in Hlt. rewrite Eps. exact (I27 t0 ns0 b0 q0 Hob Hlt).
  - (* Inv26 *) intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Eat, Ean.
    exact (I28 x y pa1 Hms).
Qed.

(* ── the last-reader branch: nobody is left, so stale the page ────── *)

Lemma release_last_ok :
  forall s a p old,
    dedup_invariant s ->
    l2p_map s a p = Some old ->
    (forall x y, l2p_map (unmap s a p) x y <> Some old) ->
    dedup_invariant (invalidate_at (unmap s a p) old).
Proof.
  intros s a p old Hinv Hold Hno.
  destruct Hinv as (I0&I1&I2&I3&I4d&I5d&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  destruct (I24 a p old Hold) as [dold Hlive].
  pose proof (I7 a p old Hold) as Hnf.
  assert (Hsub : forall x y pa0, l2p_map (unmap s a p) x y = Some pa0 ->
                   l2p_map s x y = Some pa0 /\ (x <> a \/ y <> p) /\ pa0 <> old).
  { intros x y pa0 H. destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
    - subst x y. rewrite unmap_here in H. discriminate.
    - assert (Hne2 : pa0 <> old) by (intro E; subst pa0; exact (Hno x y H)).
      rewrite (unmap_other s a p x y Hne) in H.
      split; [exact H|split; [exact Hne|exact Hne2]]. }
  assert (Hup : forall x y pa0, l2p_map s x y = Some pa0 ->
                  (x <> a \/ y <> p) -> l2p_map (unmap s a p) x y = Some pa0).
  { intros x y pa0 H Hne. rewrite (unmap_other s a p x y Hne). exact H. }
  set (s' := invalidate_at (unmap s a p) old).
  assert (Els : l2p_map s' = l2p_map (unmap s a p)) by reflexivity.
  assert (Eps : page_state s' =
                set_page_state (page_state s) (pa_block old) (pa_page old)
                               PS_Invalid) by reflexivity.
  assert (Epr : page_role s' =
                set_page_role (page_role s) (pa_block old) (pa_page old) None)
    by reflexivity.
  assert (Epm : page_meta s' =
                set_page_meta (page_meta s) (pa_block old) (pa_page old)
                              empty_page_meta) by reflexivity.
  assert (Eat : addr_tenant s' = addr_tenant s) by reflexivity.
  assert (Ean : addr_namespace s' = addr_namespace s) by reflexivity.
  assert (Ebt : block_tenant s' = block_tenant s) by reflexivity.
  assert (Ebn : block_namespace s' = block_namespace s) by reflexivity.
  assert (Ert : region_table s' = region_table s) by reflexivity.
  assert (Efbl : free_block_list s' = free_block_list s) by reflexivity.
  assert (Efb : free_block s' = free_block s) by reflexivity.
  assert (Eob : open_block s' = open_block s) by reflexivity.
  assert (Ewp : write_ptr s' = write_ptr s) by reflexivity.
  assert (Ebo : block_open s' = block_open s) by reflexivity.
  assert (Hstale : page_state s' (pa_block old) (pa_page old) = PS_Invalid)
    by (rewrite Eps; apply set_ps_here).
  assert (K15 : Inv13 s').
  { intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    - subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    - rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I15 b0 q0 d0 Hv). }
  assert (K17 : Inv15 s').
  { intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    - subst b0 q0. rewrite set_pr_here in Hr. discriminate.
    - rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I17 b0 q0 Hr). }
  assert (K20 : Inv18 s').
  { intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Ebt, Ebn, Eat, Ean.
    exact (I20 x y pa1 Hms). }
  assert (K24 : Inv22 s').
  { intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms [_ Hd]].
    rewrite Eps, (set_ps_other _ _ _ _ _ _ (phys_neq_split pa1 old Hd)).
    exact (I24 x y pa1 Hms). }
  apply make_dedup_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      destruct (I2 b0 q0 d0 Hv) as (x & y & Hmx).
      assert (Hne2 : x <> a \/ y <> p).
      { destruct (nat_pair_dec x a y p) as [[E1 E2]|G]; [|exact G].
        exfalso. subst x y. rewrite Hold in Hmx. injection Hmx as Hmx.
        subst old. cbn in Hne. destruct Hne as [Z|Z]; exact (Z eq_refl). }
      exists x, y. rewrite Els. exact (Hup x y _ Hmx Hne2).
  - (* Inv1 *) intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. exact (I3 x y pa1 Hms).
  - (* Inv2_dedup *) exact (Inv2_dedup_is_derivable s' K20 K24).
  - (* Inv3_dedup *) intros x y pa1 d0 Hm Hv. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms [_ Hd]].
    pose proof (phys_neq_split pa1 old Hd) as Hdd.
    rewrite Eps, (set_ps_other _ _ _ _ _ _ Hdd) in Hv.
    destruct (I5d x y pa1 d0 Hms Hv) as (b1 & q1 & Hst & Hmb).
    exists b1, q1. split.
    + rewrite Epm, (set_pm_other _ _ _ _ _ _ Hdd). exact Hst.
    + rewrite Els. apply (Hup b1 q1 pa1 Hmb).
      destruct (nat_pair_dec b1 a q1 p) as [[G1 G2]|G]; [|exact G].
      exfalso. subst b1 q1. rewrite Hold in Hmb. injection Hmb as Hmb.
      exact (Hd (eq_sym Hmb)).
  - (* Inv4 *) intros x y b0 q0 d0 Hv Hlpa. rewrite Eps in Hv.
    rewrite Epm in Hlpa. rewrite Els.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
      pose proof (I6 x y b0 q0 d0 Hv Hlpa) as Hmx.
      apply (Hup x y _ Hmx).
      destruct (nat_pair_dec x a y p) as [[G1 G2]|G]; [|exact G].
      exfalso. subst x y. rewrite Hold in Hmx. injection Hmx as Hmx.
      subst old. cbn in Hne. destruct Hne as [Z|Z]; exact (Z eq_refl).
  - (* Inv5 *) intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Efbl. exact (I7 x y pa1 Hms).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    assert (Hne : b0 <> pa_block old \/ q0 <> pa_page old)
      by (left; intro E; subst b0; exact (Hnf Hin)).
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hne),
            (set_pm_other _ _ _ _ _ _ Hne).
    exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros x y pa1 d0 t0 n0 Hm Hv Ht Hn. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms [_ Hd]].
    pose proof (phys_neq_split pa1 old Hd) as Hdd.
    rewrite Eps, (set_ps_other _ _ _ _ _ _ Hdd) in Hv.
    rewrite Eat in Ht. rewrite Ean in Hn.
    rewrite Epm, (set_pm_other _ _ _ _ _ _ Hdd).
    exact (I9 x y pa1 d0 t0 n0 Hms Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in Hv. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hne). exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) intros b0 Hb0.
    destruct (I12 b0 Hb0)
      as [Hin | [[t0 [ns0 Hob]] | [(x&y&pa1&Hmx&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob.
    + destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
      * subst x y. rewrite Hold in Hmx. injection Hmx as Hmx. subst pa1.
        right; right; right. exists (pa_page old). rewrite <- Hblk. exact Hstale.
      * right; right; left. exists x, y, pa1.
        split; [rewrite Els; exact (Hup x y _ Hmx Hne) | exact Hblk].
    + right; right; right. exists q0. rewrite Eps.
      destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|Hne].
      * subst b0 q0. apply set_ps_here.
      * rewrite (set_ps_other _ _ _ _ _ _ Hne). exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) exact (Inv12_from_Inv13_Inv15 s' K15 K17).
  - (* Inv13 *) exact K15.
  - (* Inv14 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hr. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I16 b0 q0 Hr).
  - (* Inv15 *) exact K17.
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in He. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in He.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    exact (I19 b0 Hf).
  - (* Inv18 *) exact K20.
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t0 ns0 b0 Hob. rewrite Eob in Hob.
    rewrite Efbl, Efb, Ebo, Ewp, Ebt, Ebn, Eob. exact (I22 t0 ns0 b0 Hob).
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob Hwp Hq0. rewrite Eob in Hob.
    rewrite Ewp in Hwp.
    destruct (I23 t0 ns0 b0 q0 Hob Hwp Hq0) as [He Hm1].
    assert (Hne : b0 <> pa_block old \/ q0 <> pa_page old).
    { destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old))
        as [[E1 E2]|H']; [|exact H'].
      exfalso. subst b0 q0. rewrite He in Hlive. discriminate. }
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hne),
            (set_pm_other _ _ _ _ _ _ Hne).
    split; [exact He|exact Hm1].
  - (* Inv22 *) exact K24.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob Hlt. rewrite Eob in Hob.
    rewrite Ewp in Hlt. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block old) q0 (pa_page old)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I27 t0 ns0 b0 q0 Hob Hlt).
  - (* Inv26 *) intros x y pa1 Hm. rewrite Els in Hm.
    destruct (Hsub x y pa1 Hm) as [Hms _]. rewrite Eat, Ean.
    exact (I28 x y pa1 Hms).
Qed.

(* ── the two branches assembled ────────────────────────────────────── *)

Theorem release_ok :
  forall s a p, dedup_invariant s -> dedup_invariant (release_old s a p).
Proof.
  intros s a p Hinv. unfold release_old.
  assert (I3 : Inv1 s) by (destruct Hinv as (_&_&_&H&_); exact H).
  destruct (l2p_map s a p) as [old|] eqn:Hold; [|exact Hinv].
  cbv zeta.
  assert (I3u : Inv1 (unmap s a p)).
  { intros x y pa0 Hm. destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
    - subst x y. rewrite unmap_here in Hm. discriminate.
    - rewrite (unmap_other s a p x y Hne) in Hm. exact (I3 x y pa0 Hm). }
  destruct (find_mapper (unmap s a p) old) as [[a0 p0]|] eqn:Hfm.
  - exact (release_shared_ok s a p old a0 p0 Hinv Hold
             (find_mapper_some (unmap s a p) old a0 p0 Hfm)).
  - exact (release_last_ok s a p old Hinv Hold
             (find_mapper_none (unmap s a p) old I3u Hfm)).
Qed.

Theorem dedup_invalidate_preserves_invariant :
  forall s a p s',
    dedup_invariant s -> dedup_step s (COpInvalidate a p) = Some s' ->
    dedup_invariant s'.
Proof.
  intros s a p s' Hinv Hstep. cbn in Hstep. injection Hstep as Hstep. subst s'.
  unfold dedup_invalidate. exact (release_ok s a p Hinv).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- the deduplicating branch of the write: attach (a, p) to an
   existing physical page.  No page is programmed and no page state
   changes; only [l2p_map] grows, and it grows non-injectively.  This is
   the step Inv2 forbade outright.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma dedup_hit_ok :
  forall s a p d t ns pa,
    dedup_invariant s ->
    l2p_map s a p = None ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s a = Some t -> addr_namespace s a = Some ns ->
    find_dup s t ns d = Some pa ->
    dedup_invariant (map_to s a p pa).
Proof.
  intros s a p d t ns pa Hinv Hnone Ha Hp Hat Han Hfd.
  destruct Hinv as (I0&I1&I2&I3&I4d&I5d&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  destruct (find_dup_spec s t ns d pa Hfd) as (Hval & Hot & Hon & Hblt & Hplt).
  (* the reused page already has a reader; everything the new mapping
     needs about it comes from that reader through Inv5, Inv7 and Inv18 *)
  destruct (I2 (pa_block pa) (pa_page pa) d Hval) as (a1 & p1 & Hm1').
  assert (Hm1 : l2p_map s a1 p1 = Some pa)
    by (rewrite Hm1', physaddr_eta; reflexivity).
  destruct (I28 a1 p1 pa Hm1) as [[t1 Ht1] [ns1 Hns1]].
  destruct (I9 a1 p1 pa d t1 ns1 Hm1 Hval Ht1 Hns1) as [Gt Gn].
  rewrite Hot in Gt. rewrite Hon in Gn. subst t1 ns1.
  destruct (I20 a1 p1 pa Hm1) as [Bt Bn].
  rewrite Ht1 in Bt. rewrite Hns1 in Bn.
  pose proof (I7 a1 p1 pa Hm1) as Hnfl.
  assert (Hne_ap : forall a0 p0 pa0, l2p_map s a0 p0 = Some pa0 ->
                     (a0 <> a \/ p0 <> p)).
  { intros a0 p0 pa0 H. destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|G];
      [|exact G]. exfalso. subst a0 p0. rewrite Hnone in H. discriminate. }
  set (s' := map_to s a p pa).
  assert (Els : l2p_map s' = set_l2p_map (l2p_map s) a p (Some pa))
    by reflexivity.
  assert (Eps : page_state s' = page_state s) by reflexivity.
  assert (Epr : page_role s' = page_role s) by reflexivity.
  assert (Epm : page_meta s' = page_meta s) by reflexivity.
  assert (Eat : addr_tenant s' = addr_tenant s) by reflexivity.
  assert (Ean : addr_namespace s' = addr_namespace s) by reflexivity.
  assert (Ebt : block_tenant s' = block_tenant s) by reflexivity.
  assert (Ebn : block_namespace s' = block_namespace s) by reflexivity.
  assert (Ert : region_table s' = region_table s) by reflexivity.
  assert (Efbl : free_block_list s' = free_block_list s) by reflexivity.
  assert (Efb : free_block s' = free_block s) by reflexivity.
  assert (Eob : open_block s' = open_block s) by reflexivity.
  assert (Ewp : write_ptr s' = write_ptr s) by reflexivity.
  assert (Ebo : block_open s' = block_open s) by reflexivity.
  assert (Hsub : forall x y pa0, l2p_map s' x y = Some pa0 ->
                   (x = a /\ y = p /\ pa0 = pa) \/ l2p_map s x y = Some pa0).
  { intros x y pa0 Hm. rewrite Els in Hm.
    destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
    - subst x y. rewrite set_l2p_here in Hm. injection Hm as Hm.
      left. split; [reflexivity|split; [reflexivity|exact (eq_sym Hm)]].
    - right. rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hm. exact Hm. }
  assert (Hkeep : forall x y pa0, l2p_map s x y = Some pa0 ->
                    l2p_map s' x y = Some pa0).
  { intros x y pa0 Hm. rewrite Els.
    rewrite (set_l2p_other _ _ _ _ _ _ (Hne_ap x y pa0 Hm)). exact Hm. }
  assert (Khere : l2p_map s' a p = Some pa)
    by (rewrite Els; apply set_l2p_here).
  assert (K20 : Inv18 s').
  { intros x y pa0 Hm. rewrite Ebt, Ebn, Eat, Ean.
    destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms].
    - subst x y pa0. rewrite Hat, Han. split; [exact Bt|exact Bn].
    - exact (I20 x y pa0 Hms). }
  assert (K24 : Inv22 s').
  { intros x y pa0 Hm. rewrite Eps.
    destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms].
    - subst x y pa0. exists d. exact Hval.
    - exact (I24 x y pa0 Hms). }
  apply make_dedup_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (I2 b0 q0 d0 Hv) as (x & y & Hmx).
    exists x, y. exact (Hkeep x y _ Hmx).
  - (* Inv1 *) intros x y pa0 Hm.
    destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms].
    + subst x y pa0. repeat split; assumption.
    + exact (I3 x y pa0 Hms).
  - (* Inv2_dedup *) exact (Inv2_dedup_is_derivable s' K20 K24).
  - (* Inv3_dedup *) intros x y pa0 d0 Hm Hv. rewrite Eps in Hv. rewrite Epm.
    assert (Hms : l2p_map s x y = Some pa0 \/ pa0 = pa).
    { destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms];
        [right; exact E3 | left; exact Hms]. }
    destruct Hms as [Hms|E].
    + destruct (I5d x y pa0 d0 Hms Hv) as (b1 & q1 & Hst & Hmb).
      exists b1, q1. split; [exact Hst | exact (Hkeep b1 q1 pa0 Hmb)].
    + subst pa0. destruct (I5d a1 p1 pa d0 Hm1 Hv) as (b1 & q1 & Hst & Hmb).
      exists b1, q1. split; [exact Hst | exact (Hkeep b1 q1 pa Hmb)].
  - (* Inv4 *) intros x y b0 q0 d0 Hv Hlpa. rewrite Eps in Hv.
    rewrite Epm in Hlpa. exact (Hkeep x y _ (I6 x y b0 q0 d0 Hv Hlpa)).
  - (* Inv5 *) intros x y pa0 Hm. rewrite Efbl.
    destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms].
    + subst pa0. exact Hnfl.
    + exact (I7 x y pa0 Hms).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin. rewrite Eps, Epm.
    exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros x y pa0 d0 t0 n0 Hm Hv Ht Hn. rewrite Eps in Hv.
    rewrite Eat in Ht. rewrite Ean in Hn. rewrite Epm.
    destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms].
    + subst x y pa0. rewrite Hat in Ht. rewrite Han in Hn.
      injection Ht as Ht. injection Hn as Hn. subst t0 n0.
      split; [exact Hot|exact Hon].
    + exact (I9 x y pa0 d0 t0 n0 Hms Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epm.
    exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) intros b0 Hb0.
    destruct (I12 b0 Hb0)
      as [Hin | [[t0 [ns0 Hob]] | [(x&y&pa0&Hmx&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob.
    + right; right; left. exists x, y, pa0.
      split; [exact (Hkeep x y _ Hmx) | exact Hblk].
    + right; right; right. exists q0. rewrite Eps. exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) intros b0 Hb0 Hr. rewrite Epr in Hr.
    destruct (I14 b0 Hb0 Hr) as [(x&y&pa0&Hmx&Hblk)|[q0 Hq0]].
    + left. exists x, y, pa0. split; [exact (Hkeep x y _ Hmx) | exact Hblk].
    + right. exists q0. rewrite Eps. exact Hq0.
  - (* Inv13 *) intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr.
    exact (I15 b0 q0 d0 Hv).
  - (* Inv14 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    exact (I16 b0 q0 Hr).
  - (* Inv15 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    exact (I17 b0 q0 Hr).
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    exact (I19 b0 Hf).
  - (* Inv18 *) exact K20.
  - (* Inv19 *) intros i r Hr. rewrite Ert in Hr. exact (I21 i r Hr).
  - (* Inv20 *) intros t0 ns0 b0 Hob. rewrite Eob in Hob.
    rewrite Efbl, Efb, Ebo, Ewp, Ebt, Ebn, Eob. exact (I22 t0 ns0 b0 Hob).
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob Hwp Hq0. rewrite Eob in Hob.
    rewrite Ewp in Hwp. rewrite Eps, Epm. exact (I23 t0 ns0 b0 q0 Hob Hwp Hq0).
  - (* Inv22 *) exact K24.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob Hlt. rewrite Eob in Hob.
    rewrite Ewp in Hlt. rewrite Eps. exact (I27 t0 ns0 b0 q0 Hob Hlt).
  - (* Inv26 *) intros x y pa0 Hm. rewrite Eat, Ean.
    destruct (Hsub x y pa0 Hm) as [(E1 & E2 & E3)|Hms].
    + subst x y. split; [exists t; exact Hat | exists ns; exact Han].
    + exact (I28 x y pa0 Hms).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- the out-of-place branch of the write: no duplicate was
   found, so a fresh page is programmed.  [pa] is the page just handed
   out by [alloc_page]: top of the open block of (t, ns), one below that
   pair's frontier, still erased.  Because [release_old] has already
   detached (a, p), the map has no entry for it, which is what replaces
   the framework's use of Inv2 to argue that the old page was staled.
   ══════════════════════════════════════════════════════════════════════ *)

Lemma program_ok_d :
  forall (s2 : FTLState) (a : Addr) (p : Page) (d : Data)
         (t : TenantId) (ns : NamespaceId) (pa : PhysAddr),
    WF0 s2 -> WF1 s2 -> Inv0 s2 -> Inv1 s2 -> Inv3_dedup s2 -> Inv4 s2 ->
    Inv5 s2 -> Inv6 s2 -> Inv7 s2 -> Inv8 s2 -> Inv9 s2 -> Inv10 s2 ->
    Inv11 s2 -> Inv13 s2 -> Inv14 s2 -> Inv15 s2 -> Inv16 s2 -> Inv17 s2 ->
    Inv18 s2 -> Inv19 s2 -> Inv20 s2 -> Inv21 s2 -> Inv22 s2 -> Inv23 s2 ->
    Inv24 s2 -> Inv26 s2 ->
    (forall t0 ns0 b0 q0, open_block s2 t0 ns0 = Some b0 ->
       q0 < write_ptr s2 t0 ns0 ->
       (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
       page_state s2 b0 q0 <> PS_Empty) ->
    l2p_map s2 a p = None ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s2 a = Some t ->
    addr_namespace s2 a = Some ns ->
    open_block s2 t ns = Some (pa_block pa) ->
    write_ptr s2 t ns = S (pa_page pa) ->
    pa_page pa < pages_per_block ->
    page_state s2 (pa_block pa) (pa_page pa) = PS_Empty ->
    dedup_invariant (program_page s2 a p d pa).
Proof.
  intros s2 a p d t ns pa I0 I1 I2 I3 I5d I6 I7 I8 I9 I10 I11 I12 I13 I15
         I16 I17 I18 I19 I20 I21 I22 I23 I24 I25 I26 I28 I27r Hnone
         Ha Hp Hat Han Hob Hwp Hpp Hempty.
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
  (* the released logical page has no entry, so no old mapping is (a, p) *)
  assert (Hne_ap : forall a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 ->
                     (a0 <> a \/ p0 <> p)).
  { intros a0 p0 pa0 H. destruct (nat_pair_dec a0 a p0 p) as [[E1 E2]|G];
      [|exact G]. exfalso. subst a0 p0. rewrite Hnone in H. discriminate. }
  assert (Hsub : forall x y pa0, l2p_map s' x y = Some pa0 ->
                   (x = a /\ y = p /\ pa0 = pa) \/ l2p_map s2 x y = Some pa0).
  { intros x y pa0 Hm. rewrite Els in Hm.
    destruct (nat_pair_dec x a y p) as [[E1 E2]|Hne].
    - subst x y. rewrite set_l2p_here in Hm. injection Hm as Hm.
      left. split; [reflexivity|split; [reflexivity|exact (eq_sym Hm)]].
    - right. rewrite (set_l2p_other _ _ _ _ _ _ Hne) in Hm. exact Hm. }
  assert (Hkeep : forall x y pa0, l2p_map s2 x y = Some pa0 ->
                    l2p_map s' x y = Some pa0).
  { intros x y pa0 Hm. rewrite Els.
    rewrite (set_l2p_other _ _ _ _ _ _ (Hne_ap x y pa0 Hm)). exact Hm. }
  assert (Khere : l2p_map s' a p = Some pa)
    by (rewrite Els; apply set_l2p_here).
  assert (K15 : Inv13 s').
  { intros b0 q0 d0 Hv. rewrite Eps in Hv. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    - subst b0 q0. apply set_pr_here.
    - rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I15 b0 q0 d0 Hv). }
  assert (K17 : Inv15 s').
  { intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    - subst b0 q0. rewrite set_pr_here in Hr. discriminate.
    - rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I17 b0 q0 Hr). }
  assert (K20 : Inv18 s').
  { intros a0 p0 pa0 Hmap. rewrite Ebt, Ebn, Eat, Ean.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    - subst a0 p0 pa0. rewrite set_bt_here, set_bn_here. split; reflexivity.
    - destruct (I20 a0 p0 pa0 Hms) as [Gt Gn].
      destruct (Nat.eq_dec (pa_block pa0) (pa_block pa)) as [E|E].
      + (* a0 already has a page in the open block: the re-stamp is a no-op *)
        rewrite E, set_bt_here, set_bn_here.
        destruct (I28 a0 p0 pa0 Hms) as [[t0 Ht0] [ns0 Hns0]].
        rewrite E in Gt, Gn. rewrite Ht0 in Gt. rewrite Hns0 in Gn.
        destruct Hbtd as [Hbtd|Hbtd]; rewrite Hbtd in Gt; [discriminate|].
        injection Gt as Gt. subst t0.
        destruct Hbnd as [Hbnd|Hbnd]; rewrite Hbnd in Gn; [discriminate|].
        injection Gn as Gn. subst ns0.
        split; [rewrite Hat, Ht0; reflexivity | rewrite Han, Hns0; reflexivity].
      + rewrite (set_bt_other _ _ _ _ E), (set_bn_other _ _ _ _ E).
        split; [exact Gt|exact Gn]. }
  assert (K24 : Inv22 s').
  { intros a0 p0 pa0 Hmap. rewrite Eps.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    - subst a0 p0 pa0. exists d. apply set_ps_here.
    - pose proof (HnotPa a0 p0 pa0 Hms) as Hd.
      destruct (I24 a0 p0 pa0 Hms) as [dd Hdd].
      exists dd. rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hdd. }
  apply make_dedup_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. exists a, p. rewrite Khere, physaddr_eta. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      destruct (I2 b0 q0 d0 Hv) as (x & y & Hmx).
      exists x, y. exact (Hkeep x y _ Hmx).
  - (* Inv1 *) intros a0 p0 pa0 Hmap.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    + subst a0 p0 pa0. split; [exact Hbtb|]. split; [exact Hpp|].
      split; [exact Ha|exact Hp].
    + exact (I3 a0 p0 pa0 Hms).
  - (* Inv2_dedup *) exact (Inv2_dedup_is_derivable s' K20 K24).
  - (* Inv3_dedup *) intros a0 p0 pa0 d0 Hmap Hv.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    + subst a0 p0 pa0. exists a, p. split; [|exact Khere].
      rewrite Epm, set_pm_here. reflexivity.
    + pose proof (HnotPa a0 p0 pa0 Hms) as Hd.
      rewrite Eps, (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      destruct (I5d a0 p0 pa0 d0 Hms Hv) as (b1 & q1 & Hst & Hmb).
      exists b1, q1. split.
      * rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd). exact Hst.
      * exact (Hkeep b1 q1 pa0 Hmb).
  - (* Inv4 *) intros a0 p0 b0 q0 d0 Hv Hlpa. rewrite Eps in Hv.
    rewrite Epm in Hlpa.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pm_here in Hlpa. cbn in Hlpa.
      injection Hlpa as F1 F2. subst a0 p0.
      rewrite Khere, physaddr_eta. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
      exact (Hkeep a0 p0 _ (I6 a0 p0 b0 q0 d0 Hv Hlpa)).
  - (* Inv5 *) intros a0 p0 pa0 Hmap. rewrite Efbl.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    + subst pa0. exact Hnfl.
    + exact (I7 a0 p0 pa0 Hms).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa)
      by (left; intro E; subst b0; exact (Hnfl Hin)).
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hd),
            (set_pm_other _ _ _ _ _ _ Hd).
    exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros a0 p0 pa0 d0 t0 n0 Hmap Hv Ht Hn.
    rewrite Eat in Ht. rewrite Ean in Hn.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    + subst a0 p0 pa0. rewrite Epm, set_pm_here, Ht, Hn. cbn.
      split; reflexivity.
    + pose proof (HnotPa a0 p0 pa0 Hms) as Hd.
      rewrite Eps, (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd).
      exact (I9 a0 p0 pa0 d0 t0 n0 Hms Hv Ht Hn).
  - (* Inv8 *) intros b0 Hin. rewrite Efbl in Hin. exact (I10 b0 Hin).
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite Epm, set_pm_here. cbn. exists d. reflexivity.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hne). exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) intros b0 Hb0.
    destruct (I12 b0 Hb0)
      as [Hin | [[t0 [ns0 Hob0]] | [(x&y&pa0&Hmx&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob0.
    + right; right; left. exists x, y, pa0.
      split; [exact (Hkeep x y _ Hmx) | exact Hblk].
    + right; right; right. exists q0. rewrite Eps.
      assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa).
      { destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa))
          as [[F1 F2]|H']; [|exact H'].
        exfalso. subst b0 q0. rewrite Hempty in Hq0. discriminate. }
      rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hq0.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) exact (Inv12_from_Inv13_Inv15 s' K15 K17).
  - (* Inv13 *) exact K15.
  - (* Inv14 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. exists d. apply set_ps_here.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I16 b0 q0 Hr).
  - (* Inv15 *) exact K17.
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in He. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in He.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    assert (Hbne : b0 <> pa_block pa)
      by (intro E; subst b0; rewrite Hfbf in Hf; discriminate).
    rewrite (set_bt_other _ _ _ _ Hbne), (set_bn_other _ _ _ _ Hbne).
    exact (I19 b0 Hf).
  - (* Inv18 *) exact K20.
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
  - (* Inv22 *) exact K24.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob0 Hlt. rewrite Eob in Hob0.
    rewrite Ewp in Hlt. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne).
      exact (I27r t0 ns0 b0 q0 Hob0 Hlt Hne).
  - (* Inv26 *) intros a0 p0 pa0 Hmap. rewrite Eat, Ean.
    destruct (Hsub a0 p0 pa0 Hmap) as [(E1 & E2 & E3)|Hms].
    + subst a0 p0. split; [exists t; exact Hat|exists ns; exact Han].
    + exact (I28 a0 p0 pa0 Hms).
Qed.

(* ── allocating the destination of the out-of-place branch ────────── *)

Lemma alloc_ok_d :
  forall s a p d t ns pa s1,
    dedup_invariant s ->
    l2p_map s a p = None ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s a = Some t -> addr_namespace s a = Some ns ->
    alloc_page s t ns = Some (pa, s1) ->
    dedup_invariant (program_page s1 a p d pa).
Proof.
  intros s a p d t ns pa s1 Hinv Hnone Ha Hp Hat Han Halloc.
  destruct Hinv as (I0&I1&I2&I3&I4d&I5d&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  assert (Hppb : pages_per_block > 0) by exact I0.
  destruct (alloc_page_fields s t ns pa s1 Halloc)
    as (Els1 & Eps1 & Epr1 & Eat1 & Ean1 & Ebt1 & Ebn1 & Epm1 & Ert1).
  assert (J0 : WF0 s1) by exact I0.
  assert (J1 : WF1 s1) by (intros b0 p0 _ _; eexists; reflexivity).
  assert (J2 : Inv0 s1) by (unfold Inv0; rewrite Eps1, Els1; exact I2).
  assert (J3 : Inv1 s1) by (unfold Inv1; rewrite Els1; exact I3).
  assert (J5d : Inv3_dedup s1)
    by (unfold Inv3_dedup; rewrite Els1, Eps1, Epm1; exact I5d).
  assert (J6 : Inv4 s1) by (unfold Inv4; rewrite Eps1, Epm1, Els1; exact I6).
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
  assert (Hnone1 : l2p_map s1 a p = None) by (rewrite Els1; exact Hnone).
  assert (Hat1 : addr_tenant s1 a = Some t) by (rewrite Eat1; exact Hat).
  assert (Han1 : addr_namespace s1 a = Some ns) by (rewrite Ean1; exact Han).
  destruct (alloc_page_shape s t ns pa s1 Halloc)
    as [(b & Hob & Hlt & Epa & Efbl1 & Efb1 & Ebo1 & Eob1 & Ewp1)
       | (Hof & Hclosed)].
  - (* ── the frontier branch: the open block simply advances ──────── *)
    assert (Eob1' : forall x y, open_block s1 x y = open_block s x y).
    { intros x y. rewrite Eob1. destruct (nat_pair_dec x t y ns) as [[E1 E2]|E].
      - subst x y. rewrite set_ob_here. symmetry. exact Hob.
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
        - subst t0 ns0. rewrite set_wp_here. lia.
        - rewrite (set_wp_other _ _ _ _ _ _ E). exact G5. }
      split; [exact G6|]. split; [exact G7|].
      intros t' ns' Hob'. rewrite Eob1' in Hob'. exact (G8 t' ns' Hob'). }
    assert (J23 : Inv21 s1).
    { intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob1' in Hob0.
      rewrite Ewp1 in Hwp0. rewrite Eps1, Epm1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0 ns0. rewrite set_wp_here in Hwp0.
        apply (I23 t ns b0 q0 Hob0); [lia|exact Hq0].
      - rewrite (set_wp_other _ _ _ _ _ _ E) in Hwp0.
        exact (I23 t0 ns0 b0 q0 Hob0 Hwp0 Hq0). }
    assert (J25 : Inv23 s1).
    { intros b0 Hbo. rewrite Ebo1 in Hbo.
      destruct (I25 b0 Hbo) as [t0 [ns0 H]]. exists t0, ns0.
      rewrite Eob1'. exact H. }
    assert (J12 : Inv10 s1).
    { intros b0 Hb0. destruct (I12 b0 Hb0) as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
      - left. rewrite Efbl1. exact Hin.
      - right; left. exists t0, ns0. rewrite Eob1'. exact Hob0.
      - right; right; left. destruct Hm as (a0&p0&pa0&Hm1&Hm2).
        exists a0, p0, pa0. rewrite Els1. split; [exact Hm1|exact Hm2].
      - right; right; right. destruct Hq as [q0 Hq0]. exists q0.
        rewrite Eps1. exact Hq0. }
    assert (J27r : forall t0 ns0 b0 q0, open_block s1 t0 ns0 = Some b0 ->
              q0 < write_ptr s1 t0 ns0 ->
              (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
              page_state s1 b0 q0 <> PS_Empty).
    { intros t0 ns0 b0 q0 Hob0 Hlt0 Hne. rewrite Eob1' in Hob0.
      rewrite Ewp1 in Hlt0. rewrite Eps1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0 ns0. rewrite set_wp_here in Hlt0.
        rewrite Hob in Hob0. injection Hob0 as Hob0. subst b0.
        rewrite Epa in Hne. cbn in Hne.
        assert (Hq : q0 < write_ptr s t ns).
        { destruct Hne as [X|X]; [exfalso; exact (X eq_refl)|lia]. }
        exact (I27 t ns b q0 Hob Hq).
      - rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt0.
        exact (I27 t0 ns0 b0 q0 Hob0 Hlt0). }
    assert (Hobf : open_block s1 t ns = Some (pa_block pa))
      by (rewrite Epa; cbn; rewrite Eob1'; exact Hob).
    assert (Hwpf : write_ptr s1 t ns = S (pa_page pa))
      by (rewrite Epa; cbn; rewrite Ewp1; apply set_wp_here).
    assert (Hppf : pa_page pa < pages_per_block)
      by (rewrite Epa; cbn; exact Hlt).
    assert (Hemptyf : page_state s1 (pa_block pa) (pa_page pa) = PS_Empty).
    { rewrite Epa. cbn. rewrite Eps1.
      exact (proj1 (I23 t ns b (write_ptr s t ns) Hob (Nat.le_refl _) Hlt)). }
    exact (program_ok_d s1 a p d t ns pa J0 J1 J2 J3 J5d J6 J7 J8 J9 J10 J11
             J12 J13 J15 J16 J17 J18 J19 J20 J21 J22 J23 J24 J25 J26 J28
             J27r Hnone1 Ha Hp Hat1 Han1 Hobf Hwpf Hppf Hemptyf).
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
      - subst t0 ns0. rewrite set_ob_here in Hob0.
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
        + exfalso. subst t' ns'. rewrite set_ob_here in Hob'.
          injection Hob' as Hob'. exact (Hbb (eq_sym Hob')).
        + rewrite (set_ob_other _ _ _ _ _ _ F) in Hob'.
          exact (G8 t' ns' Hob'). }
    assert (J23 : Inv21 s1).
    { intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob1 in Hob0.
      rewrite Ewp1 in Hwp0. rewrite Eps1, Epm1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0 ns0. rewrite set_ob_here in Hob0.
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
              exfalso. subst t' ns'. rewrite Hobt in Hob'.
              injection Hob' as Hob'. exact (E2 (eq_sym Hob')). }
            rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'.
        + destruct (I25 b0 Hbo) as [t' [ns' Hob']]. exists t', ns'.
          assert (E3 : t' <> t \/ ns' <> ns).
          { destruct (nat_pair_dec t' t ns' ns) as [[Y1 Y2]|Y]; [|exact Y].
            exfalso. subst t' ns'. rewrite Hobt in Hob'. discriminate. }
          rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'. }
    assert (J12 : Inv10 s1).
    { intros b0 Hb0. destruct (I12 b0 Hb0) as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
      - rewrite Hfbl in Hin. destruct Hin as [Ez|Hin].
        + subst b0. right; left. exists t, ns. rewrite Eob1. apply set_ob_here.
        + left. rewrite Efbl1. exact Hin.
      - destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
        + subst t0 ns0.
          assert (Hwpt : pages_per_block <= write_ptr s t ns)
            by (apply (Hclosed b0); exact Hob0).
          assert (H0 : 0 < write_ptr s t ns) by lia.
          pose proof (I27 t ns b0 0 Hob0 H0) as Hne0.
          destruct (page_state s b0 0) as [| |d0] eqn:Eps0.
          * exfalso. exact (Hne0 eq_refl).
          * right; right; right. exists 0. rewrite Eps1. exact Eps0.
          * destruct (I2 b0 0 d0 Eps0) as (a0 & p0 & Hmap).
            right; right; left. exists a0, p0, (mkPhysAddr b0 0).
            rewrite Els1. split; [exact Hmap|reflexivity].
        + right; left. exists t0, ns0.
          rewrite Eob1, (set_ob_other _ _ _ _ _ _ E). exact Hob0.
      - right; right; left. destruct Hm as (a0&p0&pa0&Hm1&Hm2).
        exists a0, p0, pa0. rewrite Els1. split; [exact Hm1|exact Hm2].
      - right; right; right. destruct Hq as [q0 Hq0]. exists q0.
        rewrite Eps1. exact Hq0. }
    assert (J27r : forall t0 ns0 b0 q0, open_block s1 t0 ns0 = Some b0 ->
              q0 < write_ptr s1 t0 ns0 ->
              (b0 <> pa_block pa \/ q0 <> pa_page pa) ->
              page_state s1 b0 q0 <> PS_Empty).
    { intros t0 ns0 b0 q0 Hob0 Hlt0 Hne. rewrite Eob1 in Hob0.
      rewrite Ewp1 in Hlt0. rewrite Eps1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - exfalso. subst t0 ns0. rewrite set_ob_here in Hob0.
        injection Hob0 as Hob0. subst b0. rewrite set_wp_here in Hlt0.
        assert (Hq0 : q0 = 0) by lia. subst q0.
        rewrite Epa in Hne. cbn in Hne.
        destruct Hne as [X|X]; exact (X eq_refl).
      - rewrite (set_ob_other _ _ _ _ _ _ E) in Hob0.
        rewrite (set_wp_other _ _ _ _ _ _ E) in Hlt0.
        exact (I27 t0 ns0 b0 q0 Hob0 Hlt0). }
    assert (Hobf : open_block s1 t ns = Some (pa_block pa))
      by (rewrite Epa; cbn; rewrite Eob1; apply set_ob_here).
    assert (Hwpf : write_ptr s1 t ns = S (pa_page pa))
      by (rewrite Epa; cbn; rewrite Ewp1; apply set_wp_here).
    assert (Hppf : pa_page pa < pages_per_block)
      by (rewrite Epa; cbn; exact Hppb).
    assert (Hemptyf : page_state s1 (pa_block pa) (pa_page pa) = PS_Empty)
      by (rewrite Epa; cbn; rewrite Eps1; exact (proj1 (Hpages 0 Hppb))).
    exact (program_ok_d s1 a p d t ns pa J0 J1 J2 J3 J5d J6 J7 J8 J9 J10 J11
             J12 J13 J15 J16 J17 J18 J19 J20 J21 J22 J23 J24 J25 J26 J28
             J27r Hnone1 Ha Hp Hat1 Han1 Hobf Hwpf Hppf Hemptyf).
Qed.

(* ── write preserves the invariant ─────────────────────────────────── *)

Lemma release_unmaps :
  forall s a p, Inv1 s -> l2p_map (release_old s a p) a p = None.
Proof.
  intros s a p I3. unfold release_old.
  destruct (l2p_map s a p) as [old|] eqn:Hold; [|exact Hold].
  cbv zeta.
  destruct (find_mapper (unmap s a p) old) as [[a0 p0]|] eqn:Hfm.
  - exact (unmap_here s a p).
  - exact (unmap_here s a p).
Qed.

Lemma release_keeps_labels :
  forall s a p,
    addr_tenant (release_old s a p) = addr_tenant s /\
    addr_namespace (release_old s a p) = addr_namespace s.
Proof.
  intros s a p. unfold release_old.
  destruct (l2p_map s a p) as [old|] eqn:Hold; [|split; reflexivity].
  cbv zeta.
  destruct (find_mapper (unmap s a p) old) as [[a0 p0]|] eqn:Hfm;
    split; reflexivity.
Qed.

Theorem dedup_write_preserves_invariant :
  forall s a p d s',
    dedup_invariant s ->
    a < addr_space -> p < pages_per_block ->
    dedup_write s a p d = Some s' ->
    dedup_invariant s'.
Proof.
  intros s a p d s' Hinv Ha Hp Hstep.
  assert (I3 : Inv1 s) by (destruct Hinv as (_&_&_&H&_); exact H).
  pose proof (release_ok s a p Hinv) as Hinv1.
  pose proof (release_unmaps s a p I3) as Hnone1.
  destruct (release_keeps_labels s a p) as [Eat1 Ean1].
  unfold dedup_write in Hstep.
  destruct (addr_tenant s a) as [t|] eqn:Eat;
    destruct (addr_namespace s a) as [ns|] eqn:Ean;
    cbv beta iota zeta in Hstep; try discriminate.
  assert (Hat1 : addr_tenant (release_old s a p) a = Some t)
    by (rewrite Eat1; exact Eat).
  assert (Han1 : addr_namespace (release_old s a p) a = Some ns)
    by (rewrite Ean1; exact Ean).
  destruct (find_dup (release_old s a p) t ns d) as [pa|] eqn:Hfd;
    cbv beta iota in Hstep.
  - (* deduplicating branch: reuse an existing page *)
    injection Hstep as Hstep. subst s'.
    exact (dedup_hit_ok (release_old s a p) a p d t ns pa
             Hinv1 Hnone1 Ha Hp Hat1 Han1 Hfd).
  - (* out-of-place branch: program a fresh one *)
    destruct (alloc_page (release_old s a p) t ns) as [[pa s2]|] eqn:Halloc;
      cbv beta iota in Hstep; [|discriminate].
    injection Hstep as Hstep. subst s'.
    exact (alloc_ok_d (release_old s a p) a p d t ns pa s2
             Hinv1 Hnone1 Ha Hp Hat1 Han1 Halloc).
Qed.

Theorem dedup_step_write_preserves_invariant :
  forall s a p d s',
    dedup_invariant s -> dedup_step s (COpWrite a p d) = Some s' ->
    dedup_invariant s'.
Proof.
  intros s a p d s' Hinv Hstep. unfold dedup_step in Hstep.
  destruct (addr_tenant s a) as [t|] eqn:Eat;
    destruct (addr_namespace s a) as [ns|] eqn:Ean;
    destruct (Nat.ltb a addr_space) eqn:Ea;
    destruct (Nat.ltb p pages_per_block) eqn:Ep;
    try rewrite Ea in Hstep; try rewrite Ep in Hstep;
    try rewrite Eat in Hstep; try rewrite Ean in Hstep;
    cbv beta iota delta [andb] in Hstep; try discriminate.
  apply Nat.ltb_lt in Ea. apply Nat.ltb_lt in Ep.
  exact (dedup_write_preserves_invariant s a p d s' Hinv Ea Ep Hstep).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 6 -- garbage collection.

   The relativised bundle carried through the reclaim fold, with Inv2
   dropped and Inv3 replaced by Inv3_dedup.  Everything else is the
   framework's [INVX] verbatim.
   ══════════════════════════════════════════════════════════════════════ *)

Record INVXD (vb : Block) (ps : list Page) (s : FTLState) : Prop := mkINVXD {
  yI0  : WF0 s;
  yI1  : WF1 s;
  yI3  : Inv1 s;
  yI5d : Inv3_dedup s;
  yI7  : Inv5 s;
  yI8  : Inv6 s;
  yI9  : Inv7 s;
  yI10 : Inv8 s;
  yI11 : Inv9 s;
  yI13 : Inv11 s;
  yI15 : Inv13 s;
  yI16 : Inv14 s;
  yI17 : Inv15 s;
  yI18 : Inv16 s;
  yI19 : Inv17 s;
  yI20 : Inv18 s;
  yI21 : Inv19 s;
  yI22 : Inv20 s;
  yI23 : Inv21 s;
  yI24 : Inv22 s;
  yI25 : Inv23 s;
  yI26 : Inv24 s;
  yI27 : Inv25 s;
  yI28 : Inv26 s;
  yI2R : forall b0 p0 d0,
           page_state s b0 p0 = PS_Valid d0 ->
           (b0 <> vb \/ In p0 ps) ->
           exists a0 q0, l2p_map s a0 q0 = Some (mkPhysAddr b0 p0);
  yI6R : forall a0 p0 b0 q0 d0,
           page_state s b0 q0 = PS_Valid d0 ->
           page_lpa (page_meta s b0 q0) = Some (a0, p0) ->
           (b0 <> vb \/ In q0 ps) ->
           l2p_map s a0 p0 = Some (mkPhysAddr b0 q0);
  yI12R : forall b0,
            b0 < total_blocks -> b0 <> vb ->
            In b0 (free_block_list s) \/
            (exists t0 ns0, open_block s t0 ns0 = Some b0) \/
            (exists a0 p0 pa0, l2p_map s a0 p0 = Some pa0 /\ pa_block pa0 = b0) \/
            (exists q0, page_state s b0 q0 = PS_Invalid);
  yfree : free_block s vb = false;
  yopen : block_open s vb = false;
  yblt  : vb < total_blocks;
  ynd   : NoDup ps;
  yprog : forall a0 p0 pa0,
            l2p_map s a0 p0 = Some pa0 -> pa_block pa0 = vb ->
            In (pa_page pa0) ps
}.

Lemma INVXD_drop :
  forall s vb q tl,
    INVXD vb (q :: tl) s ->
    (forall d, page_state s vb q <> PS_Valid d) ->
    INVXD vb tl s.
Proof.
  intros s vb q tl HX Hnv.
  destruct HX as [I0 I1 I3 I5d I7 I8 I9 I10 I11 I13 I15 I16 I17 I18 I19 I20
                  I21 I22 I23 I24 I25 I26 I27 I28 I2R I6R I12R Hfvb Hovb Hvblt
                  Hnd Iprog].
  assert (Hndtl : NoDup tl) by (inversion Hnd; assumption).
  apply mkINVXD; try assumption.
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

(* ── programming the relocation destination, redirecting every reader ─ *)

Lemma reloc_program_ok :
  forall (s2 : FTLState) (a : Addr) (p : Page) (d dsrc : Data)
         (t : TenantId) (ns : NamespaceId) (pa : PhysAddr)
         (vb : Block) (q : Page) (tl : list Page),
    WF0 s2 -> WF1 s2 -> Inv1 s2 -> Inv3_dedup s2 -> Inv5 s2 ->
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
    page_state s2 vb q = PS_Valid dsrc ->
    l2p_map s2 a p = Some (mkPhysAddr vb q) ->
    a < addr_space -> p < pages_per_block ->
    addr_tenant s2 a = Some t ->
    addr_namespace s2 a = Some ns ->
    open_block s2 t ns = Some (pa_block pa) ->
    write_ptr s2 t ns = S (pa_page pa) ->
    pa_page pa < pages_per_block ->
    page_state s2 (pa_block pa) (pa_page pa) = PS_Empty ->
    INVXD vb tl (reloc_program s2 a p d (mkPhysAddr vb q) pa).
Proof.
  intros s2 a p d dsrc t ns pa vb q tl I0 I1 I3 I5d I7 I8 I9 I10 I11 I13 I15
         I16 I17 I18 I19 I20 I21 I22 I23 I24 I25 I26 I28
         I2R I6R I12R I27R Iprog Hnd Hfvb Hovb Hvblt Hdest Hsrc Hold Ha Hp
         Hat Han Hob Hwp Hpp Hempty.
  destruct (I22 t ns (pa_block pa) Hob)
    as (Hbtb & Hnfl & Hfbf & Hbof & Hwple & Hbt & Hbn & Huniq).
  assert (Hqnt : ~ In q tl) by (inversion Hnd; assumption).
  assert (Hndtl : NoDup tl) by (inversion Hnd; assumption).
  assert (Hsrc' : page_state s2 (pa_block (mkPhysAddr vb q))
                              (pa_page (mkPhysAddr vb q)) = PS_Valid dsrc)
    by (cbn; exact Hsrc).
  assert (Hsrcne : mkPhysAddr vb q <> pa)
    by (intro E; apply Hdest; rewrite <- E; reflexivity).
  set (s' := reloc_program s2 a p d (mkPhysAddr vb q) pa).
  assert (Els : l2p_map s' = redirect (l2p_map s2) (mkPhysAddr vb q) pa)
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
  assert (Hnotdst : forall a0 p0 pa0, l2p_map s2 a0 p0 = Some pa0 -> pa0 <> pa).
  { intros a0 p0 pa0 Hmap E. subst pa0.
    destruct (I24 a0 p0 pa Hmap) as [dd Hdd]. rewrite Hempty in Hdd.
    discriminate. }
  (* the redirected map: only readers of the source moved *)
  assert (Hcase : forall x y pa0, l2p_map s' x y = Some pa0 ->
                    (pa0 = pa /\ l2p_map s2 x y = Some (mkPhysAddr vb q)) \/
                    (l2p_map s2 x y = Some pa0 /\
                     pa0 <> mkPhysAddr vb q /\ pa0 <> pa)).
  { intros x y pa0 Hm. rewrite Els in Hm.
    destruct (redirect_case (l2p_map s2) (mkPhysAddr vb q) pa x y pa0 Hm)
      as [[E1 E2]|[E1 E2]].
    - left. split; assumption.
    - right. split; [exact E1|split; [exact E2|exact (Hnotdst x y pa0 E1)]]. }
  assert (Hkeep : forall x y pa0, l2p_map s2 x y = Some pa0 ->
                    pa0 <> mkPhysAddr vb q -> l2p_map s' x y = Some pa0).
  { intros x y pa0 Hm Hne. rewrite Els.
    exact (redirect_miss (l2p_map s2) (mkPhysAddr vb q) pa x y pa0 Hm Hne). }
  assert (Hto : forall x y, l2p_map s2 x y = Some (mkPhysAddr vb q) ->
                  l2p_map s' x y = Some pa).
  { intros x y Hm. rewrite Els.
    exact (redirect_hit (l2p_map s2) (mkPhysAddr vb q) pa x y Hm). }
  (* every reader of the source is owned by the pair doing the relocation *)
  assert (Hsame : forall x y, l2p_map s2 x y = Some (mkPhysAddr vb q) ->
                    addr_tenant s2 x = Some t /\ addr_namespace s2 x = Some ns).
  { intros x y Hm. destruct (I28 x y (mkPhysAddr vb q) Hm) as [[t0 Ht0] [n0 Hn0]].
    destruct (I9 x y (mkPhysAddr vb q) dsrc t0 n0 Hm Hsrc' Ht0 Hn0) as [G1 G2].
    destruct (I9 a p (mkPhysAddr vb q) dsrc t ns Hold Hsrc' Hat Han) as [G3 G4].
    rewrite G1 in G3. rewrite G2 in G4.
    rewrite G3 in Ht0. rewrite G4 in Hn0. split; [exact Ht0|exact Hn0]. }
  assert (Hnotsrc : forall b0 q0, (b0 <> vb \/ In q0 tl) ->
                      mkPhysAddr b0 q0 <> mkPhysAddr vb q).
  { intros b0 q0 Hc E. injection E as E1 E2. subst b0 q0.
    destruct Hc as [X|X]; [exact (X eq_refl) | exact (Hqnt X)]. }
  apply mkINVXD.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv1 *) intros x y pa0 Hm.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|[E1 _]].
    + subst pa0. destruct (I3 x y (mkPhysAddr vb q) E2) as (_ & _ & Hx & Hy).
      split; [exact Hbtb|]. split; [exact Hpp|]. split; [exact Hx|exact Hy].
    + exact (I3 x y pa0 E1).
  - (* Inv3_dedup *) intros x y pa0 d0 Hm Hv.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|(E1 & E2 & E3)].
    + subst pa0. exists a, p. split.
      * rewrite Epm, set_pm_here. reflexivity.
      * exact (Hto a p Hold).
    + pose proof (phys_neq_split pa0 pa E3) as Hd.
      rewrite Eps, (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      destruct (I5d x y pa0 d0 E1 Hv) as (b1 & q1 & Hst & Hmb).
      exists b1, q1. split.
      * rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd). exact Hst.
      * exact (Hkeep b1 q1 pa0 Hmb E2).
  - (* Inv5 *) intros x y pa0 Hm. rewrite Efbl.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|[E1 _]].
    + subst pa0. exact Hnfl.
    + exact (I7 x y pa0 E1).
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    assert (Hd : b0 <> pa_block pa \/ q0 <> pa_page pa)
      by (left; intro E; subst b0; exact (Hnfl Hin)).
    rewrite Eps, Epm, (set_ps_other _ _ _ _ _ _ Hd),
            (set_pm_other _ _ _ _ _ _ Hd).
    exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros x y pa0 d0 t0 n0 Hm Hv Ht Hn.
    rewrite Eat in Ht. rewrite Ean in Hn.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|(E1 & E2 & E3)].
    + subst pa0. destruct (Hsame x y E2) as [Gt Gn].
      rewrite Gt in Ht. rewrite Gn in Hn.
      injection Ht as Ht. injection Hn as Hn. subst t0 n0.
      rewrite Epm, set_pm_here, Hat, Han. cbn. split; reflexivity.
    + pose proof (phys_neq_split pa0 pa E3) as Hd.
      rewrite Eps, (set_ps_other _ _ _ _ _ _ Hd) in Hv.
      rewrite Epm, (set_pm_other _ _ _ _ _ _ Hd).
      exact (I9 x y pa0 d0 t0 n0 E1 Hv Ht Hn).
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
  - (* Inv14 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. exists d. apply set_ps_here.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I16 b0 q0 Hr).
  - (* Inv15 *) intros b0 q0 Hr. rewrite Epr in Hr. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pr_here in Hr. discriminate.
    + rewrite (set_pr_other _ _ _ _ _ _ Hne) in Hr.
      rewrite (set_ps_other _ _ _ _ _ _ Hne). exact (I17 b0 q0 Hr).
  - (* Inv16 *) intros b0 q0 He. rewrite Eps in He. rewrite Epr.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here in He. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in He.
      rewrite (set_pr_other _ _ _ _ _ _ Hne). exact (I18 b0 q0 He).
  - (* Inv17 *) intros b0 Hf. rewrite Efb in Hf. rewrite Ebt, Ebn.
    assert (Hbne : b0 <> pa_block pa)
      by (intro E; subst b0; rewrite Hfbf in Hf; discriminate).
    rewrite (set_bt_other _ _ _ _ Hbne), (set_bn_other _ _ _ _ Hbne).
    exact (I19 b0 Hf).
  - (* Inv18 *) intros x y pa0 Hm. rewrite Ebt, Ebn, Eat, Ean.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|[E1 _]].
    + subst pa0. rewrite set_bt_here, set_bn_here.
      destruct (Hsame x y E2) as [Gt Gn]. rewrite Gt, Gn, Hat, Han.
      split; reflexivity.
    + destruct (I20 x y pa0 E1) as [Gt Gn].
      destruct (Nat.eq_dec (pa_block pa0) (pa_block pa)) as [E|E].
      * destruct (I28 x y pa0 E1) as [[t0 Ht0] [ns0 Hns0]].
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
      destruct (Huniq t0 ns0 Hob0) as [Et Ens]. subst t0 ns0.
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
  - (* Inv22 *) intros x y pa0 Hm. rewrite Eps.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|(E1 & E2 & E3)].
    + subst pa0. exists d. apply set_ps_here.
    + pose proof (phys_neq_split pa0 pa E3) as Hd.
      destruct (I24 x y pa0 E1) as [dd Hdd].
      exists dd. rewrite (set_ps_other _ _ _ _ _ _ Hd). exact Hdd.
  - (* Inv23 *) intros b0 Hbo. rewrite Ebo in Hbo. rewrite Eob.
    exact (I25 b0 Hbo).
  - (* Inv24 *) intros b0. rewrite Efb, Efbl. exact (I26 b0).
  - (* Inv25 *) intros t0 ns0 b0 q0 Hob0 Hlt. rewrite Eob in Hob0.
    rewrite Ewp in Hlt. rewrite Eps.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_ps_here. discriminate.
    + rewrite (set_ps_other _ _ _ _ _ _ Hne).
      exact (I27R t0 ns0 b0 q0 Hob0 Hlt Hne).
  - (* Inv26 *) intros x y pa0 Hm. rewrite Eat, Ean.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|[E1 _]].
    + destruct (Hsame x y E2) as [Gt Gn].
      split; [exists t; exact Gt | exists ns; exact Gn].
    + exact (I28 x y pa0 E1).
  - (* Inv0, relativised at [tl] *) intros b0 p0 d0 Hv Hc. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) p0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 p0. exists a, p. rewrite physaddr_eta. exact (Hto a p Hold).
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      assert (Hc' : b0 <> vb \/ In p0 (q :: tl))
        by (destruct Hc as [X|X]; [left; exact X | right; apply in_cons; exact X]).
      destruct (I2R b0 p0 d0 Hv Hc') as (x & y & Hmx).
      exists x, y. exact (Hkeep x y _ Hmx (Hnotsrc b0 p0 Hc)).
  - (* Inv4, relativised at [tl] *) intros x y b0 q0 d0 Hv Hlpa Hc.
    rewrite Eps in Hv. rewrite Epm in Hlpa.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite set_pm_here in Hlpa. cbn in Hlpa.
      injection Hlpa as F1 F2. subst x y.
      rewrite physaddr_eta. exact (Hto a p Hold).
    + rewrite (set_ps_other _ _ _ _ _ _ Hne) in Hv.
      rewrite (set_pm_other _ _ _ _ _ _ Hne) in Hlpa.
      assert (Hc' : b0 <> vb \/ In q0 (q :: tl))
        by (destruct Hc as [X|X]; [left; exact X | right; apply in_cons; exact X]).
      pose proof (I6R x y b0 q0 d0 Hv Hlpa Hc') as Hmx.
      exact (Hkeep x y _ Hmx (Hnotsrc b0 q0 Hc)).
  - (* Inv10, relativised at the victim *) intros b0 Hb0 Hbvb.
    destruct (I12R b0 Hb0 Hbvb)
      as [Hin | [[t0 [ns0 Hob0]] | [(x&y&pa0&Hmx&Hblk) | [q0 Hq0]]]].
    + left. rewrite Efbl. exact Hin.
    + right; left. exists t0, ns0. rewrite Eob. exact Hob0.
    + right; right; left. exists x, y, pa0. split; [|exact Hblk].
      apply (Hkeep x y pa0 Hmx). intro E. subst pa0. cbn in Hblk.
      exact (Hbvb (eq_sym Hblk)).
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
  - (* progress: no reader of the relocated page is left behind *)
    intros x y pa0 Hm Hblk.
    destruct (Hcase x y pa0 Hm) as [[E1 E2]|(E1 & E2 & E3)].
    + exfalso. subst pa0. exact (Hdest Hblk).
    + destruct (Iprog x y pa0 E1 Hblk) as [E|Hin]; [|exact Hin].
      exfalso. apply E2. rewrite <- Hblk, E. symmetry. apply physaddr_eta.
Qed.

(* ── allocating the relocation destination ────────────────────────── *)

Lemma dedup_relocate_core :
  forall s vb q tl a p d t ns pa s1,
    INVXD vb (q :: tl) s ->
    page_state s vb q = PS_Valid d ->
    page_lpa (page_meta s vb q) = Some (a, p) ->
    addr_tenant s a = Some t ->
    addr_namespace s a = Some ns ->
    alloc_page s t ns = Some (pa, s1) ->
    INVXD vb tl (reloc_program s1 a p d (mkPhysAddr vb q) pa).
Proof.
  intros s vb q tl a p d t ns pa s1 HX Hps Hlpa Hat Han Halloc.
  destruct HX as [I0 I1 I3 I5d I7 I8 I9 I10 I11 I13 I15 I16 I17 I18 I19 I20
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
  assert (J0 : WF0 s1) by exact I0.
  assert (J1 : WF1 s1) by (intros b0 p0 _ _; eexists; reflexivity).
  assert (J3 : Inv1 s1) by (unfold Inv1; rewrite Els1; exact I3).
  assert (J5d : Inv3_dedup s1)
    by (unfold Inv3_dedup; rewrite Els1, Eps1, Epm1; exact I5d).
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
  assert (Hsrc1 : page_state s1 vb q = PS_Valid d) by (rewrite Eps1; exact Hps).
  assert (Hat1 : addr_tenant s1 a = Some t) by (rewrite Eat1; exact Hat).
  assert (Han1 : addr_namespace s1 a = Some ns) by (rewrite Ean1; exact Han).
  destruct (alloc_page_shape s t ns pa s1 Halloc)
    as [(b & Hob & Hlt & Epa & Efbl1 & Efb1 & Ebo1 & Eob1 & Ewp1)
       | (Hof & Hclosed)].
  - (* ── the frontier branch ──────────────────────────────────────── *)
    assert (Eob1' : forall x y, open_block s1 x y = open_block s x y).
    { intros x y. rewrite Eob1. destruct (nat_pair_dec x t y ns) as [[E1 E2]|E].
      - subst x y. rewrite set_ob_here. symmetry. exact Hob.
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
        - subst t0 ns0. rewrite set_wp_here. lia.
        - rewrite (set_wp_other _ _ _ _ _ _ E). exact G5. }
      split; [exact G6|]. split; [exact G7|].
      intros t' ns' Hob'. rewrite Eob1' in Hob'. exact (G8 t' ns' Hob'). }
    assert (J23 : Inv21 s1).
    { intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob1' in Hob0.
      rewrite Ewp1 in Hwp0. rewrite Eps1, Epm1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0 ns0. rewrite set_wp_here in Hwp0.
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
      destruct (I12R b0 Hb0 Hbvb) as [Hin|[[t0 [ns0 Hob0]]|[Hm|Hq]]].
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
      - subst t0 ns0. rewrite set_wp_here in Hlt0.
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
    exact (reloc_program_ok s1 a p d d t ns pa vb q tl J0 J1 J3 J5d J7 J8 J9
             J10 J11 J13 J15 J16 J17 J18 J19 J20 J21 J22 J23 J24 J25 J26 J28
             J2R J6R J12R J27R Jprog Hnd Hfvb1 Hovb1 Hvblt Hdest Hsrc1 Hold1
             Ha Hp Hat1 Han1 Hobf Hwpf Hppf Hemptyf).
  - (* ── the open_fresh branch ────────────────────────────────────── *)
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
      - subst t0 ns0. rewrite set_ob_here in Hob0.
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
        + exfalso. subst t' ns'. rewrite set_ob_here in Hob'.
          injection Hob' as Hob'. exact (Hbb (eq_sym Hob')).
        + rewrite (set_ob_other _ _ _ _ _ _ F) in Hob'.
          exact (G8 t' ns' Hob'). }
    assert (J23 : Inv21 s1).
    { intros t0 ns0 b0 q0 Hob0 Hwp0 Hq0. rewrite Eob1 in Hob0.
      rewrite Ewp1 in Hwp0. rewrite Eps1, Epm1.
      destruct (nat_pair_dec t0 t ns0 ns) as [[E1 E2]|E].
      - subst t0 ns0. rewrite set_ob_here in Hob0.
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
              exfalso. subst t' ns'. rewrite Hobt in Hob'.
              injection Hob' as Hob'. exact (E2 (eq_sym Hob')). }
            rewrite (set_ob_other _ _ _ _ _ _ E3). exact Hob'.
        + destruct (I25 b0 Hbo) as [t' [ns' Hob']]. exists t', ns'.
          assert (E3 : t' <> t \/ ns' <> ns).
          { destruct (nat_pair_dec t' t ns' ns) as [[Y1 Y2]|Y]; [|exact Y].
            exfalso. subst t' ns'. rewrite Hobt in Hob'. discriminate. }
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
        + subst t0 ns0.
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
      - exfalso. subst t0 ns0. rewrite set_ob_here in Hob0.
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
    exact (reloc_program_ok s1 a p d d t ns pa vb q tl J0 J1 J3 J5d J7 J8 J9
             J10 J11 J13 J15 J16 J17 J18 J19 J20 J21 J22 J23 J24 J25 J26 J28
             J2R J6R J12R J27R Jprog Hnd Hfvb1 Hovb1 Hvblt Hdest Hsrc1 Hold1
             Ha Hp Hat1 Han1 Hobf Hwpf Hppf Hemptyf).
Qed.

(* ── the fold and the erase ───────────────────────────────────────── *)

Lemma dedup_relocate_page_INVXD :
  forall s vb q tl s',
    INVXD vb (q :: tl) s ->
    dedup_relocate_page s vb q = Some s' ->
    INVXD vb tl s'.
Proof.
  intros s vb q tl s' HX Hrel. unfold dedup_relocate_page in Hrel.
  destruct (page_state s vb q) as [| |d] eqn:Hps.
  - injection Hrel as Hrel. subst s'.
    apply (INVXD_drop s vb q tl HX). intros d0 Hc.
    rewrite Hps in Hc. discriminate.
  - injection Hrel as Hrel. subst s'.
    apply (INVXD_drop s vb q tl HX). intros d0 Hc.
    rewrite Hps in Hc. discriminate.
  - destruct (page_lpa (page_meta s vb q)) as [[a p]|] eqn:Hlpa;
      [|discriminate].
    destruct (addr_tenant s a) as [t|] eqn:Hat;
      destruct (addr_namespace s a) as [ns|] eqn:Han;
      cbv beta iota in Hrel; try discriminate.
    destruct (alloc_page s t ns) as [[pa s1]|] eqn:Halloc;
      cbv beta iota in Hrel; [|discriminate].
    injection Hrel as Hrel. subst s'.
    exact (dedup_relocate_core s vb q tl a p d t ns pa s1 HX Hps Hlpa Hat Han
             Halloc).
Qed.

Lemma dedup_relocate_pages_INVXD :
  forall ps s vb s',
    INVXD vb ps s -> dedup_relocate_pages s vb ps = Some s' -> INVXD vb [] s'.
Proof.
  intros ps. induction ps as [|q tl IH]; intros s vb s' HX H.
  - cbn [dedup_relocate_pages] in H. injection H as H. subst s'. exact HX.
  - cbn [dedup_relocate_pages] in H.
    destruct (dedup_relocate_page s vb q) as [s1|] eqn:Hr;
      cbv beta iota in H; [|discriminate].
    exact (IH s1 vb s' (dedup_relocate_page_INVXD s vb q tl s1 HX Hr) H).
Qed.

Lemma erase_ok_d :
  forall s vb, INVXD vb [] s -> dedup_invariant (erase_block s vb).
Proof.
  intros s vb HX.
  destruct HX as [I0 I1 I3 I5d I7 I8 I9 I10 I11 I13 I15 I16 I17 I18 I19 I20
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
  assert (K20 : Inv18 (erase_block s vb)).
  { intros a0 p0 pa0 Hm. rewrite eb_l2p in Hm.
    rewrite eb_bt, eb_bn, eb_at, eb_an.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (set_bt_other _ _ _ _ Hne), (set_bn_other _ _ _ _ Hne).
    exact (I20 a0 p0 pa0 Hm). }
  assert (K24 : Inv22 (erase_block s vb)).
  { intros a0 p0 pa0 Hm. rewrite eb_l2p in Hm.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne). exact (I24 a0 p0 pa0 Hm). }
  apply make_dedup_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 p0 _ _. eexists. reflexivity.
  - (* Inv0 *) intros b0 p0 d0 Hv. rewrite eb_l2p.
    destruct (Nat.eq_dec b0 vb) as [E|E].
    + subst b0. rewrite eb_ps_self in Hv. discriminate.
    + rewrite (eb_ps_other _ _ _ _ E) in Hv.
      exact (I2R b0 p0 d0 Hv (or_introl E)).
  - (* Inv1 *) unfold Inv1. rewrite eb_l2p. exact I3.
  - (* Inv2_dedup *) exact (Inv2_dedup_is_derivable _ K20 K24).
  - (* Inv3_dedup *) intros a0 p0 pa0 d0 Hm Hv. rewrite eb_l2p in Hm.
    pose proof (Hnomap a0 p0 pa0 Hm) as Hne.
    rewrite (eb_ps_other _ _ _ _ Hne) in Hv.
    destruct (I5d a0 p0 pa0 d0 Hm Hv) as (b1 & q1 & Hst & Hmb).
    exists b1, q1. rewrite eb_l2p.
    split; [rewrite (eb_pm_other _ _ _ _ Hne); exact Hst | exact Hmb].
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
  - (* Inv18 *) exact K20.
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
  - (* Inv22 *) exact K24.
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

(* ── preservation, once, for every victim chooser ──────────────────────

   The reclaim argument above never mentions how the victim was found.  It
   needs exactly three facts about it: the block is in range, its free bit
   is clear, and it is not open -- precisely [victim_sound]'s obligations.
   So the theorem is stated over [dedup_reclaim_with pick] for an arbitrary
   sound [pick], and both host-visible maintenance operations are
   instances.  This mirrors the framework's PART 5 structure exactly,
   because the chooser interface is one of the pieces deduplication does
   not disturb. *)

(* The entry condition of the fold, for any block the chooser may legally
   return.  [find_victim] appears nowhere in it. *)
Lemma dedup_reclaimable_victim_INVXD :
  forall s b,
    dedup_invariant s ->
    b < total_blocks -> reclaimable s b = true ->
    INVXD b all_pages s.
Proof.
  intros s b Hinv Hblt Hrec.
  destruct Hinv as (I0&I1&I2&I3&I4d&I5d&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  unfold reclaimable, is_open in Hrec.
  apply andb_prop in Hrec. destruct Hrec as [Hf1 Hf2].
  apply negb_true_iff in Hf1. apply negb_true_iff in Hf2.
  apply mkINVXD; try assumption.
  - intros b0 p0 d0 Hv0 _. exact (I2 b0 p0 d0 Hv0).
  - intros a0 p0 b0 q0 d0 Hv0 Hl0 _. exact (I6 a0 p0 b0 q0 d0 Hv0 Hl0).
  - intros b0 Hb0 _. exact (I12 b0 Hb0).
  - unfold all_pages. apply seq_NoDup.
  - intros a0 p0 pa0 Hm _. unfold all_pages. apply in_seq.
    destruct (I3 a0 p0 pa0 Hm) as (_ & Hpp & _). lia.
Qed.

(* Reclaiming one admissible block preserves all 28 conjuncts. *)
Theorem dedup_reclaim_preserves_invariant :
  forall s b s',
    dedup_invariant s ->
    b < total_blocks -> reclaimable s b = true ->
    dedup_reclaim s b = Some s' ->
    dedup_invariant s'.
Proof.
  intros s b s' Hinv Hblt Hrec Hrc. unfold dedup_reclaim in Hrc.
  destruct (dedup_relocate_pages s b all_pages) as [s1|] eqn:Hrel;
    cbv beta iota in Hrc; [|discriminate].
  injection Hrc as Hrc. subst s'.
  apply erase_ok_d.
  apply (dedup_relocate_pages_INVXD all_pages s b s1); [|exact Hrel].
  exact (dedup_reclaimable_victim_INVXD s b Hinv Hblt Hrec).
Qed.

(* The generalized statement.  One proof for every reclamation policy that
   meets the chooser contract.  The dedup bundle constrains [wear_count] no
   more than the framework bundle does, so a wear-aware chooser is
   admissible here for free as well. *)
Theorem dedup_reclaim_with_preserves_invariant :
  forall pick s s',
    victim_sound pick ->
    dedup_invariant s ->
    dedup_reclaim_with pick s = Some s' ->
    dedup_invariant s'.
Proof.
  intros pick s s' Hpick Hinv Hstep. unfold dedup_reclaim_with in Hstep.
  destruct (pick s) as [b|] eqn:Hv; cbv beta iota in Hstep; [|discriminate].
  destruct (Hpick s b Hv) as [Hblt Hrec].
  exact (dedup_reclaim_preserves_invariant s b s' Hinv Hblt Hrec Hstep).
Qed.

(* ── the chooser contract is necessary here too ─────────────────────────

   The framework's refutation ([unconstrained_chooser_breaks_invariant])
   shows that dropping [victim_sound] makes the generalized statement
   false: a chooser naming a *free* block relocates nothing, so the reclaim
   succeeds, and [erase_block] then pushes the block onto the free list a
   second time.  Inv11 fails.  Inv11 is one of the 27 conjuncts that survive
   deduplication verbatim and the counterexample state is [empty_state],
   which shares no pages, so the refutation transfers with only the bundle
   name changed -- but it does have to be restated, for the same reason
   every other preservation result does. *)
Lemma dedup_relocate_page_empty :
  forall s b q, page_state s b q = PS_Empty ->
    dedup_relocate_page s b q = Some s.
Proof. intros s b q He. unfold dedup_relocate_page. rewrite He. reflexivity. Qed.

Lemma dedup_relocate_pages_all_empty :
  forall ps s b,
    (forall q, page_state s b q = PS_Empty) ->
    dedup_relocate_pages s b ps = Some s.
Proof.
  induction ps as [|q tl IH]; intros s b He; [reflexivity|].
  cbn [dedup_relocate_pages].
  rewrite (dedup_relocate_page_empty s b q (He q)).
  exact (IH s b He).
Qed.

Theorem dedup_unconstrained_chooser_breaks_invariant :
  exists (pick : FTLState -> option Block) (s s' : FTLState),
    dedup_invariant s /\
    dedup_reclaim_with pick s = Some s' /\
    ~ Inv11 s'.
Proof.
  exists (fun _ => Some 0), empty_state, (erase_block empty_state 0).
  split; [exact (ftl_implies_dedup_invariant empty_state
                   (@empty_state_invariant pages_per_block_pos))|].
  split.
  - unfold dedup_reclaim_with, dedup_reclaim.
    rewrite (dedup_relocate_pages_all_empty all_pages empty_state 0
               (fun q => eq_refl)).
    reflexivity.
  - unfold Inv11. rewrite eb_fbl.
    intro Hnd. inversion Hnd as [|x l Hnin Hrest]. apply Hnin.
    change (In 0 (seq 0 total_blocks)). apply in_seq.
    pose proof total_blocks_pos. lia.
Qed.

(* ── the two assigned maintenance statements, as instances ──────────── *)

Theorem dedup_gc_preserves_invariant :
  forall s s', dedup_invariant s -> dedup_gc s = Some s' -> dedup_invariant s'.
Proof.
  intros s s' Hinv Hstep.
  change (dedup_gc s) with (dedup_reclaim_with find_victim s) in Hstep.
  exact (dedup_reclaim_with_preserves_invariant find_victim s s'
           find_victim_sound Hinv Hstep).
Qed.

(* Wear levelling is the same transformer under the least-worn-block
   policy.  Nothing in the proof changes; only the chooser instantiated
   does. *)
Theorem dedup_wear_level_preserves_invariant :
  forall s s', dedup_invariant s -> dedup_wear_level s = Some s' ->
    dedup_invariant s'.
Proof.
  intros s s' Hinv Hstep.
  change (dedup_wear_level s)
    with (dedup_reclaim_with find_least_worn_victim s) in Hstep.
  exact (dedup_reclaim_with_preserves_invariant find_least_worn_victim s s'
           find_least_worn_victim_sound Hinv Hstep).
Qed.

Theorem dedup_step_gc_preserves_invariant :
  forall s s' op,
    (op = COpGC \/ op = COpWearLevel) ->
    dedup_invariant s -> dedup_step s op = Some s' -> dedup_invariant s'.
Proof.
  intros s s' op Hop Hinv Hstep.
  destruct Hop as [E|E]; subst op; cbn [dedup_step] in Hstep.
  - exact (dedup_gc_preserves_invariant s s' Hinv Hstep).
  - exact (dedup_wear_level_preserves_invariant s s' Hinv Hstep).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 7 -- the remaining operations, and the whole step function.
   ══════════════════════════════════════════════════════════════════════ *)

Theorem dedup_read_preserves_invariant :
  forall s a p s',
    dedup_invariant s -> dedup_step s (COpRead a p) = Some s' ->
    dedup_invariant s'.
Proof.
  intros s a p s' Hinv Hstep. cbn in Hstep. injection Hstep as Hstep.
  subst s'. exact Hinv.
Qed.

Theorem dedup_set_tag_preserves_invariant :
  forall s a p tag s',
    dedup_invariant s -> dedup_step s (COpSetTag a p tag) = Some s' ->
    dedup_invariant s'.
Proof.
  intros s a p tag s' Hinv Hstep. cbn in Hstep. injection Hstep as Hstep.
  subst s'. unfold exec_set_tag.
  destruct (l2p_map s a p) as [pa|] eqn:Hm; [|exact Hinv].
  destruct (page_state s (pa_block pa) (pa_page pa)) as [| |d] eqn:Hps;
    try exact Hinv.
  destruct Hinv as (I0&I1&I2&I3&I4d&I5d&I6&I7&I8&I9&I10&I11&I12&I13&I14&I15
                   &I16&I17&I18&I19&I20&I21&I22&I23&I24&I25&I26&I27&I28).
  set (s' := set_page_tag_at s pa tag).
  assert (Els : l2p_map s' = l2p_map s) by reflexivity.
  assert (Eps : page_state s' = page_state s) by reflexivity.
  assert (Epr : page_role s' = page_role s) by reflexivity.
  assert (Eat : addr_tenant s' = addr_tenant s) by reflexivity.
  assert (Ean : addr_namespace s' = addr_namespace s) by reflexivity.
  assert (Ebt : block_tenant s' = block_tenant s) by reflexivity.
  assert (Ebn : block_namespace s' = block_namespace s) by reflexivity.
  assert (Ert : region_table s' = region_table s) by reflexivity.
  assert (Efbl : free_block_list s' = free_block_list s) by reflexivity.
  assert (Efb : free_block s' = free_block s) by reflexivity.
  assert (Eob : open_block s' = open_block s) by reflexivity.
  assert (Ewp : write_ptr s' = write_ptr s) by reflexivity.
  assert (Ebo : block_open s' = block_open s) by reflexivity.
  assert (Epm_here : page_meta s' (pa_block pa) (pa_page pa) =
            mkPageMeta
              (page_owner_tenant (page_meta s (pa_block pa) (pa_page pa)))
              (page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)))
              (Some tag) (page_lpa (page_meta s (pa_block pa) (pa_page pa))))
    by (unfold s', set_page_tag_at; cbn [page_meta]; apply set_pm_here).
  assert (Epm_other : forall x y,
            (x <> pa_block pa \/ y <> pa_page pa) ->
            page_meta s' x y = page_meta s x y).
  { intros x y H. unfold s', set_page_tag_at. cbn [page_meta].
    apply (set_pm_other (page_meta s) (pa_block pa) (pa_page pa) _ x y H). }
  assert (Epm_lpa : forall x y,
            page_lpa (page_meta s' x y) = page_lpa (page_meta s x y) /\
            page_owner_tenant (page_meta s' x y) =
            page_owner_tenant (page_meta s x y) /\
            page_owner_namespace (page_meta s' x y) =
            page_owner_namespace (page_meta s x y)).
  { intros x y. destruct (nat_pair_dec x (pa_block pa) y (pa_page pa))
      as [[E1 E2]|Hne].
    - subst x y. rewrite Epm_here. cbn. repeat split; reflexivity.
    - rewrite (Epm_other x y Hne). repeat split; reflexivity. }
  pose proof (I7 a p pa Hm) as Hnf.
  apply make_dedup_invariant.
  - (* WF0 *) exact I0.
  - (* WF1 *) intros b0 q0 _ _. eexists. reflexivity.
  - (* Inv0 *) unfold Inv0. rewrite Eps, Els. exact I2.
  - (* Inv1 *) unfold Inv1. rewrite Els. exact I3.
  - (* Inv2_dedup *) apply Inv2_dedup_is_derivable.
    + unfold Inv18. rewrite Els, Ebt, Ebn, Eat, Ean. exact I20.
    + unfold Inv22. rewrite Els, Eps. exact I24.
  - (* Inv3_dedup *) intros x y pa0 d0 Hmap Hv. rewrite Els in Hmap.
    rewrite Eps in Hv. rewrite Els.
    destruct (Epm_lpa (pa_block pa0) (pa_page pa0)) as [G1 _]. rewrite G1.
    exact (I5d x y pa0 d0 Hmap Hv).
  - (* Inv4 *) intros x y b0 q0 d0 Hv Hlpa. rewrite Eps in Hv. rewrite Els.
    destruct (Epm_lpa b0 q0) as [G1 _]. rewrite G1 in Hlpa.
    exact (I6 x y b0 q0 d0 Hv Hlpa).
  - (* Inv5 *) unfold Inv5. rewrite Els, Efbl. exact I7.
  - (* Inv6 *) intros b0 Hin q0 Hq0. rewrite Efbl in Hin.
    assert (Hne : b0 <> pa_block pa \/ q0 <> pa_page pa)
      by (left; intro E; subst b0; exact (Hnf Hin)).
    rewrite Eps, (Epm_other b0 q0 Hne). exact (I8 b0 Hin q0 Hq0).
  - (* Inv7 *) intros x y pa0 d0 t0 n0 Hmap Hv Ht Hn.
    rewrite Els in Hmap. rewrite Eps in Hv. rewrite Eat in Ht.
    rewrite Ean in Hn.
    destruct (Epm_lpa (pa_block pa0) (pa_page pa0)) as [_ [G2 G3]].
    rewrite G2, G3. exact (I9 x y pa0 d0 t0 n0 Hmap Hv Ht Hn).
  - (* Inv8 *) unfold Inv8. rewrite Efbl. exact I10.
  - (* Inv9 *) intros b0 q0 d0 Hv. rewrite Eps in Hv.
    destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa)) as [[E1 E2]|Hne].
    + subst b0 q0. rewrite Epm_here. cbn. exists tag. reflexivity.
    + rewrite (Epm_other b0 q0 Hne). exact (I11 b0 q0 d0 Hv).
  - (* Inv10 *) unfold Inv10. rewrite Efbl, Eob, Els, Eps. exact I12.
  - (* Inv11 *) unfold Inv11. rewrite Efbl. exact I13.
  - (* Inv12 *) unfold Inv12. rewrite Epr, Els, Eps. exact I14.
  - (* Inv13 *) unfold Inv13. rewrite Eps, Epr. exact I15.
  - (* Inv14 *) unfold Inv14. rewrite Epr, Eps. exact I16.
  - (* Inv15 *) unfold Inv15. rewrite Epr, Eps. exact I17.
  - (* Inv16 *) unfold Inv16. rewrite Eps, Epr. exact I18.
  - (* Inv17 *) unfold Inv17. rewrite Efb, Ebt, Ebn. exact I19.
  - (* Inv18 *) unfold Inv18. rewrite Els, Ebt, Ebn, Eat, Ean. exact I20.
  - (* Inv19 *) unfold Inv19. rewrite Ert. exact I21.
  - (* Inv20 *) unfold Inv20.
    rewrite Eob, Efbl, Efb, Ebo, Ewp, Ebt, Ebn. exact I22.
  - (* Inv21 *) intros t0 ns0 b0 q0 Hob Hwp Hq0. rewrite Eob in Hob.
    rewrite Ewp in Hwp. destruct (I23 t0 ns0 b0 q0 Hob Hwp Hq0) as [He Hm0].
    assert (Hne : b0 <> pa_block pa \/ q0 <> pa_page pa).
    { destruct (nat_pair_dec b0 (pa_block pa) q0 (pa_page pa))
        as [[E1 E2]|H']; [|exact H'].
      exfalso. subst b0 q0. rewrite He in Hps. discriminate. }
    rewrite Eps, (Epm_other b0 q0 Hne). split; [exact He|exact Hm0].
  - (* Inv22 *) unfold Inv22. rewrite Els, Eps. exact I24.
  - (* Inv23 *) unfold Inv23. rewrite Ebo, Eob. exact I25.
  - (* Inv24 *) unfold Inv24. rewrite Efb, Efbl. exact I26.
  - (* Inv25 *) unfold Inv25. rewrite Eob, Ewp, Eps. exact I27.
  - (* Inv26 *) unfold Inv26. rewrite Els, Eat, Ean. exact I28.
Qed.

Theorem dedup_step_preserves_invariant :
  forall s op s',
    dedup_invariant s -> dedup_step s op = Some s' -> dedup_invariant s'.
Proof.
  intros s op s' Hinv Hstep. destruct op as [a p|a p d|a p|a p tag| |].
  - exact (dedup_read_preserves_invariant s a p s' Hinv Hstep).
  - exact (dedup_step_write_preserves_invariant s a p d s' Hinv Hstep).
  - exact (dedup_invalidate_preserves_invariant s a p s' Hinv Hstep).
  - exact (dedup_set_tag_preserves_invariant s a p tag s' Hinv Hstep).
  - exact (dedup_step_gc_preserves_invariant s s' COpGC (or_introl eq_refl)
             Hinv Hstep).
  - exact (dedup_step_gc_preserves_invariant s s' COpWearLevel
             (or_intror eq_refl) Hinv Hstep).
Qed.

Fixpoint dedup_exec (s : FTLState) (ops : list COp) : option FTLState :=
  match ops with
  | [] => Some s
  | op :: ops' =>
      match dedup_step s op with
      | Some s' => dedup_exec s' ops'
      | None => None
      end
  end.

Theorem dedup_exec_preserves_invariant :
  forall ops s s',
    dedup_invariant s -> dedup_exec s ops = Some s' -> dedup_invariant s'.
Proof.
  intros ops. induction ops as [|op tl IH]; intros s s' Hinv H.
  - cbn [dedup_exec] in H. injection H as H. subst s'. exact Hinv.
  - cbn [dedup_exec] in H.
    destruct (dedup_step s op) as [s1|] eqn:Hs; cbv beta iota in H;
      [|discriminate].
    exact (IH s1 s' (dedup_step_preserves_invariant s op s1 Hinv Hs) H).
Qed.

Theorem empty_state_dedup_invariant : dedup_invariant empty_state.
Proof.
  apply ftl_implies_dedup_invariant.
  exact (@empty_state_invariant pages_per_block_pos).
Qed.
