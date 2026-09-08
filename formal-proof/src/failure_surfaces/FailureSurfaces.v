(* FailureSurfaces.v — the five failure surfaces.

   The weak way to state a surface is as an implication over an arbitrary
   state: "if s happens to have a mapped block b, then the fault applied to s
   breaks Inv_k".  Nothing in such a statement rules out the hypotheses being
   unsatisfiable, so it is compatible with the fault never firing.

   This file states each surface the other way round.  One concrete state
   [witness] is exhibited and *proved* to satisfy all 29 conjuncts of
   [ftl_invariant].  Each surface is then modelled as a state
   transformation that performs an operation with one per-operation check
   omitted, and the result is proved to violate a named clause.  So each
   theorem is a genuine reachability statement: an invariant-satisfying state
   exists, the unchecked operation applies to it, and the successor breaks the
   invariant.

   Surface -> clause:

     FS1  host-interface request queue   -> Inv5   (mapped block still free)
     FS2  internal DRAM, FTL metadata    -> Inv2   (translation not injective)
     FS3  embedded compute units         -> Inv7   (page owner forged)
     FS4  flash controller               -> Inv9  (live page with no tag)
     FS5  NAND flash chips               -> Inv11  (free list has a duplicate)

   FS2 carries a second, intra-address aliasing fault: see
   [FS2_intra_address_alias] at the end of the FS2 section.  Page-granular
   translation maps each logical page independently, so two pages *of one
   address* can be pointed at one physical page.  Inv2 rules that out, and the
   DRAM fault reaches it. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import Invariants.Invariants.

Import ListNotations.

(* ================================================================== *)
(* The witness state                                                   *)
(* ================================================================== *)

(* Geometry is concrete: pages_per_block = 4, total_blocks = 8,
   addr_space = 4.

   [witness] is the smallest state with a live page in it.  Logical page
   (0,0) is mapped to physical page (block 0, page 0); block 0 is the open
   block of tenant 1 in namespace 1, with the write pointer at 1, so page 0
   of block 0 is below the frontier and pages 1..3 are above it.  Blocks
   1..7 are free.  Every logical address is labelled (tenant 1,
   namespace 1), which is what a write needs in order to allocate. *)
Definition witness : FTLState :=
  mkFTLState
    (* l2p_map *)
    (fun a p => if andb (Nat.eqb a 0) (Nat.eqb p 0)
                then Some (mkPhysAddr 0 0) else None)
    (* page_state *)
    (fun b p => if andb (Nat.eqb b 0) (Nat.eqb p 0)
                then PS_Valid 7 else PS_Empty)
    (* page_role *)
    (fun b p => if andb (Nat.eqb b 0) (Nat.eqb p 0)
                then Some RData else None)
    (* addr_tenant *)
    (fun _ => Some 1)
    (* addr_namespace *)
    (fun _ => Some 1)
    (* block_tenant *)
    (fun b => if Nat.eqb b 0 then Some 1 else None)
    (* block_namespace *)
    (fun b => if Nat.eqb b 0 then Some 1 else None)
    (* page_meta *)
    (fun b p => if andb (Nat.eqb b 0) (Nat.eqb p 0)
                then mkPageMeta 1 1 (Some 9) (Some (0, 0))
                else empty_page_meta)
    (* region_table *)
    (fun _ => None)
    (* free_block_list *)
    (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil)
    (* free_block *)
    (fun b => andb (negb (Nat.eqb b 0)) (Nat.ltb b 8))
    (* wear_count *)
    (fun _ => 0)
    (* key_table *)
    (fun _ => None)
    (* open_block *)
    (fun t ns => if andb (Nat.eqb t 1) (Nat.eqb ns 1) then Some 0 else None)
    (* write_ptr *)
    (fun t ns => if andb (Nat.eqb t 1) (Nat.eqb ns 1) then 1 else 0)
    (* block_open *)
    (fun b => Nat.eqb b 0).

(* ------------------------------------------------------------------ *)
(* Free-list arithmetic, used by six of the clauses                    *)
(* ------------------------------------------------------------------ *)

Lemma w_free_in_bounds :
  forall b, In b (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil) -> 1 <= b < 8.
Proof.
  intros b H. cbn in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
    try (subst; lia); try contradiction.
Qed.

Lemma w_free_from_bounds :
  forall b, 1 <= b < 8 -> In b (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil).
Proof.
  intros b H. cbn.
  destruct b as [|[|[|[|[|[|[|[|b']]]]]]]]; lia.
Qed.

Lemma w_free_nodup : NoDup (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil).
Proof.
  repeat (apply NoDup_cons; [ cbn; lia | ]).
  apply NoDup_nil.
Qed.

(* ------------------------------------------------------------------ *)
(* The witness satisfies every clause                                  *)
(* ------------------------------------------------------------------ *)

Lemma witness_WF0 : WF0 witness.
Proof. unfold WF0, pages_per_block. lia. Qed.

Lemma witness_WF1 : WF1 witness.
Proof. unfold WF1. intros b p _ _. eexists. reflexivity. Qed.

Lemma witness_Inv0 : Inv0 witness.
Proof.
  unfold Inv0. intros b p d H. cbn in H.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  apply andb_true_iff in E. destruct E as [Eb Ep].
  apply Nat.eqb_eq in Eb. apply Nat.eqb_eq in Ep. subst.
  exists 0, 0. cbn. reflexivity.
Qed.

Lemma witness_Inv1 : Inv1 witness.
Proof.
  unfold Inv1. intros a p pa H. cbn in H.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  apply andb_true_iff in E. destruct E as [Ea Ep].
  apply Nat.eqb_eq in Ea. apply Nat.eqb_eq in Ep. subst.
  inversion H. subst pa. cbn.
  unfold total_blocks, pages_per_block, addr_space.
  repeat split; lia.
Qed.

Lemma witness_Inv2 : Inv2 witness.
Proof.
  unfold Inv2. intros a1 p1 a2 p2 pa H1 H2. cbn in H1, H2.
  destruct (andb (Nat.eqb a1 0) (Nat.eqb p1 0)) eqn:E1; [|discriminate].
  destruct (andb (Nat.eqb a2 0) (Nat.eqb p2 0)) eqn:E2; [|discriminate].
  apply andb_true_iff in E1. destruct E1 as [Ea1 Ep1].
  apply andb_true_iff in E2. destruct E2 as [Ea2 Ep2].
  apply Nat.eqb_eq in Ea1. apply Nat.eqb_eq in Ep1.
  apply Nat.eqb_eq in Ea2. apply Nat.eqb_eq in Ep2. subst.
  split; reflexivity.
Qed.

Lemma witness_Inv3 : Inv3 witness.
Proof.
  unfold Inv3. intros a p pa d Hm _. cbn in Hm.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  apply andb_true_iff in E. destruct E as [Ea Ep].
  apply Nat.eqb_eq in Ea. apply Nat.eqb_eq in Ep. subst.
  inversion Hm. subst pa. cbn. reflexivity.
Qed.

Lemma witness_Inv4 : Inv4 witness.
Proof.
  unfold Inv4. intros a p b q d Hps Hlpa. cbn in Hps.
  destruct (andb (Nat.eqb b 0) (Nat.eqb q 0)) eqn:E; [|discriminate].
  apply andb_true_iff in E. destruct E as [Eb Eq].
  apply Nat.eqb_eq in Eb. apply Nat.eqb_eq in Eq. subst.
  cbn in Hlpa. inversion Hlpa. subst. cbn. reflexivity.
Qed.

Lemma witness_Inv5 : Inv5 witness.
Proof.
  unfold Inv5. intros a p pa Hm. cbn in Hm.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  inversion Hm. subst pa. cbn.
  intro Hin. apply w_free_in_bounds in Hin. lia.
Qed.

Lemma witness_Inv6 : Inv6 witness.
Proof.
  unfold Inv6. intros b Hin p _. cbn in Hin.
  apply w_free_in_bounds in Hin.
  assert (Hb : Nat.eqb b 0 = false) by (apply Nat.eqb_neq; lia).
  cbn. rewrite Hb. cbn. split; reflexivity.
Qed.

Lemma witness_Inv7 : Inv7 witness.
Proof.
  unfold Inv7. intros a p pa d t ns Hm _ Hat Hns. cbn in Hm.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  inversion Hm. subst pa.
  cbn in Hat, Hns. inversion Hat. inversion Hns. subst.
  cbn. split; reflexivity.
Qed.

Lemma witness_Inv8 : Inv8 witness.
Proof.
  unfold Inv8. intros b Hin. cbn in Hin.
  apply w_free_in_bounds in Hin. unfold total_blocks. lia.
Qed.

Lemma witness_Inv9 : Inv9 witness.
Proof.
  unfold Inv9. intros b p d H. cbn in H.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  exists 9. cbn. rewrite E. reflexivity.
Qed.

Lemma witness_Inv10 : Inv10 witness.
Proof.
  unfold Inv10. intros b Hb.
  destruct (Nat.eqb b 0) eqn:Eb.
  - apply Nat.eqb_eq in Eb. subst b.
    right. left. exists 1, 1. cbn. reflexivity.
  - apply Nat.eqb_neq in Eb.
    left. cbn. apply w_free_from_bounds.
    unfold total_blocks in Hb. lia.
Qed.

Lemma witness_Inv11 : Inv11 witness.
Proof. unfold Inv11. cbn. apply w_free_nodup. Qed.

Lemma witness_Inv12 : Inv12 witness.
Proof.
  unfold Inv12. intros b _ [p Hrole]. cbn in Hrole.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)); discriminate.
Qed.

Lemma witness_Inv13 : Inv13 witness.
Proof.
  unfold Inv13. intros b p d H. cbn in H.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  cbn. rewrite E. reflexivity.
Qed.

Lemma witness_Inv14 : Inv14 witness.
Proof.
  unfold Inv14. intros b p H. cbn in H.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  exists 7. cbn. rewrite E. reflexivity.
Qed.

Lemma witness_Inv15 : Inv15 witness.
Proof.
  unfold Inv15. intros b p H. cbn in H.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)); discriminate.
Qed.

Lemma witness_Inv16 : Inv16 witness.
Proof.
  unfold Inv16. intros b p H. cbn in H.
  destruct (andb (Nat.eqb b 0) (Nat.eqb p 0)) eqn:E; [discriminate|].
  cbn. rewrite E. reflexivity.
Qed.

Lemma witness_Inv17 : Inv17 witness.
Proof.
  unfold Inv17. intros b H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply negb_true_iff in H1.
  cbn. rewrite H1. split; reflexivity.
Qed.

Lemma witness_Inv18 : Inv18 witness.
Proof.
  unfold Inv18. intros a p pa Hm. cbn in Hm.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  inversion Hm. subst pa. cbn. split; reflexivity.
Qed.

Lemma witness_Inv19 : Inv19 witness.
Proof. unfold Inv19. intros i r H. cbn in H. discriminate. Qed.

Lemma witness_Inv20 : Inv20 witness.
Proof.
  unfold Inv20. intros t ns b Hob. cbn in Hob.
  destruct (andb (Nat.eqb t 1) (Nat.eqb ns 1)) eqn:E; [|discriminate].
  inversion Hob. subst b.
  apply andb_true_iff in E. destruct E as [Et Ens].
  apply Nat.eqb_eq in Et. apply Nat.eqb_eq in Ens. subst t ns.
  cbn. unfold total_blocks, pages_per_block.
  split; [lia | ].
  split; [intro Hin; apply w_free_in_bounds in Hin; lia | ].
  split; [reflexivity | ].
  split; [reflexivity | ].
  split; [lia | ].
  split; [right; reflexivity | ].
  split; [right; reflexivity | ].
  intros t' ns' H'. cbn in H'.
  destruct (andb (Nat.eqb t' 1) (Nat.eqb ns' 1)) eqn:E'; [|discriminate].
  apply andb_true_iff in E'. destruct E' as [Et' Ens'].
  apply Nat.eqb_eq in Et'. apply Nat.eqb_eq in Ens'.
  split; assumption.
Qed.

Lemma witness_Inv21 : Inv21 witness.
Proof.
  unfold Inv21. intros t ns b q Hob Hwp Hq. cbn in Hob.
  destruct (andb (Nat.eqb t 1) (Nat.eqb ns 1)) eqn:E; [|discriminate].
  inversion Hob. subst b.
  apply andb_true_iff in E. destruct E as [Et Ens].
  apply Nat.eqb_eq in Et. apply Nat.eqb_eq in Ens. subst t ns.
  cbn in Hwp.
  assert (Hq0 : Nat.eqb q 0 = false) by (apply Nat.eqb_neq; lia).
  cbn. rewrite Hq0. split; reflexivity.
Qed.

Lemma witness_Inv22 : Inv22 witness.
Proof.
  unfold Inv22. intros a p pa Hm. cbn in Hm.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E; [|discriminate].
  inversion Hm. subst pa. exists 7. cbn. reflexivity.
Qed.

Lemma witness_Inv23 : Inv23 witness.
Proof.
  unfold Inv23. intros b H. cbn in H.
  apply Nat.eqb_eq in H. subst b.
  exists 1, 1. cbn. reflexivity.
Qed.

Lemma witness_Inv24 : Inv24 witness.
Proof.
  unfold Inv24. intro b. split.
  - intro H. cbn in H. apply andb_true_iff in H. destruct H as [H1 H2].
    apply negb_true_iff in H1. apply Nat.eqb_neq in H1.
    apply Nat.leb_le in H2.
    cbn. apply w_free_from_bounds. lia.
  - intro H. cbn in H. apply w_free_in_bounds in H.
    cbn. apply andb_true_iff. split.
    + apply negb_true_iff. apply Nat.eqb_neq. lia.
    + apply Nat.leb_le. lia.
Qed.

Lemma witness_Inv25 : Inv25 witness.
Proof.
  unfold Inv25. intros t ns b q Hob Hq. cbn in Hob.
  destruct (andb (Nat.eqb t 1) (Nat.eqb ns 1)) eqn:E; [|discriminate].
  inversion Hob. subst b.
  apply andb_true_iff in E. destruct E as [Et Ens].
  apply Nat.eqb_eq in Et. apply Nat.eqb_eq in Ens. subst t ns.
  cbn in Hq.
  assert (q = 0) by lia. subst q.
  cbn. discriminate.
Qed.

Lemma witness_Inv26 : Inv26 witness.
Proof.
  unfold Inv26. intros a p pa _.
  split; [exists 1 | exists 1]; cbn; reflexivity.
Qed.

Theorem witness_invariant : ftl_invariant witness.
Proof.
  apply make_ftl_invariant.
  - exact witness_WF0.   - exact witness_WF1.   - exact witness_Inv0.
  - exact witness_Inv1.   - exact witness_Inv2.   - exact witness_Inv3.
  - exact witness_Inv4.   - exact witness_Inv5.   - exact witness_Inv6.
  - exact witness_Inv7.   - exact witness_Inv8.  - exact witness_Inv9.
  - exact witness_Inv10.  - exact witness_Inv11.  - exact witness_Inv12.
  - exact witness_Inv13.  - exact witness_Inv14.  - exact witness_Inv15.
  - exact witness_Inv16.  - exact witness_Inv17.  - exact witness_Inv18.
  - exact witness_Inv19.  - exact witness_Inv20.  - exact witness_Inv21.
  - exact witness_Inv22.  - exact witness_Inv23.  - exact witness_Inv24.
  - exact witness_Inv25.  - exact witness_Inv26.
Qed.

(* ================================================================== *)
(* FS1 — host-interface request queue                                  *)
(* ================================================================== *)

(* The HIL turns a host command into an FTL mapping update.  Installing a
   mapping is legitimate only after the destination block has been taken off
   the free pool: [alloc_page] does exactly that, via [open_fresh], before
   [program_page] writes the l2p entry.  A queue command that reaches the
   mapping table without the allocator's free-list bookkeeping omits that
   check.  What is left is the transformation below: write the l2p entry,
   leave the free pool alone. *)
Definition fs1_map_without_freelist_check
    (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr) : FTLState :=
  mkFTLState
    (set_l2p_map (l2p_map s) a p (Some pa))
    (page_state s) (page_role s) (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s) (page_meta s) (region_table s)
    (free_block_list s)          (* the omitted check: block never removed *)
    (free_block s) (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

(* Block 1 is free in [witness].  The queue binds logical page (1,0) to
   physical page (block 1, page 0) anyway. *)
Definition fs1_state : FTLState :=
  fs1_map_without_freelist_check witness 1 0 (mkPhysAddr 1 0).

Lemma fs1_violates_Inv5 : ~ Inv5 fs1_state.
Proof.
  unfold Inv5, fs1_state. intro H.
  assert (Hm : l2p_map (fs1_map_without_freelist_check witness 1 0
                          (mkPhysAddr 1 0)) 1 0 = Some (mkPhysAddr 1 0))
    by reflexivity.
  specialize (H 1 0 (mkPhysAddr 1 0) Hm). cbn in H.
  apply H. cbn. left. reflexivity.
Qed.

Theorem FS1_hil_request_queue_reaches_Inv5_violation :
  ftl_invariant witness /\
  ~ Inv5 fs1_state /\
  ~ ftl_invariant fs1_state.
Proof.
  split; [exact witness_invariant | split; [exact fs1_violates_Inv5 |]].
  intro Hinv. destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [H7 _]]]]]]]].
  exact (fs1_violates_Inv5 H7).
Qed.

(* ================================================================== *)
(* FS2 — internal DRAM holding FTL metadata                            *)
(* ================================================================== *)

(* The l2p table lives in the controller's internal DRAM.  Every legitimate
   producer of a table entry ([program_page], reached through [exec_write]
   or [relocate_page]) writes an entry that points at a page just handed out
   by [alloc_page], hence at a page no other logical page owns.  A DRAM-side
   write that skips that discipline is the transformation below: it aims a
   second logical page at a physical page that is already the target of a
   first.  Structurally it is the same edit as FS1's; what makes it a
   different surface is where it points. *)
Definition fs2_dram_alias_without_injectivity_check
    (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr) : FTLState :=
  mkFTLState
    (set_l2p_map (l2p_map s) a p (Some pa))
    (page_state s) (page_role s) (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s) (page_meta s) (region_table s)
    (free_block_list s) (free_block s) (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

(* (0,0) already maps to physical page (0,0) in [witness].  Aim (1,0) at it
   too: two distinct logical addresses now resolve to one physical page. *)
Definition fs2_state : FTLState :=
  fs2_dram_alias_without_injectivity_check witness 1 0 (mkPhysAddr 0 0).

Lemma fs2_violates_Inv2 : ~ Inv2 fs2_state.
Proof.
  unfold Inv2, fs2_state. intro H.
  assert (H1 : l2p_map (fs2_dram_alias_without_injectivity_check witness 1 0
                          (mkPhysAddr 0 0)) 0 0 = Some (mkPhysAddr 0 0))
    by reflexivity.
  assert (H2 : l2p_map (fs2_dram_alias_without_injectivity_check witness 1 0
                          (mkPhysAddr 0 0)) 1 0 = Some (mkPhysAddr 0 0))
    by reflexivity.
  destruct (H 0 0 1 0 (mkPhysAddr 0 0) H1 H2) as [Ha _].
  discriminate Ha.
Qed.

Theorem FS2_internal_dram_reaches_Inv2_violation :
  ftl_invariant witness /\
  ~ Inv2 fs2_state /\
  ~ ftl_invariant fs2_state.
Proof.
  split; [exact witness_invariant | split; [exact fs2_violates_Inv2 |]].
  intro Hinv. destruct Hinv as [_ [_ [_ [_ [H4 _]]]]].
  exact (fs2_violates_Inv2 H4).
Qed.

(* The intra-address variant.  Page-granular translation gives one address
   [pages_per_block] independent entries, and Inv2 has to rule out the fault
   of pointing two of them at one physical page.  The same DRAM write
   reaches it: here address 0 keeps its page 0 mapping and additionally aims
   its page 1 at the very same physical page. *)
Definition fs2_intra_state : FTLState :=
  fs2_dram_alias_without_injectivity_check witness 0 1 (mkPhysAddr 0 0).

Lemma fs2_intra_violates_Inv2 : ~ Inv2 fs2_intra_state.
Proof.
  unfold Inv2, fs2_intra_state. intro H.
  assert (H1 : l2p_map (fs2_dram_alias_without_injectivity_check witness 0 1
                          (mkPhysAddr 0 0)) 0 0 = Some (mkPhysAddr 0 0))
    by reflexivity.
  assert (H2 : l2p_map (fs2_dram_alias_without_injectivity_check witness 0 1
                          (mkPhysAddr 0 0)) 0 1 = Some (mkPhysAddr 0 0))
    by reflexivity.
  destruct (H 0 0 0 1 (mkPhysAddr 0 0) H1 H2) as [_ Hp].
  discriminate Hp.
Qed.

Theorem FS2_intra_address_alias :
  ftl_invariant witness /\
  ~ Inv2 fs2_intra_state /\
  ~ ftl_invariant fs2_intra_state.
Proof.
  split; [exact witness_invariant | split; [exact fs2_intra_violates_Inv2 |]].
  intro Hinv. destruct Hinv as [_ [_ [_ [_ [H4 _]]]]].
  exact (fs2_intra_violates_Inv2 H4).
Qed.

(* ================================================================== *)
(* FS3 — embedded compute units                                        *)
(* ================================================================== *)

(* [program_page] stamps a page's owner from [addr_tenant]/[addr_namespace]
   of the logical address being written; that read of the address label is
   the check that keeps per-page ownership honest.  A compute unit that
   rewrites [page_meta] directly omits it and can name any owner it likes.
   The crypto tag and the OOB stamp are carried over so that Inv9, Inv3 and
   Inv4 are untouched and the violation is isolated to Inv7. *)
Definition fs3_meta_write_without_owner_check
    (s : FTLState) (b : Block) (p : Page)
    (t' : TenantId) (ns' : NamespaceId) : FTLState :=
  mkFTLState
    (l2p_map s) (page_state s) (page_role s)
    (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s)
    (set_page_meta (page_meta s) b p
       (mkPageMeta t' ns'
                   (page_tag (page_meta s b p))
                   (page_lpa (page_meta s b p))))
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

(* The live page (0,0) belongs to tenant 1.  Restamp it as tenant 2. *)
Definition fs3_state : FTLState :=
  fs3_meta_write_without_owner_check witness 0 0 2 2.

Lemma fs3_violates_Inv7 : ~ Inv7 fs3_state.
Proof.
  unfold Inv7, fs3_state. intro H.
  assert (Hm : l2p_map (fs3_meta_write_without_owner_check witness 0 0 2 2)
                 0 0 = Some (mkPhysAddr 0 0)) by reflexivity.
  assert (Hps : page_state (fs3_meta_write_without_owner_check witness 0 0 2 2)
                  (pa_block (mkPhysAddr 0 0)) (pa_page (mkPhysAddr 0 0))
                  = PS_Valid 7) by reflexivity.
  assert (Hat : addr_tenant (fs3_meta_write_without_owner_check witness 0 0 2 2)
                  0 = Some 1) by reflexivity.
  assert (Hns : addr_namespace
                  (fs3_meta_write_without_owner_check witness 0 0 2 2)
                  0 = Some 1) by reflexivity.
  destruct (H 0 0 (mkPhysAddr 0 0) 7 1 1 Hm Hps Hat Hns) as [Ht _].
  cbn in Ht. discriminate Ht.
Qed.

Theorem FS3_compute_units_reaches_Inv7_violation :
  ftl_invariant witness /\
  ~ Inv7 fs3_state /\
  ~ ftl_invariant fs3_state.
Proof.
  split; [exact witness_invariant | split; [exact fs3_violates_Inv7 |]].
  intro Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H9 _]]]]]]]]]].
  exact (fs3_violates_Inv7 H9).
Qed.

(* ================================================================== *)
(* FS4 — flash controller                                              *)
(* ================================================================== *)

(* A page program writes data and OOB together: [program_page] sets the page
   to [PS_Valid d] and its metadata to a record carrying [Some d] as the
   integrity tag, in one step.  A flash controller that issues the data
   phase and drops the tag phase leaves a page that reads back as live with
   no tag to check it against.  Everything else about the page is kept
   well-formed — the role is set to RData so Inv13 still holds — so the only
   clause left standing between this state and the invariant is Inv9. *)
Definition fs4_program_without_tag_write
    (s : FTLState) (b : Block) (p : Page) (d : Data) : FTLState :=
  mkFTLState
    (l2p_map s)
    (set_page_state (page_state s) b p (PS_Valid d))
    (set_page_role (page_role s) b p (Some RData))
    (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s)
    (set_page_meta (page_meta s) b p
       (mkPageMeta (page_owner_tenant (page_meta s b p))
                   (page_owner_namespace (page_meta s b p))
                   None                       (* the omitted tag write *)
                   (page_lpa (page_meta s b p))))
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

(* Program page 1 of the open block — the page the frontier would hand out
   next — with the tag phase dropped. *)
Definition fs4_state : FTLState :=
  fs4_program_without_tag_write witness 0 1 5.

Lemma fs4_violates_Inv9 : ~ Inv9 fs4_state.
Proof.
  unfold Inv9, fs4_state. intro H.
  assert (Hps : page_state (fs4_program_without_tag_write witness 0 1 5)
                  0 1 = PS_Valid 5) by reflexivity.
  destruct (H 0 1 5 Hps) as [tag Htag].
  cbn in Htag. discriminate Htag.
Qed.

Theorem FS4_flash_controller_reaches_Inv9_violation :
  ftl_invariant witness /\
  ~ Inv9 fs4_state /\
  ~ ftl_invariant fs4_state.
Proof.
  split; [exact witness_invariant | split; [exact fs4_violates_Inv9 |]].
  intro Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H11 _]]]]]]]]]]]].
  exact (fs4_violates_Inv9 H11).
Qed.

(* ================================================================== *)
(* FS5 — NAND flash chips                                              *)
(* ================================================================== *)

(* [erase_block] is reached only through [reclaim], and only for a block
   [find_victim] found [reclaimable] — in particular a block whose free bit
   is clear, so it is not already on the free list.  A raw chip-level erase
   that returns a block to the pool without that test pushes a second copy
   of an already-free block onto the list, and the free pool then hands the
   same physical block out twice. *)
Definition fs5_erase_without_already_free_check
    (s : FTLState) (b : Block) : FTLState :=
  mkFTLState
    (l2p_map s) (page_state s) (page_role s)
    (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s) (page_meta s) (region_table s)
    (b :: free_block_list s)              (* pushed without the test *)
    (set_free_block (free_block s) b true)
    (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

(* Block 1 is already free in [witness]. *)
Definition fs5_state : FTLState :=
  fs5_erase_without_already_free_check witness 1.

Lemma fs5_violates_Inv11 : ~ Inv11 fs5_state.
Proof.
  unfold Inv11, fs5_state. intro H. cbn in H.
  apply NoDup_cons_iff in H. destruct H as [Hnotin _].
  apply Hnotin. cbn. left. reflexivity.
Qed.

Theorem FS5_nand_flash_reaches_Inv11_violation :
  ftl_invariant witness /\
  ~ Inv11 fs5_state /\
  ~ ftl_invariant fs5_state.
Proof.
  split; [exact witness_invariant | split; [exact fs5_violates_Inv11 |]].
  intro Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H13 _]]]]]]]]]]]]]].
  exact (fs5_violates_Inv11 H13).
Qed.

(* ================================================================== *)
(* Summary                                                             *)
(* ================================================================== *)

(* One statement collecting the five surfaces: from a single state that
   satisfies all 29 conjuncts, each of the five unchecked operations reaches a
   state that does not. *)
Theorem five_failure_surfaces_reachable :
  ftl_invariant witness /\
  ~ Inv5  fs1_state /\
  ~ Inv2  fs2_state /\
  ~ Inv7  fs3_state /\
  ~ Inv9 fs4_state /\
  ~ Inv11 fs5_state.
Proof.
  split; [exact witness_invariant | ].
  split; [exact fs1_violates_Inv5 | ].
  split; [exact fs2_violates_Inv2 | ].
  split; [exact fs3_violates_Inv7 | ].
  split; [exact fs4_violates_Inv9 | ].
  exact fs5_violates_Inv11.
Qed.
