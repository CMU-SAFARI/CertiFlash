(* FSReachable.v: the failure-surface REACHABILITY results.

   [FailureSurfaces.v] exhibits one state-level witness per surface.  This file
   upgrades each witness to a genuine one-step reachability statement over the
   primitive transition system: from a well-formed state, a single *realizable*
   flash primitive drives [ftl_invariant] false.  The results are stated over
   core.Primitives and core.TraceRealizable and name clauses of the invariant
   bundle in src/Invariants/Invariants.v.

   Results and the clause each one breaks:
     FS1  AS1A  erase-while-mapped            Inv5
     FS1  AS1B  erase out-of-range            Inv8
     FS2  AS2A  inter-address map aliasing    Inv2
     FS2  AS2C  intra-address map aliasing    Inv2
     FS2  AS2B  namespace via aliasing        Inv7
     FS3  AS3   owner-tenant via aliasing     Inv7
     FS3  AS3B  namespace via aliasing        Inv7
     FS4  AS4   integrity-tag removal         Inv9
     FS5  AS5A  free-list duplication         Inv11
     FS5  AS5B  namespace via aliasing        Inv7

   AS4 and AS5A supersede the state-level witnesses [fs4_state] and [fs5_state]
   of [FailureSurfaces.v]: each is now the effect of a genuine instruction
   (the unified [PrimProgram] with an empty tag / [PrimFreePush]) issued with
   its [MicroOpPreconditions] precondition bundle omitted.  With the bundle
   the two instructions preserve all 29 conjuncts ([pre_sound_program_raw],
   [pre_sound_freepush]); the reachability results below drop exactly the
   conjunct that stands between the instruction and the break -- the tag being
   [Some _] for AS4, the block being not-already-free for AS5A.

   One attack has NO primitive-trace analogue and remains a state-level
   witness only:
     - FS2 master-key leakage: models an out-of-band DRAM field outside both
       the FTLState primitive interface and ftl_invariant.

   Note on AS5A.  With only [PrimErase] -- which prepends but never
   removes-then-re-adds within one step -- no one-step trace can break NoDup.
   [PrimFreePush] is precisely the bare push that erase never issues on its
   own: pushing a block that is already on the free list duplicates it.  Its
   bundle forbids that (and, for full soundness, also requires the block be
   closed, unowned, unmapped and erased -- the resting shape the clearing half
   of an erase leaves behind). *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Primitives.
Require Import Invariants.Invariants.
Require Import core.TraceRealizable.

Import ListNotations.

(* ── Primitive-level facts about PrimErase (page-granular) ─────────────── *)

(* PrimErase never rewrites the forward map. *)
Lemma erase_l2p_map :
  forall s b a p, l2p_map (apply_primitive s (PrimErase b)) a p = l2p_map s a p.
Proof. intros. reflexivity. Qed.

(* PrimErase prepends the erased block to the free list. *)
Lemma erase_free_block_list :
  forall s b,
    free_block_list (apply_primitive s (PrimErase b)) = b :: free_block_list s.
Proof. intros. reflexivity. Qed.

Lemma in_erase_free_block_list :
  forall s b, In b (free_block_list (apply_primitive s (PrimErase b))).
Proof.
  intros s b. rewrite erase_free_block_list. left. reflexivity.
Qed.

(* ── Primitive-level facts about PrimMapAddr (page-granular) ───────────── *)

(* PrimMapAddr installs exactly one forward-map entry at (a, p). *)
Lemma mapaddr_l2p_hit :
  forall s a p pa,
    l2p_map (apply_primitive s (PrimMapAddr a p pa)) a p = Some pa.
Proof.
  intros. cbn. unfold install_mapping, set_l2p_map. cbn.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma mapaddr_l2p_miss :
  forall s a p a' p' pa,
    (a', p') <> (a, p) ->
    l2p_map (apply_primitive s (PrimMapAddr a p pa)) a' p'
      = l2p_map s a' p'.
Proof.
  intros s a p a' p' pa Hne. cbn. unfold install_mapping, set_l2p_map. cbn.
  destruct (Nat.eqb a' a) eqn:Ea; destruct (Nat.eqb p' p) eqn:Ep; cbn;
    try reflexivity.
  apply Nat.eqb_eq in Ea. apply Nat.eqb_eq in Ep. subst. contradiction.
Qed.

(* PrimMapAddr leaves page state, page metadata and the address labelling
   untouched: it only rewrites l2p_map and the block-ownership fields. *)
Lemma mapaddr_page_state :
  forall s a p pa b q,
    page_state (apply_primitive s (PrimMapAddr a p pa)) b q = page_state s b q.
Proof. intros. reflexivity. Qed.

Lemma mapaddr_page_meta :
  forall s a p pa b q,
    page_meta (apply_primitive s (PrimMapAddr a p pa)) b q = page_meta s b q.
Proof. intros. reflexivity. Qed.

Lemma mapaddr_addr_tenant :
  forall s a p pa a',
    addr_tenant (apply_primitive s (PrimMapAddr a p pa)) a' = addr_tenant s a'.
Proof. intros. reflexivity. Qed.

Lemma mapaddr_addr_namespace :
  forall s a p pa a',
    addr_namespace (apply_primitive s (PrimMapAddr a p pa)) a' = addr_namespace s a'.
Proof. intros. reflexivity. Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS1 (host-interface request queue)                                       *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* AS1A: erase-while-mapped violates Inv5 (a mapped block must not be free).
   PrimErase carries no realizability precondition, and it appends the erased
   block to the free list without touching l2p_map -- so the logical page still
   points into a block that is now back on the free list. *)
Theorem AS1A_reachable_via_primitive :
  forall s a p pa,
    l2p_map s a p = Some pa ->
    trace_realizable s [PrimErase (pa_block pa)] /\
    ~ ftl_invariant (exec_primitives s [PrimErase (pa_block pa)]).
Proof.
  intros s a p pa Hm.
  split.
  - (* PrimErase carries no precondition, so the one-step trace is realizable *)
    cbn. tauto.
  - intro Hinv.
    assert (HInv5 : Inv5 (exec_primitives s [PrimErase (pa_block pa)]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]; exact H).
    (* the mapping is untouched: (a, p) still points at pa *)
    assert (Ha : l2p_map (exec_primitives s [PrimErase (pa_block pa)]) a p = Some pa).
    { change (exec_primitives s [PrimErase (pa_block pa)])
        with (apply_primitive s (PrimErase (pa_block pa))).
      rewrite erase_l2p_map. exact Hm. }
    (* but pa_block pa is now on the free list *)
    assert (Hin : In (pa_block pa)
                     (free_block_list (exec_primitives s [PrimErase (pa_block pa)]))).
    { change (exec_primitives s [PrimErase (pa_block pa)])
        with (apply_primitive s (PrimErase (pa_block pa))).
      apply in_erase_free_block_list. }
    exact (HInv5 a p pa Ha Hin).
Qed.

(* AS1B: erase of an out-of-range block violates Inv8 (every free block is in
   range).  PrimErase appends b >= total_blocks to the free list. *)
Theorem AS1B_reachable_via_primitive :
  forall s b,
    b >= total_blocks ->
    trace_realizable s [PrimErase b] /\
    ~ ftl_invariant (exec_primitives s [PrimErase b]).
Proof.
  intros s b Hb.
  split.
  - cbn. tauto.
  - intro Hinv.
    assert (HInv8 : Inv8 (exec_primitives s [PrimErase b]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]]; exact H).
    assert (Hin : In b (free_block_list (exec_primitives s [PrimErase b]))).
    { change (exec_primitives s [PrimErase b])
        with (apply_primitive s (PrimErase b)).
      apply in_erase_free_block_list. }
    pose proof (HInv8 b Hin) as Hlt. lia.
Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS2 (internal DRAM, FTL metadata) -- Attack A: mapping aliasing          *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* AS2A: a single PrimMapAddr re-points a second logical page (a2, p) at a
   physical page pa that (a1, p) already maps to, breaking injectivity (Inv2).
   Under page-granular translation a2 <> a1 alone suffices: both distinct
   logical pages now translate to the same physical page. *)
Theorem AS2A_reachable_via_primitive :
  forall s a1 a2 p pa,
    a1 <> a2 ->
    l2p_map s a1 p = Some pa ->
    trace_realizable s [PrimMapAddr a2 p pa] /\
    ~ ftl_invariant (exec_primitives s [PrimMapAddr a2 p pa]).
Proof.
  intros s a1 a2 p pa Hne Hm.
  split.
  - (* PrimMapAddr carries no precondition, so the one-step trace is realizable *)
    cbn. tauto.
  - intro Hinv.
    assert (HInv2 : Inv2 (exec_primitives s [PrimMapAddr a2 p pa]))
      by (destruct Hinv as [_ [_ [_ [_ [H _]]]]]; exact H).
    (* a1's mapping survives (a1 <> a2) *)
    assert (Ha1 : l2p_map (exec_primitives s [PrimMapAddr a2 p pa]) a1 p = Some pa).
    { change (exec_primitives s [PrimMapAddr a2 p pa])
        with (apply_primitive s (PrimMapAddr a2 p pa)).
      rewrite mapaddr_l2p_miss by congruence.
      exact Hm. }
    (* a2 now aliases the same physical page *)
    assert (Ha2 : l2p_map (exec_primitives s [PrimMapAddr a2 p pa]) a2 p = Some pa).
    { change (exec_primitives s [PrimMapAddr a2 p pa])
        with (apply_primitive s (PrimMapAddr a2 p pa)).
      apply mapaddr_l2p_hit. }
    destruct (HInv2 a1 p a2 p pa Ha1 Ha2) as [Ha _].
    exact (Hne Ha).
Qed.

(* AS2C: the INTRA-address form of the same aliasing move.  Where AS2A fixes
   the page offset and varies the address, AS2C fixes the address [a] and varies
   the page offset: from a state where [(a, p1)] maps to [pa], a single
   PrimMapAddr at [(a, p2)] with [p1 <> p2] re-points a second logical page of
   the SAME address at [pa].  The update at [(a, p2)] leaves [(a, p1)] untouched
   (they differ in the page offset), so both distinct logical pages now
   translate to [pa] and injectivity (Inv2) fails -- here on the page-offset
   conjunct rather than the address conjunct. *)
Theorem AS2C_reachable_via_primitive :
  forall s a p1 p2 pa,
    p1 <> p2 ->
    l2p_map s a p1 = Some pa ->
    trace_realizable s [PrimMapAddr a p2 pa] /\
    ~ ftl_invariant (exec_primitives s [PrimMapAddr a p2 pa]).
Proof.
  intros s a p1 p2 pa Hne Hm.
  split.
  - (* PrimMapAddr carries no precondition, so the one-step trace is realizable *)
    cbn. tauto.
  - intro Hinv.
    assert (HInv2 : Inv2 (exec_primitives s [PrimMapAddr a p2 pa]))
      by (destruct Hinv as [_ [_ [_ [_ [H _]]]]]; exact H).
    (* (a, p1)'s mapping survives (p1 <> p2) *)
    assert (Ha1 : l2p_map (exec_primitives s [PrimMapAddr a p2 pa]) a p1 = Some pa).
    { change (exec_primitives s [PrimMapAddr a p2 pa])
        with (apply_primitive s (PrimMapAddr a p2 pa)).
      rewrite mapaddr_l2p_miss by congruence.
      exact Hm. }
    (* (a, p2) now aliases the same physical page *)
    assert (Ha2 : l2p_map (exec_primitives s [PrimMapAddr a p2 pa]) a p2 = Some pa).
    { change (exec_primitives s [PrimMapAddr a p2 pa])
        with (apply_primitive s (PrimMapAddr a p2 pa)).
      apply mapaddr_l2p_hit. }
    destruct (HInv2 a p1 a p2 pa Ha1 Ha2) as [_ Hp].
    exact (Hne Hp).
Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS2 -- Attack B: namespace reassignment, reachable via mapping aliasing   *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* AS2B: a single PrimMapAddr re-points (a2, p2), in a foreign namespace, at a
   block that already holds a live page belonging to (a1, p1).  PrimMapAddr
   leaves page_state and page_meta untouched, so the page keeps a1's
   owner-namespace while a2 now reaches it -- Inv7 (page-owner isolation) is
   falsified on the namespace projection.

   (FS2 Attack C -- master-key leakage -- has no primitive-trace analogue and
   so gets no theorem here; it models an out-of-band DRAM field outside the
   primitive interface and ftl_invariant.)

   AS2B, AS3B (FS3) and AS5B (FS5) are the identical namespace-break fact, one
   theorem recorded per surface; they differ only in the surface whose threat
   model issues the move. AS3 is the tenant-projection variant. *)
Theorem AS2B_reachable_via_primitive :
  forall s a1 p1 a2 p2 pa d t2 ns2,
    (a1, p1) <> (a2, p2) ->
    l2p_map s a1 p1 = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    addr_tenant s a2 = Some t2 ->
    addr_namespace s a2 = Some ns2 ->
    page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)) <> ns2 ->
    trace_realizable s [PrimMapAddr a2 p2 pa] /\
    ~ ftl_invariant (exec_primitives s [PrimMapAddr a2 p2 pa]).
Proof.
  intros s a1 p1 a2 p2 pa d t2 ns2 Hne Hm Hps Hat Hans Howner.
  split.
  - cbn. tauto.
  - intro Hinv.
    assert (HInv7 : Inv7 (exec_primitives s [PrimMapAddr a2 p2 pa]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
    assert (Ha2 : l2p_map (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 p2 = Some pa)
      by (apply mapaddr_l2p_hit).
    assert (Hps' : page_state (exec_primitives s [PrimMapAddr a2 p2 pa])
                     (pa_block pa) (pa_page pa) = PS_Valid d)
      by (cbn; exact Hps).
    assert (Hat' : addr_tenant (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some t2)
      by (cbn; exact Hat).
    assert (Hans' : addr_namespace (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some ns2)
      by (cbn; exact Hans).
    destruct (HInv7 a2 p2 pa d t2 ns2 Ha2 Hps' Hat' Hans') as [_ Hns].
    cbn in Hns. exact (Howner Hns).
Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS3 (embedded compute units) -- owner-tenant override via aliasing        *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* AS3: the same aliasing move breaks Inv7 on the tenant projection.  A single
   PrimMapAddr re-points (a2, p2) -- a different tenant -- at a block that
   already holds a live page programmed for (a1, p1).  The page keeps a1's
   owner-tenant while a2 now reaches it, so its recorded owner disagrees with
   a2's tenant. *)
Theorem AS3_reachable_via_primitive :
  forall s a1 p1 a2 p2 pa d t2 ns2,
    (a1, p1) <> (a2, p2) ->
    l2p_map s a1 p1 = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    addr_tenant s a2 = Some t2 ->
    addr_namespace s a2 = Some ns2 ->
    page_owner_tenant (page_meta s (pa_block pa) (pa_page pa)) <> t2 ->
    trace_realizable s [PrimMapAddr a2 p2 pa] /\
    ~ ftl_invariant (exec_primitives s [PrimMapAddr a2 p2 pa]).
Proof.
  intros s a1 p1 a2 p2 pa d t2 ns2 Hne Hm Hps Hat Hans Howner.
  split.
  - cbn. tauto.
  - intro Hinv.
    assert (HInv7 : Inv7 (exec_primitives s [PrimMapAddr a2 p2 pa]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
    assert (Ha2 : l2p_map (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 p2 = Some pa)
      by (apply mapaddr_l2p_hit).
    assert (Hps' : page_state (exec_primitives s [PrimMapAddr a2 p2 pa])
                     (pa_block pa) (pa_page pa) = PS_Valid d)
      by (cbn; exact Hps).
    assert (Hat' : addr_tenant (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some t2)
      by (cbn; exact Hat).
    assert (Hans' : addr_namespace (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some ns2)
      by (cbn; exact Hans).
    destruct (HInv7 a2 p2 pa d t2 ns2 Ha2 Hps' Hat' Hans') as [Ht _].
    cbn in Ht. exact (Howner Ht).
Qed.

(* AS3B: the namespace projection of the FS3 override.  An accelerator routine
   re-points (a2, p2) -- in a different namespace -- at a block that already
   holds a live page programmed for (a1, p1).  The page keeps a1's
   owner-namespace, so its recorded namespace disagrees with a2's.  This is the
   compute-unit (FS3) instance of the namespace break; AS2B and AS5B are the
   same fact reached at FS2 and FS5. *)
Theorem AS3B_reachable_via_primitive :
  forall s a1 p1 a2 p2 pa d t2 ns2,
    (a1, p1) <> (a2, p2) ->
    l2p_map s a1 p1 = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    addr_tenant s a2 = Some t2 ->
    addr_namespace s a2 = Some ns2 ->
    page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)) <> ns2 ->
    trace_realizable s [PrimMapAddr a2 p2 pa] /\
    ~ ftl_invariant (exec_primitives s [PrimMapAddr a2 p2 pa]).
Proof.
  intros s a1 p1 a2 p2 pa d t2 ns2 Hne Hm Hps Hat Hans Howner.
  split.
  - cbn. tauto.
  - intro Hinv.
    assert (HInv7 : Inv7 (exec_primitives s [PrimMapAddr a2 p2 pa]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
    assert (Ha2 : l2p_map (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 p2 = Some pa)
      by (apply mapaddr_l2p_hit).
    assert (Hps' : page_state (exec_primitives s [PrimMapAddr a2 p2 pa])
                     (pa_block pa) (pa_page pa) = PS_Valid d)
      by (cbn; exact Hps).
    assert (Hat' : addr_tenant (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some t2)
      by (cbn; exact Hat).
    assert (Hans' : addr_namespace (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some ns2)
      by (cbn; exact Hans).
    destruct (HInv7 a2 p2 pa d t2 ns2 Ha2 Hps' Hat' Hans') as [_ Hns].
    cbn in Hns. exact (Howner Hns).
Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS5 (NAND flash chips) -- cross-namespace write via aliasing              *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* AS5B: cross-namespace break (Inv7, namespace projection) reachable by
   mapping aliasing, exactly as AS2B.  A single PrimMapAddr re-points (a2, p2),
   in a different namespace, at a block that already holds a live page
   belonging to (a1, p1); the page keeps a1's owner-namespace.

   (The other FS5 break -- free-list duplication, Inv11 -- is AS5A below.  No
   erase trace reaches it: PrimErase prepends the erased block, and no single
   primitive removes-then-re-adds a block within one step.  It takes the bare
   push [PrimFreePush].) *)
Theorem AS5B_reachable_via_primitive :
  forall s a1 p1 a2 p2 pa d t2 ns2,
    (a1, p1) <> (a2, p2) ->
    l2p_map s a1 p1 = Some pa ->
    page_state s (pa_block pa) (pa_page pa) = PS_Valid d ->
    addr_tenant s a2 = Some t2 ->
    addr_namespace s a2 = Some ns2 ->
    page_owner_namespace (page_meta s (pa_block pa) (pa_page pa)) <> ns2 ->
    trace_realizable s [PrimMapAddr a2 p2 pa] /\
    ~ ftl_invariant (exec_primitives s [PrimMapAddr a2 p2 pa]).
Proof.
  intros s a1 p1 a2 p2 pa d t2 ns2 Hne Hm Hps Hat Hans Howner.
  split.
  - cbn. tauto.
  - intro Hinv.
    assert (HInv7 : Inv7 (exec_primitives s [PrimMapAddr a2 p2 pa]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
    assert (Ha2 : l2p_map (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 p2 = Some pa)
      by (apply mapaddr_l2p_hit).
    assert (Hps' : page_state (exec_primitives s [PrimMapAddr a2 p2 pa])
                     (pa_block pa) (pa_page pa) = PS_Valid d)
      by (cbn; exact Hps).
    assert (Hat' : addr_tenant (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some t2)
      by (cbn; exact Hat).
    assert (Hans' : addr_namespace (exec_primitives s [PrimMapAddr a2 p2 pa]) a2 = Some ns2)
      by (cbn; exact Hans).
    destruct (HInv7 a2 p2 pa d t2 ns2 Ha2 Hps' Hat' Hans') as [_ Hns].
    cbn in Hns. exact (Howner Hns).
Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS4 (flash controller) -- integrity-tag removal                          *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* Primitive-level facts about PrimProgram: it programs the target page
   [PS_Valid d] and writes the supplied [tag] into the OOB. *)
Lemma program_page_state_hit :
  forall s pa d tag lpa,
    page_state (apply_primitive s (PrimProgram pa d tag lpa))
               (pa_block pa) (pa_page pa) = PS_Valid d.
Proof.
  intros. cbn [apply_primitive page_state]. unfold set_page_state.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma program_page_tag_hit :
  forall s pa d tag lpa,
    page_tag (page_meta (apply_primitive s (PrimProgram pa d tag lpa))
                        (pa_block pa) (pa_page pa)) = tag.
Proof.
  intros. cbn [apply_primitive page_meta]. unfold set_page_meta.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

(* AS4: a program issued with the tag phase dropped ([tag = None]) leaves a live
   page carrying no integrity tag, breaking Inv9.  The one hardware law is
   respected -- the target is erased -- so the one-step trace is realizable;
   the only thing dropped is the bundle's demand that the supplied tag be
   [Some _].  An honest expansion always supplies [Some d]; this is the same
   [PrimProgram] instruction driven by an untrusted controller. *)
Theorem AS4_reachable_via_primitive :
  forall s pa d lpa,
    page_state s (pa_block pa) (pa_page pa) = PS_Empty ->
    trace_realizable s [PrimProgram pa d None lpa] /\
    ~ ftl_invariant (exec_primitives s [PrimProgram pa d None lpa]).
Proof.
  intros s pa d lpa Hempty.
  split.
  - (* realizable: the program targets an erased page *)
    cbn [trace_realizable prim_realizable]. split; [exact Hempty | exact I].
  - intro Hinv.
    assert (HInv9 : Inv9 (exec_primitives s [PrimProgram pa d None lpa]))
      by (destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]]]; exact H).
    change (exec_primitives s [PrimProgram pa d None lpa])
      with (apply_primitive s (PrimProgram pa d None lpa)) in HInv9.
    (* the programmed page is live ... *)
    destruct (HInv9 (pa_block pa) (pa_page pa) d
                (program_page_state_hit s pa d None lpa)) as [tg Htg].
    (* ... but carries no tag *)
    rewrite (program_page_tag_hit s pa d None lpa) in Htg. discriminate Htg.
Qed.

(* ══════════════════════════════════════════════════════════════════════ *)
(* FS5A (NAND flash chips) -- free-block duplication                        *)
(* ══════════════════════════════════════════════════════════════════════ *)

(* PrimFreePush prepends its block to the free list, unconditionally. *)
Lemma freepush_free_block_list :
  forall s b,
    free_block_list (apply_primitive s (PrimFreePush b)) = b :: free_block_list s.
Proof. intros. reflexivity. Qed.

(* AS5A: pushing a block that is already on the free list duplicates it,
   breaking Inv11 (the free list is duplicate-free).  PrimFreePush carries no
   realizability precondition; the only thing dropped is the bundle's demand
   that the pushed block be not-already-free. *)
Theorem AS5A_reachable_via_primitive :
  forall s b,
    In b (free_block_list s) ->
    trace_realizable s [PrimFreePush b] /\
    ~ ftl_invariant (exec_primitives s [PrimFreePush b]).
Proof.
  intros s b Hin.
  split.
  - (* PrimFreePush carries no precondition, so the one-step trace is realizable *)
    cbn [trace_realizable prim_realizable]. tauto.
  - intro Hinv.
    assert (HInv11 : Inv11 (exec_primitives s [PrimFreePush b]))
      by (destruct Hinv as
            [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]]]]]; exact H).
    unfold Inv11 in HInv11.
    change (exec_primitives s [PrimFreePush b])
      with (apply_primitive s (PrimFreePush b)) in HInv11.
    rewrite freepush_free_block_list in HInv11.
    apply NoDup_cons_iff in HInv11. destruct HInv11 as [Hnotin _].
    exact (Hnotin Hin).
Qed.
