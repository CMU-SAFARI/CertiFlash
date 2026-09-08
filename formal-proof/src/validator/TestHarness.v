(* TestHarness.v: a random-trace runner for the PAGE-GRANULAR model.

   This is the instrument a designer reaches for BEFORE attempting a proof.
   It generates pseudo-random operation sequences, folds [Operational.step]
   over them, and runs the bounded invariant checker
   ([InvariantChecker.check_bounded_all]) after every accepted step.  A
   reported failure is not a heuristic warning: [check_refutes] turns a
   [false] verdict into a proof that the reached state violates
   [ftl_invariant], so the harness is a bug finder with no false
   positives ([run_trace_false_is_a_real_violation] below).  The converse
   does not hold — passing is evidence, not certification.

   Everything computes inside Rocq: the generator, the runner, and the
   aggregate results are closed terms, and the headline results are proved
   by [reflexivity] / [vm_compute].  No extraction, no plugin, no axiom.

   NO admitted lemmas, [admit], axiom declarations, parameters, variables or hypotheses
   is introduced; every result is closed with [Qed].

   ── The first thing the page-granular model tells you ──────────────────

   [empty_state] labels no address with a tenant or a namespace, and
   [step] REFUSES a write to an unlabelled address (allocating as tenant 0
   would relabel a genuine tenant-0 block).  A random trace started from
   [empty_state] therefore has *every* write rejected and never leaves the
   initial state — the harness would report a vacuous pass.  This is proved
   below as [empty_state_rejects_every_write] and measured as
   [empty_state_accepts_no_write].  A usable harness must start from a
   labelled state, so §2 builds [init_state] and proves it satisfies the
   full [ftl_invariant].

   ── And the second thing it tells you ─────────────────────────────────

   Once the traces get long enough the device WEDGES: no write can be
   performed and garbage collection cannot recover, while four blocks of
   pure garbage sit unclaimed.  The invariant holds throughout — this is
   a progress failure, not a safety one — so [check_bounded_all] accepts
   it, correctly.  §7 exhibits the state and pins the cause on two
   independent decisions in [Operational.v].  Nobody planted it; the
   random search walked into it. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import Invariants.Invariants.
Require Import validator.InvariantChecker.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════
   §1  A deterministic pseudo-random generator

   A linear congruential generator with the glibc constants, over binary
   naturals [N]: unary [nat] arithmetic on 2^31-sized constants is
   hopeless under [vm_compute].  Only the small residues cross back into
   [nat].

   The residue is taken from the HIGH bits.  This is not a stylistic
   choice.  A power-of-two-modulus LCG has period 2^k in its low k bits,
   so [x mod 16] cycles with period 16 in generator steps; drawing four
   words per operation collapsed the whole trace to a period-4 loop
   (COpWrite 3 0 / COpGC / COpInvalidate 3 0, forever) that touched one
   logical page and never filled a block.  Shifting right by 15 first
   uses bits 15..30 and removes the artefact.
   ══════════════════════════════════════════════════════════════ *)

Definition lcg_next (x : N) : N :=
  ((x * 1103515245 + 12345) mod 2147483648)%N.

(* Small residue of a random word, drawn from its high bits. *)
Definition nmod (x : N) (m : nat) : nat :=
  N.to_nat ((N.shiftr x 15) mod N.of_nat m).

(* An explicit nat seed, stirred so that adjacent seeds start far apart. *)
Definition seed_of (s : nat) : N :=
  lcg_next (lcg_next (lcg_next (N.of_nat s + 7)%N)).

(* ══════════════════════════════════════════════════════════════
   §2  A labelled starting state

   [init_state] is [empty_state] with the address space labelled:

       addr 0 -> (tenant 0, ns 0)     addr 2 -> (tenant 1, ns 0)
       addr 1 -> (tenant 0, ns 0)     addr 3 -> (tenant 1, ns 1)

   Three distinct (tenant, namespace) pairs, hence three independent
   allocation frontiers, one of which (0,0) is shared by two logical
   addresses — so a single block accumulates pages of two addresses, which
   is exactly the page-granular situation the reverse map (Inv3/Inv4) has
   to survive.  Nothing else changes, so the invariant proof is
   [empty_state_invariant] with two fields substituted: every clause that
   mentions [addr_tenant] or [addr_namespace] (Inv7, Inv18, Inv26) is
   guarded by [l2p_map], which is still empty.
   ══════════════════════════════════════════════════════════════ *)

Definition init_tenant (a : Addr) : option TenantId := Some (Nat.div a 2).

Definition init_namespace (a : Addr) : option NamespaceId :=
  Some (if Nat.eqb a 3 then 1 else 0).

Definition init_state : FTLState :=
  mkFTLState
    (fun _ _ => None)
    (fun _ _ => PS_Empty)
    (fun _ _ => None)
    init_tenant
    init_namespace
    (fun _ => None)
    (fun _ => None)
    (fun _ _ => empty_page_meta)
    (fun _ => None)
    (seq 0 total_blocks)
    (fun b => Nat.ltb b total_blocks)
    (fun _ => 0)
    (fun _ => None)
    (fun _ _ => None)
    (fun _ _ => 0)
    (fun _ => false).

Theorem init_state_invariant : ftl_invariant init_state.
Proof.
  apply make_ftl_invariant.
  - exact pages_per_block_pos.
  - unfold WF1, init_state. intros b p Hb Hp. exists PS_Empty. reflexivity.
  - unfold Inv0, init_state. intros b p d Hps. discriminate Hps.
  - unfold Inv1, init_state. intros a0 p0 pa0 Hm. discriminate Hm.
  - unfold Inv2, init_state. intros a1 p1 a2 p2 pa0 H1 _. discriminate H1.
  - unfold Inv3, init_state. intros a0 p0 pa0 d Hm _. discriminate Hm.
  - unfold Inv4, init_state. intros a0 p0 b0 q0 d Hps _. discriminate Hps.
  - unfold Inv5, init_state. intros a p0 pa0 Hm. discriminate Hm.
  - unfold Inv6, init_state. intros b Hin p Hp. split; reflexivity.
  - unfold Inv7, init_state. intros a p0 pa0 d t ns Hm _ _ _. discriminate Hm.
  - unfold Inv8, init_state. intros b0 Hin.
    change (In b0 (seq 0 total_blocks)) in Hin.
    apply in_seq in Hin. lia.
  - unfold Inv9, init_state. intros b p d Hps. discriminate Hps.
  - unfold Inv10, init_state. intros b Hb. left.
    change (In b (seq 0 total_blocks)). apply in_seq. lia.
  - unfold Inv11, init_state.
    change (NoDup (seq 0 total_blocks)). apply seq_NoDup.
  - unfold Inv12, init_state. intros b Hb [p Hrole]. discriminate Hrole.
  - unfold Inv13, init_state. intros b0 p0 d Hps. discriminate Hps.
  - unfold Inv14, init_state. intros b0 p0 Hrole. discriminate Hrole.
  - unfold Inv15, init_state. intros b0 p0 Hrole. discriminate Hrole.
  - unfold Inv16, init_state. intros b0 p0 Hempty. reflexivity.
  - unfold Inv17, init_state. intros b0 Hfree. split; reflexivity.
  - unfold Inv18, init_state. intros a0 p0 pa0 Hmap. discriminate Hmap.
  - unfold Inv19, init_state. intros i0 r0 Hr0. discriminate Hr0.
  - unfold Inv20, init_state. intros t0 ns0 b0 Hob. discriminate Hob.
  - unfold Inv21, init_state. intros t0 ns0 b0 q0 Hob. discriminate Hob.
  - unfold Inv22, init_state. intros a0 p0 pa0 Hm. discriminate Hm.
  - unfold Inv23, init_state. intros b0 Hbo. discriminate Hbo.
  - unfold Inv24. cbn [free_block free_block_list init_state]. intros b0. split.
    + intros H. apply Nat.ltb_lt in H. apply in_seq. lia.
    + intros H. apply in_seq in H. apply Nat.ltb_lt. lia.
  - unfold Inv25, init_state. intros t0 ns0 b0 q0 Hob. discriminate Hob.
  - unfold Inv26, init_state. intros a0 p0 pa0 Hm. discriminate Hm.
Qed.

(* The checker agrees, by computation. *)
Lemma check_accepts_init_state : check_bounded_all init_state = true.
Proof. reflexivity. Qed.

(* Why the seeding was necessary, as a theorem rather than an anecdote. *)
Theorem empty_state_rejects_every_write :
  forall a p d, step empty_state (COpWrite a p d) = None.
Proof.
  intros a p d. unfold step, empty_state. cbn.
  rewrite Bool.andb_false_r. reflexivity.
Qed.

(* ══════════════════════════════════════════════════════════════
   §3  Random operation and trace generation

   Weights (out of 16): 7 writes, 2 reads, 2 invalidates, 2 set-tags,
   2 GCs, 1 wear-level.  Write-heavy on purpose: only writes consume
   pages, and a device that never fills a block never exercises
   allocation, relocation, or reclaim.

   One draw in eight is "wild": the address and page offset are placed
   OUTSIDE the geometry (addr_space = 4, pages_per_block = 4), so the
   rejection paths of [step] are exercised too.
   ══════════════════════════════════════════════════════════════ *)

Definition gen_op (r1 r2 r3 r4 : N) : COp :=
  let wild := Nat.eqb (nmod r4 8) 0 in
  let a := if wild then addr_space + nmod r2 3 else nmod r2 addr_space in
  let p := if wild then pages_per_block + nmod r3 2 else nmod r3 pages_per_block in
  let d := nmod r4 64 in
  match nmod r1 16 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => COpWrite a p d
  | 7 | 8                     => COpRead a p
  | 9 | 10                    => COpInvalidate a p
  | 11 | 12                   => COpSetTag a p d
  | 13 | 14                   => COpGC
  | _                         => COpWearLevel
  end.

Fixpoint gen_trace_aux (r : N) (n : nat) : list COp :=
  match n with
  | O => []
  | S k =>
      let r1 := lcg_next r in
      let r2 := lcg_next r1 in
      let r3 := lcg_next r2 in
      let r4 := lcg_next r3 in
      gen_op r1 r2 r3 r4 :: gen_trace_aux r4 k
  end.

Definition gen_trace (s : nat) (n : nat) : list COp := gen_trace_aux (seed_of s) n.

(* ══════════════════════════════════════════════════════════════
   §4  The trace runner, and what a failure means

   The runner is parametric in the transition function so that §6 can
   point it at a deliberately broken one.  Rejected operations ([None])
   are NOT flagged: [step] refusing a write to an out-of-range or
   unlabelled address is the model behaving correctly, and flagging it
   would turn the harness into a noise generator.  The trace continues
   from the unchanged state; §5 reports how many were rejected, so a
   trace that is all-rejections cannot masquerade as a pass.
   ══════════════════════════════════════════════════════════════ *)

Definition StepFn := FTLState -> COp -> option FTLState.

(* The first state along the trace that the checker refutes, if any. *)
Fixpoint first_violation (stp : StepFn) (s : FTLState) (ops : list COp)
  : option FTLState :=
  match ops with
  | [] => None
  | op :: tl =>
      match stp s op with
      | None => first_violation stp s tl
      | Some s' =>
          if check_bounded_all s'
          then first_violation stp s' tl
          else Some s'
      end
  end.

(* Folding the transition function, skipping rejected operations. *)
Fixpoint exec_skip (stp : StepFn) (s : FTLState) (ops : list COp) : FTLState :=
  match ops with
  | [] => s
  | op :: tl =>
      match stp s op with
      | None => exec_skip stp s tl
      | Some s' => exec_skip stp s' tl
      end
  end.

Definition run_trace_with (stp : StepFn) (s : FTLState) (ops : list COp) : bool :=
  check_bounded_all s &&
  match first_violation stp s ops with
  | None => true
  | Some _ => false
  end.

(* The required entry point: the real model's [step]. *)
Definition run_trace (s : FTLState) (ops : list COp) : bool :=
  run_trace_with step s ops.

(* ── no false alarms ─────────────────────────────────────────────── *)

(* NOTE on the proof scripts below: every reduction is a [cbn] with an
   explicit delta list.  A bare [simpl]/[cbn] unfolds [check_bounded_all],
   whose 29 conjuncts expand [forallb] over the concrete geometry into a
   symbolic term large enough to hang the proof — this cost about ten
   minutes of wall clock to discover, so it is recorded here. *)

Lemma first_violation_refutes :
  forall stp ops s s',
    first_violation stp s ops = Some s' -> ~ ftl_invariant s'.
Proof.
  intros stp ops. induction ops as [|op tl IH]; intros s s' H.
  - discriminate H.
  - cbn [first_violation] in H. destruct (stp s op) as [s1|] eqn:E.
    + destruct (check_bounded_all s1) eqn:C.
      * exact (IH s1 s' H).
      * injection H as Hs. subst s'. apply check_refutes. exact C.
    + exact (IH s s' H).
Qed.

(* ...and the refuted state is one the trace actually reaches. *)
Lemma first_violation_reachable :
  forall stp ops s s',
    first_violation stp s ops = Some s' ->
    exists pre suf, ops = pre ++ suf /\ exec_skip stp s pre = s'.
Proof.
  intros stp ops. induction ops as [|op tl IH]; intros s s' H.
  - discriminate H.
  - cbn [first_violation] in H. destruct (stp s op) as [s1|] eqn:E.
    + destruct (check_bounded_all s1) eqn:C.
      * destruct (IH s1 s' H) as [pre [suf [Happ Hex]]].
        exists (op :: pre), suf. split.
        -- cbn [app]. rewrite Happ. reflexivity.
        -- cbn [exec_skip]. rewrite E. exact Hex.
      * injection H as Hs. subst s'.
        exists [op], tl. split.
        -- reflexivity.
        -- cbn [exec_skip]. rewrite E. reflexivity.
    + destruct (IH s s' H) as [pre [suf [Happ Hex]]].
      exists (op :: pre), suf. split.
      * cbn [app]. rewrite Happ. reflexivity.
      * cbn [exec_skip]. rewrite E. exact Hex.
Qed.

(* THE MEANING OF A HARNESS FAILURE.  Started from a state the checker
   accepts, a [false] verdict exhibits a concrete state, reached by a
   prefix of the trace, that provably breaks the global invariant.  The
   harness never cries wolf. *)
Theorem run_trace_false_is_a_real_violation :
  forall stp s ops,
    check_bounded_all s = true ->
    run_trace_with stp s ops = false ->
    exists s' pre suf,
      ops = pre ++ suf /\
      exec_skip stp s pre = s' /\
      ~ ftl_invariant s'.
Proof.
  intros stp s ops Hs Hrun. unfold run_trace_with in Hrun.
  rewrite Hs, Bool.andb_true_l in Hrun.
  destruct (first_violation stp s ops) as [s'|] eqn:E; [|discriminate].
  destruct (first_violation_reachable stp ops s s' E) as [pre [suf [Happ Hex]]].
  exists s', pre, suf. repeat split; [exact Happ | exact Hex |].
  apply (first_violation_refutes stp ops s s' E).
Qed.

(* Specialised to the model's own [step] and the seeded state. *)
Corollary run_trace_false_from_init :
  forall ops,
    run_trace init_state ops = false ->
    exists s' pre suf,
      ops = pre ++ suf /\
      exec_skip step init_state pre = s' /\
      ~ ftl_invariant s'.
Proof.
  intros ops H.
  apply (run_trace_false_is_a_real_violation step init_state ops
           check_accepts_init_state H).
Qed.

(* ══════════════════════════════════════════════════════════════
   §5  Evidence: it runs, and what it ran

   A tally, so a "pass" can be read as coverage and not as an accident of
   everything being rejected.
   ══════════════════════════════════════════════════════════════ *)

Record Tally := mkTally {
  t_accepted : nat;       (* operations the model performed *)
  t_rejected : nat;       (* operations the model refused *)
  t_writes_ok : nat;      (* writes that actually programmed a page *)
  t_gc_ok : nat           (* GC / wear-level reclaims that succeeded *)
}.

Definition tally_bump (c : Tally) (op : COp) (ok : bool) : Tally :=
  match ok with
  | false => mkTally (t_accepted c) (S (t_rejected c)) (t_writes_ok c) (t_gc_ok c)
  | true =>
      match op with
      | COpWrite _ _ _ =>
          mkTally (S (t_accepted c)) (t_rejected c) (S (t_writes_ok c)) (t_gc_ok c)
      | COpGC | COpWearLevel =>
          mkTally (S (t_accepted c)) (t_rejected c) (t_writes_ok c) (S (t_gc_ok c))
      | _ =>
          mkTally (S (t_accepted c)) (t_rejected c) (t_writes_ok c) (t_gc_ok c)
      end
  end.

Definition tally_add (x y : Tally) : Tally :=
  mkTally (t_accepted x + t_accepted y) (t_rejected x + t_rejected y)
          (t_writes_ok x + t_writes_ok y) (t_gc_ok x + t_gc_ok y).

Fixpoint tally_from (s : FTLState) (ops : list COp) (c : Tally) : Tally :=
  match ops with
  | [] => c
  | op :: tl =>
      match step s op with
      | None => tally_from s tl (tally_bump c op false)
      | Some s' => tally_from s' tl (tally_bump c op true)
      end
  end.

Definition tally_trace (s : FTLState) (ops : list COp) : Tally :=
  tally_from s ops (mkTally 0 0 0 0).

Definition tally_all (s : FTLState) (nseeds len : nat) : Tally :=
  fold_right (fun k acc => tally_add (tally_trace s (gen_trace k len)) acc)
             (mkTally 0 0 0 0) (seq 0 nseeds).

(* ── the headline runs ───────────────────────────────────────────────

   Sizing.  The per-step cost is the 29-conjunct bounded check over the
   whole geometry, applied to a state whose sixteen fields are closure
   chains that lengthen with every accepted operation; a campaign is
   therefore superlinear in the trace length.  Measured here (Apple
   silicon, coqc, [vm_compute], excluding the [Qed] re-check):

       200 traces x  40 ops   7.4 s
       200 traces x  50 ops  12.0 s      <- [all_seeds_pass]
       200 traces x  60 ops  14.6 s
        24 traces x 200 ops   8.7 s      <- [deep_traces_pass]
        40 traces x 400 ops  35.5 s

   200 x 50 is the working point: wide enough that the traces disagree
   about when blocks fill and reclaim fires, long enough that each one
   drains the free list, opens several blocks and garbage-collects, and
   still ~12 s.  The narrower 24 x 200 campaign goes deeper, into states
   where blocks have been erased and re-used many times.  Everything
   past those sizes buys depth at quadratic cost.
   ──────────────────────────────────────────────────────────────────── *)

(* 200 traces of 50 operations from the seeded state: 10 000 operations. *)
Theorem all_seeds_pass :
  forallb (fun s => run_trace init_state (gen_trace s 50)) (seq 0 200) = true.
Proof. vm_compute. reflexivity. Qed.

(* Deeper: 24 traces of 200 operations, 4 800 operations.  Most of these
   end in the write-blocked state that §7 dissects — the invariant holds
   throughout anyway, which is the point: safety survives, progress does
   not. *)
Theorem deep_traces_pass :
  forallb (fun s => run_trace init_state (gen_trace s 200)) (seq 0 24) = true.
Proof. vm_compute. reflexivity. Qed.

(* What those 10 000 operations actually did: 8 283 were performed and
   1 717 refused; 3 760 writes programmed a page and 756 reclaims
   completed.  So the pass is not an artefact of everything being
   rejected — the device fills, relocates and recycles.

   The reclaim figure moved from 748 to 756 when [COpWearLevel] stopped
   being [COpGC].  Both operations reclaim, but they now choose different
   victims once erase counts diverge, and the least-worn block is on average
   the easier one to empty: eight wear-level draws that the cleaning
   heuristic's victim would have refused (a live page with nowhere to go)
   now complete.  The write count is unchanged, as it must be — the two
   choosers agree until the first erase, and a reclaim never programs a
   host page. *)
Theorem campaign_coverage :
  tally_all init_state 200 50 = mkTally 8283 1717 3760 756.
Proof. vm_compute. reflexivity. Qed.

(* The seeding problem, measured.  The same 200 traces run from
   [empty_state] program nothing whatsoever: every one of the 6 233
   refusals is a write turned away for want of a tenant label, no page is
   ever allocated, and consequently no reclaim ever fires either.  A
   campaign from [empty_state] would report a pass having exercised
   nothing but the read and no-op paths. *)
Theorem empty_state_campaign_is_vacuous :
  tally_all empty_state 200 50 = mkTally 3767 6233 0 0.
Proof. vm_compute. reflexivity. Qed.

(* ══════════════════════════════════════════════════════════════
   §6  Planted bugs: the harness is itself tested

   A harness that has never reported [false] is not known to be able to.
   Two deliberately broken transition functions, each a plausible slip,
   are run through the same runner.
   ══════════════════════════════════════════════════════════════ *)

(* ── Bug A: the write installs the mapping but forgets to program ───
   [bug_program_page] is [program_page] with the three flash-side updates
   dropped: [page_state], [page_role] and [page_meta] are left untouched,
   while [l2p_map] and the block ownership fields are updated exactly as
   before.  The logical address now points at a page that was never
   programmed — Inv22 (the map points only at live pages), and with it
   Inv0, Inv3 and Inv9.  This is the shape of a real FTL bug: the
   metadata update and the flash program are separate operations, and an
   error path that returns after the first leaves precisely this state. *)
Definition bug_program_page (s : FTLState) (a : Addr) (p : Page)
                            (d : Data) (pa : PhysAddr) : FTLState :=
  mkFTLState
    (set_l2p_map (l2p_map s) a p (Some pa))
    (page_state s)                                   (* NOT programmed *)
    (page_role s)                                    (* NOT programmed *)
    (addr_tenant s)
    (addr_namespace s)
    (set_block_tenant (block_tenant s) (pa_block pa) (addr_tenant s a))
    (set_block_namespace (block_namespace s) (pa_block pa) (addr_namespace s a))
    (page_meta s)                                    (* NOT stamped *)
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s) (open_block s) (write_ptr s)
    (block_open s).

Definition bug_exec_write (s : FTLState) (a : Addr) (p : Page) (d : Data)
  : option FTLState :=
  let s1 := match l2p_map s a p with
            | Some old => invalidate_at s old
            | None => s
            end in
  match addr_tenant s a, addr_namespace s a with
  | Some t, Some ns =>
      match alloc_page s1 t ns with
      | Some (pa, s2) => Some (bug_program_page s2 a p d pa)
      | None => None
      end
  | _, _ => None
  end.

Definition bug_step_write : StepFn :=
  fun s op =>
    match op with
    | COpWrite a p d =>
        if andb (andb (Nat.ltb a addr_space) (Nat.ltb p pages_per_block))
                (match addr_tenant s a, addr_namespace s a with
                 | Some _, Some _ => true | _, _ => false end)
        then bug_exec_write s a p d
        else None
    | _ => step s op
    end.

(* ── Bug B: erase returns the block to the free list twice ──────────
   [bug_erase_block] is [erase_block] with [b :: b :: free_block_list s]
   in place of [b :: free_block_list s] — a duplicated push, the sort of
   thing a refactor that frees the block in both the caller and the callee
   produces.  It breaks Inv11 (the free list has no duplicates), and the
   block can then be allocated twice. *)
Definition bug_erase_block (s : FTLState) (b : Block) : FTLState :=
  mkFTLState (l2p_map s)
    (fun blk pg => if Nat.eqb blk b then PS_Empty else page_state s blk pg)
    (fun blk pg => if Nat.eqb blk b then None else page_role s blk pg)
    (addr_tenant s) (addr_namespace s)
    (set_block_tenant (block_tenant s) b None)
    (set_block_namespace (block_namespace s) b None)
    (fun blk pg => if Nat.eqb blk b then empty_page_meta else page_meta s blk pg)
    (region_table s)
    (b :: b :: free_block_list s)                    (* freed TWICE *)
    (set_free_block (free_block s) b true)
    (fun blk => if Nat.eqb blk b then S (wear_count s blk) else wear_count s blk)
    (key_table s) (open_block s) (write_ptr s)
    (set_block_open (block_open s) b false).

Definition bug_reclaim (s : FTLState) (b : Block) : option FTLState :=
  match relocate_pages s b all_pages with
  | Some s1 => Some (bug_erase_block s1 b)
  | None => None
  end.

Definition bug_gc (s : FTLState) : option FTLState :=
  match find_victim s with
  | Some b => bug_reclaim s b
  | None => None
  end.

Definition bug_step_erase : StepFn :=
  fun s op =>
    match op with
    | COpGC => bug_gc s
    | COpWearLevel => bug_gc s
    | _ => step s op
    end.

(* ── a hand-built trace that forces both paths ──────────────────────
   Addresses 0 and 1 share the (tenant 0, ns 0) frontier, so four writes
   fill block 0 exactly; the fifth opens block 1, leaving block 0 closed,
   holding three live pages and one stale one — a reclaimable victim.
   The final COpGC therefore relocates and erases. *)
Definition forcing_trace : list COp :=
  [COpWrite 0 0 11; COpWrite 0 1 12; COpWrite 1 0 13; COpWrite 1 1 14;
   COpWrite 0 0 15; COpGC].

(* The trace itself is fine: the real model runs it clean. *)
Theorem forcing_trace_ok_on_real_step :
  run_trace init_state forcing_trace = true.
Proof. vm_compute. reflexivity. Qed.

Theorem forcing_trace_reclaims :
  t_gc_ok (tally_trace init_state forcing_trace) = 1.
Proof. vm_compute. reflexivity. Qed.

(* ── the harness catches both ───────────────────────────────────── *)

(* Bug A is caught on the very first write. *)
Theorem harness_catches_missing_program :
  run_trace_with bug_step_write init_state forcing_trace = false.
Proof. vm_compute. reflexivity. Qed.

(* Bug B needs a reclaim to happen first; the forcing trace supplies one. *)
Theorem harness_catches_double_free :
  run_trace_with bug_step_erase init_state forcing_trace = false.
Proof. vm_compute. reflexivity. Qed.

(* And the random search finds them without being told where to look. *)
Theorem random_search_finds_missing_program :
  forallb (fun s => run_trace_with bug_step_write init_state (gen_trace s 40))
          (seq 0 20) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem random_search_finds_double_free :
  forallb (fun s => run_trace_with bug_step_erase init_state (gen_trace s 120))
          (seq 0 20) = false.
Proof. vm_compute. reflexivity. Qed.

(* ── and the reports are proofs, not warnings ──────────────────────
   Composing the two: each planted bug drives the model into a state
   that provably fails [ftl_invariant]. *)
Corollary missing_program_reaches_a_broken_state :
  exists s' pre suf,
    forcing_trace = pre ++ suf /\
    exec_skip bug_step_write init_state pre = s' /\
    ~ ftl_invariant s'.
Proof.
  apply (run_trace_false_is_a_real_violation bug_step_write init_state
           forcing_trace check_accepts_init_state
           harness_catches_missing_program).
Qed.

Corollary double_free_reaches_a_broken_state :
  exists s' pre suf,
    forcing_trace = pre ++ suf /\
    exec_skip bug_step_erase init_state pre = s' /\
    ~ ftl_invariant s'.
Proof.
  apply (run_trace_false_is_a_real_violation bug_step_erase init_state
           forcing_trace check_accepts_init_state
           harness_catches_double_free).
Qed.

(* ══════════════════════════════════════════════════════════════
   §7  What the search found that nobody planted: the device wedges

   Every trace above passes the invariant, so the model is safe on
   everything the campaign touched.  It is not, however, LIVE.  Long
   traces reach a state in which no write can be performed and garbage
   collection cannot recover — a progress failure, invisible to
   [check_bounded_all] because none of the 29 conjuncts is about progress.
   The checker is right to accept it; that is exactly the division of
   labour, and exactly why a designer wants a runner and not only a
   checker.

   The witness is the final state of trace 0 at length 200.  What it
   looks like:

     - one block on the free list (block 7, the reserve [open_fresh]
       refuses to hand out);
     - all three frontiers full: (0,0) -> block 5, (1,0) -> block 0,
       (1,1) -> block 4, each with write_ptr = pages_per_block;
     - blocks 1 and 3 hold nothing but stale pages — two blocks that
       could be erased with no relocation at all;
     - [find_victim] nevertheless returns block 6, which holds two live
       pages, because it scans downward from [total_blocks] and takes the
       first block that is neither free nor open, with no regard to how
       much live data it carries.

   [reclaim] then has to relocate those two live pages; their owner's
   frontier is full, [open_fresh] needs two free blocks and sees one, so
   the relocation fails, [reclaim] returns None — and [gc] gives up
   rather than trying the next victim.  Two erasable blocks sit
   untouched.

   The wear-aware chooser does not rescue it, and that is the point of
   measuring both.  [find_least_worn_victim] returns block 2, whose erase
   count of 3 is the lowest among the reclaimable blocks; block 2 still
   holds one live page, so the same missing destination stops the same
   relocation and [wear_level] returns None as well.  Neither policy is
   at fault, because neither policy is what is wrong:

   Two independent causes, both in [Operational.v]:

     (1) [reclaim_with] tries exactly one victim, whatever the policy.  A
         failed [reclaim] should fall through to another candidate, not
         abort the collection.  Both [gc] and [wear_level] inherit this.
     (2) [open_fresh] keeps ONE block in reserve device-wide, but there
         is one allocation frontier per (tenant, namespace) pair.  One
         reserve cannot guarantee a destination to N frontiers.

   Neither is a soundness bug, and neither shows up in a preservation
   proof: preservation says the invariant survives a step, not that a
   step exists.  The onset is measured below.
   ══════════════════════════════════════════════════════════════ *)

Definition write_blocked (s : FTLState) : bool :=
  forallb (fun a =>
    forallb (fun p =>
      match step s (COpWrite a p 1) with None => true | Some _ => false end)
      (seq 0 pages_per_block))
    (seq 0 addr_space).

Definition all_invalid (s : FTLState) (b : Block) : bool :=
  forallb (fun p => match page_state s b p with PS_Invalid => true | _ => false end)
          (seq 0 pages_per_block).

Definition wedged_witness : FTLState := exec_skip step init_state (gen_trace 0 200).

Theorem wedged_witness_blocks_every_write : write_blocked wedged_witness = true.
Proof. vm_compute. reflexivity. Qed.

Theorem wedged_witness_gc_cannot_recover : gc wedged_witness = None.
Proof. vm_compute. reflexivity. Qed.

(* Nor can wear levelling, which now picks a different victim.  The progress
   failure is a property of the one-victim reclaim and the single reserve
   block, not of the cleaning heuristic. *)
Theorem wedged_witness_wear_level_cannot_recover :
  wear_level wedged_witness = None.
Proof. vm_compute. reflexivity. Qed.

(* ...and the checker is perfectly happy with it, as it should be. *)
Theorem wedged_witness_passes_the_checker :
  check_bounded_all wedged_witness = true.
Proof. vm_compute. reflexivity. Qed.

Theorem wedged_witness_free_list : free_block_list wedged_witness = [7].
Proof. vm_compute. reflexivity. Qed.

(* The victim actually chosen holds live data... *)
Theorem wedged_witness_victim : find_victim wedged_witness = Some 6.
Proof. vm_compute. reflexivity. Qed.

(* ...and so does the least worn block, which is the one wear levelling
   picks: erase count 3, the lowest among the reclaimable blocks, and one
   live page. *)
Theorem wedged_witness_wear_level_victim :
  find_least_worn_victim wedged_witness = Some 2.
Proof. vm_compute. reflexivity. Qed.

Theorem wedged_witness_wear_counts :
  map (wear_count wedged_witness) (seq 0 total_blocks) = [5; 6; 3; 5; 5; 4; 4; 0].
Proof. vm_compute. reflexivity. Qed.

(* ...while two blocks are pure garbage and need no relocation at all. *)
Theorem wedged_witness_has_erasable_garbage :
  filter (all_invalid wedged_witness) (seq 0 total_blocks) = [1; 3].
Proof. vm_compute. reflexivity. Qed.

(* Onset: of 60 traces, how many end write-blocked, as length grows.
   Nothing at 60 operations, a handful at 100, five eighths at 200.  These
   figures fell across the board (from [0; 13; 39; 44]) when wear levelling
   stopped being a second copy of garbage collection: two policies reclaim
   two different blocks, so a trace that alternates between them recycles
   more of the device before exhausting it. *)
Definition wedged_count (nseeds len : nat) : nat :=
  length (filter (fun k => write_blocked (exec_skip step init_state (gen_trace k len)))
                 (seq 0 nseeds)).

Theorem wedging_onset :
  map (fun n => wedged_count 60 n) [60; 100; 150; 200] = [0; 2; 24; 37].
Proof. vm_compute. reflexivity. Qed.
