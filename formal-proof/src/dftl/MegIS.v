(* MegIS.v: the MegIS case study (DFTL + in-storage processing), under
   page-granular translation.  The third point of the extension-effort taxonomy.

   [framework/Composition.v] lays out four points on the scale of what an
   FTL extension can cost its designer:

     (1) new state, no new obligations         -- the orthogonal extension;
     (2) new state, new operations that touch the base state;
     (3) new clauses added to the invariant;
     (4) a change to the base model itself.

   ISP is the third.  It layers in-storage processing on DFTL: DRAM-resident
   bookkeeping (coarse sequential runs, accelerator job status, tenant-owned
   ISP zones) plus four operations over that bookkeeping, none of which
   issues a NAND primitive and none of which the framework's data plane can
   see.  The four host-visible FTL operations are inherited from
   [DFTLConcreteFTL] unchanged in their effect on flash.

   The result of putting that through the framework is not one number but
   two, and they point in opposite directions:

   * The five [CUSTOM_FTL] hypotheses cost nothing.  [user_to_model] is
     [ds_model] after [isp_base], the ISP fields are invisible to it, and
     each hypothesis is [intros] then [exact] of DFTL's own.  Section 8
     records the exact count.  Section 9 goes further and shows that ISP is
     a bona fide [STATE_EXTENSION]: [LayeredCUSTOM_FTL] manufactures the
     same five with no designer proof at all, and throws in the harmlessness
     of the four ISP operations.

   * The feature's own invariant costs real work, and one of its
     preservation goals is *false as stated*.  A coarse run claims that a
     logical range maps contiguously onto a physical one.  Garbage
     collection and wear levelling relocate pages on the data plane.  When a
     relocated page falls inside a claimed range the claim becomes false
     while the data plane stays perfectly correct -- the framework notices
     nothing, because there is nothing at the framework's level to notice.

     Section 7 proves that.  It exhibits a concrete device state satisfying
     all 29 conjuncts of [ftl_invariant], DFTL's own [dftl_ok], and every
     ISP invariant, on which the *unwrapped* garbage collector falsifies the
     coarse-run invariant.  The negation is machine-checked, not asserted.

     The repair is Section 5's [coarse_resync]: after maintenance, drop
     every coarse run whose range contains a page that moved -- which
     [coarse_resync_drop_means_moved] proves is exactly the set it drops --
     so a later ISP query gets a clean miss instead of a false answer.  With
     the wrapper, preservation holds unconditionally (Section 6).

   Page granularity is what makes the break visible in this shape.  Under
   [Addr -> Page -> option PhysAddr] a run is what an ISP scan kernel
   actually wants -- consecutive logical pages on consecutive physical pages
   of one block -- and *any* out-of-place page movement breaks it.  That
   includes a host write to a page inside the run, which is why Section 6
   wraps [user_write] as well and Section 7 refutes the unwrapped write too.

   No admitted lemmas, no [admit], no axiom declarations, and no parameters, variables or
   hypotheses beyond a module type's own. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.
Require Import core.CustomFTLInterface.
Require Import Invariants.Invariants.
Require Import Invariants.Preservation.
Require Import Refinement.
Require Import dftl.DFTL.
Require Import framework.Composition.

Import ListNotations.

(* ══════════════════════════════════════════════════════════════════════
   PART 1 -- the ISP state
   ══════════════════════════════════════════════════════════════════════ *)

(* A coarse run is the one thing an ISP scan kernel needs and a demand-paged
   map cannot give it cheaply: a promise that a stretch of consecutive
   logical pages of one address sits on consecutive physical pages of one
   block.  With such a run the kernel issues one sequential NAND read for
   [cr_len] pages instead of [cr_len] translations through the CMT.  That is
   the whole point of the structure, and it is also exactly why it is
   fragile: it is a claim about physical layout, and the FTL moves pages. *)
Record CoarseRun := mkCoarseRun {
  cr_page : Page;      (* first logical page offset covered by the run *)
  cr_pa   : PhysAddr;  (* physical page the run starts on *)
  cr_len  : nat        (* how many consecutive pages the run claims *)
}.

Definition CoarseMap := Addr -> option CoarseRun.

(* Per-job accelerator status.  [job_pending = true] means the job has been
   submitted and not yet observed to finish; [job_in] and [job_out] name the
   logical addresses of its input and output buffers. *)
Record JobStatus := mkJobStatus {
  job_pending : bool;
  job_in      : Addr;
  job_out     : Addr
}.

Definition JobMap := nat -> option JobStatus.

(* A host-declared ISP zone: a tenant-owned span of logical addresses on
   which the accelerator is permitted to operate.  Pure metadata; it never
   reaches flash.  [zone_tenant] is the owner an access-control unit would
   check; the invariants below constrain the span (bounds, and containment
   of runs and jobs) and carry the owner without constraining it. *)
Record ZoneMeta := mkZoneMeta {
  zone_start  : Addr;
  zone_len    : nat;
  zone_tenant : TenantId
}.

Definition ZoneMap := nat -> option ZoneMeta.

(* The widened state.  [isp_base] is the whole of DFTL; the three new fields
   live in controller DRAM and are read by nothing on the data plane. *)
Record ISPState := mkISPState {
  isp_base  : DFTLState;
  isp_runs  : CoarseMap;
  isp_jobs  : JobMap;
  isp_zones : ZoneMap
}.

Definition set_runs (s : ISPState) (c : CoarseMap) : ISPState :=
  mkISPState (isp_base s) c (isp_jobs s) (isp_zones s).

Definition set_jobs (s : ISPState) (j : JobMap) : ISPState :=
  mkISPState (isp_base s) (isp_runs s) j (isp_zones s).

Definition set_zones (s : ISPState) (z : ZoneMap) : ISPState :=
  mkISPState (isp_base s) (isp_runs s) (isp_jobs s) z.

Definition empty_isp : ISPState :=
  mkISPState (mkDFTLState empty_state [] (fun _ _ => None))
             (fun _ => None) (fun _ => None) (fun _ => None).

(* ══════════════════════════════════════════════════════════════════════
   PART 2 -- the four ISP operations, and the query they exist to serve
   ══════════════════════════════════════════════════════════════════════

   None of the four touches [isp_base].  That is what makes them "the
   feature's own operations" rather than a change to the FTL. *)

(* (i) Register a coarse run for logical address [a]. *)
Definition isp_register_run (s : ISPState) (a : Addr) (r : CoarseRun)
  : ISPState :=
  set_runs s (fun x => if Nat.eqb x a then Some r else isp_runs s x).

(* (ii) Submit an accelerator job, pending, over an input/output pair. *)
Definition isp_submit_job (s : ISPState) (j : nat) (ia oa : Addr) : ISPState :=
  set_jobs s (fun x => if Nat.eqb x j
                       then Some (mkJobStatus true ia oa)
                       else isp_jobs s x).

(* (iii) Query a job's status.  A read of the bookkeeping: no state moves,
   which is visible in the type. *)
Definition isp_job_status (s : ISPState) (j : nat) : option JobStatus :=
  isp_jobs s j.

(* (iv) Declare a tenant-owned ISP zone. *)
Definition isp_declare_zone (s : ISPState) (zid : nat) (start : Addr)
                            (len : nat) (t : TenantId) : ISPState :=
  set_zones s (fun x => if Nat.eqb x zid
                        then Some (mkZoneMeta start len t)
                        else isp_zones s x).

(* The scan kernel's fast path: resolve a logical page through a coarse run,
   without consulting the CMT or the translation pages at all.  This is the
   query that must never lie -- an accelerator handed a wrong physical page
   reads another tenant's data, or data that has since been erased. *)
Definition isp_scan_resolve (s : ISPState) (a : Addr) (p : Page)
  : option PhysAddr :=
  match isp_runs s a with
  | Some r =>
      if andb (Nat.leb (cr_page r) p) (Nat.ltb p (cr_page r + cr_len r))
      then Some (mkPhysAddr (pa_block (cr_pa r))
                            (pa_page (cr_pa r) + (p - cr_page r)))
      else None
  | None => None
  end.

(* ══════════════════════════════════════════════════════════════════════
   PART 3 -- the ISP invariants
   ══════════════════════════════════════════════════════════════════════ *)

(* The load-bearing one: a registered coarse run's claim is true of the
   device's own forward map.  Note what it is stated over -- [l2p_map] of
   [ds_model (isp_base s)], the real flash state, not an ISP-side copy. *)
Definition ISPRunsSound (s : ISPState) : Prop :=
  forall a r k,
    isp_runs s a = Some r ->
    k < cr_len r ->
    l2p_map (ds_model (isp_base s)) a (cr_page r + k)
      = Some (mkPhysAddr (pa_block (cr_pa r)) (pa_page (cr_pa r) + k)).

Definition addr_in_zone (a : Addr) (z : ZoneMeta) : Prop :=
  zone_start z <= a < zone_start z + zone_len z.

(* Every pending job operates on buffers inside declared zones. *)
Definition ISPJobsInZone (s : ISPState) : Prop :=
  forall j st,
    isp_jobs s j = Some st ->
    job_pending st = true ->
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone (job_in st) z) /\
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone (job_out st) z).

(* Every declared zone lies inside the address space. *)
Definition ISPZoneBounds (s : ISPState) : Prop :=
  forall zid z,
    isp_zones s zid = Some z ->
    zone_start z + zone_len z <= addr_space.

(* Every coarse run belongs to a declared zone: the accelerator may not
   scan outside a tenant's own region. *)
Definition ISPRunInZone (s : ISPState) : Prop :=
  forall a r,
    isp_runs s a = Some r ->
    exists zid z, isp_zones s zid = Some z /\ addr_in_zone a z.

Definition isp_ok (s : ISPState) : Prop :=
  dftl_ok (isp_base s) /\
  ISPRunsSound s /\
  ISPJobsInZone s /\
  ISPZoneBounds s /\
  ISPRunInZone s.

Lemma empty_isp_ok : isp_ok empty_isp.
Proof.
  unfold isp_ok, empty_isp. cbn [isp_base isp_runs isp_jobs isp_zones].
  split.
  { unfold dftl_ok, CMTBounded, CMTSound, CMTCleanSynced, TransComplete.
    cbn [ds_cmt ds_tpages ds_model].
    split; [apply Nat.le_0_l|].
    split; [intros e He; cbn in He; contradiction|].
    split; [intros e He; cbn in He; contradiction|].
    intros a p _. reflexivity. }
  split; [intros a r k H; cbn [isp_runs] in H; discriminate H|].
  split; [intros j st H; cbn [isp_jobs] in H; discriminate H|].
  split; [intros zid z H; cbn [isp_zones] in H; discriminate H|].
  intros a r H; cbn [isp_runs] in H; discriminate H.
Qed.

(* The query the whole feature exists for is sound exactly when the
   coarse-run invariant holds.  This is the theorem that makes
   [ISPRunsSound] worth maintaining rather than a decoration. *)
Theorem isp_scan_resolve_sound :
  forall s a p pa,
    ISPRunsSound s ->
    isp_scan_resolve s a p = Some pa ->
    l2p_map (ds_model (isp_base s)) a p = Some pa.
Proof.
  intros s a p pa Hrs Hres. unfold isp_scan_resolve in Hres.
  destruct (isp_runs s a) as [r|] eqn:Hr; [|discriminate].
  destruct (andb (Nat.leb (cr_page r) p) (Nat.ltb p (cr_page r + cr_len r)))
    eqn:Hg; [|discriminate].
  apply andb_prop in Hg as [Hlo Hhi].
  apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
  injection Hres as Hpa. subst pa.
  pose proof (Hrs a r (p - cr_page r) Hr ltac:(lia)) as Hmap.
  replace (cr_page r + (p - cr_page r)) with p in Hmap by lia.
  exact Hmap.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 4 -- the four ISP operations preserve the ISP invariants
   ══════════════════════════════════════════════════════════════════════ *)

(* Registering a run has two side conditions and they are the honest ones:
   the run must actually be true of the map at registration time, and it
   must lie inside a declared zone.  Neither can be dispensed with -- the
   first is the invariant itself at the new key, the second is the tenancy
   check. *)
Theorem isp_ok_register_run :
  forall s a r,
    isp_ok s ->
    (forall k, k < cr_len r ->
       l2p_map (ds_model (isp_base s)) a (cr_page r + k)
         = Some (mkPhysAddr (pa_block (cr_pa r)) (pa_page (cr_pa r) + k))) ->
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone a z) ->
    isp_ok (isp_register_run s a r).
Proof.
  intros s a r (Hd & Hrs & Hj & Hz & Hrz) Hwit Hzone.
  unfold isp_register_run, set_runs, isp_ok.
  cbn [isp_base isp_runs isp_jobs isp_zones].
  split; [exact Hd|].
  split.
  { intros a0 r0 k H Hk. cbn [isp_runs] in H. destruct (Nat.eqb a0 a) eqn:E.
    - apply Nat.eqb_eq in E. subst a0. injection H as H. subst r0.
      exact (Hwit k Hk).
    - exact (Hrs a0 r0 k H Hk). }
  split; [exact Hj|].
  split; [exact Hz|].
  intros a0 r0 H. cbn [isp_runs] in H. destruct (Nat.eqb a0 a) eqn:E.
  - apply Nat.eqb_eq in E. subst a0. exact Hzone.
  - exact (Hrz a0 r0 H).
Qed.

Theorem isp_ok_submit_job :
  forall s j ia oa,
    isp_ok s ->
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone ia z) ->
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone oa z) ->
    isp_ok (isp_submit_job s j ia oa).
Proof.
  intros s j ia oa (Hd & Hrs & Hjb & Hz & Hrz) Hin Hout.
  unfold isp_submit_job, set_jobs, isp_ok.
  cbn [isp_base isp_runs isp_jobs isp_zones].
  split; [exact Hd|].
  split; [exact Hrs|].
  split.
  { intros j0 st H Hp. cbn [isp_jobs] in H. destruct (Nat.eqb j0 j) eqn:E.
    - injection H as H. subst st. cbn [job_in job_out].
      split; [exact Hin|exact Hout].
    - exact (Hjb j0 st H Hp). }
  split; [exact Hz|].
  exact Hrz.
Qed.

(* Declaring a zone needs a fresh slot.  Overwriting a live zone would
   orphan the run or job whose only witness was the previous occupant; that
   is a host-level error, and requiring freshness is how the model says so.
   The bound is what [ISPZoneBounds] asks of the new entry. *)
Theorem isp_ok_declare_zone :
  forall s zid start len t,
    isp_ok s ->
    isp_zones s zid = None ->
    start + len <= addr_space ->
    isp_ok (isp_declare_zone s zid start len t).
Proof.
  intros s zid start len t (Hd & Hrs & Hjb & Hz & Hrz) Hfresh Hbnd.
  assert (Hkeep : forall zid' z',
            isp_zones s zid' = Some z' ->
            isp_zones (isp_declare_zone s zid start len t) zid' = Some z').
  { intros zid' z' H. unfold isp_declare_zone, set_zones.
    cbn [isp_zones]. destruct (Nat.eqb zid' zid) eqn:E; [|exact H].
    apply Nat.eqb_eq in E. subst zid'. rewrite Hfresh in H. discriminate H. }
  unfold isp_ok.
  split; [exact Hd|].
  split; [exact Hrs|].
  split.
  { intros j st H Hp.
    destruct (Hjb j st H Hp) as [[z1 [m1 [Hm1 Hi1]]] [z2 [m2 [Hm2 Hi2]]]].
    split.
    - exists z1, m1. split; [exact (Hkeep _ _ Hm1)|exact Hi1].
    - exists z2, m2. split; [exact (Hkeep _ _ Hm2)|exact Hi2]. }
  split.
  { intros zid' z H. unfold isp_declare_zone, set_zones in H.
    cbn [isp_zones] in H. destruct (Nat.eqb zid' zid) eqn:E.
    - injection H as H. subst z. cbn [zone_start zone_len]. exact Hbnd.
    - exact (Hz zid' z H). }
  intros a r H.
  destruct (Hrz a r H) as [z0 [m0 [Hm0 Hin]]].
  exists z0, m0. split; [exact (Hkeep _ _ Hm0)|exact Hin].
Qed.

(* The query moves nothing, and what it returns is constrained by the
   invariant: a pending job it reports back is a job inside declared
   zones. *)
Theorem isp_job_status_spec :
  forall s j st,
    isp_ok s ->
    isp_job_status s j = Some st ->
    job_pending st = true ->
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone (job_in st) z) /\
    (exists zid z, isp_zones s zid = Some z /\ addr_in_zone (job_out st) z).
Proof.
  intros s j st (_ & _ & Hjb & _ & _) H Hp. exact (Hjb j st H Hp).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 5 -- the repair pass
   ══════════════════════════════════════════════════════════════════════

   [coarse_resync m c] keeps a run only if [m] still witnesses it, and drops
   it otherwise.  Two lemmas give the pass its meaning:

     [coarse_resync_holds]              -- what survives is true;
     [coarse_resync_drop_means_moved]   -- what is dropped had a page move
                                           inside its claimed range.

   Together they say the pass is exactly "drop every run containing a page
   that moved", neither more nor less.  DFTL's own reclaim path already does
   the same thing one level down, filtering the CMT with [entry_agrees]; the
   ISP layer needs its own because its unit is a run, not an entry. *)

Lemma phys_eqb_refl : forall x, phys_eqb x x = true.
Proof. intros [b q]. unfold phys_eqb. cbn. apply lpa_eqb_refl. Qed.

Definition run_step_ok (m : FTLState) (a : Addr) (r : CoarseRun) (k : nat)
  : bool :=
  match l2p_map m a (cr_page r + k) with
  | Some x => phys_eqb x (mkPhysAddr (pa_block (cr_pa r)) (pa_page (cr_pa r) + k))
  | None => false
  end.

Fixpoint run_ok_upto (m : FTLState) (a : Addr) (r : CoarseRun) (n : nat)
  : bool :=
  match n with
  | 0 => true
  | S k => andb (run_ok_upto m a r k) (run_step_ok m a r k)
  end.

Definition run_holds (m : FTLState) (a : Addr) (r : CoarseRun) : bool :=
  run_ok_upto m a r (cr_len r).

Lemma run_ok_upto_true :
  forall m a r n,
    run_ok_upto m a r n = true ->
    forall k, k < n ->
      l2p_map m a (cr_page r + k)
        = Some (mkPhysAddr (pa_block (cr_pa r)) (pa_page (cr_pa r) + k)).
Proof.
  intros m a r. induction n as [|n IH]; intros H k Hk; [lia|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct (Nat.eq_dec k n) as [Heq|Hne].
  - subst k. unfold run_step_ok in H2.
    destruct (l2p_map m a (cr_page r + n)) as [x|] eqn:Hx; [|discriminate].
    apply phys_eqb_eq in H2. now subst x.
  - apply (IH H1 k). lia.
Qed.

Lemma run_ok_upto_false :
  forall m a r n,
    run_ok_upto m a r n = false ->
    exists k, k < n /\ run_step_ok m a r k = false.
Proof.
  intros m a r. induction n as [|n IH]; intros H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - destruct (IH H) as [k [Hk Hf]]. exists k. split; [lia|exact Hf].
  - exists n. split; [lia|exact H].
Qed.

Definition coarse_resync (m : FTLState) (c : CoarseMap) : CoarseMap :=
  fun a =>
    match c a with
    | Some r => if run_holds m a r then Some r else None
    | None => None
    end.

Lemma coarse_resync_some :
  forall m c a r, coarse_resync m c a = Some r -> c a = Some r.
Proof.
  intros m c a r H. unfold coarse_resync in H.
  destruct (c a) as [r0|] eqn:Hc; [|discriminate].
  destruct (run_holds m a r0); [|discriminate].
  injection H as H. now subst r0.
Qed.

Lemma coarse_resync_holds :
  forall m c a r k,
    coarse_resync m c a = Some r ->
    k < cr_len r ->
    l2p_map m a (cr_page r + k)
      = Some (mkPhysAddr (pa_block (cr_pa r)) (pa_page (cr_pa r) + k)).
Proof.
  intros m c a r k Hres Hk. unfold coarse_resync in Hres.
  destruct (c a) as [r0|] eqn:Hc; [|discriminate].
  destruct (run_holds m a r0) eqn:Hh; [|discriminate].
  injection Hres as Hres. subst r0.
  exact (run_ok_upto_true m a r (cr_len r) Hh k Hk).
Qed.

(* The pass is not over-eager: a run it drops had a page move inside the
   range it claimed.  This is the statement that licenses reading
   [coarse_resync] as "drop every run whose range contains a page that
   moved" rather than as an unexplained filter. *)
Lemma coarse_resync_drop_means_moved :
  forall m0 m c a r,
    c a = Some r ->
    (forall k, k < cr_len r ->
       l2p_map m0 a (cr_page r + k)
         = Some (mkPhysAddr (pa_block (cr_pa r)) (pa_page (cr_pa r) + k))) ->
    coarse_resync m c a = None ->
    exists k, k < cr_len r /\
              l2p_map m a (cr_page r + k) <> l2p_map m0 a (cr_page r + k).
Proof.
  intros m0 m c a r Hc Hpre Hres.
  unfold coarse_resync in Hres. rewrite Hc in Hres.
  destruct (run_holds m a r) eqn:Hh; [discriminate|].
  unfold run_holds in Hh.
  destruct (run_ok_upto_false m a r (cr_len r) Hh) as [k [Hk Hf]].
  exists k. split; [exact Hk|].
  rewrite (Hpre k Hk). unfold run_step_ok in Hf.
  destruct (l2p_map m a (cr_page r + k)) as [x|] eqn:Hx.
  - intros Heq. injection Heq as Heq. subst x.
    rewrite phys_eqb_refl in Hf. discriminate.
  - discriminate.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 6 -- the wrapped operations, and their preservation proofs
   ══════════════════════════════════════════════════════════════════════

   Each wrapper runs DFTL's operation on [isp_base] and then re-syncs the
   coarse runs against the *post-operation* map.  The data plane is
   untouched by the second half, which is what keeps the framework-level
   obligations free; the second half is the whole ISP-level cost.

   [user_write] is wrapped for the same reason [user_gc] is: an out-of-place
   write moves the page it writes, and if that page is inside a claimed run
   the claim is false afterwards. *)

Definition isp_read (s : ISPState) (a : Addr) (p : Page) : option Data :=
  dftl_read (isp_base s) a p.

Definition isp_write (s : ISPState) (a : Addr) (p : Page) (d : Data)
  : ISPState :=
  let b' := dftl_write (isp_base s) a p d in
  mkISPState b' (coarse_resync (ds_model b') (isp_runs s))
             (isp_jobs s) (isp_zones s).

Definition isp_gc (s : ISPState) : ISPState :=
  let b' := dftl_gc (isp_base s) in
  mkISPState b' (coarse_resync (ds_model b') (isp_runs s))
             (isp_jobs s) (isp_zones s).

Definition isp_wear_level (s : ISPState) : ISPState :=
  let b' := dftl_wear_level (isp_base s) in
  mkISPState b' (coarse_resync (ds_model b') (isp_runs s))
             (isp_jobs s) (isp_zones s).

(* The unwrapped versions: DFTL's operation, ISP fields carried across
   verbatim.  This is what a designer writes if they believe the extension
   is orthogonal.  Part 7 proves they are wrong. *)

Definition isp_write_unwrapped (s : ISPState) (a : Addr) (p : Page) (d : Data)
  : ISPState :=
  mkISPState (dftl_write (isp_base s) a p d)
             (isp_runs s) (isp_jobs s) (isp_zones s).

Definition isp_gc_unwrapped (s : ISPState) : ISPState :=
  mkISPState (dftl_gc (isp_base s))
             (isp_runs s) (isp_jobs s) (isp_zones s).

Definition isp_wear_level_unwrapped (s : ISPState) : ISPState :=
  mkISPState (dftl_wear_level (isp_base s))
             (isp_runs s) (isp_jobs s) (isp_zones s).

(* One lemma serves all three wrappers: the ISP invariants survive any
   change of the DFTL state that is followed by a re-sync. *)
Lemma isp_ok_after_resync :
  forall s b',
    isp_ok s ->
    dftl_ok b' ->
    isp_ok (mkISPState b' (coarse_resync (ds_model b') (isp_runs s))
                       (isp_jobs s) (isp_zones s)).
Proof.
  intros s b' (_ & _ & Hjb & Hz & Hrz) Hd.
  unfold isp_ok. cbn [isp_base isp_runs isp_jobs isp_zones].
  split; [exact Hd|].
  split.
  { intros a r k H Hk. cbn [isp_runs] in H.
    exact (coarse_resync_holds _ _ _ _ _ H Hk). }
  split; [exact Hjb|].
  split; [exact Hz|].
  intros a r H. cbn [isp_runs] in H.
  exact (Hrz a r (coarse_resync_some _ _ _ _ H)).
Qed.

Theorem isp_ok_write :
  forall s a p d, isp_ok s -> isp_ok (isp_write s a p d).
Proof.
  intros s a p d Hok. unfold isp_write.
  apply isp_ok_after_resync; [exact Hok|].
  apply dftl_ok_write. exact (proj1 Hok).
Qed.

(* The crucial one, and the reason this file is not a copy of
   [Composition]'s read-disturb tracker: it is *false* without the
   [coarse_resync] in [isp_gc].  See [unwrapped_gc_breaks_coarse_runs]. *)
Theorem isp_ok_gc : forall s, isp_ok s -> isp_ok (isp_gc s).
Proof.
  intros s Hok. unfold isp_gc.
  apply isp_ok_after_resync; [exact Hok|].
  apply dftl_ok_gc. exact (proj1 Hok).
Qed.

Theorem isp_ok_wear_level : forall s, isp_ok s -> isp_ok (isp_wear_level s).
Proof.
  intros s Hok. unfold isp_wear_level.
  apply isp_ok_after_resync; [exact Hok|].
  apply dftl_ok_wear_level. exact (proj1 Hok).
Qed.

(* The payoff, stated at the query rather than at the invariant: after
   maintenance, whatever the ISP fast path answers is what the device's own
   forward map says.  A run that maintenance broke answers [None] -- a miss
   the kernel handles -- and never a stale physical address. *)
Theorem scan_after_gc_never_lies :
  forall s a p pa,
    isp_ok s ->
    isp_scan_resolve (isp_gc s) a p = Some pa ->
    l2p_map (ds_model (isp_base (isp_gc s))) a p = Some pa.
Proof.
  intros s a p pa Hok Hres.
  apply (isp_scan_resolve_sound (isp_gc s) a p pa); [|exact Hres].
  destruct (isp_ok_gc s Hok) as (_ & Hrs & _). exact Hrs.
Qed.

Theorem scan_after_wear_level_never_lies :
  forall s a p pa,
    isp_ok s ->
    isp_scan_resolve (isp_wear_level s) a p = Some pa ->
    l2p_map (ds_model (isp_base (isp_wear_level s))) a p = Some pa.
Proof.
  intros s a p pa Hok Hres.
  apply (isp_scan_resolve_sound (isp_wear_level s) a p pa); [|exact Hres].
  destruct (isp_ok_wear_level s Hok) as (_ & Hrs & _). exact Hrs.
Qed.

Theorem scan_after_write_never_lies :
  forall s a p d a0 p0 pa,
    isp_ok s ->
    isp_scan_resolve (isp_write s a p d) a0 p0 = Some pa ->
    l2p_map (ds_model (isp_base (isp_write s a p d))) a0 p0 = Some pa.
Proof.
  intros s a p d a0 p0 pa Hok Hres.
  apply (isp_scan_resolve_sound (isp_write s a p d) a0 p0 pa); [|exact Hres].
  destruct (isp_ok_write s a p d Hok) as (_ & Hrs & _). exact Hrs.
Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 7 -- the counterexample: the unwrapped maintenance case is false
   ══════════════════════════════════════════════════════════════════════

   A concrete eight-block device.  Logical address 0 has its pages 0 and 1
   on physical pages (3,0) and (3,1): a genuine two-page coarse run.  Block
   3 is neither free nor open, so it is the reclaim victim [find_victim]
   picks; blocks 4, 6 and 7 are free and block 5 is tenant 0's open block
   with three pages already programmed.

   Garbage collection therefore relocates the run's two pages.  The first
   fits in the tail of the open block and lands on (5,3); the frontier is
   then exhausted, so the second opens a fresh block and lands on (4,0).
   The run is not merely displaced, it is *split across two blocks*: no
   re-pointing of the run's start repairs it, which is why the only sound
   repair is to drop it.

   The state satisfies all 29 conjuncts of [ftl_invariant] (proved below,
   clause by clause, not assumed), DFTL's [dftl_ok], and every ISP
   invariant.  So the refutation cannot be dismissed as a state the FTL
   could never be in. *)

Definition cx_l2p : Addr -> Page -> option PhysAddr :=
  fun a p =>
    if andb (Nat.eqb a 0) (Nat.eqb p 0) then Some (mkPhysAddr 3 0)
    else if andb (Nat.eqb a 0) (Nat.eqb p 1) then Some (mkPhysAddr 3 1)
    else None.

Definition cx_ps : Block -> Page -> PageState :=
  fun b p =>
    if andb (Nat.eqb b 3) (Nat.ltb p 2) then PS_Valid (10 + p)
    else if andb (Nat.ltb b 3) (Nat.eqb p 0) then PS_Invalid
    else if andb (Nat.eqb b 5) (Nat.ltb p 3) then PS_Invalid
    else PS_Empty.

Definition cx_role : Block -> Page -> option Role :=
  fun b p => if andb (Nat.eqb b 3) (Nat.ltb p 2) then Some RData else None.

Definition cx_meta : Block -> Page -> PageMeta :=
  fun b p =>
    if andb (Nat.eqb b 3) (Nat.eqb p 0)
    then mkPageMeta 0 0 (Some 1) (Some (0, 0))
    else if andb (Nat.eqb b 3) (Nat.eqb p 1)
    then mkPageMeta 0 0 (Some 1) (Some (0, 1))
    else empty_page_meta.

Definition cx_model : FTLState :=
  mkFTLState
    cx_l2p cx_ps cx_role
    (fun a => if Nat.ltb a 4 then Some 0 else None)
    (fun a => if Nat.ltb a 4 then Some 0 else None)
    (fun b => if orb (Nat.eqb b 3) (Nat.eqb b 5) then Some 0 else None)
    (fun b => if orb (Nat.eqb b 3) (Nat.eqb b 5) then Some 0 else None)
    cx_meta
    (fun _ => None)
    [4; 6; 7]
    (fun b => orb (Nat.eqb b 4) (orb (Nat.eqb b 6) (Nat.eqb b 7)))
    (fun _ => 0)
    (fun _ => None)
    (fun t ns => if andb (Nat.eqb t 0) (Nat.eqb ns 0) then Some 5 else None)
    (fun t ns => if andb (Nat.eqb t 0) (Nat.eqb ns 0) then 3 else 0)
    (fun b => Nat.eqb b 5).

(* ── the counterexample state satisfies all 29 framework clauses ────── *)

Lemma cx_write_ptr_00 : write_ptr cx_model 0 0 = 3.
Proof. reflexivity. Qed.

Lemma cx_valid_pages :
  forall b p d, page_state cx_model b p = PS_Valid d -> b = 3 /\ (p = 0 \/ p = 1).
Proof.
  intros b p d H. cbn [page_state cx_model] in H. unfold cx_ps in H.
  destruct (andb (Nat.eqb b 3) (Nat.ltb p 2)) eqn:E.
  - apply andb_prop in E as [E1 E2].
    apply Nat.eqb_eq in E1. apply Nat.ltb_lt in E2. split; [exact E1|lia].
  - destruct (andb (Nat.ltb b 3) (Nat.eqb p 0)); [discriminate|].
    destruct (andb (Nat.eqb b 5) (Nat.ltb p 3)); discriminate.
Qed.

Lemma cx_map_inv :
  forall a p pa, l2p_map cx_model a p = Some pa ->
    (a = 0 /\ p = 0 /\ pa = mkPhysAddr 3 0) \/
    (a = 0 /\ p = 1 /\ pa = mkPhysAddr 3 1).
Proof.
  intros a p pa H. cbn [l2p_map cx_model] in H. unfold cx_l2p in H.
  destruct (andb (Nat.eqb a 0) (Nat.eqb p 0)) eqn:E0.
  - apply andb_prop in E0 as [E1 E2].
    apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2.
    injection H as H. left. split; [exact E1|split; [exact E2|now subst pa]].
  - destruct (andb (Nat.eqb a 0) (Nat.eqb p 1)) eqn:E1; [|discriminate].
    apply andb_prop in E1 as [Ea Ep].
    apply Nat.eqb_eq in Ea. apply Nat.eqb_eq in Ep.
    injection H as H. right. split; [exact Ea|split; [exact Ep|now subst pa]].
Qed.

Theorem cx_model_invariant : ftl_invariant cx_model.
Proof.
  apply make_ftl_invariant.
  - (* WF0 *) exact pages_per_block_pos.
  - (* WF1 *) intros b p _ _. eexists. reflexivity.
  - (* Inv0 *) intros b p d H. apply cx_valid_pages in H as [Hb [Hp|Hp]];
      subst; [exists 0, 0|exists 0, 1]; reflexivity.
  - (* Inv1 *) intros a p pa H. apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]];
      cbn [pa_block pa_page];
      unfold total_blocks, addr_space, pages_per_block; repeat split; lia.
  - (* Inv2 *) intros a1 p1 a2 p2 pa H1 H2.
    apply cx_map_inv in H1 as [[Ha1 [Hp1 Hq1]]|[Ha1 [Hp1 Hq1]]];
    apply cx_map_inv in H2 as [[Ha2 [Hp2 Hq2]]|[Ha2 [Hp2 Hq2]]];
    subst; split; congruence.
  - (* Inv3 *) intros a p pa d H _.
    apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]]; reflexivity.
  - (* Inv4 *) intros a p b q d Hps Hlpa.
    apply cx_valid_pages in Hps as [Hb [Hp|Hp]]; subst;
      cbn [page_meta cx_model page_lpa] in Hlpa; unfold cx_meta in Hlpa;
      cbn in Hlpa; injection Hlpa as H1 H2; subst; reflexivity.
  - (* Inv5 *) intros a p pa H.
    apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]];
      cbn [pa_block free_block_list cx_model]; intros [H|[H|[H|H]]];
      solve [discriminate | exact H].
  - (* Inv6 *) intros b Hin p _.
    cbn [free_block_list cx_model] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; split; reflexivity.
  - (* Inv7 *) intros a p pa d t ns H _ Ht Hns.
    apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]];
      cbn in Ht, Hns |- *; split; congruence.
  - (* Inv8 *) intros b Hin. cbn [free_block_list cx_model] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; unfold total_blocks; lia.
  - (* Inv9 *) intros b p d H. apply cx_valid_pages in H as [Hb [Hp|Hp]];
      subst; exists 1; reflexivity.
  - (* Inv10 *) intros b Hb.
    destruct b as [|[|[|[|[|[|[|[|b]]]]]]]].
    + right; right; right. exists 0. reflexivity.
    + right; right; right. exists 0. reflexivity.
    + right; right; right. exists 0. reflexivity.
    + right; right; left. exists 0, 0, (mkPhysAddr 3 0). split; reflexivity.
    + left. cbn. auto.
    + right; left. exists 0, 0. reflexivity.
    + left. cbn. auto.
    + left. cbn. auto.
    + exfalso. unfold total_blocks in Hb. lia.
  - (* Inv11 *) cbn [free_block_list cx_model].
    apply NoDup_cons; [intros [H|[H|[]]]; discriminate|].
    apply NoDup_cons; [intros [H|[]]; discriminate|].
    apply NoDup_cons; [intros []|]. apply NoDup_nil.
  - (* Inv12 *) intros b _ [p Hrole].
    cbn [page_role cx_model] in Hrole. unfold cx_role in Hrole.
    destruct (andb (Nat.eqb b 3) (Nat.ltb p 2)); discriminate.
  - (* Inv13 *) intros b p d H. apply cx_valid_pages in H as [Hb [Hp|Hp]];
      subst; reflexivity.
  - (* Inv14 *) intros b p H.
    cbn [page_role cx_model] in H. unfold cx_role in H.
    destruct (andb (Nat.eqb b 3) (Nat.ltb p 2)) eqn:E; [|discriminate].
    exists (10 + p). cbn [page_state cx_model]. unfold cx_ps. rewrite E.
    reflexivity.
  - (* Inv15 *) intros b p H.
    cbn [page_role cx_model] in H. unfold cx_role in H.
    destruct (andb (Nat.eqb b 3) (Nat.ltb p 2)); discriminate.
  - (* Inv16 *) intros b p H.
    cbn [page_state cx_model] in H. unfold cx_ps in H.
    cbn [page_role cx_model]. unfold cx_role.
    destruct (andb (Nat.eqb b 3) (Nat.ltb p 2)); [discriminate H|reflexivity].
  - (* Inv17 *) intros b H. cbn [free_block cx_model] in H.
    apply orb_true_iff in H as [H|H]; [|apply orb_true_iff in H as [H|H]];
      apply Nat.eqb_eq in H; subst b; split; reflexivity.
  - (* Inv18 *) intros a p pa H.
    apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]]; split; reflexivity.
  - (* Inv19 *) intros i r H. discriminate H.
  - (* Inv20 *) intros t ns b Hob. cbn [open_block cx_model] in Hob.
    destruct (andb (Nat.eqb t 0) (Nat.eqb ns 0)) eqn:E; [|discriminate].
    injection Hob as Hob. subst b.
    apply andb_prop in E as [Et Ens].
    apply Nat.eqb_eq in Et. apply Nat.eqb_eq in Ens. subst t ns.
    split; [unfold total_blocks; lia|].
    split; [cbn [free_block_list cx_model]; intros [H|[H|[H|H]]];
            solve [discriminate|exact H]|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [rewrite cx_write_ptr_00; unfold pages_per_block; lia|].
    split; [right; reflexivity|].
    split; [right; reflexivity|].
    intros t' ns' H. cbn [open_block cx_model] in H.
    destruct (andb (Nat.eqb t' 0) (Nat.eqb ns' 0)) eqn:E'; [|discriminate].
    apply andb_prop in E' as [Et' Ens'].
    split; [now apply Nat.eqb_eq in Et'|now apply Nat.eqb_eq in Ens'].
  - (* Inv21 *) intros t ns b q Hob Hge Hlt.
    cbn [open_block cx_model] in Hob.
    destruct (andb (Nat.eqb t 0) (Nat.eqb ns 0)) eqn:E; [|discriminate].
    injection Hob as Hob. subst b.
    apply andb_prop in E as [Et Ens].
    apply Nat.eqb_eq in Et. apply Nat.eqb_eq in Ens. subst t ns.
    rewrite cx_write_ptr_00 in Hge. unfold pages_per_block in Hlt.
    assert (q = 3) by lia. subst q. split; reflexivity.
  - (* Inv22 *) intros a p pa H.
    apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]];
      [exists 10|exists 11]; reflexivity.
  - (* Inv23 *) intros b H. cbn [block_open cx_model] in H.
    apply Nat.eqb_eq in H. subst b. exists 0, 0. reflexivity.
  - (* Inv24 *) intros b. cbn [free_block free_block_list cx_model]. split.
    + intros H. apply orb_true_iff in H as [H|H];
        [|apply orb_true_iff in H as [H|H]];
        apply Nat.eqb_eq in H; subst b; cbn; auto.
    + intros [<-|[<-|[<-|[]]]]; reflexivity.
  - (* Inv25 *) intros t ns b q Hob Hlt.
    cbn [open_block cx_model] in Hob.
    destruct (andb (Nat.eqb t 0) (Nat.eqb ns 0)) eqn:E; [|discriminate].
    injection Hob as Hob. subst b.
    apply andb_prop in E as [Et Ens].
    apply Nat.eqb_eq in Et. apply Nat.eqb_eq in Ens. subst t ns.
    rewrite cx_write_ptr_00 in Hlt.
    assert (Hq : Nat.ltb q 3 = true) by (apply Nat.ltb_lt; lia).
    cbn [page_state cx_model]. unfold cx_ps. rewrite Hq. cbn. discriminate.
  - (* Inv26 *) intros a p pa H.
    apply cx_map_inv in H as [[-> [-> ->]]|[-> [-> ->]]];
      split; [exists 0|exists 0|exists 0|exists 0]; reflexivity.
Qed.

(* ── the ISP state on top of it ─────────────────────────────────────── *)

Definition cx_run : CoarseRun := mkCoarseRun 0 (mkPhysAddr 3 0) 2.

Definition cx_isp : ISPState :=
  mkISPState
    (mkDFTLState cx_model [] cx_l2p)
    (fun a => if Nat.eqb a 0 then Some cx_run else None)
    (fun j => if Nat.eqb j 0 then Some (mkJobStatus true 0 1) else None)
    (fun z => if Nat.eqb z 0 then Some (mkZoneMeta 0 4 0) else None).

Theorem cx_isp_ok : isp_ok cx_isp.
Proof.
  unfold isp_ok, cx_isp. cbn [isp_base isp_runs isp_jobs isp_zones].
  split.
  { unfold dftl_ok, CMTBounded, CMTSound, CMTCleanSynced, TransComplete.
    cbn [ds_cmt ds_tpages ds_model].
    split; [apply Nat.le_0_l|].
    split; [intros e He; cbn in He; contradiction|].
    split; [intros e He; cbn in He; contradiction|].
    intros a p _. reflexivity. }
  split.
  { intros a r k H Hk. cbn [isp_runs] in H.
    destruct (Nat.eqb a 0) eqn:Ea; [|discriminate].
    apply Nat.eqb_eq in Ea. subst a. injection H as H. subst r.
    cbn [cr_len cr_page cr_pa pa_block pa_page cx_run] in *.
    destruct k as [|[|k]]; [reflexivity|reflexivity|lia]. }
  split.
  { intros j st H Hp. cbn [isp_jobs] in H.
    destruct (Nat.eqb j 0) eqn:Ej; [|discriminate].
    injection H as H. subst st. cbn [job_in job_out].
    split; exists 0, (mkZoneMeta 0 4 0); (split; [reflexivity|]);
      unfold addr_in_zone; cbn [zone_start zone_len]; lia. }
  split.
  { intros zid z H. cbn [isp_zones] in H.
    destruct (Nat.eqb zid 0) eqn:Ez; [|discriminate].
    injection H as H. subst z. cbn [zone_start zone_len].
    unfold addr_space. lia. }
  { intros a r H. cbn [isp_runs] in H.
    destruct (Nat.eqb a 0) eqn:Ea; [|discriminate].
    apply Nat.eqb_eq in Ea. subst a.
    exists 0, (mkZoneMeta 0 4 0). split; [reflexivity|].
    unfold addr_in_zone. cbn [zone_start zone_len]. lia. }
Qed.

(* ── what garbage collection actually does to the run ───────────────── *)

Example cx_gc_fires : exists m, step cx_model COpGC = Some m.
Proof. eexists. vm_compute. reflexivity. Qed.

(* Page (0,0) leaves block 3 for the tail of the open block ... *)
Example cx_run_page0_moves :
  l2p_map (ds_model (isp_base (isp_gc_unwrapped cx_isp))) 0 0
    = Some (mkPhysAddr 5 3).
Proof. vm_compute. reflexivity. Qed.

(* ... and page (0,1) for a freshly opened one.  Different blocks: the run
   is split, and no re-pointing of its start can restore it. *)
Example cx_run_page1_moves :
  l2p_map (ds_model (isp_base (isp_gc_unwrapped cx_isp))) 0 1
    = Some (mkPhysAddr 4 0).
Proof. vm_compute. reflexivity. Qed.

(* ── the negations ─────────────────────────────────────────────────────

   The hypotheses are as strong as they can be made: the state satisfies the
   framework's full invariant, DFTL's own, and every ISP invariant.  Even so
   the conclusion fails.  This is the machine-checked form of "the extension
   is not orthogonal on the maintenance front". *)

Theorem unwrapped_gc_breaks_coarse_runs :
  ~ (forall s,
       isp_ok s ->
       ftl_invariant (ds_model (isp_base s)) ->
       ISPRunsSound (isp_gc_unwrapped s)).
Proof.
  intros Hclaim.
  specialize (Hclaim cx_isp cx_isp_ok cx_model_invariant).
  specialize (Hclaim 0 cx_run 0 eq_refl ltac:(cbn [cr_len cx_run]; lia)).
  vm_compute in Hclaim. discriminate Hclaim.
Qed.

Theorem unwrapped_wear_level_breaks_coarse_runs :
  ~ (forall s,
       isp_ok s ->
       ftl_invariant (ds_model (isp_base s)) ->
       ISPRunsSound (isp_wear_level_unwrapped s)).
Proof.
  intros Hclaim.
  specialize (Hclaim cx_isp cx_isp_ok cx_model_invariant).
  specialize (Hclaim 0 cx_run 0 eq_refl ltac:(cbn [cr_len cx_run]; lia)).
  vm_compute in Hclaim. discriminate Hclaim.
Qed.

(* Page granularity makes the same break reachable through an ordinary host
   write: writing logical page (0,0) relocates it out of place, out of the
   run's claimed block. *)
Theorem unwrapped_write_breaks_coarse_runs :
  ~ (forall s a p d,
       isp_ok s ->
       ftl_invariant (ds_model (isp_base s)) ->
       ISPRunsSound (isp_write_unwrapped s a p d)).
Proof.
  intros Hclaim.
  specialize (Hclaim cx_isp 0 0 99 cx_isp_ok cx_model_invariant).
  specialize (Hclaim 0 cx_run 0 eq_refl ltac:(cbn [cr_len cx_run]; lia)).
  vm_compute in Hclaim. discriminate Hclaim.
Qed.

(* ── and what the wrapper buys, concretely ──────────────────────────── *)

(* Unwrapped, the ISP fast path hands the accelerator (3,0) -- a page in a
   block garbage collection has just erased and returned to the free pool.
   The answer is not stale-but-harmless; it points into space that will be
   handed to whichever tenant allocates next. *)
Example cx_unwrapped_scan_lies :
  isp_scan_resolve (isp_gc_unwrapped cx_isp) 0 0 = Some (mkPhysAddr 3 0) /\
  page_state (ds_model (isp_base (isp_gc_unwrapped cx_isp))) 3 0 = PS_Empty /\
  free_block (ds_model (isp_base (isp_gc_unwrapped cx_isp))) 3 = true.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(* Wrapped, the same query is a clean miss. *)
Example cx_wrapped_scan_misses :
  isp_scan_resolve (isp_gc cx_isp) 0 0 = None.
Proof. vm_compute. reflexivity. Qed.

(* And the run it dropped is one whose range contains a page that moved --
   the general statement of that is [coarse_resync_drop_means_moved]. *)
Example cx_wrapped_dropped_the_run :
  isp_runs (isp_gc cx_isp) 0 = None.
Proof. vm_compute. reflexivity. Qed.

(* ══════════════════════════════════════════════════════════════════════
   PART 8 -- the interface instance
   ══════════════════════════════════════════════════════════════════════

   The flash data plane is DFTL's, unchanged.  [user_to_model] is [ds_model]
   after [isp_base], so every clause the framework states is stated about
   the same device DFTL's own ascription talked about, and each of the five
   hypotheses is DFTL's own hypothesis applied to [isp_base s].

   The five delegating proofs are delimited by the markers below so that the
   count in the file's closing accounting can be checked mechanically. *)

Module DFTLwithISP <: CUSTOM_FTL.

  Definition user_state := ISPState.

  Definition user_read       := isp_read.
  Definition user_write      := isp_write.
  Definition user_gc         := isp_gc.
  Definition user_wear_level := isp_wear_level.

  Definition user_to_model (s : ISPState) : FTLState :=
    DFTLConcreteFTL.user_to_model (isp_base s).

  Definition user_write_ready (s : ISPState) (a : Addr) (p : Page) : Prop :=
    DFTLConcreteFTL.user_write_ready (isp_base s) a p.

  Definition admissible (s : user_state) (a : Addr) (p : Page) : Prop :=
    a < addr_space /\ p < pages_per_block /\
    (exists t, addr_tenant (user_to_model s) a = Some t) /\
    (exists ns, addr_namespace (user_to_model s) a = Some ns).

  Definition security_contract (m : FTLState) : Prop := ftl_invariant m.

  (* BEGIN five-hypothesis delegation *)
  Lemma invariants_preserved_on_write :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_write s a p d)).
  Proof.
    intros s a p d Hadm Hready Hinv.
    exact (DFTLConcreteFTL.invariants_preserved_on_write
             (isp_base s) a p d Hadm Hready Hinv).
  Qed.

  Lemma invariants_preserved_on_gc :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_gc s)).
  Proof.
    intros s Hinv.
    exact (DFTLConcreteFTL.invariants_preserved_on_gc (isp_base s) Hinv).
  Qed.

  Lemma invariants_preserved_on_wear_level :
    forall s,
      security_contract (user_to_model s) ->
      security_contract (user_to_model (user_wear_level s)).
  Proof.
    intros s Hinv.
    exact (DFTLConcreteFTL.invariants_preserved_on_wear_level (isp_base s) Hinv).
  Qed.

  Lemma read_after_write_correctness :
    forall s a p d,
      admissible s a p ->
      user_write_ready s a p ->
      security_contract (user_to_model s) ->
      user_read (user_write s a p d) a p = Some d.
  Proof.
    intros s a p d Hadm Hready Hinv.
    exact (DFTLConcreteFTL.read_after_write_correctness
             (isp_base s) a p d Hadm Hready Hinv).
  Qed.

  Lemma isolation_property :
    forall s a1 p1 a2 p2 d1 d2,
      (a1 <> a2 \/ p1 <> p2) ->
      admissible s a1 p1 ->
      admissible (user_write s a1 p1 d1) a2 p2 ->
      user_write_ready s a1 p1 ->
      user_write_ready (user_write s a1 p1 d1) a2 p2 ->
      security_contract (user_to_model s) ->
      user_read (user_write (user_write s a1 p1 d1) a2 p2 d2) a1 p1 = Some d1.
  Proof.
    intros s a1 p1 a2 p2 d1 d2 Hne Hadm1 Hadm2 Hr1 Hr2 Hinv.
    exact (DFTLConcreteFTL.isolation_property (isp_base s) a1 p1 a2 p2 d1 d2
             Hne Hadm1 Hadm2 Hr1 Hr2 Hinv).
  Qed.
  (* END five-hypothesis delegation *)

End DFTLwithISP.

Module MegISCertificate := Validator DFTLwithISP.

(* ══════════════════════════════════════════════════════════════════════
   PART 9 -- does the orthogonal-extension functor apply?
   ══════════════════════════════════════════════════════════════════════

   It does, and it carries strictly more than Part 8 wrote by hand -- and
   strictly less than the feature needs.  Both halves of that are worth
   stating precisely, because "is this extension orthogonal?" turns out to
   have two different answers depending on what is being preserved.

   What the functor carries.  [STATE_EXTENSION]'s four commutation equations
   all hold by [reflexivity], *including* [gc_commutes] for the wrapped
   [isp_gc]: the wrapper's re-sync rewrites only [isp_runs], so projecting
   after it is the same as projecting before.  So [LayeredCUSTOM_FTL]
   manufactures the five [CUSTOM_FTL] hypotheses with no designer proof, and
   its [local_op_preserves_contract] and [local_op_preserves_reads] cover
   the four ISP operations for free.

   What it cannot carry.  [STATE_EXTENSION] says nothing whatever about the
   extension's own state beyond "the base cannot see it".  [ISPRunsSound] is
   a relation *between* the new state and the base state, and the functor
   has no vocabulary for such a relation -- which is exactly right, because
   the relation is not preserved.  Every line of Parts 5, 6 and 7 lies
   outside what any orthogonality functor can supply.

   So the honest summary is: ISP is orthogonal in the direction the
   framework looks (new state invisible to the data plane) and non-orthogonal
   in the opposite direction (the data plane visible to, and destructive of,
   the new state).  Case (1) of the taxonomy for the five hypotheses; case
   (3) for the feature's own clauses. *)

Module ISPExtension <: STATE_EXTENSION DFTLConcreteFTL.

  Definition ext_state : Type := ISPState.

  Definition proj (s : ext_state) : DFTLConcreteFTL.user_state := isp_base s.
  Definition inj (b : DFTLConcreteFTL.user_state) : ext_state :=
    mkISPState b (fun _ => None) (fun _ => None) (fun _ => None).

  Lemma proj_inj : forall b, proj (inj b) = b.
  Proof. intros b. reflexivity. Qed.

  Definition ext_read (s : ext_state) (a : Addr) (p : Page) : option Data :=
    isp_read s a p.
  Definition ext_write (s : ext_state) (a : Addr) (p : Page) (d : Data)
    : ext_state := isp_write s a p d.
  Definition ext_gc (s : ext_state) : ext_state := isp_gc s.
  Definition ext_wear_level (s : ext_state) : ext_state := isp_wear_level s.

  Lemma read_commutes :
    forall s a p, ext_read s a p = DFTLConcreteFTL.user_read (proj s) a p.
  Proof. intros. reflexivity. Qed.

  Lemma write_commutes :
    forall s a p d,
      proj (ext_write s a p d) = DFTLConcreteFTL.user_write (proj s) a p d.
  Proof. intros. reflexivity. Qed.

  (* The wrapper is invisible to the projection.  This one equation is the
     whole reason the maintenance repair costs the framework nothing. *)
  Lemma gc_commutes : forall s, proj (ext_gc s) = DFTLConcreteFTL.user_gc (proj s).
  Proof. intros. reflexivity. Qed.

  Lemma wear_level_commutes :
    forall s, proj (ext_wear_level s) = DFTLConcreteFTL.user_wear_level (proj s).
  Proof. intros. reflexivity. Qed.

  (* An ISP-local operation is any rewrite of the three DRAM fields. *)
  Definition ext_local : Type :=
    (CoarseMap * JobMap * ZoneMap) -> (CoarseMap * JobMap * ZoneMap).

  Definition ext_apply (o : ext_local) (s : ext_state) : ext_state :=
    match o (isp_runs s, isp_jobs s, isp_zones s) with
    | (c, j, z) => mkISPState (isp_base s) c j z
    end.

  Lemma apply_commutes : forall o s, proj (ext_apply o s) = proj s.
  Proof.
    intros o s. unfold ext_apply, proj.
    destruct (o (isp_runs s, isp_jobs s, isp_zones s)) as [[c j] z].
    reflexivity.
  Qed.

End ISPExtension.

Module ISPLayered := LayeredCUSTOM_FTL DFTLConcreteFTL ISPExtension.
Module ISPLayeredCertificate := Validator ISPLayered.

(* The five, obtained from the functor rather than written.  Each proof is
   [exact <the functor's field>]; none contains a proof step. *)

Theorem isp_hyp1_from_functor :
  forall s a p d,
    ISPLayered.admissible s a p ->
    ISPLayered.user_write_ready s a p ->
    ISPLayered.security_contract (ISPLayered.user_to_model s) ->
    ISPLayered.security_contract
      (ISPLayered.user_to_model (ISPLayered.user_write s a p d)).
Proof. exact ISPLayered.invariants_preserved_on_write. Qed.

Theorem isp_hyp2_from_functor :
  forall s,
    ISPLayered.security_contract (ISPLayered.user_to_model s) ->
    ISPLayered.security_contract
      (ISPLayered.user_to_model (ISPLayered.user_gc s)).
Proof. exact ISPLayered.invariants_preserved_on_gc. Qed.

Theorem isp_hyp3_from_functor :
  forall s,
    ISPLayered.security_contract (ISPLayered.user_to_model s) ->
    ISPLayered.security_contract
      (ISPLayered.user_to_model (ISPLayered.user_wear_level s)).
Proof. exact ISPLayered.invariants_preserved_on_wear_level. Qed.

Theorem isp_hyp4_from_functor :
  forall s a p d,
    ISPLayered.admissible s a p ->
    ISPLayered.user_write_ready s a p ->
    ISPLayered.security_contract (ISPLayered.user_to_model s) ->
    ISPLayered.user_read (ISPLayered.user_write s a p d) a p = Some d.
Proof. exact ISPLayered.read_after_write_correctness. Qed.

Theorem isp_hyp5_from_functor :
  forall s a1 p1 a2 p2 d1 d2,
    (a1 <> a2 \/ p1 <> p2) ->
    ISPLayered.admissible s a1 p1 ->
    ISPLayered.admissible (ISPLayered.user_write s a1 p1 d1) a2 p2 ->
    ISPLayered.user_write_ready s a1 p1 ->
    ISPLayered.user_write_ready (ISPLayered.user_write s a1 p1 d1) a2 p2 ->
    ISPLayered.security_contract (ISPLayered.user_to_model s) ->
    ISPLayered.user_read
      (ISPLayered.user_write (ISPLayered.user_write s a1 p1 d1) a2 p2 d2)
      a1 p1 = Some d1.
Proof. exact ISPLayered.isolation_property. Qed.

(* The four ISP operations are [ext_apply]s, so the functor's generic
   harmlessness results apply to them verbatim. *)

Definition register_run_local (a : Addr) (r : CoarseRun) : ISPExtension.ext_local :=
  fun cjz => match cjz with
             | (c, j, z) => ((fun x => if Nat.eqb x a then Some r else c x), j, z)
             end.

Lemma register_run_is_local :
  forall s a r,
    isp_register_run s a r = ISPExtension.ext_apply (register_run_local a r) s.
Proof. intros. reflexivity. Qed.

Theorem register_run_preserves_contract :
  forall s a r,
    ISPLayered.security_contract (ISPLayered.user_to_model s) ->
    ISPLayered.security_contract
      (ISPLayered.user_to_model (isp_register_run s a r)).
Proof.
  intros s a r Hinv. rewrite register_run_is_local.
  exact (ISPLayered.local_op_preserves_contract (register_run_local a r) s Hinv).
Qed.

Theorem register_run_preserves_reads :
  forall s a r a0 p0,
    ISPLayered.user_read (isp_register_run s a r) a0 p0 =
    ISPLayered.user_read s a0 p0.
Proof.
  intros s a r a0 p0. rewrite register_run_is_local.
  exact (ISPLayered.local_op_preserves_reads (register_run_local a r) s a0 p0).
Qed.

(* ══════════════════════════════════════════════════════════════════════
   The accounting
   ══════════════════════════════════════════════════════════════════════

   Framework-level cost of the feature (Part 8), counted exactly:

     the five [CUSTOM_FTL] hypotheses   13 physical lines of proof script
                                        between [Proof.] and [Qed.] --
                                        ten tactic invocations, one [intros]
                                        and one [exact <DFTL's own lemma>]
                                        per hypothesis, three of which wrap.
     the whole delegated block          58 lines including the five
                                        statements and the two markers.
     supporting development required     0 -- it is DFTL's, unchanged.

   And zero proof lines if routed through Part 9's functor instead, at the
   price of eleven [reflexivity]-grade lines ascribing [STATE_EXTENSION].

   The comparison that makes this a compounding-reuse claim rather than a
   tautology is with DFTL's own discharge in [DFTL.v]: 64 lines of proof
   script for the same five hypotheses, resting on 505 non-comment lines of
   supporting development -- [dftl_ok] and its four preservation theorems,
   the eviction and write-back algebra, and the refinement relation carried
   across two [step]s.  569 against 13, for the same five guarantees over a
   strictly larger state.  The reason is one sentence long: [user_to_model]
   forgets the ISP fields, so DFTL's proofs never mentioned them and
   transfer unchanged.

   Feature-level cost (Parts 3-7), which the framework does not reduce, in
   non-comment lines:

     the ISP invariants                                    67
     the four ISP operations' preservation                 97
     the re-sync pass and its two characterisation lemmas 104
     the wrappers and their preservation proofs           109
     the concrete counterexample, its 27-clause invariant
       and the three negations                            305

   The last of those is the interesting number.  It is not overhead; it is
   the price of finding out that one of the preservation goals a designer
   would naturally write down is false.  Nothing in the framework, and
   nothing in [Composition]'s orthogonality functor, would have flagged
   it: the framework's 29 conjuncts hold across the unwrapped garbage
   collector, because the data plane really is correct.  It is the feature's
   own claim about physical layout that dies, and only a proof obligation
   stated at the feature's level can catch that.

   The one-line summary a designer should take away: an extension is
   orthogonal only in the direction it is checked.  ISP is invisible to the
   data plane, and the data plane is emphatically not invisible to ISP. *)

Check MegISCertificate.custom_ftl_security_suite.
Check ISPLayeredCertificate.custom_ftl_security_suite.

Print Assumptions MegISCertificate.custom_ftl_security_suite.
Print Assumptions isp_ok_gc.
Print Assumptions unwrapped_gc_breaks_coarse_runs.
Print Assumptions unwrapped_write_breaks_coarse_runs.
Print Assumptions cx_model_invariant.
