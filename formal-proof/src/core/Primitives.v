(* Primitives.v: the instruction level of the page-granular model.

   [Operational.v] gives each host operation as one atomic state function.  A
   real controller does not have that luxury: it issues a sequence of flash
   commands and mapping-table updates, and a checker that watches the flash
   bus sees only those.  This file rebuilds that level for page-granular
   translation.

   [apply_primitive] gives the effect of one instruction, [op_primitives]
   expands an operation into instructions, and [step_mqsim] runs an
   expansion.  The theorem at the end is the first half of faithfulness: the
   two levels are defined on exactly the same operations.

   Page granularity keeps the write expansion short: a write stales one page
   and programs one page, and all relocation lives in garbage collection,
   which is the only operation whose expansion is unbounded.

   Two further features of the expansions come from the model as it stands
   rather than from page granularity as such.  The allocation frontier is per
   tenant, so the bookkeeping [PrimProgram] has to reproduce names a tenant
   and has to retire that tenant's outgoing open block; and relocation is
   option-valued, so a reclaim that cannot find a destination for a live page
   refuses instead of erasing.  Both are visible in the expansions below: the
   expansion of a reclaim is itself option-valued, and refuses on exactly the
   states where the atomic [reclaim] does. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.
Require Import core.Operational.

Import ListNotations.

(* ── installing one forward mapping ───────────────────────────────── *)

(* Both [PrimMapAddr] and [PrimRemap] point one logical page at one physical
   page and hand the destination block the address's ownership, which is what
   [program_page] does atomically.  The two primitives differ in intent — a
   host write installs a mapping, a relocation repoints an existing one — but
   under page-granular translation they have the same effect, so they share
   this helper. *)
Definition install_mapping (s : FTLState) (a : Addr) (p : Page) (pa : PhysAddr)
  : FTLState :=
  mkFTLState
    (set_l2p_map (l2p_map s) a p (Some pa))
    (page_state s) (page_role s) (addr_tenant s) (addr_namespace s)
    (set_block_tenant (block_tenant s) (pa_block pa) (addr_tenant s a))
    (set_block_namespace (block_namespace s) (pa_block pa) (addr_namespace s a))
    (page_meta s) (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s) (open_block s) (write_ptr s) (block_open s).

(* ── one instruction ──────────────────────────────────────────────── *)

Definition apply_primitive (s : FTLState) (prim : FlashPrimitive) : FTLState :=
  match prim with
  (* a read leaves no trace in the state *)
  | PrimRead _ => s
  | PrimProgram pa d tag lpa =>
      let b := pa_block pa in
      let q := pa_page pa in
      (* The programmed page's owner comes from the block's ownership, which a
         preceding PrimMapAddr or PrimRemap has just installed, rather than
         from whatever stale metadata the physical slot happened to hold.
         That same pair names the frontier this program consumes.  The
         frontier is per (tenant, namespace), and a block belongs to one
         such pair, so the block's owner is the only frontier that can be
         pointing here. *)
      let t := match block_tenant s b with Some t => t | None => 0 end in
      let n := match block_namespace s b with Some n => n | None => 0 end in
      (* Programming consumes the page from the write frontier, which is the
         bookkeeping [alloc_page] does atomically just before [program_page].
         Appending to the block that is already open leaves the free pool and
         the open-block mirror alone; the first page of a block that is not
         open also claims that block out of the pool, marks it open, and
         retires whatever block the tenant had open before — the three things
         [open_fresh] does. *)
      let fbl := if is_open s b
                 then free_block_list s
                 else remove_block_once b (free_block_list s) in
      let fb := if is_open s b
                then free_block s
                else set_free_block (free_block s) b false in
      let bo := if is_open s b
                then block_open s
                else set_block_open (close_open s t n) b true in
      (* The out-of-band area written is exactly the [tag] and [lpa] the caller
         supplies.  An honest expansion passes the integrity tag it derives
         from the data; a controller free to drive the data phase without the
         tag phase passes [None], the FS#4 surface. *)
      let m := mkPageMeta t n tag lpa in
      mkFTLState
        (l2p_map s)
        (set_page_state (page_state s) b q (PS_Valid d))
        (set_page_role (page_role s) b q (Some RData))
        (addr_tenant s) (addr_namespace s)
        (block_tenant s) (block_namespace s)
        (set_page_meta (page_meta s) b q m)
        (region_table s) fbl fb (wear_count s) (key_table s)
        (set_open_block (open_block s) t n (Some b))
        (set_write_ptr (write_ptr s) t n (S q))
        bo
  (* Staling a page also drops the forward mapping that pointed at it.  The
     page's own OOB stamp says which logical page that was, so the controller
     needs no search: this is what the reverse map is for.  A page with no
     stamp leaves the mapping table alone. *)
  | PrimInvalidate pa =>
      match page_lpa (page_meta s (pa_block pa) (pa_page pa)) with
      | Some (a, p) => unmap (invalidate_at s pa) a p
      | None => invalidate_at s pa
      end
  | PrimSetTag pa tag =>
      match page_state s (pa_block pa) (pa_page pa) with
      | PS_Valid _ => set_page_tag_at s pa tag
      | _ => s
      end
  | PrimMapAddr a p pa => install_mapping s a p pa
  | PrimRemap a p dst => install_mapping s a p dst
  (* Erasing also clears the open-block mirror: a block on the free list is
     not open, and the erase is what puts it back there. *)
  | PrimErase b =>
      mkFTLState (l2p_map s)
        (clear_block_state (page_state s) b)
        (clear_block_role (page_role s) b)
        (addr_tenant s) (addr_namespace s)
        (set_block_tenant (block_tenant s) b None)
        (set_block_namespace (block_namespace s) b None)
        (clear_block_meta (page_meta s) b)
        (region_table s)
        (b :: free_block_list s)
        (set_free_block (free_block s) b true)
        (set_wear_count (wear_count s) b (S (wear_count s b)))
        (key_table s) (open_block s) (write_ptr s)
        (set_block_open (block_open s) b false)
  (* Barriers are transaction markers: they delimit a compound operation in
     the instruction stream and have no state effect. *)
  | PrimBarrierEnter _ => s
  | PrimBarrierExit _ => s
  (* A free-list push appends [b] and sets its free bit; nothing else moves. *)
  | PrimFreePush b =>
      mkFTLState (l2p_map s) (page_state s) (page_role s)
        (addr_tenant s) (addr_namespace s)
        (block_tenant s) (block_namespace s)
        (page_meta s) (region_table s)
        (b :: free_block_list s)
        (set_free_block (free_block s) b true)
        (wear_count s) (key_table s) (open_block s) (write_ptr s) (block_open s)
  end.

Fixpoint exec_primitives (s : FTLState) (prims : list FlashPrimitive) : FTLState :=
  match prims with
  | [] => s
  | prim :: tl => exec_primitives (apply_primitive s prim) tl
  end.

(* ── expanding a write ────────────────────────────────────────────── *)

(* An out-of-place write is three instructions and a barrier pair: stale the
   old page if the logical page had one, point the logical page at the fresh
   page the frontier hands out, program it.  The destination is read off
   [alloc_page] applied to the same intermediate state and the same tenant
   the atomic [exec_write] uses, so the two agree on which page gets
   programmed and, in particular, on when no page is available at all. *)
Definition write_primitives (s : FTLState) (a : Addr) (p : Page) (d : Data)
  : option (list FlashPrimitive) :=
  let s1 := match l2p_map s a p with
            | Some old => invalidate_at s old
            | None => s
            end in
  match (match addr_tenant s a, addr_namespace s a with
         | Some t, Some ns => alloc_page s1 t ns
         | _, _ => None
         end) with
  | Some (pa, _) =>
      Some ([PrimBarrierEnter a]
            ++ (match l2p_map s a p with
                | Some old => [PrimInvalidate old]
                | None => []
                end)
            ++ [PrimMapAddr a p pa;
                (* the OOB is computed here in the expansion: the integrity tag
                   is stamped from the data [d] and the reverse map names the
                   logical page [(a, p)] being written *)
                PrimProgram pa d (Some d) (Some (a, p));
                PrimBarrierExit a])
  | None => None
  end.

(* ── expanding a reclaim ──────────────────────────────────────────── *)

(* Moving one live page: read it, repoint its logical page at the fresh
   destination, program it there.  The logical identity comes from the page's
   OOB stamp.  A page that is not live issues no instructions, exactly as
   [relocate_page] leaves the state alone; a live page with no stamp, or one
   for which the frontier has nothing to give, has no faithful expansion at
   all, and the reclaim refuses rather than erasing the page away.  The
   source page is not staled: the whole block is about to be erased. *)
Definition page_reloc_primitives (s : FTLState) (b : Block) (q : Page)
  : option (list FlashPrimitive) :=
  match page_state s b q with
  | PS_Valid d =>
      match page_lpa (page_meta s b q) with
      | Some (a, p) =>
          match addr_tenant s a, addr_namespace s a with
          | Some t, Some ns =>
              match alloc_page s t ns with
              | Some (pa, _) =>
                  (* the OOB is recomputed for the relocated copy: the tag is
                     re-stamped from the page's data [d] and the reverse map
                     re-names its logical page [(a, p)], read off the source
                     page's own OOB stamp *)
                  Some [PrimRead (mkPhysAddr b q);
                        PrimRemap a p pa;
                        PrimProgram pa d (Some d) (Some (a, p))]
              | None => None    (* no destination: refuse, do not erase *)
              end
          | _, _ => None    (* unlabelled owner: refuse, do not erase *)
          end
      | None => None        (* live page with no stamp: refuse *)
      end
  | _ => Some []            (* not live: nothing to move *)
  end.

(* The two levels refuse on the same page for the same reason: the expansion
   consults the same three scrutinees [relocate_page] does. *)
Lemma page_reloc_primitives_domain :
  forall s b q,
    page_reloc_primitives s b q = None <-> relocate_page s b q = None.
Proof.
  intros s b q. unfold page_reloc_primitives, relocate_page.
  destruct (page_state s b q) as [| |d]; try (split; intros H; discriminate H).
  destruct (page_lpa (page_meta s b q)) as [[a p]|];
    [| split; intros _; reflexivity].
  (* the relocated page's owner must be labelled, else both levels refuse *)
  destruct (addr_tenant s a) as [t|]; destruct (addr_namespace s a) as [ns|];
    try (split; intros _; reflexivity).
  destruct (alloc_page s t ns) as [[pa s1]|];
    [split; intros H; discriminate H | split; intros _; reflexivity].
Qed.

(* Pages move one at a time and each one consumes the frontier, so the
   expansion of page q has to be read off the state that the previous pages
   left behind.  Threading [relocate_page] here is what keeps the two levels
   allocating the same destinations — and, now that relocation is
   option-valued, what makes the two abort at the same page. *)
Fixpoint reloc_primitives (s : FTLState) (b : Block) (qs : list Page)
  : option (list FlashPrimitive) :=
  match qs with
  | [] => Some []
  | q :: tl =>
      match page_reloc_primitives s b q with
      | Some pr =>
          match relocate_page s b q with
          | Some s1 =>
              match reloc_primitives s1 b tl with
              | Some rest => Some (pr ++ rest)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Lemma reloc_primitives_domain :
  forall qs s b,
    reloc_primitives s b qs = None <-> relocate_pages s b qs = None.
Proof.
  induction qs as [|q tl IH]; intros s b; simpl.
  - split; intros H; discriminate H.
  - destruct (relocate_page s b q) as [s1|] eqn:Er.
    + (* the page moves; the tails decide *)
      destruct (page_reloc_primitives s b q) as [pr|] eqn:Ep.
      * destruct (reloc_primitives s1 b tl) as [rest|] eqn:Erp.
        -- split; intros H; [discriminate H|].
           apply (IH s1 b) in H. rewrite Erp in H. discriminate H.
        -- split; intros _; [apply (IH s1 b); exact Erp | reflexivity].
      * (* impossible: the expansion refuses only where relocation does *)
        apply (proj1 (page_reloc_primitives_domain s b q)) in Ep.
        rewrite Ep in Er. discriminate Er.
    + (* the page cannot move; both levels abort here *)
      rewrite (proj2 (page_reloc_primitives_domain s b q) Er).
      split; intros _; reflexivity.
Qed.

Definition reclaim_primitives (bt : nat) (s : FTLState) (b : Block)
  : option (list FlashPrimitive) :=
  match reloc_primitives s b all_pages with
  | Some rs =>
      Some ([PrimBarrierEnter bt] ++ rs ++ [PrimErase b; PrimBarrierExit bt])
  | None => None
  end.

Lemma reclaim_primitives_domain :
  forall bt s b, reclaim_primitives bt s b = None <-> reclaim s b = None.
Proof.
  intros bt s b. unfold reclaim_primitives, reclaim.
  destruct (reloc_primitives s b all_pages) as [rs|] eqn:Ep.
  - destruct (relocate_pages s b all_pages) as [s1|] eqn:Er.
    + split; intros H; discriminate H.
    + apply (proj2 (reloc_primitives_domain all_pages s b)) in Er.
      rewrite Ep in Er. discriminate Er.
  - apply (proj1 (reloc_primitives_domain all_pages s b)) in Ep.
    rewrite Ep. split; intros _; reflexivity.
Qed.

(* ── expanding an operation ───────────────────────────────────────── *)

Definition op_primitives (s : FTLState) (op : COp) : option (list FlashPrimitive) :=
  match op with
  | COpRead a p =>
      match l2p_map s a p with
      | Some pa => Some [PrimRead pa]
      | None => Some []
      end
  | COpWrite a p d =>
      (* the same guards [step] applies: an out-of-range logical page, or an
         address the vendor never labelled, is rejected before any
         instruction is issued *)
      if andb (andb (Nat.ltb a addr_space) (Nat.ltb p pages_per_block))
              (match addr_tenant s a, addr_namespace s a with
               | Some _, Some _ => true | _, _ => false end)
      then write_primitives s a p d
      else None
  | COpInvalidate a p =>
      match l2p_map s a p with
      | Some pa => Some [PrimInvalidate pa]
      | None => Some []
      end
  | COpSetTag a p tag =>
      match l2p_map s a p with
      | Some pa => Some [PrimSetTag pa tag]
      | None => Some []
      end
  | COpGC =>
      match find_victim s with
      | Some b => reclaim_primitives 0 s b
      | None => None
      end
  (* wear levelling expands to the same reclaim, over the block its own
     policy names: the least worn reclaimable block rather than the one the
     cleaning heuristic picks.  The barrier tag differs too, so the two
     maintenance windows are distinguishable in the instruction stream. *)
  | COpWearLevel =>
      match find_least_worn_victim s with
      | Some b => reclaim_primitives 1 s b
      | None => None
      end
  end.

Definition step_mqsim (s : FTLState) (op : COp) : option FTLState :=
  match op_primitives s op with
  | Some prims => Some (exec_primitives s prims)
  | None => None
  end.

Fixpoint exec_mqsim (s : FTLState) (ops : list COp) : option FTLState :=
  match ops with
  | [] => Some s
  | op :: tl =>
      match step_mqsim s op with
      | Some s' => exec_mqsim s' tl
      | None => None
      end
  end.

(* ── domain agreement ─────────────────────────────────────────────── *)

(* The instruction level refuses an operation exactly when the atomic level
   does, with no invariant hypothesis.  Read, invalidate and set-tag never
   refuse on either side.  A write refuses on the range guard, and otherwise
   on [alloc_page] of the very same intermediate state and the same tenant,
   so the two branches are the same test written twice.  Reclaiming refuses
   when there is no victim, and also when some live page of the victim has
   nowhere to go.  What makes this hold without hypotheses is that the
   expansion consults the same partial functions the atomic definitions do
   rather than re-deriving the choice of destination. *)
Theorem decompose_domains_agree :
  forall s op, step s op = None <-> step_mqsim s op = None.
Proof.
  intros s op. destruct op; unfold step, step_mqsim, op_primitives.
  - (* COpRead: neither level can refuse *)
    destruct (l2p_map s a p) as [pa|]; simpl;
      split; intros H; discriminate H.
  - (* COpWrite: the range guard first, then the same allocation *)
    destruct (andb (andb (Nat.ltb a addr_space) (Nat.ltb p pages_per_block))
                   (match addr_tenant s a, addr_namespace s a with
               | Some _, Some _ => true | _, _ => false end));
      [| split; intros _; reflexivity].
    unfold exec_write, write_primitives.
    destruct (addr_tenant s a) as [t|]; destruct (addr_namespace s a) as [ns|];
      try (split; intros _; reflexivity).
    destruct (l2p_map s a p) as [old|].
    + destruct (alloc_page (invalidate_at s old) t ns)
        as [[pa s2]|]; simpl;
        [split; intros H; discriminate H | split; intros _; reflexivity].
    + destruct (alloc_page s t ns) as [[pa s2]|]; simpl;
        [split; intros H; discriminate H | split; intros _; reflexivity].
  - (* COpInvalidate *)
    destruct (l2p_map s a p) as [pa|]; simpl;
      split; intros H; discriminate H.
  - (* COpSetTag *)
    destruct (l2p_map s a p) as [pa|]; simpl;
      split; intros H; discriminate H.
  - (* COpGC: no victim, or a victim whose live pages cannot all be moved *)
    unfold gc, reclaim_with. destruct (find_victim s) as [b|];
      [| split; intros _; reflexivity].
    destruct (reclaim_primitives 0 s b) as [prims|] eqn:E.
    + split; intros H; [| discriminate H].
      apply (proj2 (reclaim_primitives_domain 0 s b)) in H.
      rewrite E in H. discriminate H.
    + split; intros _;
        [reflexivity | apply (proj1 (reclaim_primitives_domain 0 s b)); exact E].
  - (* COpWearLevel: the same test over the wear-aware chooser's victim, and
       a different barrier tag *)
    unfold wear_level, reclaim_with.
    destruct (find_least_worn_victim s) as [b|];
      [| split; intros _; reflexivity].
    destruct (reclaim_primitives 1 s b) as [prims|] eqn:E.
    + split; intros H; [| discriminate H].
      apply (proj2 (reclaim_primitives_domain 1 s b)) in H.
      rewrite E in H. discriminate H.
    + split; intros _;
        [reflexivity | apply (proj1 (reclaim_primitives_domain 1 s b)); exact E].
Qed.

(* A convenient contrapositive: agreement on the total part of the domain. *)
Corollary decompose_domains_agree_some :
  forall s op,
    (exists s', step s op = Some s') <-> (exists s'', step_mqsim s op = Some s'').
Proof.
  intros s op. split; intros [s' H].
  - destruct (step_mqsim s op) as [s''|] eqn:E.
    + exists s''. reflexivity.
    + pose proof (proj2 (decompose_domains_agree s op) E) as Hn.
      rewrite H in Hn. discriminate Hn.
  - destruct (step s op) as [s''|] eqn:E.
    + exists s''. reflexivity.
    + pose proof (proj1 (decompose_domains_agree s op) E) as Hn.
      rewrite H in Hn. discriminate Hn.
Qed.
