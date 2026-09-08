(* Operational.v: executable operations over the page-granular FTLState.

   Translation is page-granular: [l2p_map] sends each logical page (a, p) to
   its own physical page.  Two consequences shape this file.

   1. A write does not relocate a block.  It marks the old physical page
      stale, takes a fresh page from the open block, and programs it, which is
      what production FTLs do.

   2. Erase is deferred to garbage collection, which is the only operation
      that erases. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Model.

Import ListNotations.

Inductive COp :=
  | COpRead (a : Addr) (p : Page)
  | COpWrite (a : Addr) (p : Page) (d : Data)
  | COpInvalidate (a : Addr) (p : Page)
  | COpSetTag (a : Addr) (p : Page) (tag : CryptoTag)
  | COpGC
  | COpWearLevel.

Fixpoint in_block_list (b : Block) (xs : list Block) : bool :=
  match xs with
  | [] => false
  | x :: tl => if Nat.eqb x b then true else in_block_list b tl
  end.

Fixpoint remove_block_once (b : Block) (xs : list Block) : list Block :=
  match xs with
  | [] => []
  | x :: tl => if Nat.eqb x b then tl else x :: remove_block_once b tl
  end.

Definition all_pages : list Page := seq 0 pages_per_block.

(* ── reading ──────────────────────────────────────────────────────── *)

Definition read_page (s : FTLState) (a : Addr) (p : Page) : option Data :=
  match l2p_map s a p with
  | Some pa =>
      match page_state s (pa_block pa) (pa_page pa) with
      | PS_Valid d => Some d
      | _ => None
      end
  | None => None
  end.

(* ── the open block and its write frontier ────────────────────────── *)

Definition with_frontier (s : FTLState) (t : TenantId) (ns : NamespaceId)
                         (ob : option Block) (wp : Page) (fbl : list Block)
                         (fb : Block -> bool) (bo : Block -> bool) : FTLState :=
  mkFTLState (l2p_map s) (page_state s) (page_role s) (addr_tenant s)
             (addr_namespace s) (block_tenant s) (block_namespace s)
             (page_meta s) (region_table s) fbl fb (wear_count s)
             (key_table s) (set_open_block (open_block s) t ns ob)
             (set_write_ptr (write_ptr s) t ns wp) bo.

(* Retiring tenant [t]'s current open block, if it has one. *)
Definition close_open (s : FTLState) (t : TenantId) (ns : NamespaceId)
  : Block -> bool :=
  match open_block s t ns with
  | Some ob => set_block_open (block_open s) ob false
  | None => block_open s
  end.

(* Open the head of the free list, keeping one block in reserve so that
   garbage collection always has a destination. *)
Definition open_fresh (s : FTLState) (t : TenantId) (ns : NamespaceId)
  : option (PhysAddr * FTLState) :=
  match free_block_list s with
  | b :: _ :: _ =>
      Some (mkPhysAddr b 0,
            with_frontier s t ns (Some b) 1
              (remove_block_once b (free_block_list s))
              (set_free_block (free_block s) b false)
              (set_block_open (close_open s t ns) b true))
  | _ => None
  end.

(* Pages are handed out in increasing offset order inside the open block,
   which is the programming order NAND requires. *)
Definition alloc_page (s : FTLState) (t : TenantId) (ns : NamespaceId)
  : option (PhysAddr * FTLState) :=
  match open_block s t ns with
  | Some b =>
      if Nat.ltb (write_ptr s t ns) pages_per_block
      then Some (mkPhysAddr b (write_ptr s t ns),
                 with_frontier s t ns (Some b) (S (write_ptr s t ns))
                               (free_block_list s) (free_block s)
                               (block_open s))
      else open_fresh s t ns
  | None => open_fresh s t ns
  end.

(* ── programming and invalidating a single physical page ──────────── *)

Definition program_page (s : FTLState) (a : Addr) (p : Page)
                        (d : Data) (pa : PhysAddr) : FTLState :=
  let t := match addr_tenant s a with Some t => t | None => 0 end in
  let n := match addr_namespace s a with Some n => n | None => 0 end in
  mkFTLState
    (set_l2p_map (l2p_map s) a p (Some pa))
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

Definition invalidate_at (s : FTLState) (pa : PhysAddr) : FTLState :=
  mkFTLState (l2p_map s)
    (set_page_state (page_state s) (pa_block pa) (pa_page pa) PS_Invalid)
    (set_page_role  (page_role s)  (pa_block pa) (pa_page pa) None)
    (addr_tenant s) (addr_namespace s) (block_tenant s) (block_namespace s)
    (set_page_meta (page_meta s) (pa_block pa) (pa_page pa) empty_page_meta)
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s) (open_block s) (write_ptr s)
    (block_open s).

(* Detaching a logical page drops the forward mapping as well. *)
Definition unmap (s : FTLState) (a : Addr) (p : Page) : FTLState :=
  mkFTLState (set_l2p_map (l2p_map s) a p None)
    (page_state s) (page_role s) (addr_tenant s) (addr_namespace s)
    (block_tenant s) (block_namespace s) (page_meta s) (region_table s)
    (free_block_list s) (free_block s) (wear_count s) (key_table s)
    (open_block s) (write_ptr s) (block_open s).

(* ── host-visible operations ──────────────────────────────────────── *)

(* Out-of-place write: stale the old page, program a fresh one.  No erase. *)
Definition exec_write (s : FTLState) (a : Addr) (p : Page) (d : Data)
  : option FTLState :=
  let s1 := match l2p_map s a p with
            | Some old => invalidate_at s old
            | None => s
            end in
  match addr_tenant s a, addr_namespace s a with
  | Some t, Some ns =>
      match alloc_page s1 t ns with
      | Some (pa, s2) => Some (program_page s2 a p d pa)
      | None => None
      end
  | _, _ => None
  end.

Definition exec_invalidate (s : FTLState) (a : Addr) (p : Page) : FTLState :=
  match l2p_map s a p with
  | Some pa => unmap (invalidate_at s pa) a p
  | None => s
  end.

Definition set_page_tag_at (s : FTLState) (pa : PhysAddr) (tag : CryptoTag)
  : FTLState :=
  let m := page_meta s (pa_block pa) (pa_page pa) in
  mkFTLState (l2p_map s) (page_state s) (page_role s) (addr_tenant s)
    (addr_namespace s) (block_tenant s) (block_namespace s)
    (set_page_meta (page_meta s) (pa_block pa) (pa_page pa)
       (mkPageMeta (page_owner_tenant m) (page_owner_namespace m)
                   (Some tag) (page_lpa m)))
    (region_table s) (free_block_list s) (free_block s)
    (wear_count s) (key_table s) (open_block s) (write_ptr s)
    (block_open s).

Definition exec_set_tag (s : FTLState) (a : Addr) (p : Page) (tag : CryptoTag)
  : FTLState :=
  match l2p_map s a p with
  | Some pa =>
      match page_state s (pa_block pa) (pa_page pa) with
      | PS_Valid _ => set_page_tag_at s pa tag
      | _ => s
      end
  | None => s
  end.

(* ── relocation, garbage collection, wear leveling ────────────────── *)

(* Move one live page of [b] to a fresh page, carrying its logical identity
   from the OOB stamp.  A page with no stamp, or a page that is not live, is
   left alone: garbage collection never resurrects stale data. *)
Definition relocate_page (s : FTLState) (b : Block) (q : Page)
  : option FTLState :=
  match page_state s b q with
  | PS_Valid d =>
      match page_lpa (page_meta s b q) with
      | Some (a, p) =>
          match addr_tenant s a, addr_namespace s a with
          | Some t, Some ns =>
              match alloc_page s t ns with
              | Some (pa, s1) => Some (program_page s1 a p d pa)
              | None => None    (* no destination: refuse, do not erase *)
              end
          | _, _ => None    (* unlabelled owner: refuse, do not erase *)
          end
      | None => None        (* live page with no stamp: refuse *)
      end
  | _ => Some s             (* not live: nothing to move *)
  end.

Fixpoint relocate_pages (s : FTLState) (b : Block) (ps : list Page)
  : option FTLState :=
  match ps with
  | [] => Some s
  | q :: tl =>
      match relocate_page s b q with
      | Some s1 => relocate_pages s1 b tl
      | None => None
      end
  end.

(* Erasing returns the block to the free pool, clears its ownership, and
   bumps its wear count.  This is the only operation that erases. *)
Definition erase_block (s : FTLState) (b : Block) : FTLState :=
  mkFTLState (l2p_map s)
    (fun blk pg => if Nat.eqb blk b then PS_Empty else page_state s blk pg)
    (fun blk pg => if Nat.eqb blk b then None else page_role s blk pg)
    (addr_tenant s) (addr_namespace s)
    (set_block_tenant (block_tenant s) b None)
    (set_block_namespace (block_namespace s) b None)
    (fun blk pg => if Nat.eqb blk b then empty_page_meta else page_meta s blk pg)
    (region_table s)
    (b :: free_block_list s)
    (set_free_block (free_block s) b true)
    (fun blk => if Nat.eqb blk b then S (wear_count s blk) else wear_count s blk)
    (key_table s) (open_block s) (write_ptr s)
    (set_block_open (block_open s) b false).

Definition is_open (s : FTLState) (b : Block) : bool := block_open s b.

(* A block is reclaimable when it is neither free nor the open block. *)
Definition reclaimable (s : FTLState) (b : Block) : bool :=
  andb (negb (free_block s b)) (negb (is_open s b)).

Fixpoint find_victim_aux (s : FTLState) (n : nat) : option Block :=
  match n with
  | 0 => None
  | S k => if reclaimable s k then Some k else find_victim_aux s k
  end.

Definition find_victim (s : FTLState) : option Block :=
  find_victim_aux s total_blocks.

(* If any live page of the victim cannot be moved, the reclaim fails and the
   block is left alone.  Erasing regardless would destroy live data. *)
Definition reclaim (s : FTLState) (b : Block) : option FTLState :=
  match relocate_pages s b all_pages with
  | Some s1 => Some (erase_block s1 b)
  | None => None
  end.

(* ── reclamation, parameterized over the victim chooser ────────────────

   Reclaiming a block is one state transformer; *which* block is reclaimed is
   a policy.  Both host-visible maintenance operations are instances of the
   same transformer under different policies, and separating the two is what
   lets the model carry a reclamation policy at all instead of hard-coding
   one.  [reclaim] itself is total on nothing: it refuses when a live page of
   the victim has nowhere to go.  It is sound only on a block that is in
   range, not free and not open ([victim_sound] below), because [erase_block]
   pushes the victim onto the free list and clears its ownership. *)
Definition reclaim_with (pick : FTLState -> option Block) (s : FTLState)
  : option FTLState :=
  match pick s with
  | Some b => reclaim s b
  | None => None
  end.

(* The contract a chooser must meet.  A block outside the geometry, a block
   already on the free list, or a tenant's open block are each states in which
   [erase_block] would break the invariant -- a second entry on the free list,
   a frontier pointing into an erased block -- so a chooser that can return
   one of them is not usable, whatever its policy. *)
Definition victim_sound (pick : FTLState -> option Block) : Prop :=
  forall s b, pick s = Some b -> b < total_blocks /\ reclaimable s b = true.

(* Garbage collection: reclaim whichever block the cleaning policy names.
   [find_victim] scans by descending index and is a placeholder for a
   cleaning-efficiency heuristic (greedy on stale pages, per Agrawal et al.,
   "Design Tradeoffs for SSD Performance", USENIX ATC '08); nothing below
   depends on which reclaimable block it returns. *)
Definition gc (s : FTLState) : option FTLState := reclaim_with find_victim s.

(* ── static wear leveling ─────────────────────────────────────────────

   Conventional FTLs level wear two ways, and only one of them is a reclaim.

   *Dynamic* wear leveling is an allocation-time policy: "pooling the
   available blocks that are free of data and selecting the block with the
   lowest erase count for the next write" (Micron TN-29-42, "Wear-Leveling
   Techniques in NAND Flash Devices").  It never moves data that the host did
   not rewrite, so blocks holding cold data are never recycled and never
   age.  In this model that policy is the choice [open_fresh] makes when it
   takes a block off [free_block_list], not an operation of its own.

   *Static* wear leveling is a reclaim.  It "attempt[s] to move cold data to
   more worn blocks thereby facilitating more even spread of wear" (Murugan
   and Du, "Rejuvenator", MSST '11, §I); the block chosen as the migration
   source is the one whose erase count lags -- "[b]locks that contain static
   data with erase counts that begin to lag behind other blocks will be
   included in the wear-leveling block pool, with the static data being moved
   to blocks with higher erase counts" (Micron TN-29-42).  Agrawal et al.
   describe the same mechanism: "data from a cold block is used to fill it.
   The cold block is then recycled and added to the free queue."

   That is exactly relocate-the-live-pages-then-erase, applied to the
   *least-worn* reclaimable block rather than to the dirtiest one.  Its live
   pages go onto the write frontier, which sits in a block that has been
   erased at least as often, and the freed low-count block then absorbs the
   host's subsequent hot writes.  So the two maintenance operations differ
   in exactly one place, the extremum they take over [wear_count].

   Ties go to the higher index, which is the order [find_victim] scans in, so
   on a device whose blocks are all equally worn the two choosers agree
   ([find_least_worn_victim_uniform] below). *)
Fixpoint find_least_worn_aux (s : FTLState) (n : nat) : option Block :=
  match n with
  | 0 => None
  | S k =>
      match find_least_worn_aux s k with
      | Some b =>
          if reclaimable s k
          then (if Nat.leb (wear_count s k) (wear_count s b) then Some k
                else Some b)
          else Some b
      | None => if reclaimable s k then Some k else None
      end
  end.

Definition find_least_worn_victim (s : FTLState) : option Block :=
  find_least_worn_aux s total_blocks.

Definition wear_level (s : FTLState) : option FTLState :=
  reclaim_with find_least_worn_victim s.

(* ── both choosers meet the contract ──────────────────────────────────── *)

Lemma find_victim_aux_sound :
  forall s n b, find_victim_aux s n = Some b -> b < n /\ reclaimable s b = true.
Proof.
  intros s n. induction n as [|k IH]; intros b H.
  - cbn [find_victim_aux] in H. discriminate.
  - cbn [find_victim_aux] in H. destruct (reclaimable s k) eqn:E.
    + injection H as H. subst b. split; [lia|exact E].
    + destruct (IH b H) as [Hlt Hr]. split; [lia|exact Hr].
Qed.

Lemma find_victim_sound : victim_sound find_victim.
Proof.
  intros s b H. unfold find_victim in H.
  destruct (find_victim_aux_sound s total_blocks b H) as [Hlt Hr].
  split; [exact Hlt | exact Hr].
Qed.

Lemma find_least_worn_aux_none :
  forall s n, find_least_worn_aux s n = None ->
    forall b, b < n -> reclaimable s b = false.
Proof.
  intros s n. induction n as [|k IH]; intros H b Hb.
  - lia.
  - cbn [find_least_worn_aux] in H.
    destruct (find_least_worn_aux s k) as [b0|] eqn:Hk.
    + destruct (reclaimable s k);
        [destruct (Nat.leb (wear_count s k) (wear_count s b0))|]; discriminate H.
    + destruct (reclaimable s k) eqn:Ek; [discriminate H|].
      destruct (Nat.eq_dec b k) as [E|E]; [subst b; exact Ek|].
      apply (IH eq_refl b). lia.
Qed.

Lemma find_least_worn_aux_sound :
  forall s n b, find_least_worn_aux s n = Some b ->
    b < n /\ reclaimable s b = true.
Proof.
  intros s n. induction n as [|k IH]; intros b H.
  - cbn [find_least_worn_aux] in H. discriminate.
  - cbn [find_least_worn_aux] in H.
    destruct (find_least_worn_aux s k) as [b0|] eqn:Hk.
    + destruct (IH b0 eq_refl) as [Hlt0 Hr0].
      destruct (reclaimable s k) eqn:Ek.
      * destruct (Nat.leb (wear_count s k) (wear_count s b0));
          injection H as H; subst b; split; [lia|exact Ek|lia|exact Hr0].
      * injection H as H. subst b. split; [lia|exact Hr0].
    + destruct (reclaimable s k) eqn:Ek; [|discriminate H].
      injection H as H. subst b. split; [lia|exact Ek].
Qed.

Lemma find_least_worn_victim_sound : victim_sound find_least_worn_victim.
Proof.
  intros s b H. unfold find_least_worn_victim in H.
  destruct (find_least_worn_aux_sound s total_blocks b H) as [Hlt Hr].
  split; [exact Hlt | exact Hr].
Qed.

(* The chooser really is an extremum over [wear_count]: no reclaimable block
   is less worn than the one it returns.  This is the property that makes it
   static wear leveling rather than an arbitrary second copy of [gc]. *)
Lemma find_least_worn_aux_minimal :
  forall s n b, find_least_worn_aux s n = Some b ->
    forall b', b' < n -> reclaimable s b' = true ->
      wear_count s b <= wear_count s b'.
Proof.
  intros s n. induction n as [|k IH]; intros b H b' Hb' Hr'.
  - lia.
  - cbn [find_least_worn_aux] in H.
    destruct (find_least_worn_aux s k) as [b0|] eqn:Hk.
    + destruct (reclaimable s k) eqn:Ek.
      * destruct (Nat.leb (wear_count s k) (wear_count s b0)) eqn:El;
          injection H as H; subst b.
        -- apply Nat.leb_le in El.
           destruct (Nat.eq_dec b' k) as [E|E]; [subst b'; lia|].
           assert (Hb'k : b' < k) by lia.
           pose proof (IH b0 eq_refl b' Hb'k Hr'). lia.
        -- apply Nat.leb_gt in El.
           destruct (Nat.eq_dec b' k) as [E|E]; [subst b'; lia|].
           assert (Hb'k : b' < k) by lia.
           exact (IH b0 eq_refl b' Hb'k Hr').
      * injection H as H. subst b.
        destruct (Nat.eq_dec b' k) as [E|E].
        -- subst b'. rewrite Ek in Hr'. discriminate.
        -- assert (Hb'k : b' < k) by lia. exact (IH b0 eq_refl b' Hb'k Hr').
    + destruct (reclaimable s k) eqn:Ek; [|discriminate H].
      injection H as H. subst b.
      destruct (Nat.eq_dec b' k) as [E|E]; [subst b'; lia|].
      assert (Hb'k : b' < k) by lia.
      pose proof (find_least_worn_aux_none s k Hk b' Hb'k) as Hf.
      rewrite Hf in Hr'. discriminate.
Qed.

Theorem find_least_worn_victim_is_minimal :
  forall s b, find_least_worn_victim s = Some b ->
    forall b', b' < total_blocks -> reclaimable s b' = true ->
      wear_count s b <= wear_count s b'.
Proof. intros s b H. exact (find_least_worn_aux_minimal s total_blocks b H). Qed.

(* On a device whose blocks are all equally worn -- a freshly formatted one,
   and every state of a run that has not yet erased anything -- the wear-aware
   chooser makes the same choice [find_victim] does.  So the two operations
   separate only once erase counts actually diverge. *)
Definition wear_uniform (s : FTLState) : Prop :=
  forall b b', wear_count s b = wear_count s b'.

Lemma find_least_worn_aux_uniform :
  forall s n, wear_uniform s -> find_least_worn_aux s n = find_victim_aux s n.
Proof.
  intros s n Hu. induction n as [|k IH]; [reflexivity|].
  cbn [find_least_worn_aux find_victim_aux]. rewrite IH.
  destruct (find_victim_aux s k) as [b|].
  - destruct (reclaimable s k); [|reflexivity].
    rewrite (Hu k b), Nat.leb_refl. reflexivity.
  - reflexivity.
Qed.

Theorem find_least_worn_victim_uniform :
  forall s, wear_uniform s -> find_least_worn_victim s = find_victim s.
Proof.
  intros s Hu. unfold find_least_worn_victim, find_victim.
  exact (find_least_worn_aux_uniform s total_blocks Hu).
Qed.

Definition step (s : FTLState) (op : COp) : option FTLState :=
  match op with
  | COpRead _ _ => Some s
  | COpWrite a p d =>
      (* An unlabelled address has no tenant to allocate for.  Allocating as
         tenant 0 would retag a genuine tenant-0 block, so refuse instead. *)
      if andb (andb (Nat.ltb a addr_space) (Nat.ltb p pages_per_block))
              (match addr_tenant s a, addr_namespace s a with
               | Some _, Some _ => true | _, _ => false end)
      then exec_write s a p d
      else None
  | COpInvalidate a p => Some (exec_invalidate s a p)
  | COpSetTag a p tag => Some (exec_set_tag s a p tag)
  | COpGC => gc s
  | COpWearLevel => wear_level s
  end.

Fixpoint exec (s : FTLState) (ops : list COp) : option FTLState :=
  match ops with
  | [] => Some s
  | op :: ops' =>
      match step s op with
      | Some s' => exec s' ops'
      | None => None
      end
  end.
