(* Model.v: the multi-tenant FTL state the formal contract is stated over. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import core.Geometry.

Import ListNotations.

(* Bring the default geometry's three size constants and their positivity
   lemmas into the top-level namespace so that downstream files continue to
   refer to them by their bare names.  An alternative geometry can be plugged
   in by replacing the [Include] line below with a different module that
   ascribes to GEOMETRY. *)
Include DefaultGeometry.

Definition Addr := nat.
Definition Block := nat.
Definition Page := nat.
Definition Data := nat.
Definition TenantId := nat.
Definition NamespaceId := nat.
Definition CryptoTag := nat.
Definition KeyId := nat.
Definition WearCount := nat.

Record PhysAddr := mkPhysAddr {
  pa_block : Block;
  pa_page : Page
}.

(* A *logical page* is a host address together with a page offset inside it.
   Translation is page-granular: each logical page is mapped independently,
   so an address's pages may live in different blocks.  Block-granular
   designs are the special case in which they do not. *)
Definition LPA := (Addr * Page)%type.

Inductive FlashPrimitive :=
  | PrimRead (pa : PhysAddr)
  (* A page program writes the data and the page's out-of-band area together,
     exactly as real NAND does: one program command carries both the data and
     the spare-area bytes the controller drives.  The OOB is supplied
     explicitly -- the integrity [tag] and the reverse-map [lpa] are arguments
     rather than values derived from the data.  An honest expansion computes
     the tag it stamps (see [op_primitives]); an untrusted controller is free
     to drive the data phase while leaving the tag phase off ([tag = None]),
     which is the FS#4 integrity-tag-removal surface. *)
  | PrimProgram (pa : PhysAddr) (d : Data) (tag : option CryptoTag)
                (lpa : option LPA)
  | PrimInvalidate (pa : PhysAddr)
  | PrimSetTag (pa : PhysAddr) (tag : CryptoTag)
  | PrimMapAddr (a : Addr) (p : Page) (pa : PhysAddr)
  | PrimRemap (a : Addr) (p : Page) (dst : PhysAddr)
  | PrimErase (b : Block)
  | PrimBarrierEnter (tag : nat)
  | PrimBarrierExit (tag : nat)
  (* A raw free-list push: append [b] to [free_block_list] and set its free
     bit, with no check that [b] is genuinely erasable.  This is the FS#5
     free-block-duplication surface: [PrimErase] does the same push but only
     after clearing the block and only for a block not already free; a bare
     push can return an already-free block to the pool a second time.  No host
     operation expands into this constructor. *)
  | PrimFreePush (b : Block).

Inductive PageState :=
  | PS_Empty
  | PS_Invalid
  | PS_Valid (d : Data).

Inductive Role :=
  | RMeta
  | RData.

Record RegionMeta := mkRegionMeta {
  region_tenant : TenantId;
  region_namespace : NamespaceId;
  region_start : Addr;
  region_len : nat
}.

(* Per-page out-of-band metadata.  [page_lpa] is the logical address stamped
   into the page's OOB area when the page is programmed: the reverse mapping
   that a real FTL relies on to find, after relocating a page, which logical
   address pointed at it.  Inv3 and Inv4 tie it to [l2p_map] in both
   directions. *)
Record PageMeta := mkPageMeta {
  page_owner_tenant : TenantId;
  page_owner_namespace : NamespaceId;
  page_tag : option CryptoTag;
  page_lpa : option LPA
}.

Record KeyMeta := mkKeyMeta {
  key_owner : TenantId;
  key_material : nat
}.

Record FTLState := mkFTLState {
  l2p_map : Addr -> Page -> option PhysAddr;
  page_state : Block -> Page -> PageState;
  page_role : Block -> Page -> option Role;
  addr_tenant : Addr -> option TenantId;
  addr_namespace : Addr -> option NamespaceId;
  block_tenant : Block -> option TenantId;
  block_namespace : Block -> option NamespaceId;
  page_meta : Block -> Page -> PageMeta;
  region_table : nat -> option RegionMeta;
  free_block_list : list Block;
  free_block : Block -> bool;
  wear_count : Block -> WearCount;
  key_table : KeyId -> option KeyMeta;
  (* Allocation frontier, one per tenant.  Page-granular translation lets a
     single block accumulate pages of several logical addresses, so a shared
     frontier would let one block hold two tenants' data and leave
     [block_tenant] ill-defined.  Per-tenant frontiers keep a block
     single-tenant, which is what the block-granular access-control unit
     needs.  Pages are programmed in increasing offset order inside a block,
     the order NAND requires.  [block_open] mirrors [open_block] the way
     [free_block] mirrors [free_block_list], so that "is this block open"
     is a test rather than a search over tenants. *)
  open_block : TenantId -> NamespaceId -> option Block;
  write_ptr : TenantId -> NamespaceId -> Page;
  block_open : Block -> bool
}.

Definition empty_page_meta : PageMeta := mkPageMeta 0 0 None None.

Definition empty_state : FTLState :=
  mkFTLState
    (fun _ _ => None)
    (fun _ _ => PS_Empty)
    (fun _ _ => None)
    (fun _ => None)
    (fun _ => None)
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

(* The frontier is indexed by the (tenant, namespace) pair that owns it.
   Indexing by tenant alone would let one block hold pages of two of a
   tenant's namespaces, and a program would then re-stamp the block's
   namespace out from under a co-resident page. *)
Definition set_open_block (f : TenantId -> NamespaceId -> option Block)
                          (t : TenantId) (ns : NamespaceId) (ob : option Block) :=
  fun x y => if andb (Nat.eqb x t) (Nat.eqb y ns) then ob else f x y.

Definition set_write_ptr (f : TenantId -> NamespaceId -> Page)
                         (t : TenantId) (ns : NamespaceId) (wp : Page) :=
  fun x y => if andb (Nat.eqb x t) (Nat.eqb y ns) then wp else f x y.

Definition set_block_open (f : Block -> bool) (b : Block) (v : bool) :=
  fun x => if Nat.eqb x b then v else f x.

Definition set_l2p_map (m : Addr -> Page -> option PhysAddr)
                       (a : Addr) (p : Page) (opa : option PhysAddr) :=
  fun x y => if andb (Nat.eqb x a) (Nat.eqb y p) then opa else m x y.

Definition set_page_state (ps : Block -> Page -> PageState) (b : Block) (p : Page) (st : PageState) :=
  fun blk pg => if andb (Nat.eqb blk b) (Nat.eqb pg p) then st else ps blk pg.

Definition set_page_role (pr : Block -> Page -> option Role) (b : Block) (p : Page) (r : option Role) :=
  fun blk pg => if andb (Nat.eqb blk b) (Nat.eqb pg p) then r else pr blk pg.

Definition set_page_meta (pm : Block -> Page -> PageMeta) (b : Block) (p : Page) (m : PageMeta) :=
  fun blk pg => if andb (Nat.eqb blk b) (Nat.eqb pg p) then m else pm blk pg.

Definition set_addr_tenant (f : Addr -> option TenantId) (a : Addr) (t : option TenantId) :=
  fun x => if Nat.eqb x a then t else f x.

Definition set_addr_namespace (f : Addr -> option NamespaceId) (a : Addr) (ns : option NamespaceId) :=
  fun x => if Nat.eqb x a then ns else f x.

Definition set_block_tenant (f : Block -> option TenantId) (b : Block) (t : option TenantId) :=
  fun x => if Nat.eqb x b then t else f x.

Definition set_block_namespace (f : Block -> option NamespaceId) (b : Block) (ns : option NamespaceId) :=
  fun x => if Nat.eqb x b then ns else f x.

Definition set_free_block (f : Block -> bool) (b : Block) (v : bool) :=
  fun x => if Nat.eqb x b then v else f x.

Definition set_wear_count (f : Block -> WearCount) (b : Block) (wc : WearCount) :=
  fun x => if Nat.eqb x b then wc else f x.

Definition set_key_table (f : KeyId -> option KeyMeta) (k : KeyId) (m : option KeyMeta) :=
  fun x => if Nat.eqb x k then m else f x.

(* ══════════════════════════════════════════════════════════════
   Block-level clear helpers
   Used by both Operational.v (PrimErase) and Primitives.v (apply_erase).
   Defined here to avoid circular dependencies.
   ══════════════════════════════════════════════════════════════ *)

Definition clear_block_state
    (ps : Block -> Page -> PageState) (b : Block) : Block -> Page -> PageState :=
  fun blk pg => if Nat.eqb blk b then PS_Empty else ps blk pg.

Definition clear_block_role
    (pr : Block -> Page -> option Role) (b : Block) : Block -> Page -> option Role :=
  fun blk pg => if Nat.eqb blk b then None else pr blk pg.

Definition clear_block_meta
    (pm : Block -> Page -> PageMeta) (b : Block) : Block -> Page -> PageMeta :=
  fun blk pg => if Nat.eqb blk b then empty_page_meta else pm blk pg.

Lemma clear_block_state_self :
  forall ps b p,
    clear_block_state ps b b p = PS_Empty.
Proof.
  intros ps b p. unfold clear_block_state. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma clear_block_state_other :
  forall ps b blk p,
    blk <> b ->
    clear_block_state ps b blk p = ps blk p.
Proof.
  intros ps b blk p Hne. unfold clear_block_state.
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma clear_block_role_self :
  forall pr b p,
    clear_block_role pr b b p = None.
Proof.
  intros pr b p. unfold clear_block_role. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma clear_block_role_other :
  forall pr b blk p,
    blk <> b ->
    clear_block_role pr b blk p = pr blk p.
Proof.
  intros pr b blk p Hne. unfold clear_block_role.
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma clear_block_meta_self :
  forall pm b p,
    clear_block_meta pm b b p = empty_page_meta.
Proof.
  intros pm b p. unfold clear_block_meta. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma clear_block_meta_other :
  forall pm b blk p,
    blk <> b ->
    clear_block_meta pm b blk p = pm blk p.
Proof.
  intros pm b blk p Hne. unfold clear_block_meta.
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.
