# On-silicon alias attack: CONFIRMED (DaisyPlus OpenSSD, NVMe host I/O)

Date: 2026-08-31.  Board: /dev/nvme0n1 = DaisyPlus OpenSSD (SN SSDD515T, 30.79 GB, 4 KiB LBA).
Firmware: <build>/ftl_alias_headless.elf (gr3ftl alias-attack build, headless inbyte patch),
booted clean over JTAG (boot_headless.tcl) after cold power-cycle; core never halted.
Host: build workstation, nvme-cli. NVMe host reached the board via PCIe rescan of 01:00.0 (10ee:903f).

Mapping: BYTES_PER_SLICE=16384, BYTES_PER_NVME_BLOCK=4096 -> NVME_BLOCKS_PER_SLICE=4,
request_transform.c:85 tempLsa = startLba/4.  DEMO_VICTIM_LSA=1024, DEMO_ATTACKER_LSA=2048.
  victim  LSA 1024 <-> LBA 4096 ; attacker LSA 2048 <-> LBA 8192 ; control LSA 3072 <-> LBA 12288.
Attack (address_translation.c AddrTransRead/Write): if logicalSliceAddr==2048,
  GetAliasedVirtualSliceAddr() sets logicalSlice[2048].vsa = logicalSlice[1024].vsa and returns it.

Procedure (alias_demo3.sh): write victim secret to LSA 1024; write control to LSA 3072;
write 1024 padding slices (32-block MDTS-safe chunks) to evict the 16*USER_DIES DRAM buffer
and commit the victim slice to NAND; flush; read victim, control, attacker.

RESULT:
  victim.read  sha256 = 9436f68de6aca64e688e33f77e22b263fcedb6b0e9c8b7cece3fb57391dfdcba
  control.read sha256 = 07bdd78f585b22b51937cdb505a277e63a724c9905a249915cf0b5febf89af2f
  attack.read  sha256 = 9436f68de6aca64e688e33f77e22b263fcedb6b0e9c8b7cece3fb57391dfdcba  (== victim)
  attacker LSA 2048 first bytes: "VICTIM-SECRET!! tenant A private data."

=> Reading the attacker LBA returns the victim tenant private data. Aliasing
   confidentiality break reproduced on real silicon over the standard NVMe interface.

Key point re write buffer: FindDataBufHashTableEntry = LSA % (16*USER_DIES); NVMe Flush alone
did NOT commit the victim slice, so v1/v2 read garbage from the aliased VSA on NAND. Padding
eviction (>buffer size) was required to land victim data on NAND before the aliased read.

Script: scripts/alias_demo3.sh.

## Guarded firmware stops the leak (2026-09-01)

This is not a demonstration of CertiFlash prevention on hardware. The guard
below is a hand-written C check transcribed from the Rocq Inv2 clause, not the
verified checker and not a synthesized circuit. It is recorded here because it
isolates the attack to the single condition Inv2 states. The guarantee that a
certified FTL cannot reach these states is the mechanized proof, not this run.

Booted <build>/ftl_checked_headless.elf (attack code + software Inv2 injectivity guard
in GetAliasedVirtualSliceAddr) via boot_headless_checked.tcl after a cold
power-cycle; PCIe rescan re-enumerated /dev/nvme0n1 (DaisyPlus OpenSSD).
Same scripts/alias_demo3.sh sequence as the attack run.

RESULT (checked firmware):
  victim.read  sha256 = 9436f68de6aca64e688e33f77e22b263fcedb6b0e9c8b7cece3fb57391dfdcba  (secret intact)
  control.read sha256 = 07bdd78f585b22b51937cdb505a277e63a724c9905a249915cf0b5febf89af2f
  attack.read  sha256 = f9662416c4a8e32d47fa452e416f36e132e1f258d338cfe227c43e3959a78978  (!= victim)
  attacker LSA 2048 first bytes: "flush PADDING-flush PADDING-flush" (unrelated, NOT victim secret)

Before/after, identical board + identical NVMe sequence, only the Inv2 guard added:
  unmodified attack fw : attacker.read == victim.read  -> victim secret leaked
  + Inv2 guard (checked): attacker.read != victim.read  -> remap refused, no leak
The single-variable flip (guard on/off) attributes the prevention to the Inv2 check.

## Multi-attack on-silicon result (3 runtime attacks, 2 host-observable) 2026-09-01

Unified firmwares (redirect project PS_LPDDR4_B, ATTACK_MODE=ATTACK_ALL_RUNTIME):
  <build>/ftl_allattacks_headless.elf  = ALIAS(LSA2048/LBA8192) + REDIRECT(LSA2064/LBA8256) + RAW_RETARGET(LSA2096/LBA8384)
  <build>/ftl_allchecked_headless.elf  = same + CERTIFLASH_GUARD (Inv2 guard on each)
  boot_allattacks.tcl / boot_allchecked.tcl ; scripts/all_attacks_demo.sh (shared victim LSA1024/LBA4096)

ATTACK firmware:
  ALIAS         attacker read LBA8192 sha=9436f68d..dcba == victim  -> LEAK
  REDIRECT      attacker read LBA8256 sha=9436f68d..dcba == victim  -> LEAK
  RAW_RETARGET  victim after attacker write = 9436f68d..dcba (unchanged) -> no host-visible effect
CHECKED firmware (same board, same NVMe sequence, only Inv2 guards added):
  ALIAS         attacker read = f9662416..8978 != victim  -> REFUSED
  REDIRECT      attacker read = 1b76cfc4..099b != victim  -> REFUSED
  RAW_RETARGET  victim intact (no diff either way)

=> Two Inv2 cross-tenant leaks at two layers (DRAM L2P map; request-transform), each flipped
   LEAK->refused by the CertiFlash Inv2 guard on real silicon. RAW_RETARGET (flash-controller
   row) fires internally but NAND cannot reprogram the victim page, so no clean host-visible
   effect; covered by the formal proof + host-side C image instead.

## MegIS coarse-run: FORMAL + ON-SILICON (2026-09-01)

Formal (formal-proof/src/dftl/MegIS.v, all Qed, 0 admits): the coarse-run predicate
ISPRunsSound couples a coarse run (a,(b,len)) to the base l2p_map.
  unwrapped_gc_breaks_coarse_runs, unwrapped_wear_level_breaks_coarse_runs and
  unwrapped_write_breaks_coarse_runs : relocating a page inside a run falsifies it.
  isp_ok_gc, isp_ok_wear_level and isp_ok_write : the wrapped operations (drop the
  touched run) preserve it.
  Also fixes a real MegIS gap: its user_write never dropped stale runs.

On-silicon (DaisyPlus, ATTACK_MEGIS mode in gr3ftl): a coarse run over LSA[4096,4112)
caches the range translation; reads in range use the run (fast path). A write to a slice
in the range relocates it (fine L2P updated).
  ftl_megis_attack_headless.elf  : run left stale -> read slice3 = OLD (1f629829..) STALE
  ftl_megis_checked_headless.elf : write drops run  -> read slice3 = NEW (08cee9fe..) CORRECT
  (overwrite new = 08cee9fe.., old = 1f629829..). Same board, same scripts/megis_demo.sh;
  only the CERTIFLASH_GUARD (drop stale run on write) differs. Mirrors isp_ok_write.
  Scripts: boot_megis_{attack,checked}.tcl, megis_demo.sh. Source edits in redirect project
  address_translation.c/ftl_config.h (ATTACK_MEGIS=13).
