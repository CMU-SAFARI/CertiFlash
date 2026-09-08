# On-silicon RUNBOOK: all five failure surfaces (DaisyPlus OpenSSD)

Prepared 2026-09-04. Mirrors the MegIS/alias/DFTL/dedup on-silicon flow. These
firmwares are STAGED (source patch + boot scripts + host demo scripts) but NOT
yet built or booted/run: building needs the gr3ftl tree on the build host, and running
needs the user physically at the board (cold power-cycle + JTAG boot). Nothing
here has been executed on hardware.

Board: `/dev/nvme0n1` = DaisyPlus OpenSSD only. NEVER target `/dev/nvme1`
(the host's own boot disk). Every demo script hard-guards on model =~
DaisyPlus/OpenSSD and uses `/dev/nvme0n1` exclusively; it aborts on any other
model.

## Scope: the ten violations across five surfaces

The paper defines five failure surfaces with ten violations. Two are already
demonstrated by earlier work in this directory; this runbook adds the other
eight, grouped into one firmware mode per surface.

| # | Surface | Violation | FTL instruction (precond. unchecked) | Invariant | How demonstrated | Status |
|---|---------|-----------|--------------------------------------|-----------|------------------|--------|
| FS#1(a) | HIL request queue | HIL mapping injection | PrimErase a still-mapped block | Inv5 | **UART self-test** | new (ATTACK_FS1) |
| FS#1(b) | HIL request queue | HIL queue overflow | PrimErase an out-of-range block index | Inv8 | **UART self-test** | new (ATTACK_FS1) |
| FS#2(a) | internal DRAM | L2P aliasing, cross-address | PrimMapAddr two addresses to one page | Inv2 | host-observable (NVMe read) | **already covered** (alias family / DFTL) |
| FS#2(b) | internal DRAM | L2P aliasing, intra-address | PrimMapAddr two offsets of one address to one page | Inv2 | **host-observable (NVMe read)** | new (ATTACK_FS2) |
| FS#2(c) | internal DRAM | namespace reassignment | PrimMapAddr an address to a page recorded under another namespace | Inv7 | **host-observable (NVMe read)** | new (ATTACK_FS2) |
| FS#3(a) | embedded compute units | ownership override | PrimMapAddr another tenant's address to a page it doesn't own | Inv7 | **host-observable (NVMe read)** | new (ATTACK_FS3) |
| FS#3(b) | embedded compute units | namespace-enforcement override | same, via the namespace projection | Inv7 | **host-observable (NVMe read)** | new (ATTACK_FS3) |
| FS#4 | flash controller | integrity-tag removal | PrimProgramRaw marks a page live with no tag | Inv9 | **UART self-test** | new (ATTACK_FS4) |
| FS#5(a) | NAND flash chips | free-block duplication | PrimFreePush a block already free | Inv11 | **UART self-test** | new (ATTACK_FS5) |
| FS#5(b) | NAND flash chips | cross-namespace NAND write | PrimMapAddr program+map a page for an address in another namespace | Inv7 | host-observable (NVMe read) | **already covered** (ATTACK_DEDUP) |

### Host-observable vs UART-only, and why

- **Host-observable (NVMe read/write diff).** FS#2(a,b,c), FS#3(a,b), FS#5(b).
  These are read-path remaps: the attacker's own LSA resolves to a victim/donor
  slice, so an ordinary NVMe read of the attacker LBA returns the victim's bytes
  (sha256 match). The demo script prints the victim/attacker-own/attacker-read
  digests and a LEAK-vs-refused verdict, exactly like `alias_demo3.sh`.
- **UART self-test only.** FS#1(a), FS#1(b), FS#4, FS#5(a). These falsify
  *metadata* invariants (erase precondition, queue-index bound, integrity tag,
  free-list uniqueness). The corruption is internal; it does NOT surface as a
  specific attacker-LBA read returning victim bytes, so there is no host sha diff
  to compare. The verdict is the firmware's boot-time UART self-test, which
  transcribes the invariant clause and prints `PASS` / `VIOLATION` (attack build)
  or `REFUSED` (checked build). The host script only triggers the self-test with
  one read and greps the saved UART log; it does NOT pretend an NVMe read
  observed the metadata corruption.

  Honesty note on FS#1(a): erasing a still-mapped block DOES destroy the
  victim's slice, so its effect is host-visible *in principle* (a later victim
  read would return erased NAND). We still demonstrate it via the self-test,
  because a faithful host-observable hook would have to issue a real `PrimErase`
  against live host data on the shared board -- unsafe, and outside the
  read-path-only discipline of the existing hooks (`PrimErase`'s API is not in
  the two files the patch touches). The self-test transcribes Inv5 over the map
  metadata the patch can reach.

### One mode per surface, not one per violation

The task brief says "one ATTACK_MODE per violation." A compiled ELF hosts
exactly one `ATTACK_MODE` (every hook is `#if (ATTACK_MODE == ...)`), and the
runnable deliverables (fs1..fs5 scripts, one attack+checked ELF per surface, one
boot `.tcl` per surface) are per surface. Those cannot both be literal, so the
firmware uses **one mode per surface** (`ATTACK_FS1..ATTACK_FS5`, 16..20,
continuing after `ATTACK_DEDUP=15`), and each mode carries a **separate,
individually `#if`-guarded, idempotent hook/self-test per violation**, each with
its own demo LSAs and its own PASS/VIOLATION/REFUSED line. See the header of
`firmware/apply_surface_modes.py`.

## What was added (firmware source, gr3ftl tree)

Tree: `OpenSSD-DaisyPlus/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2/ftl/run-gr3ftl/src`

`firmware/apply_surface_modes.py` patches `ftl_config.h` (mode selectors 16..20 +
demo LSAs/constants) and `address_translation.c` (read-path remap hooks for the
host-observable violations; boot-time `SurfaceSelfTestsOnce()` for the
metadata-only ones, run once on the first `AddrTransRead` after boot). It reuses
`DedupNsOfLsa` / `DEDUP_NS_SPLIT` (6000): LSA < 6000 is namespace 1, LSA >= 6000
is namespace 2. It anchors on `ATTACK_DEDUP=15` and the MegIS read block, so
`apply_newmodes.py` must have run first (`build_surface_modes.sh` runs both;
both are idempotent).

Attack vs checked is the single-line `CERTIFLASH_GUARD` toggle in `ftl_config.h`
(0 attack / 1 checked); `ATTACK_MODE` selects the surface. The tree is left set
to `ATTACK_MEGIS` + `CERTIFLASH_GUARD 1` (original state); the new defs/code are
inert under other modes. The staged MegIS/DFTL/dedup ELFs are untouched.

### Demo LSAs (LSA = NVMe LBA / 4)

| Violation | victim LSA (LBA) | attacker LSA (LBA) | namespaces |
|-----------|------------------|--------------------|-----------|
| FS#2(b) intra-address alias | 5248 (20992) | 5264 (21056) | both ns1 |
| FS#2(c) namespace reassignment | 5280 (21120) | 6208 (24832) | ns1 <- ns2 |
| FS#3(a) ownership override | 6304 (25216) | 6320 (25280) | both ns2 |
| FS#3(b) namespace-enforce override | 5312 (21248) | 6336 (25344) | ns1 <- ns2 |
| FS#1(a) erase still-mapped (self-test) | 5344 (21376) | -- | -- |
| FS#1(b) queue overflow (self-test) | idx 9001 vs cap 4096 | -- | -- |
| FS#4 integrity-tag (self-test) | 5376 (21504) | -- | -- |
| FS#5(a) free-block dup (self-test) | block 777 | -- | -- |

## Build (on the build host)

    cd firmware ; ./build_surface_modes.sh     # firmware/build_surface_modes.sh

Builds ten ELFs into the build output directory, headless-patches each (inbyte ->
`mov w0,#0; ret`, like the MegIS/DFTL ELFs), and restores the tree to the
MegIS-checked state. **ELFs are build products and are NOT checked in.**

## Staged artifacts (one attack + one checked ELF per surface)

| firmware ELF (headless)        | mode        | guard | boot script                 | demo         | class |
|--------------------------------|-------------|-------|-----------------------------|--------------|-------|
| ftl_fs1_attack_headless.elf    | ATTACK_FS1  | 0     | boot/boot_fs1_attack.tcl    | fs1_demo.sh  | UART self-test |
| ftl_fs1_checked_headless.elf   | ATTACK_FS1  | 1     | boot/boot_fs1_checked.tcl   | fs1_demo.sh  | UART self-test |
| ftl_fs2_attack_headless.elf    | ATTACK_FS2  | 0     | boot/boot_fs2_attack.tcl    | fs2_demo.sh  | host-observable |
| ftl_fs2_checked_headless.elf   | ATTACK_FS2  | 1     | boot/boot_fs2_checked.tcl   | fs2_demo.sh  | host-observable |
| ftl_fs3_attack_headless.elf    | ATTACK_FS3  | 0     | boot/boot_fs3_attack.tcl    | fs3_demo.sh  | host-observable |
| ftl_fs3_checked_headless.elf   | ATTACK_FS3  | 1     | boot/boot_fs3_checked.tcl   | fs3_demo.sh  | host-observable |
| ftl_fs4_attack_headless.elf    | ATTACK_FS4  | 0     | boot/boot_fs4_attack.tcl    | fs4_demo.sh  | UART self-test |
| ftl_fs4_checked_headless.elf   | ATTACK_FS4  | 1     | boot/boot_fs4_checked.tcl   | fs4_demo.sh  | UART self-test |
| ftl_fs5_attack_headless.elf    | ATTACK_FS5  | 0     | boot/boot_fs5_attack.tcl    | fs5_demo.sh  | UART self-test |
| ftl_fs5_checked_headless.elf   | ATTACK_FS5  | 1     | boot/boot_fs5_checked.tcl   | fs5_demo.sh  | UART self-test |

The `boot/*.tcl` files are byte-for-byte copies of `boot_dftl_attack.tcl` with
only the `retry_dow .../ftl_*_headless.elf` line changed; bitstream, psu_init and
FSBL are shared with the existing boot scripts and must not change.

## Per-firmware run sequence (repeat for each of the ten)

Do this once per firmware. A cold power-cycle before each boot avoids the A53
debug-domain wedge documented in BOARD_BRINGUP.md.

1. COLD POWER-CYCLE the board (full power off, then on).

2. (UART-only surfaces FS#1/FS#4/FS#5 only) Start capturing the board UART to a
   log BEFORE booting, so the boot-time self-test lines are recorded, e.g.:

       picocom -b 115200 /dev/ttyUSB1 | tee ~/fs1_uart.log      # FS#1
       # or the xsdb jtaguart, whichever the board exposes.

   The self-test also runs on the first NVMe read after boot (one-shot), so a
   capture started just before the demo script still works.

3. Boot the firmware over JTAG (from the build host):

       cd firmware/boot
       /tools/2025.1/Vitis/bin/xsct boot_fs1_attack.tcl        # <- the row's boot script

   Wait for "done - firmware running headless, core never halted" and
   `disconnect`. XSCT should exit 0.

4. Re-enumerate the board on the NVMe host (PCIe rescan of 01:00.0):

       sudo sh -c 'echo 1 > /sys/bus/pci/devices/0000:01:00.0/remove; sleep 2; echo 1 > /sys/bus/pci/rescan'
       nvme list        # confirm /dev/nvme0n1 shows model "DaisyPlus OpenSSD"

5. Run the matching demo (it re-checks the model and aborts if not DaisyPlus):

       sudo scripts/fs2_demo.sh                             # host-observable: prints sha verdict
       sudo UARTLOG=~/fs1_uart.log scripts/fs1_demo.sh      # UART-only: greps the saved log

6. Record the RESULT block the script prints (host-observable: the three sha256
   lines + verdict; UART-only: the grepped PASS/VIOLATION/REFUSED lines).

## Expected results (fill the paper's placeholders from these)

### Host-observable surfaces (fs2_demo.sh, fs3_demo.sh)

For each violation the script writes a victim slice, the attacker's own slice,
flushes to NAND, then reads the attacker LSA back:

- attack fw (`CERTIFLASH_GUARD 0`): `attacker read sha256 == victim sha256`
  -> verdict "LEAK". The remap installed the alias; the attacker's NVMe read
  returned the victim's bytes.
- checked fw (`CERTIFLASH_GUARD 1`): `attacker read sha256 == attacker-own sha256`
  (!= victim) -> verdict "refused". The transcribed Inv2/Inv7 clause denied the
  remap; the attacker read its own slice.

### UART-only surfaces (fs1_demo.sh, fs4_demo.sh, fs5_demo.sh)

Read from the boot UART log:

- attack fw: `[FS1a] VIOLATION ... Inv5`, `[FS1b] VIOLATION ... Inv8`,
  `[FS4] VIOLATION ... Inv9`, `[FS5a] VIOLATION ... Inv11`.
- checked fw: `[CERTIFLASH] FS1a REFUSED ... (Inv5)`, `FS1b REFUSED ... (Inv8)`,
  `FS4 REFUSED ... (Inv9)`, `FS5a REFUSED ... (Inv11)`.

The single-variable flip (`CERTIFLASH_GUARD` off->on, same board, same firmware,
same sequence) attributes the prevention to the transcribed invariant check,
matching the MegIS/alias/DFTL/dedup methodology.

## Write-buffer note (same as MegIS/alias)

gr3ftl buffers writes in DRAM; an NVMe Flush alone does NOT always commit a slice
to NAND. The host-observable demo scripts therefore issue ~4096 padding LBAs
(MDTS-safe chunks, auto-sized) to evict the write buffer before the aliased read.
If a read returns neither expected value ("matched neither"), the buffer was not
fully evicted -- rerun; the padding size can be increased.

## If a boot fails

- FSBL download fails / "EDITR not ready": debug domain is wedged -> cold
  power-cycle and retry (do not repeatedly rst over JTAG).
- `nvme list` does not show DaisyPlus after rescan: reboot the NVMe host, then
  rescan again.
- Re-staging a rebuilt ELF only changes the `retry_dow .../ftl_*_headless.elf`
  line in the boot script; everything else is shared with the existing boot
  scripts and must not change.

## RESULT LOG (to be filled on the board)

    FS2b  attack  : attacker.read sha = ____  (== victim? ____)
    FS2b  checked : attacker.read sha = ____  (== attacker own? ____)
    FS2c  attack  : attacker.read sha = ____  (== victim? ____)
    FS2c  checked : attacker.read sha = ____  (== attacker own? ____)
    FS3a  attack  : attacker.read sha = ____  (== victim? ____)
    FS3a  checked : attacker.read sha = ____  (== attacker own? ____)
    FS3b  attack  : attacker.read sha = ____  (== victim? ____)
    FS3b  checked : attacker.read sha = ____  (== attacker own? ____)
    FS1a  attack/checked : UART line = ____
    FS1b  attack/checked : UART line = ____
    FS4   attack/checked : UART line = ____
    FS5a  attack/checked : UART line = ____
