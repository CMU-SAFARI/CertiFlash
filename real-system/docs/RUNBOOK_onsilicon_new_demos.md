# On-silicon RUNBOOK: DFTL demand-paging + Deduplication demos (DaisyPlus OpenSSD)

Prepared 2026-09-02. Mirrors the MegIS/alias on-silicon flow. These four
firmwares are STAGED and BUILT but NOT yet booted/run -- running them needs the
user physically at the board (cold power-cycle + JTAG boot). The paper's two
`\pending{}` placeholders get filled from the RESULT lines below once the runs
succeed.

Board: /dev/nvme0n1 = DaisyPlus OpenSSD only. NEVER target /dev/nvme1 (Kingston
boot disk). Every demo script hard-guards on model =~ DaisyPlus/OpenSSD and uses
/dev/nvme0n1 exclusively; it aborts on any other model.

## What was added (firmware source, gr3ftl tree)

Tree: `OpenSSD-DaisyPlus/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2/ftl/run-gr3ftl/src`
Two new ATTACK modes, mirroring ATTACK_MEGIS exactly (read-path hooks only, no
write-path/GC changes):

- `ATTACK_DFTL` (14): DFTL-style demand-paged mapping. A read of the attacker
  LSA (3088) misses the cached mapping table (CMT) and demand-pages in its L2P
  entry; the malicious page-in resolves it to the VICTIM slice (LSA 3072) -- an
  aliasing remap. Checked build enforces Inv2 injectivity on the paged-in entry
  via the reverse map and refuses the alias. `DftlDemandPageIn()` in
  address_translation.c.
- `ATTACK_DEDUP` (15): content dedup across tenants in different namespaces
  (A = LSA 5120 / ns1, B = LSA 6144 / ns2). Tenant B's read is served from
  tenant A's shared physical slice. Checked build refuses the cross-namespace
  share (Inv7 namespace isolation) via the reverse map + `DedupNsOfLsa()`.

Attack vs checked is a single-line toggle in ftl_config.h: `CERTIFLASH_GUARD`
0 (attack) / 1 (checked); `ATTACK_MODE` selects the mode. The tree is left set
to ATTACK_MEGIS + CERTIFLASH_GUARD 1 (original MegIS-checked state); the new
mode defs/code are inert under MegIS. The staged MegIS ELFs are untouched.

## Staged artifacts (all in the build output directory)

| firmware ELF (headless)              | mode         | guard | boot script                          | demo            |
|--------------------------------------|--------------|-------|--------------------------------------|-----------------|
| ftl_dftl_attack_headless.elf         | ATTACK_DFTL  | 0     | firmware/boot/boot_dftl_attack.tcl  | dftl_demo.sh  |
| ftl_dftl_checked_headless.elf        | ATTACK_DFTL  | 1     | firmware/boot/boot_dftl_checked.tcl | dftl_demo.sh  |
| ftl_dedup_attack_headless.elf        | ATTACK_DEDUP | 0     | firmware/boot/boot_dedup_attack.tcl | dedup_demo.sh |
| ftl_dedup_checked_headless.elf       | ATTACK_DEDUP | 1     | firmware/boot/boot_dedup_checked.tcl| dedup_demo.sh |

Each ELF is headless-patched (inbyte -> `mov w0,#0; ret`) so the JTAG boot
auto-proceeds with no UART wait and no core halt, exactly like the MegIS ELFs.
Non-headless copies (ftl_dftl_attack.elf, etc.) are also staged.

## Per-firmware run sequence (repeat for each of the four)

Do this once per firmware. A cold power-cycle before each boot avoids the A53
debug-domain wedge documented in BOARD_BRINGUP.md.

1. COLD POWER-CYCLE the board (full power off, then on) so the PMU/boot-ROM
   brings the APU debug domain up clean.

2. Boot the firmware over JTAG (from the build host):

       cd firmware/boot
       /tools/2025.1/Vitis/bin/xsct boot_dftl_attack.tcl      # <- the row's boot script

   Wait for it to reach "done - firmware running headless, core never halted"
   and `disconnect`. XSCT should exit 0.

3. Re-enumerate the board on the NVMe host (PCIe rescan of 01:00.0):

       sudo sh -c 'echo 1 > /sys/bus/pci/devices/0000:01:00.0/remove; sleep 2; echo 1 > /sys/bus/pci/rescan'
       nvme list        # confirm /dev/nvme0n1 shows model "DaisyPlus OpenSSD"

4. Run the matching demo (it re-checks the model and aborts if not DaisyPlus):

       sudo scripts/dftl_demo.sh          # for the two dftl_* firmwares
       sudo scripts/dedup_demo.sh         # for the two dedup_* firmwares

5. Record the RESULT block the script prints (the three sha256 lines + verdict).

## Expected results (fill the \pending{} from these)

### DFTL demand-paging (dftl_demo.sh)
- `ftl_dftl_attack_headless.elf`  : attacker read sha256 == victim secret sha256
  -> verdict "ALIASED ... (attack succeeded)". The demand-paged remap installs
  the alias; attacker LSA 3088 returns the victim's LSA-3072 data.
- `ftl_dftl_checked_headless.elf` : attacker read sha256 == attacker own sha256
  (!= victim) -> verdict "CORRECT ... injectivity refused the aliasing remap".
  Confirms the injectivity guard holds under demand paging.

### Deduplication cross-tenant (dedup_demo.sh)
Both tenants first write identical content P; tenant A then privately overwrites
with secret Q; tenant B reads.
- `ftl_dedup_attack_headless.elf`  : tenant-B read sha256 == tenant-A secret Q
  sha256 -> verdict "CROSS-TENANT LEAK". B is served from A's shared physical
  slice and sees A's private update.
- `ftl_dedup_checked_headless.elf` : tenant-B read sha256 == shared content P
  sha256 -> verdict "CORRECT ... cross-namespace share refused". Inv7 namespace
  check gives B its own slice.

The single-variable flip (CERTIFLASH_GUARD off->on, same board, same NVMe
sequence) attributes the prevention to the Inv2 (DFTL) / Inv7 (dedup) check,
matching the MegIS/alias methodology.

## Write-buffer note (same as MegIS/alias)

gr3ftl buffers writes in DRAM (hash = LSA % (16*USER_DIES)); an NVMe Flush alone
does NOT always commit a slice to NAND. Both demo scripts therefore issue ~4096
padding LBAs (MDTS-safe chunks, auto-sized) to evict the write buffer before the
aliased/stale read. If a read returns neither expected value ("matched neither"),
the buffer was not fully evicted -- rerun; the padding size can be increased.

## If a boot fails

- FSBL download fails / "EDITR not ready": debug domain is wedged -> cold
  power-cycle and retry (do not repeatedly rst over JTAG).
- `nvme list` does not show DaisyPlus after rescan: reboot the NVMe host so it
  enumerates the board with CSTS.RDY set, then rescan again.
- Re-staging a rebuilt ELF only changes the `retry_dow .../ftl_*_headless.elf`
  line in the boot script; everything else (bitstream, psu_init, FSBL) is shared
  with the MegIS boot scripts and must not change.

## RESULT LOG (to be filled on the board)

    DFTL   attack  : attacker.read sha = ____  (== victim? ____)
    DFTL   checked : attacker.read sha = ____  (== attacker own? ____)
    DEDUP  attack  : tenantB.read  sha = ____  (== A secret Q? ____)
    DEDUP  checked : tenantB.read  sha = ____  (== shared P? ____)
