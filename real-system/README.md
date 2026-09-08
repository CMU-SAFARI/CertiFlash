# On-silicon experiments (DaisyPlus OpenSSD)

This directory holds the host-side scripts, firmware patch, and JTAG boot files
for the on-silicon experiments in the paper. They reproduce the modeled failure
surfaces on a real SSD over the standard NVMe interface: a modified FTL, running
ordinary host I/O with no privileged access, drives the device into a state that
violates the global invariant.

These board experiments demonstrate the **attacks** on real silicon. Prevention
is not claimed on hardware — the guarantee that a certified FTL cannot reach any
of these states is the mechanized proof (the per-instruction precondition
bundles) in the rest of this repository, which stands on its own and needs no
hardware.

## Hardware

- **Board.** DaisyPlus OpenSSD: Xilinx Zynq UltraScale+ ZU17EG, Micron NAND,
  running the open-channel FTL `gr3ftl` with its NVMe controller in firmware.
  It attaches to a Linux host over PCIe and enumerates as an ordinary NVMe SSD.
- **Addressing.** The FTL maps in 16 KiB slices of four 4 KiB blocks, so a
  logical slice address is `LSA = NVMe LBA / 4`. Tenants are logical-address
  ranges.
- **Toolchain.** Xilinx Vitis 2025.1 (`xsct` for JTAG boot) on the board host;
  the `nvme` CLI on the NVMe host.

## Acknowledgement

The board experiments run on the DaisyPlus OpenSSD platform and its reference
flash translation layer, `gr3ftl` (GreedyFTL v3), from the OpenSSD Project:

- CRZ Technology, *DaisyPlus OpenSSD Platform*.
  <https://github.com/CRZ-Technology/OpenSSD-OpenChannelSSD>
- Jaewook Kwak, Sangjin Lee, Kibin Park, Jinwoo Jeong, and Yong Ho Song,
  *"Cosmos+ OpenSSD: Rapid Prototype for Flash Storage Systems,"* ACM
  Transactions on Storage (TOS), 2020.

`firmware/` holds patches against that tree and the JTAG boot scripts. The
platform sources and the FTL are not redistributed here; obtain them from the
OpenSSD Project and apply the patches on top.

## Safety

Every demo script targets `/dev/nvme0n1` only, and aborts unless the NVMe model
string is DaisyPlus / OpenSSD. It never touches any other device. On the test
host `/dev/nvme1` is the machine's own boot disk; the scripts never address it.
Read the model-guard block at the top of each script before running.

## Layout

```
real-system/
  scripts/        host-side demo drivers (issue NVMe I/O, compare digests)
  firmware/       gr3ftl source patch + build, and JTAG boot scripts
    apply_newmodes.py    patches ftl_config.h + address_translation.c
    build_newmodes.sh    rebuilds the attack firmware ELFs
    boot/                xsct/xsdb boot scripts, one per firmware build
  docs/           runbook and result logs from the board runs
```

The firmware ELFs are ~630 KB build products and are **not** checked in.
`firmware/build_newmodes.sh` regenerates them from the gr3ftl tree after
`firmware/apply_newmodes.py` applies the source patch.

## What each demo shows, and the failure surface it maps to

| Demo script            | Paper | Violation                              | Invariant violated |
|------------------------|-------|----------------------------------------|--------------------|
| `alias_demo3.sh`       | FS#2  | L2P aliasing: attacker LSA reads victim slice | Inv2 (L2P injectivity) |
| `all_attacks_demo.sh`  | FS#2  | alias + redirect, both L2P aliasing at different layers | Inv2 |
| `dftl_demo.sh`         | FS#2  | DFTL demand page-in resolves attacker LSA to victim slice | Inv2 |
| `dedup_demo.sh`        | FS#3/5| cross-namespace dedup: tenant B read served from tenant A slice | Inv7 (namespace isolation) |
| `megis_demo.sh`        | eval  | MegIS coarse run left stale after a relocation | coarse-run local invariant |
| `fs1_demo.sh`          | FS#1  | HIL queue: erase a still-mapped block (Inv5) + out-of-range block index (Inv8) | Inv5, Inv8 (UART self-test) |
| `fs2_demo.sh`          | FS#2  | internal DRAM: intra-address L2P alias (Inv2) + namespace reassignment (Inv7) | Inv2, Inv7 |
| `fs3_demo.sh`          | FS#3  | embedded compute: ownership override + namespace-enforcement override | Inv7 (both) |
| `fs4_demo.sh`          | FS#4  | flash controller: page marked live with no integrity tag (Inv9) | Inv9 (UART self-test) |
| `fs5_demo.sh`          | FS#5  | NAND free-list: push a block already free (Inv11) | Inv11 (UART self-test) |
| `verify_only.sh`       | -     | host-side verification helper                 | - |

The five `fs#_demo.sh` scripts cover the paper's ten violations across the five
failure surfaces. FS#2(a) L2P cross-address aliasing (Inv2) is already shown by
the alias family above, and FS#5(b) cross-namespace NAND write (Inv7) by
`dedup_demo.sh`, so the per-surface scripts add the other eight. **Metadata-only
violations (FS#1, FS#4, FS#5(a)) do not surface as an attacker-LBA NVMe read
returning victim bytes**; there is no host-side sha diff for them. They are shown
via the firmware's boot-time UART self-test of the violated invariant clause,
which prints `PASS`/`VIOLATION`; the `fs1/fs4/fs5` scripts trigger it with one
read and grep the saved UART log. See `docs/RUNBOOK_onsilicon_all_surfaces.md` for
the full classification table, demo LSAs, and per-firmware run sequence.
