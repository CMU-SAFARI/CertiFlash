# DaisyPlus OpenSSD bring-up notes

Three problems block a first boot of this board, in the order they appear. Each
one presents as a hang with no error message, so they are recorded here to save
the next person the diagnosis. Once past them the firmware reaches its
steady-state FTL loop and serves NVMe I/O, which is what the demos in
`../scripts/` drive.

## 1. DDR does not train: rank mismatch

The board is **LPDDR4 rev B, single-rank**. A dual-rank `psu_init`
(`ACTIVE_RANKS 0x3`) trains rank 0 through the coarse stages, then fails
data-training a rank 1 that is not populated:

    PGSR0 (0xFD080030) = 0x8064807f   WDERR(21) + REERR(22) set,
                                      data-eye DONE bits 7-11 never set
    DDRC STAT (0xFD070004) = 0x0      controller stuck in Init

A single-rank `psu_init` (`ACTIVE_RANKS 0x1`) trains clean:

    PGSR0 = 0x80008fff   all DONE bits (0-11) + VDONE + APLOCK, no errors
    DDRC STAT = 0x1      Normal mode

## 2. Firmware spins at NAND Read-ID: wrong NAND vendor

With DDR trained, a mismatched firmware loads and runs but spins at

    V2FReadIdSync+0x68 :  b <self>

waiting for a flash-controller status that never arrives, because it issues
Read-ID to a NAND part that is not present. This board carries **Micron** NAND;
use the Micron project (single-rank, matching the DDR fix), not the Toshiba one.
The core is halt-able rather than wedged here, so a PC sample over JTAG
identifies it.

DDR is not the cause of this hang: a JTAG memory test writes and reads
0xA5A5A5A5 correctly at 0x00100000, 0x10000000, 0x40000000 and 0x7FFF0000, the
full 2 GB span the firmware's `memory_map.h` uses.

## 3. Boot menu blocks on UART

The stock firmware waits in `inbyte()` at an interactive boot menu, and key `X`
triggers a full NAND format (`EraseTotalBlockSpace`); any other key boots
normally. The demo firmwares are patched **headless** so `inbyte()` returns a
fixed non-`X` value, which removes both the blocking wait and the need to halt
the core at run time. The boot scripts in `../firmware/boot/` assume the
headless build.

## A53 debug wedge

Repeatedly halting the core, or injecting keypresses at run time, can leave the
A53 debug domain wedged. The JTAG chain still enumerates and `psu_init` still
runs, but the FSBL download fails with

    Cortex-A53 #0: EDITR not ready / EDITR timeout
    Memory write error at 0xFFFC0000

`rst -system` and `rst -srst` do not clear it. A cold power-cycle does. Prefer
the headless firmware, which never needs a run-time halt.
