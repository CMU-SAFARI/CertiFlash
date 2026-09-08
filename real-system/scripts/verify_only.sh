#!/bin/bash
# Edit these for your local Xilinx Vitis install and DaisyPlus build tree:
. "${VITIS:-/tools/Xilinx/Vitis/2025.1}/settings64.sh" 2>/dev/null
WS="${WS:-/path/to/openssd/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2}"
FSBL="$WS/daisyplus_new/zynqmp_fsbl/build/fsbl.elf"
BOOT_BIN="${BOOT_BIN:-$WS/BOOT.BIN}"
program_flash -f "$BOOT_BIN" -offset 0 -flash_type qspi-x8-dual_parallel -flash_density 512 -fsbl "$FSBL" -no_program -verify -url tcp:127.0.0.1:3121 2>&1 | grep -iE "Running FSBL|Finished|Verify|Successful|mismatch|ERROR"
echo "VERIFY_EXIT=$?"
