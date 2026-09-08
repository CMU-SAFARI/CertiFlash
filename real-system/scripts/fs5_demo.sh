#!/usr/bin/env bash
# FS#5 (NAND flash chips) on-silicon demo on the DaisyPlus OpenSSD.
# Violation shown here: free-block duplication (Inv11) -- PrimFreePush a block
# already on the free list.  This corrupts the free-list metadata and does NOT
# surface as an attacker-LBA NVMe read returning victim bytes, so the verdict is
# the firmware's boot-time UART self-test.
# The other FS#5 violation, cross-namespace NAND write (Inv7), IS host-observable
# and is already demonstrated by dedup_demo.sh (ATTACK_DEDUP) -- run that for 5(b).
# Capture the board UART to a file first (see RUNBOOK_onsilicon_all_surfaces.md):
#   export UARTLOG=~/fs5_uart.log
# DaisyPlus-only guard; /dev/nvme0n1 only.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
UARTLOG=${UARTLOG:-$HOME/fs5_uart.log}
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# Any read triggers the one-shot self-test; use a neutral scratch LSA (LBA 200000).
TRIGGER_LBA=200000; NBLK=3; SZ=16384
python3 -c "open('$WORK/pad.bin','wb').write((b'PADDING-flush '*80000)[:1048576])"
CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
echo "== issue one read (LBA $TRIGGER_LBA) to trigger the boot self-test =="
nvme read "$NS" --start-block=$TRIGGER_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/rd" >/dev/null 2>&1

echo; echo "===================== RESULT ====================="
if [ ! -f "$UARTLOG" ]; then
  echo "UART log not found: $UARTLOG"
  echo "Capture the board UART to that path (or set UARTLOG=...) and re-run."
  echo "Expected lines -- attack fw:  [FS5a] VIOLATION ... Inv11 falsified"
  echo "                  checked fw: [CERTIFLASH] FS5a REFUSED ... (Inv11)"
  exit 2
fi
echo "UART log: $UARTLOG"
echo "--- FS#5 self-test lines ---"
grep -E "\[(CERTIFLASH|FS5a)\].*(FS5a|Inv11)" "$UARTLOG" || echo "(no FS#5 self-test lines found -- re-read to trigger it)"
echo "----------------------------"
if grep -q "\[FS5a\] VIOLATION" "$UARTLOG"; then
  echo ">>> FS#5 ATTACK build: Inv11 VIOLATED (block duplicated on the free list)."
elif grep -q "FS5a REFUSED" "$UARTLOG"; then
  echo ">>> FS#5 CHECKED build: Inv11 check REFUSED the duplicate free-push (prevented)."
else
  echo ">>> FS#5 verdict inconclusive -- inspect the lines above against the expected set."
fi
echo "=================================================="
