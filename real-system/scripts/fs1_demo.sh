#!/usr/bin/env bash
# FS#1 (HIL request queue) on-silicon demo on the DaisyPlus OpenSSD.
# Both FS#1 violations corrupt INTERNAL metadata and do NOT surface as an
# attacker-LBA NVMe read returning victim bytes, so there is no host-side sha
# diff to compare.  The verdict is the firmware's boot-time UART self-test:
#   FS#1(a) HIL mapping injection  (Inv5): PrimErase a still-mapped block.
#   FS#1(b) HIL queue overflow     (Inv8): PrimErase an out-of-range block index.
# This script (1) confirms the device is the DaisyPlus and alive, (2) issues one
# NVMe read to trigger the one-shot self-test if it has not run yet, then
# (3) greps the SAVED UART LOG for the PASS / VIOLATION / REFUSED lines.
# You MUST capture the board UART to a file first (see RUNBOOK_onsilicon_all_surfaces.md):
#   export UARTLOG=~/fs1_uart.log      # picocom/screen/xsdb jtaguart capture
# DaisyPlus-only guard; /dev/nvme0n1 only.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
UARTLOG=${UARTLOG:-$HOME/fs1_uart.log}
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# Trigger the one-shot self-test with a single slice read (self-test runs on the
# first AddrTransRead after boot).  LSA 5344 -> LBA 21376.
TRIGGER_LBA=21376; NBLK=3; SZ=16384
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
  echo "Expected lines -- attack fw:  [FS1a] VIOLATION ... / [FS1b] VIOLATION ..."
  echo "                  checked fw: [CERTIFLASH] FS1a REFUSED ... / FS1b REFUSED ..."
  exit 2
fi
echo "UART log: $UARTLOG"
echo "--- FS#1 self-test lines ---"
grep -E "\[(CERTIFLASH|FS1a|FS1b)\].*(FS1a|FS1b|Inv5|Inv8)" "$UARTLOG" || echo "(no FS#1 self-test lines found -- did the self-test run? re-read to trigger it)"
echo "----------------------------"
if grep -q "\[FS1a\] VIOLATION" "$UARTLOG" && grep -q "\[FS1b\] VIOLATION" "$UARTLOG"; then
  echo ">>> FS#1 ATTACK build: Inv5 and Inv8 both VIOLATED (metadata corruption confirmed at boot)."
elif grep -q "FS1a REFUSED" "$UARTLOG" && grep -q "FS1b REFUSED" "$UARTLOG"; then
  echo ">>> FS#1 CHECKED build: Inv5 and Inv8 checks REFUSED both violations (prevented)."
else
  echo ">>> FS#1 verdict inconclusive -- inspect the lines above against the expected set."
fi
echo "=================================================="
