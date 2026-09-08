#!/usr/bin/env bash
# FS#4 (flash controller) on-silicon demo on the DaisyPlus OpenSSD.
# Violation: integrity-tag removal (Inv9) -- PrimProgramRaw marks a page live
# with no integrity tag.  The tag lives in out-of-band metadata that is NOT
# returned by a standard NVMe data read, so there is no host-side sha diff.
# The verdict is the firmware's boot-time UART self-test.
# Capture the board UART to a file first (see RUNBOOK_onsilicon_all_surfaces.md):
#   export UARTLOG=~/fs4_uart.log
# DaisyPlus-only guard; /dev/nvme0n1 only.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
UARTLOG=${UARTLOG:-$HOME/fs4_uart.log}
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# LSA 5376 -> LBA 21504.
TRIGGER_LBA=21504; NBLK=3; SZ=16384
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
  echo "Expected lines -- attack fw:  [FS4] VIOLATION ... Inv9 falsified"
  echo "                  checked fw: [CERTIFLASH] FS4 REFUSED ... (Inv9)"
  exit 2
fi
echo "UART log: $UARTLOG"
echo "--- FS#4 self-test lines ---"
grep -E "\[(CERTIFLASH|FS4)\].*(FS4|Inv9)" "$UARTLOG" || echo "(no FS#4 self-test lines found -- re-read to trigger it)"
echo "----------------------------"
if grep -q "\[FS4\] VIOLATION" "$UARTLOG"; then
  echo ">>> FS#4 ATTACK build: Inv9 VIOLATED (page marked live with no integrity tag)."
elif grep -q "FS4 REFUSED" "$UARTLOG"; then
  echo ">>> FS#4 CHECKED build: Inv9 check REFUSED the untagged mark-live (prevented)."
else
  echo ">>> FS#4 verdict inconclusive -- inspect the lines above against the expected set."
fi
echo "=================================================="
