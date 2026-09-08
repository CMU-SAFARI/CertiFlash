#!/usr/bin/env bash
# Deduplication cross-tenant-sharing demo on the DaisyPlus OpenSSD.
# Two tenants live in different NVMe namespaces (modeled per-LSA):
#   tenant A = LSA 5120 (namespace 1) ; tenant B = LSA 6144 (namespace 2).
# Both tenants write IDENTICAL content P, so a content-deduplicating FTL shares
# one physical slice: tenant B's logical slice is served from tenant A's
# physical slice.  Tenant A then privately overwrites its slice with a new
# secret Q (out of place).  Because B is served from A's *current* physical
# slice:
#   attack  fw (CERTIFLASH_GUARD 0): B's read returns Q -- tenant A's private
#                                    updated data (cross-tenant leak).
#   checked fw (CERTIFLASH_GUARD 1): Inv7 namespace-isolation check REFUSES the
#                                    cross-namespace share -> B reads its OWN
#                                    content P.
# DaisyPlus-only guard; /dev/nvme0n1 only.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# LSA = NVMe LBA/4.  tenant A LSA 5120 -> LBA 20480 ; tenant B LSA 6144 -> LBA 24576.
TA_LBA=20480; TB_LBA=24576; PAD=100000
NBLK=3; SZ=16384   # block-count 3 => 4 LBAs => one 16 KiB slice

python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
# P: the identical content both tenants write (dedup trigger).
open(os.path.join(w,"shared.bin"),"wb").write((b"DEDUP-SHARED-CONTENT both tenants write this. "*400)[:16384])
# Q: tenant A's later private secret.
open(os.path.join(w,"secretQ.bin"),"wb").write((b"DEDUP-TENANT-A-PRIVATE-Q updated secret only A wrote. "*400)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])
PY

CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
w1(){ nvme write "$NS" --start-block=$1 --block-count=$NBLK --data-size=$SZ --data="$2" >/dev/null 2>&1; }
flush(){ local lba=$PAD b=0 t=$((1024*4)); while [ $b -lt $t ]; do local st=$CHUNK; [ $((b+st)) -gt $t ] && st=$((t-b));
  nvme write "$NS" --start-block=$lba --block-count=$((st-1)) --data-size=$((st*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; lba=$((lba+st)); b=$((b+st)); done; nvme flush "$NS" >/dev/null 2>&1; }
sha(){ sha256sum "$1"|awk '{print $1}'; }

echo "== tenant A (LSA 5120 / LBA $TA_LBA) writes shared content P =="
w1 $TA_LBA "$WORK/shared.bin"
echo "== tenant B (LSA 6144 / LBA $TB_LBA) writes IDENTICAL content P (dedup trigger) =="
w1 $TB_LBA "$WORK/shared.bin"
flush
echo "== tenant A privately OVERWRITES its slice with secret Q =="
w1 $TA_LBA "$WORK/secretQ.bin"
flush

echo "== tenant B reads its slice (LSA 6144) back =="
nvme read "$NS" --start-block=$TB_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/readB" >/dev/null 2>&1

P=$(sha "$WORK/shared.bin"); Q=$(sha "$WORK/secretQ.bin"); R=$(sha "$WORK/readB")
echo; echo "===================== RESULT ====================="
echo "shared content P sha256 = $P"
echo "tenant-A secret Q sha256 = $Q"
echo "tenant-B read    sha256 = $R"
echo "tenant-B read first 48 bytes:"; head -c 48 "$WORK/readB"; echo
echo
if [ "$R" = "$Q" ]; then
  echo ">>> CROSS-TENANT LEAK: tenant B read tenant A's private secret Q via the shared slice (attack succeeded)."
elif [ "$R" = "$P" ]; then
  echo ">>> CORRECT: tenant B read its OWN content P; cross-namespace share refused (prevented)."
else
  echo ">>> read matched neither Q nor P (unexpected)."
fi
echo "=================================================="
