#!/usr/bin/env bash
# FS#3 (embedded compute units) on-silicon demo on the DaisyPlus OpenSSD.
# Two host-observable violations, each an attacker NVMe read that returns the
# victim slice unless the checked build refuses the remap:
#   FS#3(a) ownership override (Inv7 ownership):
#           attacker LSA 6320 <- victim/owner LSA 6304 (same namespace 2);
#           attacker maps a page it does not own.
#   FS#3(b) namespace-enforcement override (Inv7 namespace projection):
#           attacker LSA 6336 (ns2) <- victim LSA 5312 (ns1).
#   attack  fw (CERTIFLASH_GUARD 0): attacker read == victim secret (LEAK).
#   checked fw (CERTIFLASH_GUARD 1): attacker read == attacker's OWN data
#                                    (remap refused).
# DaisyPlus-only guard; /dev/nvme0n1 only.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# LSA = NVMe LBA/4.
FS3A_VICTIM_LBA=25216; FS3A_ATTACKER_LBA=25280   # LSA 6304 / 6320 (ownership, ns2)
FS3B_VICTIM_LBA=21248; FS3B_ATTACKER_LBA=25344   # LSA 5312 (ns1) / 6336 (ns2)
PAD=100000; NBLK=3; SZ=16384

python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
open(os.path.join(w,"a_victim.bin"),"wb").write((b"FS3a-OWNER-VICTIM secret owned by another tenant. "*300)[:16384])
open(os.path.join(w,"a_attacker.bin"),"wb").write((b"FS3a-ATTACKER-OWN benign data. "*400)[:16384])
open(os.path.join(w,"b_victim.bin"),"wb").write((b"FS3b-NS1-VICTIM secret in namespace 1. "*400)[:16384])
open(os.path.join(w,"b_attacker.bin"),"wb").write((b"FS3b-NS2-ATTACKER own data in namespace 2. "*400)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])
PY

CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
w1(){ nvme write "$NS" --start-block=$1 --block-count=$NBLK --data-size=$SZ --data="$2" >/dev/null 2>&1; }
flush(){ local lba=$PAD b=0 t=$((1024*4)); while [ $b -lt $t ]; do local st=$CHUNK; [ $((b+st)) -gt $t ] && st=$((t-b));
  nvme write "$NS" --start-block=$lba --block-count=$((st-1)) --data-size=$((st*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; lba=$((lba+st)); b=$((b+st)); done; nvme flush "$NS" >/dev/null 2>&1; }
sha(){ sha256sum "$1"|awk '{print $1}'; }
verdict(){ if [ "$2" = "$3" ]; then echo ">>> $1: LEAK (attacker read == victim secret; remap installed)";
  elif [ "$2" = "$4" ]; then echo ">>> $1: refused (attacker read == its OWN data; remap denied)";
  else echo ">>> $1: matched neither (unexpected; re-run, buffer may not have evicted)"; fi; }

echo "== FS#3(a) setup: write owner-victim (LSA 6304) + attacker own (LSA 6320) =="
w1 $FS3A_VICTIM_LBA "$WORK/a_victim.bin"; w1 $FS3A_ATTACKER_LBA "$WORK/a_attacker.bin"
echo "== FS#3(b) setup: write ns1 victim (LSA 5312) + ns2 attacker own (LSA 6336) =="
w1 $FS3B_VICTIM_LBA "$WORK/b_victim.bin"; w1 $FS3B_ATTACKER_LBA "$WORK/b_attacker.bin"
flush

echo "== read attacker LSAs back (triggers the remap hooks) =="
nvme read "$NS" --start-block=$FS3A_ATTACKER_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/a_read" >/dev/null 2>&1
nvme read "$NS" --start-block=$FS3B_ATTACKER_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/b_read" >/dev/null 2>&1

AV=$(sha "$WORK/a_victim.bin"); AA=$(sha "$WORK/a_attacker.bin"); AR=$(sha "$WORK/a_read")
BV=$(sha "$WORK/b_victim.bin"); BA=$(sha "$WORK/b_attacker.bin"); BR=$(sha "$WORK/b_read")
echo; echo "===================== RESULT ====================="
echo "FS#3(a) owner-victim sha = $AV"
echo "FS#3(a) attacker own     = $AA"
echo "FS#3(a) attacker read    = $AR"; verdict "FS3a (Inv7 ownership override)" "$AR" "$AV" "$AA"
echo "FS#3(b) ns1 victim sha   = $BV"
echo "FS#3(b) ns2 attacker own = $BA"
echo "FS#3(b) attacker read    = $BR"; verdict "FS3b (Inv7 namespace-enforcement override)" "$BR" "$BV" "$BA"
echo "=================================================="
