#!/usr/bin/env bash
# FS#2 (internal DRAM / L2P) on-silicon demo on the DaisyPlus OpenSSD.
# Two host-observable violations, each an attacker NVMe read that returns the
# victim slice unless the checked build refuses the remap:
#   FS#2(b) L2P aliasing, intra-address (Inv2 injectivity):
#           attacker LSA 5264 <- victim LSA 5248 (same namespace).
#   FS#2(c) namespace reassignment (Inv7 namespace isolation):
#           attacker LSA 6208 (ns2) <- victim LSA 5280 (ns1).
# FS#2(a) L2P aliasing cross-address (Inv2) is already demonstrated by
# alias_demo3.sh / all_attacks_demo.sh / dftl_demo.sh -- run those for 2(a).
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

# LSA = NVMe LBA/4 (16 KiB slice = 4x4 KiB).
FS2B_VICTIM_LBA=20992; FS2B_ATTACKER_LBA=21056   # LSA 5248 / 5264 (intra-address)
FS2C_VICTIM_LBA=21120; FS2C_ATTACKER_LBA=24832   # LSA 5280 (ns1) / 6208 (ns2)
PAD=100000; NBLK=3; SZ=16384

python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
open(os.path.join(w,"b_victim.bin"),"wb").write((b"FS2b-VICTIM-SECRET intra-address offset A. "*400)[:16384])
open(os.path.join(w,"b_attacker.bin"),"wb").write((b"FS2b-ATTACKER-OWN benign offset B data. "*400)[:16384])
open(os.path.join(w,"c_victim.bin"),"wb").write((b"FS2c-NS1-VICTIM secret in namespace 1. "*400)[:16384])
open(os.path.join(w,"c_attacker.bin"),"wb").write((b"FS2c-NS2-ATTACKER own data in namespace 2. "*400)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])
PY

# MDTS-safe chunk probe.
CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
w1(){ nvme write "$NS" --start-block=$1 --block-count=$NBLK --data-size=$SZ --data="$2" >/dev/null 2>&1; }
flush(){ local lba=$PAD b=0 t=$((1024*4)); while [ $b -lt $t ]; do local st=$CHUNK; [ $((b+st)) -gt $t ] && st=$((t-b));
  nvme write "$NS" --start-block=$lba --block-count=$((st-1)) --data-size=$((st*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; lba=$((lba+st)); b=$((b+st)); done; nvme flush "$NS" >/dev/null 2>&1; }
sha(){ sha256sum "$1"|awk '{print $1}'; }
verdict(){ # $1 label  $2 attacker-read-sha  $3 victim-sha  $4 attacker-own-sha
  if [ "$2" = "$3" ]; then echo ">>> $1: LEAK (attacker read == victim secret; remap installed)";
  elif [ "$2" = "$4" ]; then echo ">>> $1: refused (attacker read == its OWN data; remap denied)";
  else echo ">>> $1: matched neither (unexpected; re-run, buffer may not have evicted)"; fi; }

echo "== FS#2(b) setup: write victim (LSA 5248) + attacker own (LSA 5264) =="
w1 $FS2B_VICTIM_LBA "$WORK/b_victim.bin"; w1 $FS2B_ATTACKER_LBA "$WORK/b_attacker.bin"
echo "== FS#2(c) setup: write ns1 victim (LSA 5280) + ns2 attacker own (LSA 6208) =="
w1 $FS2C_VICTIM_LBA "$WORK/c_victim.bin"; w1 $FS2C_ATTACKER_LBA "$WORK/c_attacker.bin"
flush

echo "== read attacker LSAs back (triggers the remap hooks) =="
nvme read "$NS" --start-block=$FS2B_ATTACKER_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/b_read" >/dev/null 2>&1
nvme read "$NS" --start-block=$FS2C_ATTACKER_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/c_read" >/dev/null 2>&1

BV=$(sha "$WORK/b_victim.bin"); BA=$(sha "$WORK/b_attacker.bin"); BR=$(sha "$WORK/b_read")
CV=$(sha "$WORK/c_victim.bin"); CA=$(sha "$WORK/c_attacker.bin"); CR=$(sha "$WORK/c_read")
echo; echo "===================== RESULT ====================="
echo "FS#2(b) victim sha256   = $BV"
echo "FS#2(b) attacker own    = $BA"
echo "FS#2(b) attacker read   = $BR"; verdict "FS2b (Inv2 intra-address alias)" "$BR" "$BV" "$BA"
echo "FS#2(c) ns1 victim sha  = $CV"
echo "FS#2(c) ns2 attacker own= $CA"
echo "FS#2(c) attacker read   = $CR"; verdict "FS2c (Inv7 namespace reassignment)" "$CR" "$CV" "$CA"
echo "=================================================="
