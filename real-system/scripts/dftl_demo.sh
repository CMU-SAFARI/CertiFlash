#!/usr/bin/env bash
# DFTL demand-paged-mapping demo on the DaisyPlus OpenSSD.
# A victim slice (LSA 3072) holds a secret.  The attacker owns LSA 3088.
# The firmware models a DFTL cached-mapping-table (CMT) miss: reading the
# attacker LSA triggers a demand page-in of its mapping entry, which the
# malicious translation-page store resolves to the VICTIM's physical slice
# (an aliasing remap).
#   attack  fw (CERTIFLASH_GUARD 0): page-in installs the alias -> attacker read
#                                    returns the VICTIM's data.
#   checked fw (CERTIFLASH_GUARD 1): Inv2 injectivity check on the paged-in
#                                    entry (reverse map) REFUSES the alias ->
#                                    attacker read returns the attacker's OWN data.
# DaisyPlus-only guard; /dev/nvme0n1 only.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# LSA = NVMe LBA/4 (16 KiB slice = 4x4 KiB).
# victim LSA 3072 -> LBA 12288 ; attacker LSA 3088 -> LBA 12352.
VICTIM_LBA=12288; ATTACKER_LBA=12352; PAD=100000
NBLK=3; SZ=16384   # block-count 3 => 4 LBAs => one 16 KiB slice

python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
open(os.path.join(w,"victim.bin"),"wb").write((b"DFTL-VICTIM-SECRET private mapping data. "*500)[:16384])
open(os.path.join(w,"attacker.bin"),"wb").write((b"DFTL-ATTACKER-OWN benign attacker data. "*500)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])
PY

CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
w1(){ nvme write "$NS" --start-block=$1 --block-count=$NBLK --data-size=$SZ --data="$2" >/dev/null 2>&1; }
flush(){ local lba=$PAD b=0 t=$((1024*4)); while [ $b -lt $t ]; do local st=$CHUNK; [ $((b+st)) -gt $t ] && st=$((t-b));
  nvme write "$NS" --start-block=$lba --block-count=$((st-1)) --data-size=$((st*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; lba=$((lba+st)); b=$((b+st)); done; nvme flush "$NS" >/dev/null 2>&1; }
sha(){ sha256sum "$1"|awk '{print $1}'; }

echo "== write victim secret (LSA 3072 / LBA $VICTIM_LBA) =="
w1 $VICTIM_LBA "$WORK/victim.bin"
echo "== write attacker own data (LSA 3088 / LBA $ATTACKER_LBA) =="
w1 $ATTACKER_LBA "$WORK/attacker.bin"
flush

echo "== read attacker LSA 3088 back (this triggers the DFTL demand page-in) =="
nvme read "$NS" --start-block=$ATTACKER_LBA --block-count=$NBLK --data-size=$SZ --data="$WORK/readback" >/dev/null 2>&1

V=$(sha "$WORK/victim.bin"); A=$(sha "$WORK/attacker.bin"); R=$(sha "$WORK/readback")
echo; echo "===================== RESULT ====================="
echo "victim secret   sha256 = $V"
echo "attacker own    sha256 = $A"
echo "attacker read   sha256 = $R"
echo "attacker read first 48 bytes:"; head -c 48 "$WORK/readback"; echo
echo
if [ "$R" = "$V" ]; then
  echo ">>> ALIASED: attacker read returned the VICTIM secret via the demand-paged alias (attack succeeded)."
elif [ "$R" = "$A" ]; then
  echo ">>> CORRECT: attacker read returned its OWN data; injectivity refused the aliasing remap (prevented)."
else
  echo ">>> read matched neither victim nor attacker (unexpected)."
fi
echo "=================================================="
