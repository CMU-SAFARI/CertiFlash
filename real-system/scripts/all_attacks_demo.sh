#!/usr/bin/env bash
# Drives the 3 host-observable FTL attacks on the DaisyPlus OpenSSD and prints a
# per-attack verdict. Works on both the attack firmware (leak/corrupt) and the
# checked firmware (refused). DaisyPlus-only safety guard.
set -u
DEV=/dev/nvme0; NS=/dev/nvme0n1
MODEL=$(nvme id-ctrl "$DEV" 2>/dev/null | awk -F: '/^mn /{sub(/^[ ]+/,"",$2);print $2}')
echo "Target $DEV model: [$MODEL]"
case "$MODEL" in *DaisyPlus*|*OpenSSD*) : ;; *) echo "ABORT: not DaisyPlus (got '$MODEL')."; exit 1;; esac
WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT

# LSA = LBA/4.  victim 1024=LBA4096, alias 2048=8192, redirect 2064=8256, retarget 2096=8384, control 3072=12288
VICTIM=4096; ALIAS=8192; REDIR=8256; RETARG=8384; CTRL=12288; PAD=100000
CNT=3; SZ=16384
python3 - "$WORK" <<'PY'
import sys,os; w=sys.argv[1]
open(os.path.join(w,"victim.bin"),"wb").write((b"VICTIM-SECRET!! tenant A private data. "*500)[:16384])
open(os.path.join(w,"control.bin"),"wb").write((b"CONTROL-neutral tenant C block. "*600)[:16384])
open(os.path.join(w,"attk.bin"),"wb").write((b"ATTACKER-TAMPER payload owns you. "*600)[:16384])
open(os.path.join(w,"pad.bin"),"wb").write((b"PADDING-flush "*80000)[:1048576])
PY
# MDTS-safe chunk probe
CHUNK=0; for c in 256 128 64 32 16 8 4; do
  nvme write "$NS" --start-block=200000 --block-count=$((c-1)) --data-size=$((c*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1 && { CHUNK=$c; break; }; done
[ "$CHUNK" -gt 0 ] || { echo "no working chunk"; exit 1; }
w1(){ nvme write "$NS" --start-block=$1 --block-count=$CNT --data-size=$SZ --data="$2" >/dev/null 2>&1; }
r1(){ nvme read  "$NS" --start-block=$1 --block-count=$CNT --data-size=$SZ --data="$2" >/dev/null 2>&1; }
flush(){ local lba=$PAD b=0 t=$((1024*4)); while [ $b -lt $t ]; do local st=$CHUNK; [ $((b+st)) -gt $t ] && st=$((t-b));
  nvme write "$NS" --start-block=$lba --block-count=$((st-1)) --data-size=$((st*4096)) --data="$WORK/pad.bin" >/dev/null 2>&1; lba=$((lba+st)); b=$((b+st)); done; nvme flush "$NS" >/dev/null 2>&1; }
sha(){ sha256sum "$1"|awk '{print $1}'; }

echo "== setup: write victim secret + control, flush to NAND =="
w1 $VICTIM "$WORK/victim.bin"; w1 $CTRL "$WORK/control.bin"; flush
r1 $VICTIM "$WORK/victim.read"; r1 $CTRL "$WORK/control.read"
V=$(sha "$WORK/victim.read"); C=$(sha "$WORK/control.read")
echo "   victim=$V"; echo "   control=$C"

echo "== ATTACK 1 (ALIAS, LSA2048/LBA8192): read attacker's own address =="
r1 $ALIAS "$WORK/alias.read"; A1=$(sha "$WORK/alias.read")
echo "   alias.read=$A1"
[ "$A1" = "$V" ] && echo "   >>> ALIAS: LEAK (attacker read == victim secret)" || echo "   >>> ALIAS: refused (attacker read != victim)"

echo "== ATTACK 2 (REDIRECT, LSA2064/LBA8256): read attacker address, offset-mapped to victim =="
r1 $REDIR "$WORK/redir.read"; A2=$(sha "$WORK/redir.read")
echo "   redirect.read=$A2"
[ "$A2" = "$V" ] && echo "   >>> REDIRECT: LEAK (attacker read == victim secret)" || echo "   >>> REDIRECT: refused (attacker read != victim)"

echo "== ATTACK 3 (RAW_RETARGET, LSA2096/LBA8384 write): attacker write row-retargeted onto victim page =="
w1 $RETARG "$WORK/attk.bin"; flush
r1 $VICTIM "$WORK/victim2.read"; V2=$(sha "$WORK/victim2.read"); ATK=$(sha "$WORK/attk.bin")
echo "   victim.read (after attacker write)=$V2"
echo "   (victim before=$V ; attacker payload=$ATK)"
if [ "$V2" != "$V" ]; then echo "   >>> RAW_RETARGET: CORRUPTION (victim data changed by attacker write)"; else echo "   >>> RAW_RETARGET: refused (victim data intact)"; fi

echo "=================================================="
echo "SUMMARY: alias $([ "$A1" = "$V" ] && echo LEAK || echo refused) | redirect $([ "$A2" = "$V" ] && echo LEAK || echo refused) | retarget $([ "$V2" != "$V" ] && echo CORRUPT || echo refused)"
