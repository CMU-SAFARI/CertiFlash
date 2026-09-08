#!/usr/bin/env bash
# Build the ten per-surface demo firmwares (fs1..fs5 x attack/checked) from the
# gr3ftl tree, headless-patch each, and stage them.  Mirrors
# build_newmodes.sh exactly.  Restores ftl_config.h to the original
# ATTACK_MEGIS + CERTIFLASH_GUARD 1 state and rebuilds so the tree and
# build/ftl.elf are left exactly as found.
#
# Prereq: the source must already carry the FS defs/hooks.  This script applies
# both patch scripts first (both idempotent): apply_newmodes.py adds
# ATTACK_DFTL/ATTACK_DEDUP (whose ATTACK_DEDUP=15 the surface patch anchors on),
# then apply_surface_modes.py adds ATTACK_FS1..ATTACK_FS5.
set -euo pipefail

# Edit for your local build tree:
WS="${WS:-/path/to/openssd/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2}"
OUT="${OUT:-/path/to/build}"

export PATH=/tools/2025.1/gnu/aarch64/lin/aarch64-none/bin:/tools/2025.1/Vitis/gnu/aarch64/lin/aarch64-none/bin:$PATH

HERE="$(cd "$(dirname "$0")" && pwd)"
FTL=$WS/ftl
SRC="$FTL/run-gr3ftl/src"
BUILD="$FTL/build"
CFG="$SRC/ftl_config.h"
CMAKE=/usr/bin/cmake
HDL=$OUT/headless_any.py
BK=$OUT/src_backup/surfacemodes_backup
mkdir -p "$BK"

# Preserve pristine copies of the two files the surface patch touches.
[ -f "$BK/ftl_config.h.orig" ]          || cp "$CFG" "$BK/ftl_config.h.orig"
[ -f "$BK/address_translation.c.orig" ] || cp "$SRC/address_translation.c" "$BK/address_translation.c.orig"

echo "==================== apply source patches (idempotent) ===================="
python3 "$HERE/apply_newmodes.py"
python3 "$HERE/apply_surface_modes.py"

set_mode()  { sed -i "s/#define ATTACK_MODE[[:space:]].*/#define ATTACK_MODE\t$1/" "$CFG"; }
set_guard() { sed -i "s/#define CERTIFLASH_GUARD[[:space:]].*/#define CERTIFLASH_GUARD\t$1/" "$CFG"; }

build_one() {
	local mode="$1" guard="$2" out="$3"
	echo "==================== build $out  (ATTACK_MODE=$mode CERTIFLASH_GUARD=$guard) ===================="
	set_mode "$mode"; set_guard "$guard"
	echo "--- config now:"; grep -E "define ATTACK_MODE[[:space:]]|define CERTIFLASH_GUARD[[:space:]]" "$CFG"
	"$CMAKE" --build "$BUILD" -j4
	cp -f "$BUILD/ftl.elf" "$OUT/${out}.elf"
	python3 "$HDL" "$BUILD/ftl.elf" "$OUT/${out}_headless.elf"
	echo "--- staged $OUT/${out}.elf and _headless.elf"
	strings "$OUT/${out}_headless.elf" | grep -E "ATTACK_MODE ATTACK_|CERTIFLASH_GUARD [01]" | sort -u | head
}

build_one ATTACK_FS1 0 ftl_fs1_attack
build_one ATTACK_FS1 1 ftl_fs1_checked
build_one ATTACK_FS2 0 ftl_fs2_attack
build_one ATTACK_FS2 1 ftl_fs2_checked
build_one ATTACK_FS3 0 ftl_fs3_attack
build_one ATTACK_FS3 1 ftl_fs3_checked
build_one ATTACK_FS4 0 ftl_fs4_attack
build_one ATTACK_FS4 1 ftl_fs4_checked
build_one ATTACK_FS5 0 ftl_fs5_attack
build_one ATTACK_FS5 1 ftl_fs5_checked

echo "==================== restore active mode to original MegIS-checked state ===================="
set_mode ATTACK_MEGIS; set_guard 1
grep -E "define ATTACK_MODE[[:space:]]|define CERTIFLASH_GUARD[[:space:]]" "$CFG"
"$CMAKE" --build "$BUILD" -j4
echo "restored build/ftl.elf strings:"; strings "$BUILD/ftl.elf" | grep -E "ATTACK_MODE ATTACK_|CERTIFLASH_GUARD [01]" | sort -u | head

echo "==================== staged files ===================="
ls -la $OUT/ftl_fs*_attack*.elf $OUT/ftl_fs*_checked*.elf
echo "ALL BUILDS DONE"
