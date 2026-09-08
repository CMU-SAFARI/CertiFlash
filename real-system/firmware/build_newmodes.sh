#!/usr/bin/env bash
# Build the four new demo firmwares (dftl/dedup x attack/checked) from the
# gr3ftl tree, headless-patch each, and stage them.  Restores
# ftl_config.h to the original ATTACK_MEGIS + CERTIFLASH_GUARD 1 state and
# rebuilds so the tree and build/ftl.elf are left exactly as found.
set -euo pipefail

# Edit for your local build tree:
WS="${WS:-/path/to/openssd/DaisyPlus/2025.1/Micron_NAND/PS_LPDDR4_B/ws2}"
OUT="${OUT:-/path/to/build}"

# The generated link rule invokes aarch64-none-elf-size bare; put the GNU
# aarch64 toolchain bin on PATH so the post-link size step resolves.
export PATH=/tools/2025.1/gnu/aarch64/lin/aarch64-none/bin:/tools/2025.1/Vitis/gnu/aarch64/lin/aarch64-none/bin:$PATH

FTL=$WS/ftl
SRC="$FTL/run-gr3ftl/src"
BUILD="$FTL/build"
CFG="$SRC/ftl_config.h"
CMAKE=/usr/bin/cmake
HDL=$OUT/headless_any.py
BK=$OUT/src_backup/newmodes_backup
mkdir -p "$BK"

# Preserve pristine copies of the two files this run touches.
[ -f "$BK/ftl_config.h.orig" ]         || cp "$CFG" "$BK/ftl_config.h.orig"
[ -f "$BK/address_translation.c.orig" ] || cp "$SRC/address_translation.c" "$BK/address_translation.c.orig"

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
	echo "--- baked config strings (DWARF):"
	strings "$OUT/${out}_headless.elf" | grep -E "ATTACK_MODE ATTACK_|CERTIFLASH_GUARD [01]" | sort -u | head
}

build_one ATTACK_DFTL  0 ftl_dftl_attack
build_one ATTACK_DFTL  1 ftl_dftl_checked
build_one ATTACK_DEDUP 0 ftl_dedup_attack
build_one ATTACK_DEDUP 1 ftl_dedup_checked

echo "==================== restore active mode to original MegIS-checked state ===================="
# Keep the new mode definitions in the tree; just reset the ACTIVE mode+guard
# so build/ftl.elf is rebuilt byte-for-byte as the original MegIS-checked FTL.
set_mode ATTACK_MEGIS; set_guard 1
grep -E "define ATTACK_MODE[[:space:]]|define CERTIFLASH_GUARD[[:space:]]" "$CFG"
"$CMAKE" --build "$BUILD" -j4
echo "restored build/ftl.elf strings:"; strings "$BUILD/ftl.elf" | grep -E "ATTACK_MODE ATTACK_|CERTIFLASH_GUARD [01]" | sort -u | head

echo "==================== staged files ===================="
ls -la $OUT/ftl_dftl_*.elf $OUT/ftl_dedup_*.elf
echo "ALL BUILDS DONE"
