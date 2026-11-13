#!/bin/sh
# The engine library node_worker links (REORGANIZATION_PLAN.md S8), built on Linux.
#
# On the macOS build machine this is `build_hybrid_v3.py --engine-abi VARIANT`, which replays the
# recorded Homebrew/clang commands and cannot run on Linux. This script does the same two things
# against the Linux build of deployment/vm_pair_test/build_linux.sh (run first, from the bundle):
#   1. compile handshake_backend/EmpHybridWork/engine_abi.cpp (with legacy_abi.cpp and through it
#      tls_worker_v3.cpp) with the flags build_linux.sh gives the workers, and archive it with the
#      field engine object of the same mode (no EMP_HYBRID_TEST_FAULTS: production);
#   2. write the link arguments, one per line, that node_worker/build.rs passes to the linker.
#
#   build_engine_abi.sh BUNDLE SRC OUT WORD_DIR VARIANT      VARIANT: v3 | sh-v3
#
# BUNDLE: the unpacked make_bundle.py tree after build_linux.sh; SRC: the repository sources;
# OUT: where libengine-abi-VARIANT.a and engine-abi-link-VARIANT.txt go (NODE_WORKER_ENGINE_DIR);
# WORD_DIR: the run-time path of the word circuits, compiled in (EMP_WORD_CIRCUIT_DIR); the worker
# image mounts the word-circuit volume there. The -test variants are never built here.
set -eu
BUNDLE=$1; SRC=$2; OUT=$3; WORD_DIR=$4; VARIANT=$5
CXX=${CXX:-clang++}
INSTALL=$BUNDLE/install
MP=$BUNDLE/engines/MP-SPDZ
LIB_DIR=${RUNTIME_LIB_DIR:-/opt/tls-mpc/lib}
mkdir -p "$OUT"
case "$VARIANT" in
v3) SH=; FIELD_OBJECT=$BUNDLE/build/obj/field_engine.o ;;
sh-v3) SH=-DEMP_HYBRID_SEMI_HONEST=1; FIELD_OBJECT=$BUNDLE/build/obj/field_engine-sh.o ;;
*) echo "build_engine_abi.sh: VARIANT is v3 or sh-v3 (the -test variants are not deployable)" >&2; exit 2 ;;
esac
[ -f "$FIELD_OBJECT" ] || { echo "missing $FIELD_OBJECT: run build_linux.sh first" >&2; exit 1; }
if grep -q EMP_TEST_NATIVE_OPEN_MAC "$FIELD_OBJECT"; then
    echo "$FIELD_OBJECT contains the test-fault hook: refusing (SECURITY_MAP A.7)" >&2; exit 1
fi
# What emp-tool tells its users to compile with (as build_linux.sh and build_hybrid_v3.py read it).
EMP_OPTIONS=$(sed -n 's/.*INTERFACE_COMPILE_OPTIONS "\([^"]*\)".*/\1/p' "$INSTALL/lib/cmake/emp-tool/emp-toolTargets.cmake" | head -n 1 | tr ';' ' ')
[ -n "$EMP_OPTIONS" ] || { echo "emp-tool compile options not found" >&2; exit 1; }
# The workers' flags of build_linux.sh (FIXTURE_FLAGS) plus the word-circuit directory and the
# pins headers, as build_hybrid_v3.py's WORD list.
$CXX -std=c++20 -O3 -DNDEBUG $EMP_OPTIONS -DEMP_CONTEXT_CHECKS=1 -DEMP_HYBRID_STATISTICAL=128 \
    -I"$BUNDLE/pins/curve" -I"$BUNDLE/pins/word" "-DEMP_WORD_CIRCUIT_DIR=\"$WORD_DIR\"" $SH \
    -I"$BUNDLE/engines/emp-ag2pc-validated-v3" -I"$INSTALL/include" \
    -c "$SRC/handshake_backend/EmpHybridWork/engine_abi.cpp" -o "$OUT/engine-abi-$VARIANT.o"
rm -f "$OUT/libengine-abi-$VARIANT.a"
ar rcs "$OUT/libengine-abi-$VARIANT.a" "$OUT/engine-abi-$VARIANT.o" "$FIELD_OBJECT"
# Link arguments: build_linux.sh's FIELD_LIBS (the field engine's library, its OT objects,
# SimplestOT, libOTe in one group, the system libraries) with the run-time library directory in
# place of the build tree, then EMP's libraries and the C++ runtime.
OT_OBJECTS="OT/BaseOT.o OT/BitDiagonal.o OT/MascotParams.o OT/OTExtension.o OT/OTExtensionWithMatrix.o OT/OTTripleSetup.o"
{
    echo "$MP/libSPDZ.so"
    for object in $OT_OBJECTS; do echo "$MP/$object"; done
    echo "$MP/deps/SimplestOT_C/ref10/libSimplestOT.a"
    echo "-Wl,--start-group"
    echo "$MP/local/lib/liblibOTe.a"
    echo "$MP/local/lib/libmacoro.a"
    echo "$MP/local/lib/libcryptoTools.a"
    echo "$MP/local/lib/libcoproto.a"
    echo "-Wl,--end-group"
    for lib in -lgmpxx -lgmp -lsodium -lssl -lcrypto -lboost_filesystem -lboost_iostreams -lboost_system; do echo "$lib"; done
    echo "-Wl,-rpath,$LIB_DIR"
    echo "-pthread"
    echo "-L$INSTALL/lib"
    echo "-lemp-ot"
    echo "-lemp-tool"
    echo "-lstdc++"
    # rustc links with -nodefaultlibs and puts -lc before these arguments; the static C libraries
    # above (SimplestOT: __stack_chk_guard, which aarch64 glibc defines in the dynamic loader)
    # need the C library again after them.
    echo "-lm"
    echo "-lc"
} >"$OUT/engine-abi-link-$VARIANT.txt"
echo "engine library $OUT/libengine-abi-$VARIANT.a ($(sha256sum "$OUT/libengine-abi-$VARIANT.a" | cut -c1-16)...), word circuits at $WORD_DIR"
