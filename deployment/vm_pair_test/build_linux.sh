#!/bin/sh
# Build the benchmark (and, if the bundle carries their sources, the two workers) on Linux from
# the source bundle made by make_bundle.py. Run from anywhere; it works inside the bundle:
#
#     sh vm-pair/kit/build_linux.sh --packages      # first time: also installs distribution packages (root or sudo)
#     sh vm-pair/kit/build_linux.sh                 # later: rebuild only what is missing
#
# Tested layout: Ubuntu 24.04 LTS, clang 18. Options: --packages, --jobs N (default: cores),
# --portable (do not build for this exact CPU; see README "Building on Linux").
# Output: vm-pair/bin/{pair-bench,pair-bench-sh,rounds,rounds-sh[,tls-worker,tls-worker-sh]},
# logs in vm-pair/build/logs/. Nothing is installed outside vm-pair/ except the packages.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
JOBS=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)
PACKAGES=0; PORTABLE=0
while [ $# -gt 0 ]; do
    case "$1" in
    --packages) PACKAGES=1 ;;
    --portable) PORTABLE=1 ;;
    --jobs) shift; JOBS=$1 ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
    esac
    shift
done
CXX=${CXX:-clang++}; CC=${CC:-clang}
LOGS=$ROOT/build/logs; mkdir -p "$LOGS" "$ROOT/bin" "$ROOT/build/obj"
MP=$ROOT/engines/MP-SPDZ
INSTALL=$ROOT/install
SRC=$ROOT/repo/handshake_backend/EmpHybridWork

step() {   # step NAME COMMAND...: run with output to a log; on failure show the end of the log
    step_name=$1; shift          # (plain sh has no local variables: names here must not clash with `build`)
    printf '%s ... ' "$step_name"
    step_start=$(date +%s)
    if "$@" >"$LOGS/$step_name.log" 2>&1; then
        echo "ok ($(( $(date +%s) - step_start )) s)"
    else
        echo "FAILED; last lines of $LOGS/$step_name.log:"; tail -n 40 "$LOGS/$step_name.log"; exit 1
    fi
}

if [ "$PACKAGES" = 1 ]; then
    SUDO=; [ "$(id -u)" = 0 ] || SUDO=sudo
    export DEBIAN_FRONTEND=noninteractive
    step packages-update $SUDO apt-get update
    # Compiler and build tools; the libraries both engines link (OpenSSL, libsodium, GMP, Boost);
    # the tools the network tests use.
    step packages-install $SUDO apt-get install -y --no-install-recommends \
        build-essential clang cmake make git python3 pkg-config ca-certificates openssl \
        libssl-dev libsodium-dev libgmp-dev libboost-dev libboost-filesystem-dev libboost-iostreams-dev libboost-thread-dev libboost-system-dev \
        wireguard-tools iproute2 iputils-ping iperf3 mtr-tiny sysstat procps
fi

case "$(uname -m)" in
x86_64)
    ARCH=-march=native
    [ "$PORTABLE" = 1 ] && ARCH="-march=x86-64-v3 -maes -mpclmul"
    for flag in aes pclmulqdq sse4_2 avx2 bmi2; do
        grep -qw "$flag" /proc/cpuinfo || echo "WARNING: this CPU does not report '$flag'; the engines need AES-NI and PCLMUL and are built for AVX2"
    done ;;
aarch64)
    ARCH=-mcpu=native
    [ "$PORTABLE" = 1 ] && ARCH="-march=armv8-a+crypto+crc" ;;
*) echo "unsupported machine $(uname -m)" >&2; exit 1 ;;
esac
NATIVE=ON; [ "$PORTABLE" = 1 ] && NATIVE=OFF
echo "bundle $ROOT; compiler $($CXX --version | head -n 1); $ARCH; $JOBS jobs"
# libOTe's build runs `git show-ref`, `git fetch` and `git checkout PIN` in the source trees of
# its dependencies. The bundle ships those trees at their pins without history, each marked by
# a file .bundle-pinned; for such a tree the three commands have nothing to do. Everything else
# goes to the real git. Used for the libOTe step only.
mkdir -p "$ROOT/build/git-shim"
REAL_GIT=$(command -v git || echo /usr/bin/git)
cat >"$ROOT/build/git-shim/git" <<EOF
#!/bin/sh
if [ -f .bundle-pinned ]; then
    case "\${1:-}" in show-ref|fetch|checkout) echo "bundle tree at \$(cat .bundle-pinned): git \$1 skipped"; exit 0 ;; esac
fi
exec "$REAL_GIT" "\$@"
EOF
chmod 755 "$ROOT/build/git-shim/git"

# 1. Boolean engine libraries: emp-tool, then emp-ot against it. (The validated-v3 engine itself is headers.)
if [ ! -f "$INSTALL/lib/libemp-tool.a" ]; then
    step emp-tool-configure cmake -S "$ROOT/engines/emp-tool" -B "$ROOT/build/emp-tool" -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" -DCMAKE_INSTALL_PREFIX="$INSTALL" -DCMAKE_PREFIX_PATH="$INSTALL" \
        -DEMP_TOOL_BUILD_TESTS=OFF -DEMP_TOOL_BUILD_TOOLS=OFF -DEMP_TOOL_BUILD_BENCHMARKS=OFF -DEMP_TOOL_NATIVE_ARCH=$NATIVE
    step emp-tool-build cmake --build "$ROOT/build/emp-tool" --parallel "$JOBS"
    step emp-tool-install cmake --install "$ROOT/build/emp-tool"
fi
if [ ! -f "$INSTALL/lib/libemp-ot.a" ]; then
    step emp-ot-configure cmake -S "$ROOT/engines/emp-ot" -B "$ROOT/build/emp-ot" -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" -DCMAKE_INSTALL_PREFIX="$INSTALL" -DCMAKE_PREFIX_PATH="$INSTALL" \
        -DEMP_OT_BUILD_TESTS=OFF -DEMP_TOOL_BUILD_TOOLS=OFF
    step emp-ot-build cmake --build "$ROOT/build/emp-ot" --parallel "$JOBS"
    step emp-ot-install cmake --install "$ROOT/build/emp-ot"
fi
# What emp-tool tells its users to compile with (as build_hybrid_v3.py reads it on the build machine).
EMP_OPTIONS=$(sed -n 's/.*INTERFACE_COMPILE_OPTIONS "\([^"]*\)".*/\1/p' "$INSTALL/lib/cmake/emp-tool/emp-toolTargets.cmake" | head -n 1 | tr ';' ' ')
[ -n "$EMP_OPTIONS" ] || { echo "emp-tool compile options not found" >&2; exit 1; }
echo "emp-tool compile options: $EMP_OPTIONS"

# 2. Field engine library (MP-SPDZ): its shared library, six OT objects, SimplestOT, libOTe.
#    Machine settings as on the build machine (no AVX base OT, SoftSpoken OT through libOTe 2).
cat >"$ROOT/build/CONFIG.mine" <<EOF
CXX = $CXX
ARCH = $ARCH
AVX_OT = 0
USE_KOS = 0
USE_LIBOTE2 = 1
GDEBUG =
ERROR =
EOF
# (Its objects depend on this file: replace it only when it differs, or every run rebuilds them.)
cmp -s "$ROOT/build/CONFIG.mine" "$MP/CONFIG.mine" || cp "$ROOT/build/CONFIG.mine" "$MP/CONFIG.mine"
OT_OBJECTS="OT/BaseOT.o OT/BitDiagonal.o OT/MascotParams.o OT/OTExtension.o OT/OTExtensionWithMatrix.o OT/OTTripleSetup.o"
if [ ! -f "$MP/deps/SimplestOT_C/ref10/Makefile" ]; then
    step simplestot-configure sh -c "cd '$MP/deps/SimplestOT_C/ref10' && cmake ."
fi
if [ ! -f "$MP/local/lib/liblibOTe.a" ]; then
    step libote env "PATH=$ROOT/build/git-shim:$PATH" make -C "$MP" local/lib/liblibOTe.a
fi
step field-library make -C "$MP" -j "$JOBS" libSPDZ.so $OT_OBJECTS deps/SimplestOT_C/ref10/libSimplestOT.a
FIELD_LIBS="$MP/libSPDZ.so"
for object in $OT_OBJECTS; do FIELD_LIBS="$FIELD_LIBS $MP/$object"; done
FIELD_LIBS="$FIELD_LIBS $MP/deps/SimplestOT_C/ref10/libSimplestOT.a -Wl,--start-group $MP/local/lib/liblibOTe.a $MP/local/lib/libmacoro.a $MP/local/lib/libcryptoTools.a $MP/local/lib/libcoproto.a -Wl,--end-group"
FIELD_LIBS="$FIELD_LIBS -lgmpxx -lgmp -lsodium -lssl -lcrypto -lboost_filesystem -lboost_iostreams -lboost_system -Wl,-rpath,$MP -pthread"

# 3. Our field engine wrapper, statistical 128, in both modes (as build_hybrid_v3.py).
# No -DEMP_HYBRID_TEST_FAULTS: that test-only cheating hook stays out of these objects (SECURITY_MAP A.7).
FIELD_FLAGS="-std=c++20 -O3 $ARCH -DNO_AVX_OT -DUSE_GF2N_LONG -DEMP_HYBRID_NATIVE_SECURITY=128 -I$MP -I$MP/deps -I$MP/local/include -Wno-deprecated-literal-operator -Wno-deprecated-declarations -Wno-unknown-warning-option"
step field-engine $CXX $FIELD_FLAGS -c "$SRC/field_engine.cpp" -o "$ROOT/build/obj/field_engine.o"
step field-engine-sh $CXX $FIELD_FLAGS -DEMP_HYBRID_SEMI_HONEST=1 -c "$SRC/field_engine.cpp" -o "$ROOT/build/obj/field_engine-sh.o"

# 4. The fixtures (and the workers when their source is in the bundle).
FIXTURE_FLAGS="-std=c++20 -O3 -DNDEBUG $EMP_OPTIONS -DEMP_CONTEXT_CHECKS=1 -DEMP_HYBRID_STATISTICAL=128 -I$ROOT/pins/curve -I$ROOT/pins/word -I$ROOT/engines/emp-ag2pc-validated-v3 -I$INSTALL/include"
build() {   # build NAME SOURCE [sh]
    name=$1; source=$2; mode=${3:-}
    extra=; engine=$ROOT/build/obj/field_engine.o
    if [ "$mode" = sh ]; then extra=-DEMP_HYBRID_SEMI_HONEST=1; engine=$ROOT/build/obj/field_engine-sh.o; fi
    step "$name-compile" $CXX $FIXTURE_FLAGS "-DEMP_WORD_CIRCUIT_DIR=\"$ROOT/pins/word\"" $extra -c "$SRC/$source" -o "$ROOT/build/obj/$name.o"
    step "$name-link" $CXX -o "$ROOT/bin/$name" "$ROOT/build/obj/$name.o" "$engine" $FIELD_LIBS "-L$INSTALL/lib" -lemp-ot -lemp-tool
}
build pair-bench pair_bench_fixture.cpp
build pair-bench-sh pair_bench_fixture.cpp sh
build rounds rounds_fixture.cpp
build rounds-sh rounds_fixture.cpp sh
if [ -f "$SRC/tls_worker_v3.cpp" ]; then
    build tls-worker tls_worker_v3.cpp
    build tls-worker-sh tls_worker_v3.cpp sh
fi
echo "built: $(ls "$ROOT/bin" | tr '\n' ' ')"
echo "next: kit/bench_certs.sh, then kit/run_bench.py (README, part 3). A one-machine check: kit/selftest.sh"
