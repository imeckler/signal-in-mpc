#!/bin/bash
# Download a user-local Temurin JDK 25 (macOS aarch64) into third_party/jdk.
# Source: github.com/adoptium (allowed); checksum verified against the release's .sha256.txt.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
TP="$HERE/third_party"
VERSION_TAG="jdk-25.0.5%2B8"
FILE="OpenJDK25U-jdk_aarch64_mac_hotspot_25.0.5_8.tar.gz"
URL="https://github.com/adoptium/temurin25-binaries/releases/download/$VERSION_TAG/$FILE"
mkdir -p "$TP/downloads/jdk" "$TP/jdk"
if [ -x "$TP/jdk/current/Contents/Home/bin/java" ]; then
  echo "JDK already present: $TP/jdk/current"; exit 0
fi
curl -sSfL -o "$TP/downloads/jdk/$FILE" "$URL"
curl -sSfL -o "$TP/downloads/jdk/$FILE.sha256.txt" "$URL.sha256.txt"
expected="$(cut -d' ' -f1 < "$TP/downloads/jdk/$FILE.sha256.txt")"
actual="$(shasum -a 256 "$TP/downloads/jdk/$FILE" | cut -d' ' -f1)"
if [ "$expected" != "$actual" ]; then echo "JDK checksum mismatch" >&2; exit 1; fi
tar -xzf "$TP/downloads/jdk/$FILE" -C "$TP/jdk"
dir="$(find "$TP/jdk" -maxdepth 1 -type d -name 'jdk-25*' | head -n 1)"
ln -sfn "$dir" "$TP/jdk/current"
"$TP/jdk/current/Contents/Home/bin/java" -version
