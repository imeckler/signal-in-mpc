#!/bin/bash
# Build Signal-Server (owner's pinned commit) for local runs. No packaging/jib/shade:
# compiles main + test classes and writes the runtime classpath to state/classpath.txt.
#
# Steps:
#   1. clone github.com/signalapp/Signal-Server into third_party/ if missing, check out $SIGNAL_SERVER_COMMIT
#   2. apply patches/*.patch (only if not already applied)
#   3. mvn test-compile service (+ websocket-resources in the same reactor); write test classpath
#
# Never contacts Signal-operated hosts: config/maven-settings.xml mirrors the
# `signal-build-artifacts` repository to Maven Central.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
TP="$HERE/third_party"
SRC="$TP/Signal-Server"
SIGNAL_SERVER_COMMIT="${SIGNAL_SERVER_COMMIT:-b9a24fede}"   # = /Users/izzy/repos/Signal-Server HEAD (2026-05-19)
export JAVA_HOME="$TP/jdk/current/Contents/Home"
export MAVEN_USER_HOME="$TP/maven-home"
M2="$TP/m2/repository"
mkdir -p "$HERE/state" "$HERE/logs" "$M2"

if [ ! -x "$JAVA_HOME/bin/java" ]; then bash "$HERE/scripts/fetch_jdk.sh"; fi
if [ ! -d "$SRC/.git" ]; then
  git clone --filter=blob:none https://github.com/signalapp/Signal-Server.git "$SRC"
fi
if [ "$(git -C "$SRC" rev-parse --short=9 HEAD)" != "$SIGNAL_SERVER_COMMIT" ]; then
  if [ -n "$(git -C "$SRC" status --porcelain --untracked-files=no)" ]; then
    echo "third_party/Signal-Server has local changes and is not at $SIGNAL_SERVER_COMMIT; resolve manually" >&2; exit 1
  fi
  git -C "$SRC" checkout -q "$SIGNAL_SERVER_COMMIT"
fi
for p in "$HERE"/patches/*.patch; do
  if git -C "$SRC" apply --check "$p" 2>/dev/null; then
    git -C "$SRC" apply "$p"; echo "applied $(basename "$p")"
  elif git -C "$SRC" apply --reverse --check "$p" 2>/dev/null; then
    echo "already applied $(basename "$p")"
  else
    echo "patch does not apply: $p" >&2; exit 1
  fi
done

MVN=("$SRC/mvnw" -B -e -s "$HERE/config/maven-settings.xml" "-Dmaven.repo.local=$M2" -f "$SRC/pom.xml")
# The root pom skips maven-install-plugin, so build service and its sibling module in
# one reactor; the reactor resolves websocket-resources to its target/classes.
# build-classpath runs for every reactor module; service runs last, so its classpath wins.
"${MVN[@]}" -pl service -am -DskipTests test-compile dependency:build-classpath \
  -Dmdep.includeScope=test "-Dmdep.outputFile=$HERE/state/classpath.txt"
echo "build ok; classpath at $HERE/state/classpath.txt"
