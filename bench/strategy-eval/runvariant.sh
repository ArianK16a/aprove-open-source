#!/bin/bash
# usage: runvariant.sh VARIANT SET [timeout]
cd "$(dirname "$0")"
line=$(grep "^$1|" variants.sh) || { echo "unknown variant $1"; exit 1; }
defs=${line#*|}
args=()
if [ -n "$defs" ]; then
  IFS=$'\n'
  for d in $(echo "$defs" | sed 's/ ;; /\n/g'); do args+=(--set "$d"); done
  unset IFS
fi
# optional environment: JAR=jars/x.jar (default: dist/lib/aprove.jar of the repo), PREFIX=n- (prefix of the
# run name), JOBS (files in parallel, default 2), CORES (cores per file, default 4), MEM (heap, default 3g)
jar=()
[ -n "$JAR" ] && jar=(--jar "$JAR")
[ -n "$JOBS" ] && jar+=(-j "$JOBS")
[ -n "$CORES" ] && jar+=(--cores "$CORES")
[ -n "$MEM" ] && jar+=(--mem "$MEM")
name="${PREFIX}$1_$2"
python3 run.py --name "$name" "${args[@]}" "${jar[@]}" --files "sets/$2.txt" -t "${3:-30}" > "runs/$name.log" 2>&1
tail -1 "runs/$name.log"
