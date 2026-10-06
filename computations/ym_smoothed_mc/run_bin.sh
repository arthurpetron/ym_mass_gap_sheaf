#!/bin/bash
# usage: run.sh <rundir> <threads> [p4run args...]   (out prefix is <rundir>/data)
dir=$1; th=$2; shift 2; mkdir -p "$dir"
{ echo "pre-run snapshot $(date '+%F %T %Z')"; echo "nproc: $(nproc)"; free -g; echo "loadavg: $(cat /proc/loadavg)"; uptime; } > "$dir/prerun_snapshot.txt"
echo "args: --threads $th --out $dir/data $*" >> "$dir/prerun_snapshot.txt"
BIN=${P4BIN:-/workspace/ymmc/p4_smoothed/target/release/p4run}
$BIN --threads "$th" --out "$dir/data" "$@" > "$dir/run.log" 2>&1 &
jp=$!
bash /workspace/ymmc/p4_smoothed/sampler.sh $jp "$dir/resources.log" "$th" &
sp=$!
wait $jp; rc=$?
echo "exit $rc $(date '+%F %T')" >> "$dir/run.log"
kill $sp 2>/dev/null; wait $sp 2>/dev/null
echo "# $(date +%T) run finished rc=$rc; sampler stopped" >> "$dir/resources.log"
