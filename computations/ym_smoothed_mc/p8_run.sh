#!/bin/bash
# usage: p8_run.sh <rundir> <threads> [p4run args...]  -- runs bin/p4run_p8 with threads file + sampler_p8
cd /workspace/ymmc/p4_smoothed; dir=$1; th=$2; shift 2; mkdir -p "$dir"; echo $th > "$dir/threads"
{ echo "pre-run snapshot $(date '+%F %T %Z')"; echo "nproc --all: $(nproc --all)"; free -m; echo "loadavg: $(cat /proc/loadavg)"; echo "args: $*"; } >> "$dir/prerun_snapshot.txt"
bin/p4run_p8 --threads $th --threads-file "$dir/threads" --out "$dir/data" "$@" >> "$dir/run.log" 2>&1 &
jp=$!; echo $jp > "$dir/pid"
bash sampler_p8.sh $jp "$dir/resources.log" "$dir/threads" $th 1 &
sp=$!; wait $jp; rc=$?; echo "exit $rc $(date '+%F %T')" >> "$dir/run.log"; kill $sp 2>/dev/null; wait $sp 2>/dev/null
