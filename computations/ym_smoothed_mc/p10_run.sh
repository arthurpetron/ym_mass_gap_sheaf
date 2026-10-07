#!/bin/bash
# P10 multilevel production wrapper. usage: p10_run.sh <rundir> <threads> [--resume] [p4run args...]
# Runs bin/p4run_p9 (multilevel, --ml-d/--ml-nsub) with a threads file + 30-s sampler (sampler_p10.sh), then the auto-report watcher's final pass.
# OMP/RAYON thread env vars are unset so they cannot silently force 1 thread (threads come from --threads / threads file).
cd /workspace/ymmc/p4_smoothed; dir=$1; th=$2; shift 2; mkdir -p "$dir"; echo $th > "$dir/threads"; echo $$ > "$dir/wrapper.pid"
{ echo "pre-run snapshot $(date '+%F %T %Z')"; echo "nproc --all: $(nproc --all)"; free -m; echo "loadavg: $(cat /proc/loadavg)"; echo "args: $*"; } >> "$dir/prerun_snapshot.txt"
env -u OMP_NUM_THREADS -u RAYON_NUM_THREADS bin/p4run_p9 --threads $th --threads-file "$dir/threads" --out "$dir/data" "$@" >> "$dir/run.log" 2>&1 &
jp=$!; echo $jp > "$dir/pid"
bash sampler_p10.sh $jp "$dir/resources.log" "$dir/threads" $th 2 &
sp=$!; wait $jp; rc=$?; echo "exit $rc $(date '+%F %T')" >> "$dir/run.log"; kill $sp 2>/dev/null; wait $sp 2>/dev/null
