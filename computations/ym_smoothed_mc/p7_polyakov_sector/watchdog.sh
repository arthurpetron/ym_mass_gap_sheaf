#!/bin/bash
# 30-s sampler + memory watchdog for the p7_polyakov_sector job (pid read from file $1). MC tooling only.
PIDF=$1; LOG=resource_sampler.log; paused=0
while true; do
  ma=$(awk '/MemAvailable/{print $2}' /proc/meminfo); ld=$(cut -d' ' -f1-3 /proc/loadavg)
  jp=$(cat "$PIDF" 2>/dev/null); st=""
  if [ -n "$jp" ] && kill -0 "$jp" 2>/dev/null; then
    if [ "$ma" -lt 4000000 ] && [ $paused -eq 0 ]; then kill -STOP "$jp"; paused=1; st=" PAUSE(job $jp)"; fi
    if [ "$ma" -gt 4500000 ] && [ $paused -eq 1 ]; then kill -CONT "$jp"; paused=0; st=" RESUME(job $jp)"; fi
    [ $paused -eq 1 ] && [ -z "$st" ] && st=" paused"
  else st=" (no job)"; fi
  echo "$(date +%H:%M:%S) MemAvailable=${ma}kB load=${ld}${st}" >> $LOG
  sleep 30
done
