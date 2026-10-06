#!/bin/bash
# P8 sampler: usage sampler_p8.sh <pid> <log> <threads_file> <full> <low>
# 30 s samples. threads -> low if load1 > 7 for 2 samples; restore after 10 min of load1 < 5.5.
# SIGSTOP if MemAvailable < 3000 MB; SIGCONT when > 4000 MB.
pid=$1; log=$2; tf=$3; full=$4; low=$5; paused=0; hi=0; ok=0
echo "# ts epoch memavail_MB memfree_MB load1 load5 load15 job_cpu_pct job_rss_MB threads paused" >> "$log"
while kill -0 "$pid" 2>/dev/null; do
  av=$(( $(awk '/MemAvailable/{print $2}' /proc/meminfo) / 1024 )); fr=$(( $(awk '/MemFree/{print $2}' /proc/meminfo) / 1024 ))
  read l1 l5 l15 _ < /proc/loadavg
  cpu=$(ps -o %cpu= -p "$pid" 2>/dev/null | tr -d ' '); rss=$(( $(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' ' || echo 0) / 1024 ))
  cur=$(cat "$tf" 2>/dev/null || echo $full)
  if awk -v l=$l1 'BEGIN{exit !(l>7)}'; then hi=$((hi+1)); else hi=0; fi
  if [ "$cur" -eq "$full" ] && [ $hi -ge 2 ]; then echo $low > "$tf"; cur=$low; ok=0; echo "# $(date +%T) THROTTLE: threads -> $low (load1 $l1)" >> "$log"; fi
  if [ "$cur" -eq "$low" ] && [ "$low" -ne "$full" ]; then if awk -v l=$l1 'BEGIN{exit !(l<5.5)}'; then ok=$((ok+1)); else ok=0; fi
    if [ $ok -ge 20 ]; then echo $full > "$tf"; cur=$full; ok=0; echo "# $(date +%T) RESTORE: threads -> $full" >> "$log"; fi; fi
  if [ $paused -eq 0 ] && [ $av -lt 3000 ]; then kill -STOP "$pid"; paused=1; echo "# $(date +%T) PAUSE (memavail ${av} MB)" >> "$log"; fi
  if [ $paused -eq 1 ] && [ $av -gt 4000 ]; then kill -CONT "$pid"; paused=0; echo "# $(date +%T) RESUME (memavail ${av} MB)" >> "$log"; fi
  echo "$(date +%T) $(date +%s) $av $fr $l1 $l5 $l15 ${cpu:-0} $rss $cur $paused" >> "$log"
  sleep 30
done
echo "# $(date +%T) job $pid ended" >> "$log"
