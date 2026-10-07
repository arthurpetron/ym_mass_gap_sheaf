#!/bin/bash
# P10 sampler: usage sampler_p10.sh <pid> <log> <threads_file> <full> <low>
# 30-s samples of MemAvailable/load/job CPU/RSS.
# Throttle (threads file -> low) if MemAvailable < THR_MB (4000) or load1 > 7.5 for 2 samples;
# restore to full after 10 min with MemAvailable > RESTORE_MB (5000) and load1 < 5.5.
# Hard pause (SIGSTOP) if MemAvailable < PAUSE_MB (3500); SIGCONT when > RESUME_MB (4500).
pid=$1; log=$2; tf=$3; full=$4; low=$5; paused=0; hi=0; ok=0
THR=${THR_MB:-4000}; RST=${RESTORE_MB:-5000}; PAU=${PAUSE_MB:-3500}; RES=${RESUME_MB:-4500}
echo "# ts epoch memavail_MB memfree_MB load1 load5 load15 job_cpu_pct job_rss_MB threads paused" >> "$log"
while kill -0 "$pid" 2>/dev/null; do
  av=$(( $(awk '/MemAvailable/{print $2}' /proc/meminfo) / 1024 )); fr=$(( $(awk '/MemFree/{print $2}' /proc/meminfo) / 1024 ))
  read l1 l5 l15 _ < /proc/loadavg
  cpu=$(ps -o %cpu= -p "$pid" 2>/dev/null | tr -d ' '); rss=$(( $(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' ' || echo 0) / 1024 ))
  cur=$(cat "$tf" 2>/dev/null || echo $full)
  if awk -v l=$l1 'BEGIN{exit !(l>7.5)}' || [ $av -lt $THR ]; then hi=$((hi+1)); else hi=0; fi
  if [ "$cur" -eq "$full" ] && [ $hi -ge 2 ]; then echo $low > "$tf"; cur=$low; ok=0; echo "# $(date +%T) THROTTLE: threads -> $low (load1 $l1, memavail $av MB)" >> "$log"; fi
  if [ "$cur" -eq "$low" ] && [ "$low" -ne "$full" ]; then
    if awk -v l=$l1 'BEGIN{exit !(l<5.5)}' && [ $av -gt $RST ]; then ok=$((ok+1)); else ok=0; fi
    if [ $ok -ge 20 ]; then echo $full > "$tf"; cur=$full; ok=0; echo "# $(date +%T) RESTORE: threads -> $full" >> "$log"; fi; fi
  if [ $paused -eq 0 ] && [ $av -lt $PAU ]; then kill -STOP "$pid"; paused=1; echo "# $(date +%T) PAUSE (memavail ${av} MB)" >> "$log"; fi
  if [ $paused -eq 1 ] && [ $av -gt $RES ]; then kill -CONT "$pid"; paused=0; echo "# $(date +%T) RESUME (memavail ${av} MB)" >> "$log"; fi
  echo "$(date +%T) $(date +%s) $av $fr $l1 $l5 $l15 ${cpu:-0} $rss $cur $paused" >> "$log"
  sleep 30
done
echo "# $(date +%T) job $pid ended" >> "$log"
