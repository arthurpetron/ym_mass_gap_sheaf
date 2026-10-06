#!/bin/bash
# P7 sampler with thread throttling via a threads file that p4run re-reads before every sweep.
# usage: sampler_p7.sh <pid> <logfile> <threads_file> <full_threads> <low_threads>
#  - every 30 s logs: ts epoch memavail_MB memfree_MB memavail_pct load1 load5 load15 job_cpu_pct job_rss_MB threads paused
#  - THROTTLE (write low_threads): MemAvailable < 2500 MB (immediately) or load1 > 7 for 2 consecutive samples (60 s).
#  - RESTORE  (write full_threads): MemAvailable > 3500 MB and load1 < 5.5 for 20 consecutive samples (10 min).
#  - Memory emergency (thread count does not free memory): SIGSTOP the job if MemAvailable < 1200 MB, SIGCONT when > 2000 MB.
pid=$1; log=$2; tf=$3; full=$4; low=$5; paused=0; hi=0; ok=0
tot=$(awk '/MemTotal/{print $2}' /proc/meminfo)
echo "# ts epoch memavail_MB memfree_MB memavail_pct load1 load5 load15 job_cpu_pct job_rss_MB threads paused" >> "$log"
while kill -0 "$pid" 2>/dev/null; do
  av=$(( $(awk '/MemAvailable/{print $2}' /proc/meminfo) / 1024 )); fr=$(( $(awk '/MemFree/{print $2}' /proc/meminfo) / 1024 ))
  read l1 l5 l15 _ < /proc/loadavg
  pct=$(awk -v a=$av -v t=$tot 'BEGIN{printf "%.1f", 100*a*1024/t}')
  cpu=$(ps -o %cpu= -p "$pid" 2>/dev/null | tr -d ' '); rss=$(( $(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' ' || echo 0) / 1024 ))
  cur=$(cat "$tf" 2>/dev/null || echo $full)
  if awk -v l=$l1 'BEGIN{exit !(l>7)}'; then hi=$((hi+1)); else hi=0; fi
  if [ "$cur" -eq "$full" ] && { [ $av -lt 2500 ] || [ $hi -ge 2 ]; }; then echo $low > "$tf"; cur=$low; ok=0; echo "# $(date +%T) THROTTLE: threads -> $low (memavail ${av} MB, load1 $l1)" >> "$log"; fi
  if [ "$cur" -eq "$low" ]; then
    if [ $av -gt 3500 ] && awk -v l=$l1 'BEGIN{exit !(l<5.5)}'; then ok=$((ok+1)); else ok=0; fi
    if [ $ok -ge 20 ]; then echo $full > "$tf"; cur=$full; ok=0; echo "# $(date +%T) RESTORE: threads -> $full (memavail ${av} MB, load1 $l1)" >> "$log"; fi
  fi
  if [ $paused -eq 0 ] && [ $av -lt 1200 ]; then kill -STOP "$pid"; paused=1; echo "# $(date +%T) MEM EMERGENCY: SIGSTOP (memavail ${av} MB)" >> "$log"; fi
  if [ $paused -eq 1 ] && [ $av -gt 2000 ]; then kill -CONT "$pid"; paused=0; echo "# $(date +%T) MEM OK: SIGCONT (memavail ${av} MB)" >> "$log"; fi
  echo "$(date +%T) $(date +%s) $av $fr $pct $l1 $l5 $l15 ${cpu:-0} $rss $cur $paused" >> "$log"
  sleep 30
done
echo "# $(date +%T) job $pid ended; sampler exit" >> "$log"
