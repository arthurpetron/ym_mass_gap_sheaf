#!/bin/bash
# usage: sampler.sh <pid> <logfile> <job_threads>
# Logs MemAvailable/MemFree/load every 30 s; throttles (SIGSTOP/SIGCONT) the job if
# MemAvailable < 15% of total or 1-min load > nproc (resume when mem >= 17% and load1 + job_threads <= nproc).
pid=$1; log=$2; jt=$3; np=$(nproc); paused=0
tot=$(awk '/MemTotal/{print $2}' /proc/meminfo)
echo "# ts epoch memavail_MB memfree_MB memavail_pct load1 load5 load15 job_cpu_pct paused" >> "$log"
while kill -0 "$pid" 2>/dev/null; do
  av=$(awk '/MemAvailable/{print $2}' /proc/meminfo); fr=$(awk '/MemFree/{print $2}' /proc/meminfo)
  read l1 l5 l15 _ < /proc/loadavg
  pct=$(awk -v a=$av -v t=$tot 'BEGIN{printf "%.1f", 100*a/t}')
  cpu=$(ps -o %cpu= -p "$pid" 2>/dev/null | tr -d ' ')
  if [ $paused -eq 0 ]; then
    if awk -v p=$pct -v l=$l1 -v n=$np 'BEGIN{exit !(p<15 || l>n)}'; then kill -STOP "$pid"; paused=1; echo "# $(date +%T) THROTTLE: paused job (memavail ${pct}% load1 $l1)" >> "$log"; fi
  else
    if awk -v p=$pct -v l=$l1 -v n=$np -v j=$jt 'BEGIN{exit !(p>=17 && l+j<=n)}'; then kill -CONT "$pid"; paused=0; echo "# $(date +%T) THROTTLE: resumed job (memavail ${pct}% load1 $l1)" >> "$log"; fi
  fi
  echo "$(date +%T) $(date +%s) $((av/1024)) $((fr/1024)) $pct $l1 $l5 $l15 ${cpu:-0} $paused" >> "$log"
  sleep 30
done
echo "# $(date +%T) job $pid ended; sampler exit" >> "$log"
