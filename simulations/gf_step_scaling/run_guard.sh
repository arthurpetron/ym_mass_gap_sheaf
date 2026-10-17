#!/bin/bash
# Resource guard for Mac runs (darthur's machine). Usage: run_guard.sh LOGFILE
# Watches only our own binaries (su2gf/u1gf under the ym_numerics_runs target dir).
# Every INTERVAL s it logs: ncpu, load1, free-memory % (memory_pressure), vm_stat free/inactive pages, #procs, state.
#  * free memory < 15 %           -> SIGSTOP all of our processes
#  * load1 > ncpu (machine busy)  -> THROTTLE: only the oldest ONE of our processes is allowed to run, others SIGSTOPped
#  * otherwise                    -> all SIGCONT (driver caps concurrency at <= 4, default 3)
# Exits when STOPFILE exists or when no process has been seen for 20 min.
LOG="$1"
NCPU=$(sysctl -n hw.ncpu); MEM=$(sysctl -n hw.memsize)
INTERVAL=${INTERVAL:-30}
PAT='ym_numerics_runs/target/release/(su2gf|u1gf)'
STOPFILE=${STOPFILE:-/Users/darthur/ym_numerics_runs/GUARD_STOP}
echo "# guard start $(date '+%F %T %Z') ncpu=$NCPU memsize=$MEM interval=$INTERVAL" >> "$LOG"
IDLE=0
while [ ! -e "$STOPFILE" ]; do
  PIDS=$(pgrep -f "$PAT" | sort -n | tr '\n' ' ')
  LOAD=$(sysctl -n vm.loadavg | awk '{print $2}')
  FREEPCT=$(memory_pressure | awk '/free percentage/ {gsub("%","",$NF); print $NF}')
  PG=$(vm_stat | awk '/Pages free/ {gsub("\\.","",$3); f=$3} /Pages inactive/ {gsub("\\.","",$3); i=$3} END {print f","i}')
  LOWMEM=$(awk -v f="$FREEPCT" 'BEGIN{print (f<15)?1:0}')
  BUSY=$(awk -v l="$LOAD" -v m="$NCPU" 'BEGIN{print (l>m)?1:0}')
  STATE=run; N=0
  for p in $PIDS; do
    N=$((N+1))
    if [ "$LOWMEM" = "1" ]; then kill -STOP $p 2>/dev/null; STATE=paused_lowmem
    elif [ "$BUSY" = "1" ] && [ $N -gt 1 ]; then kill -STOP $p 2>/dev/null; STATE=throttled_1proc
    else kill -CONT $p 2>/dev/null; [ "$BUSY" = "1" ] && STATE=throttled_1proc; fi
  done
  echo "$(date '+%F %T') load1=$LOAD freepct=$FREEPCT pages_free,inactive=$PG nproc=$N state=$STATE" >> "$LOG"
  if [ "$N" = "0" ]; then IDLE=$((IDLE+INTERVAL)); else IDLE=0; fi
  [ $IDLE -gt 1200 ] && break
  sleep $INTERVAL
done
echo "# guard end $(date '+%F %T %Z')" >> "$LOG"
