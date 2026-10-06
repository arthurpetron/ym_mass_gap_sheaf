#!/bin/bash
# regenerates runs/P5_STATUS.md every 60 s while P5 queues run
cd /workspace/ymmc/p4_smoothed
while true; do
  {
  echo "# P5 status (auto-updated $(date '+%F %T %Z'))"
  echo; echo "queues: $(pgrep -fa 'p5_queue[XY].sh' | awk '{print $1, $3}' | tr '\n' ';')"
  echo "box: nproc $(nproc); $(free -m | awk '/Mem:/{print "MemAvailable "$7" MB of "$2}'); loadavg $(cut -d' ' -f1-3 /proc/loadavg)"
  echo; echo "| run | pid | status | progress | s/meas | ETA |"; echo "|---|---|---|---|---|---|"
  for d in runs/b2.95_L32x48_s8 runs/b3.00_L32x48_s10_A runs/p5_b2.85_L24x32_s6 runs/p5_b2.70_L24x32_s4 runs/p5_b2.60_L24x32_s3 runs/p5_b2.50_L24x32_s2 runs/b3.00_L32x48_s10_B; do
    if [ ! -f $d/run.log ]; then echo "| $(basename $d) | - | queued | - | - | - |"; continue; fi
    pid=$(pgrep -f "out $d/data" | head -1); last=$(grep -E "^meas|^therm|^exit|^done" $d/run.log | tail -1)
    nmeas=$(grep -o -- '--meas [0-9]*' $d/prerun_snapshot.txt | awk '{print $2}')
    if echo "$last" | grep -q '^exit'; then echo "| $(basename $d) | - | finished ($last) | - | - | - |"; continue; fi
    if echo "$last" | grep -q '^meas'; then
      m=$(echo "$last" | awk '{print $2}' | cut -d/ -f1); spm=$(echo "$last" | grep -o '([0-9.]*s/meas' | tr -d '(s/meas')
      eta=$(python3 -c "import datetime;print((datetime.datetime.now()+datetime.timedelta(seconds=($nmeas-$m)*$spm)).strftime('%H:%M'))")
      echo "| $(basename $d) | $pid | running | $m/$nmeas | $spm | $eta PT |"
    else echo "| $(basename $d) | $pid | thermalizing | $last | - | - |"; fi
  done
  echo; echo "Logs: runs/<run>/run.log, resources.log, prerun_snapshot.txt. Interim (auto when b2.95 finishes): runs/P5_INTERIM.md"
  } > runs/P5_STATUS.md.tmp && mv runs/P5_STATUS.md.tmp runs/P5_STATUS.md
  pgrep -f 'p5_queue[XY].sh' > /dev/null || { echo "All P5 queues finished $(date '+%T')" >> runs/P5_STATUS.md; exit 0; }
  sleep 60
done
