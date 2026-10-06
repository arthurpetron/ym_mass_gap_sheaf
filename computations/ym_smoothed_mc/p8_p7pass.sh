#!/bin/bash
# P8: incremental measurement of the P7 saved configs (read-only on P7 files). Re-scans every 5 min; stops when P7 has
# exited and every cfg is measured. usage: setsid nohup bash p8_p7pass.sh > runs/p8_p7pass.log 2>&1 &
cd /workspace/ymmc/p4_smoothed
dir=runs/p8_anchor_b2.95_L48x48; mkdir -p $dir
P7PID=$(cat runs/b2.95_L48x48_s8/pid)
while true; do
  ls runs/b2.95_L48x48_s8/cfg/cfg_*.f32 2>/dev/null | sort > $dir/cfgs.list.new
  n_new=$(wc -l < $dir/cfgs.list.new); n_done=$( [ -f $dir/data.cfglist ] && wc -l < $dir/data.cfglist || echo 0 )
  mv $dir/cfgs.list.new $dir/cfgs.list
  if [ "$n_new" -gt "$n_done" ]; then
    echo "$(date '+%F %T') measuring cfgs $((n_done+1))..$n_new"
    bash p8_run.sh $dir 2 --Ls 48 --Lt 48 --beta 2.95 --sides 1,2,3,4,6,8 --tflow 0 --linear-variants 0.2:2:none:13/30/53/120/213 --measure-cfgs $dir/cfgs.list
  fi
  if ! kill -0 $P7PID 2>/dev/null; then
    ls runs/b2.95_L48x48_s8/cfg/cfg_*.f32 2>/dev/null | sort > $dir/cfgs.list; n_new=$(wc -l < $dir/cfgs.list); n_done=$(wc -l < $dir/data.cfglist)
    [ "$n_new" -le "$n_done" ] && { echo "$(date '+%F %T') P7 finished and all $n_done cfgs measured"; break; }
  else sleep 300; fi
done
