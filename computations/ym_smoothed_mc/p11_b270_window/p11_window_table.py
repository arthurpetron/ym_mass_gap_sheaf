#!/usr/bin/env python3
"""P11 final window-survival table (MC/lit only, not proof).
Reproduce from the run dir (box: /workspace/ymmc/p4_smoothed/runs/p11_ml_d4_b2.70_L24x32) with the repo tools:
  python3 ana/p10_report.py <rundir> --tag P11_B270 --norefs --direct none --nmeas 1200 --mode final --out P11_FINAL.md
  python3 ana/p10_stepratio.py <rundir> --out P11_STEPRATIO.md
This script prints z = W/sigma and step ratios from p11_b270_window.csv."""
import csv
for r in csv.DictReader(open(__file__.replace('p11_window_table.py','p11_b270_window.csv'))):
    print(r['nsub'], r['side'], 'W=%s(%s) z=%.2f'%(r['W_E1'],r['sigma_E1'],float(r['W_E1'])/float(r['sigma_E1'])), 'c0',r['c0'],'c_s2',r['c_s2'])
