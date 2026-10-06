# Smoothed-loop SU(2) Monte Carlo (box numerics, 2026-10-05/06)

Heat-bath/overrelaxation SU(2) Wilson-action Monte Carlo (`src/main.rs`, Rust) measuring
time-correlators of a spatially smoothed (gradient-flowed) square Wilson loop of side `side`,
used to test the survival hypotheses on the A03 nontriviality route.

- `ana/analyze.py`: jackknife analysis (eps = 1 - R(1)/R(0), eps*side, shifted variants).
- `ana/window_analyze.py`, `ana/window_table.py`: adds the window-survival ratio
  W = R(side+1)/R(side/2) (the hypothesis of the c944edfa theorem: backward-window survival
  => shifted H1 with c0 = 2(1-W)/W), plus -2 log W.
- `runs/*.md`: tables; `runs/<run>/prerun_snapshot.txt`: pre-run free CPU/RAM. The `*.log` files
  (run logs, periodic CPU/RAM samples) are gitignored and stay on the box under
  /workspace/ymmc/p4_smoothed/runs/. Raw configurations/correlator binaries are NOT committed.

Caveats (read before citing):
- This is the WILSON action and a SPATIALLY smoothed loop. The Lean state Y_j is a
  time-smoothed plaquette family, so these numbers are evidence about a neighbouring
  state, not a measurement of the Lean hypothesis.
- Heuristic numerics only; nothing here is a proof. Run b3.00_L32x48_s10_B (second stream at
  beta=3.0, side 10) was still running at commit time and is excluded.
