# SU(2) Wilson loop-correlator Monte Carlo for the direct-response repoint (2026-10-05)

Numerical evidence only. This is not a proof input and does not affect the Lean
gates. Interpretation: `audits/AUDIT-ROUTE-REPOINT-DIRECT-RESPONSE-2026-10-05.md`.

## What was measured
- L=16^4, SU(2) Wilson action, heatbath plus 4 overrelaxation sweeps,
  1000 thermalization sweeps, 3000 measurements every 4 sweeps.
- beta = 2.3, 2.4, 2.5, 2.6 (seeds 23, 24, 25, 26).
- Observable F = Tr W for spatial s x s Wilson loops, s = 1..4, measured raw
  and after APE spatial smearing (alpha = 0.5, 8 and 20 steps).
- `loc` = one fixed position (the literal padded square); `zm` =
  zero-momentum sum over spatial positions (a coherent state).
- Connected temporal correlator R(t) for t = 0..8. Jackknife over 60 bins.

## Files
- `loopcorr.rs`: binary (copy to `simulations/src/bin/` and add a `[[bin]]
  loopcorr` entry to `simulations/Cargo.toml`). It needs `lib_pub.patch`, which
  makes `lget` and `ape_smear_spatial_into` public. Nothing else changes.
- Run: `cargo run --release --bin loopcorr -- --L 16 --beta B --therm 1000
  --meas 3000 --interval 4 --overrelax 4 --sides 1,2,3,4 --smear 0,8,20
  --alpha 0.5 --seed S --threads 4 --out runs/bB.bin`
- `analyze.py` (record reader) and `summary.py runs/b*.bin > summary.txt`:
  jackknife table. `summary.txt` is the table for these runs.
- `guards.py`, `guards2.py`, `guards3.py`: matched-nome guard numbers. The
  convention w^3 = I2(beta)/I1(beta) is an ASSUMED nome matching.
- `runs/*.runlog.txt`: run logs. `runs/SHA256SUMS`: hashes of the 5.5 MB binary
  record files. These files are not committed. They are kept on the
  generating box at `/workspace/ymmc/runs/`.

## Columns of summary.txt
R(2s)/R(s) is the macro ratio at lag s. R(s)/R(0) is the survival (CS floor)
quantity. (R1/R0)^s is the Jensen lower bound. eps = 1-R(1)/R(0).
For even s=2u, window kappa_b = 1 - 2*sum_{t=u}^{2u-1}(R(2t)-R(2t+1))/R(2u).
This is a correlator proxy for the kappa that the joint window budget
2*windowCost <= (1-kappa)*R(2u) would certify, with each signed cost read as
the one-step loss R(2t)-R(2t+1).

## Caveats
On L=16, lag 8 wraps halfway around the torus and can inflate R(8)/R(4) by
up to 2x. The smearing radius is fixed in lattice units, not physical units.
Statistics at s >= 3 for raw loops are noise dominated.
