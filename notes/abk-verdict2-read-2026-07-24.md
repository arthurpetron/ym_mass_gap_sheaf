# ABK verdict2 read: completed β = 4κ correlation run (2026-07-24)

Source (Mac, read-only): `ym_mass_gap_sheaf/computations/abk_verdict2.py` and
`ym_mass_gap_sheaf/computations/abk_verdict2_ckpt.json`.
Mirrored checkpoint: `abk_verdict2_ckpt.json` (this directory).
Analysis: `abk_verdict2_analysis.py` → `abk_verdict2_analysis.json` (exact
arithmetic, `fractions.Fraction`).

## Schema (from abk_verdict2.py)

- Sample: 150 κ=1 + 150 κ=0 non-decomposable admissible spin configs
  (`kap`, `decomposable`, seed 99), shuffled; checkpoint `{"i": idx, "rows": [...]}`.
- Per row: `kappa` always; `b1` unless the complex build failed; then either
  `beta` (Brown invariant of the assembled (q, B) via `brown_fixed`) or
  `fail` ∈ {`build`, `b1_big` (b1 > 12), `q` (some `q_embedded` undefined),
  `B` (bilinear-consistency violation `(q(x+y)−q(x)−q(y))` odd), `nonpin`
  (`brown_fixed` returned None)}.
- Match conventions: **direct** `beta == 4*kappa (mod 8)`; **mirror**
  `(8−beta) % 8 == 4*kappa`. Since the targets {0, 4} are fixed by β ↦ −β,
  direct and mirror match sets coincide by construction on the target values.
- Baseline: uniform β mod 8 → p = 1/8 (docstring notes 1/4 if β were forced
  even; empirically 43/52 computed β are even, 9 are odd).

## Completed-run verdict (exact)

- **Run complete: i = 300/300.** β computed for **52/300** rows (17.3%).
  Failures: `nonpin` 143, `q` 69, `B` 26, `b1_big` 10 (248 total).
- **Direct matches: 22/52 = 11/26 ≈ 0.4231** (mirror identical: 22/52).
- **Exact binomial tail** P(X ≥ 22 | n = 52, p = 1/8) =
  933345752990730906036166023603547804185 /
  11417981541647679048466287755595961091061972992
  **≈ 8.174 × 10⁻⁸**.
- β × κ histogram: (0,0):20 (0,1):8 (1,0):2 (1,1):2 (2,0):7 (2,1):1 (3,1):1
  (4,1):2 (6,0):3 (6,1):2 (7,0):3 (7,1):1.

## Miss structure — the d2 pattern does NOT persist

Circular distance |β − 4κ| mod 8 over the 30 misses:
**d1: 6, d2: 13, d3: 3, d4: 8.** The earlier band-geometry finding
("every miss exactly d2") fails here: only 13/30 misses are d2, 9 misses are
odd-distance (odd β occurs 9/52 times), and 8 misses are maximal (d4) —
all 8 of these are κ=1 configs landing at β=0.

## Honesty cuts (what drives the signal)

- `b1 = 0` rows have β = 0 by construction — they test nothing about Brown.
  14 such rows; 13 matched (all κ=0), 1 mismatched (κ=1, worst-case d4).
- **Excluding b1 = 0: 9/38 ≈ 0.237**, exact tail P(X ≥ 9 | 38, 1/8) =
  214116682493530831941001637466123 / 5192296858534827628530496329220096
  **≈ 0.0412**.
- Per stratum (b1 > 0): **κ=0: 7/22** (tail ≈ 0.0147); **κ=1: 2/16 = 0.125**
  (tail ≈ 0.612 — **exactly at the 1/8 baseline**).
- Match rate decays with b1: b1=0: 13/14, b1=2: 3/10, b1=4: 3/11,
  b1∈{6,7,8,11,12}: 2/15.

## Interpretation

The nominal headline (22/52, p ≈ 8×10⁻⁸) overstates the case: the signal is
carried almost entirely by β = 0 outcomes on κ=0 and by the 14 trivial
b1 = 0 rows. The load-bearing half of β = 4κ — that κ = 1 forces β = 4 —
shows **no signal at all** (2/16, exactly baseline; and 8 of the 17 κ=1
completions land at β = 0, the maximal-distance miss). What the completed run
actually supports is weaker: on vote-gated geometry the assembled (q, B) is
biased toward β ≡ 0, with mild κ=0 enrichment (p ≈ 0.015 in-stratum) that
survives the honesty cut only marginally overall (p ≈ 0.04). Meanwhile the
pipeline itself discarded 83% of samples (nonpin/q/B failures) and produced
9 odd-β rows, so the correlation-mode estimator is both lossy and internally
noisy. Verdict on prioritization: **yes, move to the embedded-surface Pin⁻
realization, but as the decider, not the confirmer.** The current heuristic
q/B assembly cannot distinguish "β = 4κ is true but the assembly corrupts
κ=1 configs" from "β = 4κ is false"; only the genuine embedded Pin⁻
structure — which would make q well-defined, kill the nonpin/q/B failure
modes, and turn the correlation into a computable theorem statement — can
separate those. If a first batch of embedded-surface computations reproduces
the κ=1 → β=4 half, the conjecture is alive; if it reproduces the β=0
attractor instead, β = 4κ should be dropped in favor of a β ≡ 0 rigidity
statement.
