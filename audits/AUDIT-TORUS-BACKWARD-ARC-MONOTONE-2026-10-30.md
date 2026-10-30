# Audit — Torus Backward-Arc Monotonicity (r52, 2026-10-30)

## Scope & honest label
- Module: `lean/YMGap/Continuum/TorusBackwardArcMonotone.lean` (70 lines).
- Label: **elementary monotonicity lemma, NOT gap evidence, does NOT discharge `hcov`.** U(1) also satisfies it.
- Relabels the HP note claim "two-cut reflection discharges hcov" (misattributed to Hsu 2610.29019 App. F.5, which is a site-reflection factorization). The real content is power monotonicity of a positive contraction.

## Proved
- `c_antitone`, `c_antitone'`: one-step `c(k+1) ≤ c k` ⟹ antitone.
- `backward_arc_le_forward`: `2m+1 ≤ M ⟹ c(2M-2m) ≤ c(2m)`.
- `twoArc_le_twice_forward`, `twoArc_cov_of_forward`: two-arc bound with constant `2C` from the single-arc bound.

## OPEN
- `hstep` for the repo carrier (`completedTime`) is a hypothesis here, not instantiated.
- `hforward_OPEN` and the identification of `EhatHK` with the transfer correlator (rest of `hcov`).

## Verification
- Mac worktree, `LEAN_NUM_THREADS=2 nice -n 10 safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check`: 0 errors, 0 warnings.
- Axioms (temp-file collectAxioms, file deleted): `{propext, Quot.sound}`.
