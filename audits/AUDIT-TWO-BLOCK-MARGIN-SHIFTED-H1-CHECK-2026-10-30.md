# Audit — Two-Block Margin vs Shifted H1 Finite Check (r53, 2026-10-30)

## Scope & honest label
- Module: `lean/YMGap/RG/TwoBlockMarginShiftedH1Check.lean` (66 lines). Approved optional item 4 of `HP-YM-REVIEW-2026-10-29`.
- Label: **NO-GO / consistency check, NOT gap evidence.** Abelian-valid.

## Proved
- `twoBlock_margin_must_shrink`: `(1-s_j)a_j ≤ 1-r_j` and `side_j(1-r_j) ≤ c0` ⟹ `side_j·(1-s_j)·a_j ≤ c0` for `j ≥ 1`.
- `twoBlock_fixedMargin_noGo`: fixed `s < 1` with a fixed floor `a ≤ a_j`, `a > 0` contradicts the shifted H1 (reuses r40 `exists_side_mul_gt`). Reproduces the r40 no-go for the two-block route.
- `fixedMargin_instance` (decide): `1 < 1024·(1/2)·(1/100)`.

## Reading
- The two-block route can meet `side_j θ_j ≤ c0` only if the margin shrinks, `1 - s_j ≲ c0/(side_j a_j)`; the margin must carry the dimensional transmutation. The assembly does not supply it.

## OPEN
- `hgap_OPEN` (two-block gap ≤ lattice gap on the carrier) and `hshift` (supplied in the repo by `path_shiftedEps_forces_rate` under H1 + nondegeneracy; not re-instantiated here).

## Verification
- Mac worktree, `LEAN_NUM_THREADS=2 nice -n 10 safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check`: 0 errors, 0 warnings.
- Axioms (temp-file collectAxioms, file deleted): `{propext, Quot.sound}`.
