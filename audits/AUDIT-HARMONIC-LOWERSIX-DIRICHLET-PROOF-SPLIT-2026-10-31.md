# Audit: HarmonicMassCrossLowerSixDirichlet proof split (2026-10-31)

Scope: proof-only change in `lean/YMGap/Continuum/HarmonicMassCrossLowerSixDirichlet.lean`.
No statement of any existing declaration changed.

Problem: full build `full3` failed on this module with a kernel `function expected`
error on the auto-generated `lowerSix_dirichletPayment_firstBand._proof_1_1 k`
(line 306) and kernel `excessive memory consumption` at lines 278, 300, 314
(the `omega`-driven 28-way and 10-way `rcases ... <;> unfold ... <;> decide` proofs).

Fix:
- New helper theorems `lowerSix_dirichletPayment_at_k` for k = 11..47 (k = 10 reuses
  the existing `lowerSix_dirichletPayment_k10`), each one closed `unfold ...; decide`.
- `lowerSix_dirichletPayment_below_thirty_eight` and `lowerSix_dirichletPayment_firstBand`
  now case-split by repeated `Nat.eq_or_lt_of_le` and dispatch to the helpers; the empty
  tail is closed by `absurd ... (by decide)`. `omega` is no longer used in this file
  (also removed from `growingResidualLowerSix_below_forty_eight`, via
  `Nat.le_of_not_lt` / `Nat.le_of_lt_succ`).
- Pre-existing `simpa` uses in the algebra lemmas (lines ~77, ~116) are untouched.

Verification (this session, darthur's Mac, guard2/safe_lean_build, --jobs 1,
LEAN_NUM_THREADS=2, nice 10): targeted `+YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet:olean`
at a 16 GiB worker limit: rc=0, 40 s, peak Lean RSS 4.52 GiB, no errors or warnings.
`#print axioms` (temp file, deleted) on both restructured theorems,
`growingResidualLowerSix_below_forty_eight`, `_at_37`, `_at_47`: `[propext, Quot.sound]`.
Full-tree build and repo axiom audit: delegated to the follow-up orchestrator run;
not claimed here.
