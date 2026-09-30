# The unchanged collar coefficient cannot supply the proposed patch test

2026-09-30 UTC; source baseline `672be2d` plus the named new module.

## Checked claim

`lean/YMGap/Continuum/BF4ExactSlabPatchCollarBudgetObstruction.lean`
proves three statements about the EXISTING computed coefficient
`BF4ExactSlabLocalSupportVariance.supportRatio`:

1. `linear_scaled_ratio_le_one`: for L <= 6*size,
   `L*supportRatio(w,size) <= 1`.
2. `scaled_margin_le_neg_fourteen`: additionally L>=1 implies
   `L^2*supportRatio(w,size) - (18*L-3) <= -14`.
3. `full_box_budget_margin_le_neg_fourteen`: this holds for size=4*L^4
   and every L>=1, at every rational 0<w<1.

The proof reuses the checked eighth-power ceiling on the coefficient and
the constructive geometric-beats-linear inequality. It uses no numerical
sampling, fixed cutoff experiment, spectral theorem, or new analytic input.

## What it rules out

The proposed box-patch criterion in
`audits/RESEARCH-COLLECTIVE-PATCH-THRESHOLD-2026-09-30.md` needs
`L^2*lambda > 18*L-3`. If the chosen producer were exactly the existing
conservative coefficient at budget 4*L^4, increasing L could never make that
strict test hold. Therefore do not invest in a patch compiler whose planned
analytic input is that unchanged coefficient.

This theorem does NOT:

- prove that the coefficient is a conditional-patch square-energy bound;
- formalize the overlapping-box counting or operator-composition theorem;
- upper-bound the true patch gap or exclude sharper coefficients;
- exclude a boundary-adjusted or differently weighted covering argument;
- close a physical scaling, OS, Hamiltonian, or continuum Yang--Mills atom.

The assertion is about a certificate number, not the actual physical gap.
The underlying local-support theorem requires literal local representatives;
it cannot silently be applied to arbitrary exterior-conditioned states.

## Parallel review and consequence

Luna checked the existing collar constants and the absence of a strict patch
bound in the inspected block-projection APIs. Sol independently checked the
new scalar proof and its scope. Sol also found that the separate nonzero
fundamental-plaquette branch already has a positive normalized variance floor
in `BF4ExactSlabSelectedStarVariance.normalizedVariance_floor`, with the
original completed pairing supplied by
`BF4ExactSlabConditionalCovariance.completed_covariance`. An additional
gauge-witness wrapper would not supply a new quantitative estimate.

Next mathematical priority remains a sharper, cancellation-preserving bound
for the actual original action or its actual auxiliary states. Retain the
conditional normalizer and all incident action factors. No new bundle merely
assuming that estimate was introduced.

## Verification boundary

The final successful focused check used:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabPatchCollarBudgetObstruction.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabPatchCollarBudgetObstruction.olean
```

It completed successfully in under five seconds. All three printed axiom
gates reported exactly `[propext, Quot.sound]`. No sorry or axiom was added.
No full library, semantic-root, broad guard or axiom-audit run was performed;
the semantic root only gained the new module's import. The safe-build skill
kept verification focused, serialized and capped; continuous safety
monitoring remained enabled. There was no long-running job to poll.

The canonical chart's displayed claims are unchanged, so it is not reprinted.
The full constructive same-theory Clay goal remains open.
