# Direction checkpoint: the missing estimate is source-specific

Source review at `c98d53d1fa2afe0ae5ded09e2bbc208a0a273559`,
2026-10-04 UTC. Three parallel mathematical/source reviews; no Lean edits
or compiler run. The calculation below is independently reviewed mathematics,
NOT a new kernel-checked theorem. No canonical chart claim closes.

The unchanged goal is constructive continuum Yang--Mills on R^4 for EVERY
compact simple group, with SAME-theory QFT axioms, nontrivial survival and
a finite positive physical Hamiltonian gap. It remains OPEN.

## The two faces do not yet meet

The backward consumer is `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`. It requires
an eventual ORIGINAL doubling-window cost estimate against the SAME
surviving filtered-start variance. It does not require separate absolute
bounds on every term in an energy decomposition.

The forward companion identities and their non-coercivity are recorded in
`audits/AUDIT-ORIGINAL-COMPANION-OBSERVED-LOSS-2026-10-04.md`.
Two further attempted bridges are unsupported:

- The score envelope cannot become small: `gap_score_square_ge_one`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialScoreCalibrationObstruction.lean:83`,
  proves `(1-w)*C(w)^2 >= 1` for `1/2 <= w < 1`. This concerns the computed
  UPPER coefficient, not a lower bound on actual energy. Moreover, the
  original-marginal angular cost is not automatically the raw channel cap.
- `originalOwnBlockVariance_comparison`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeOriginalVarianceComparison.lean:79`,
  bounds later variance ABOVE. It supplies no survival lower bound.
  `timeAverage_defect`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeTimeAverages.lean:298`, telescopes
  absolute defect; averaging a fast eigenvector only rescales that vector.
  Neither estimate produces the missing relative dissipation bound.

## A concrete obstruction to generic Ward absorption

An attempted shortcut would bound a negative OWN Ward residue by the
quadratic source cap deficit D, using only positive-source/heat hypotheses.
That inference fails even for a uniformly positive, arbitrarily small
one-link source perturbation.

Let Haar expectation be H, `f=chi_1=2*x_0`, `c=chi_2=f^2-1`, and fix a
strict nome w. Put `lambda=w^8`, `q=1-t*c` with `0<t<=1/64`, and let P be
the finite positive heat with `K>=max(2,headCutoff(w))`.
The exact moment formula `sphereMoment4`,
`lean/YMGap/Continuum/SU2QuaternionPolynomialHaarCarrier.lean:194`, gives
`H(f^2)=1`, `H(f^4)=2`, `H(f^6)=5`, and odd moments zero. Hence
`H(c)=0`, `H(c^2)=H(c^3)=1`. Label-two heat transmission is
`productMap_spinTwo_word`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonSpinTwo.lean:242`,
specialized to a one-letter word: `Pc=lambda*c`.

Under the SAME marginal `W=q*Pq`, direct expansion gives

```
Z = H(W) = 1 + lambda*t^2
m1 = H(W*f)/Z = 0
m2 = H(W*c)/Z = (-(1+lambda)*t + lambda*t^2)/Z
Ward = 4*m2
M = H(q^2) = 1+t^2
L = M-Z = (1-lambda)*t^2.
```

The OWN Ward convention is `complete_ward_own_mean`,
`lean/YMGap/Continuum/SU2QuaternionWeightedCasimirWard.lean:257`.
For this one-link f, `Gamma(f)=4-f^2` and the Casimir is 3; therefore
`Ward=3*Var-H(W*Gamma(f))/Z=4*m2-3*m1^2`.
The corresponding ACTUAL growing-loop identity is `paddedSquare_ward`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean:385`; the
one-link example is NOT an instance of its BF4 terminal source.

Using exactly the two-copy deficit in `sourceCapDeficitCost`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceCompanion.lean:61`,
positivity and `|f|<=2` give the same upper bound as
`companion_add_capDeficit_heatLoss_pin` at `:349` and the nonnegative
companion square:

```
0 <= D = H2[heat*(q-q')^2*(16-(f+f')^2)] <= 32*L.
```

For any rational `C>=0`, choose the explicit rational
`t=1/[64*(C+1)]`. The source satisfies `q>=1-3t>=61/64>1/2`, but

```
-Z*Ward = 4*t*(1+lambda-lambda*t) >= 4*t
C*D <= 32*C*t^2 = [C/(2*(C+1))]*t < t/2.
```

Thus `-Ward > C*D/Z`, even at the FIXED nome `w=1/2`. A linear,
sign-changing Ward response cannot be absorbed by this quadratic deficit
using generic source positivity. This refutes neither the actual BF4 source
nor a JOINT estimate retaining its other linear terms. In particular, it is
not a Yang--Mills counterexample. No extra obstruction module is needed to
continue the actual-source route.

## The spatial alternative already has its geometric lemma

For opposite link incidences `H_plus=U*p`, `H_minus=q*U^-1`, equal
coefficients give

```
Gamma(f+g) + (f-g)^2 = 4*||H_plus-H_minus||^2.
```

This is ALREADY `oriented_pair_angular_difference`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentAngularCancellation.lean:210`.
Its actual original-marginal inequality is
`original_adjacent_marginal_angular_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentAngularCancellation.lean:249`.
For DIFFERENCE rather than SUM, the mismatch requires conjugating
`H_minus`; dropping that orientation is incorrect.

The full signed-family producer is `family_coherent_energy_retained_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`.
The family already has an original completed-state realization via
`familyState`, `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilySourcePin.lean:69`,
and a fixed-nome norm floor via `familyExcitation_norm_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`.
The latter requires `qs.Nodup`; a nonzero excitation also requires a
positive coefficient-square budget.
None of these statements controls the action-weighted holonomy-mismatch
moment relative to a surviving norm on a justified changing family.
Do not duplicate the adjacent cancellation or treat a fixed-nome floor as
its missing scaling estimate.

## Execution decision and verification boundary

Keep TWO analytic candidates, without another interface:

1. Actual growing-square source: complete signed chronological cancellation
   against its SAME filtered-start norm; preserve stage OWN mean and BOTH
   partitions. Do not substitute generic Ward absorption or a circular energy
   re-expansion.
2. Existing coherent spatial family: estimate the SAME interacting mismatch
   moments and its SAME centered norm, then pay the full retained temporal
   debts. Local cancellation alone supplies neither quantitative input.

Prefer whichever obtains an independent original-action estimate first;
the particular growing-square probe is not itself a Clay requirement.
No new premise, sorry, axiom, carrier substitution, frontier weakening,
resource change or CI change was introduced. Source review and the displayed
paper-level calculation do NOT extend any historical compiler/axiom check.
Survival, justified scaling, physical calibration, full OS/QFT, continuum
construction, every-group extension and Clay remain OPEN.
