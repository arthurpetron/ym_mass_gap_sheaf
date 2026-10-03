# Selected-response survival: a checked two-mode obstruction

## Goal and result

The whole-project target remains a nontrivial continuum Yang--Mills theory
on R^4 for every compact simple group, with same-theory QFT axioms and a
positive physical Hamiltonian gap. This checkpoint closes no continuum node.

The generic implication from a rate-compatible slow mode, positive overlap
and unit zero-time response to a uniform selected-response macroscopic ratio
is false. An explicit rational two-mode family proves this constructively.
This is scalar positive-mode data, NOT an original BF4 carrier/action
instance and NOT a Yang--Mills counterexample.

## Explicit family and declarations

Write s=n+1, v=2^(-s), alpha=v^4, q=1-1/(2s), r=1/(1+alpha).
The literal response is C_n(j)=r*(alpha*q^j+2^(-j)). Alpha is the raw
slow-mode weight; its normalized weight is r*alpha. Only a known positive
rational total weight is inverted.

All declarations in this section belong to
`YMGap.Continuum.RationalTwoModeSurvivalObstruction`.

| Declaration | Source | Checked conclusion |
| --- | --- | --- |
| `horizon`, `fastHorizon`, `slowOverlap`, `slowRate` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:33`, `:35`, `:37`, `:40` | Literal computed s, v, alpha and q. |
| `slowOverlap_positive` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:67` | Alpha is positive at every finite n; no uniform floor is asserted. |
| `slowRate_bounds`, `slowRate_lt_one` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:78`, `:89` | 1/2<=q<1, so there is no stationary extra mode. |
| `horizon_rate_loss` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:97` | s*(1-q)=1/2 exactly. |
| `normalization`, `response`, `response_zero` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:112`, `:115`, `:118` | The actual normalized positive two-mode response has C_n(0)=1. |
| `response_fast_floor`, `response_positive` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:126`, `:139` | C_n(j)>=r*2^(-j)>0. |
| `response_doubling_upper` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:145` | C_n(2s)<=2*2^(-s)*C_n(s). |
| `failureCutoff`, `eventual_macro_floor_false` | `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:193`, `:208` | For every rational kappa>0, kappa*C_n(s)<=C_n(2s) fails whenever geometricCutoff(1/2,2,kappa/2)<=s. |

The short argument retains both modes: alpha<=v^2 and q<=1 give the raw
doubling numerator at most 2*v^2, while the raw horizon response is at
least v. The SAME positive r multiplies both. The existing explicit
geometric cutoff gives 2*v<=kappa/2; positive C_n(s) contradicts the
proposed kappa floor. No spectral theorem, choice, or arbitrary-real
division enters the proof.

## Forward/backward consequence for the actual route

The EXISTING backward endpoint is
`BF4WilsonAllNomeWindowSignedCost.original_window_budget_macro_ratio` at
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
It consumes an actual eventual finite ORIGINAL normalized budget

    2*sum_(t=u..2u-1) originalOwnBlockCost(stage,t)
      <=(1-kappa)*originalOwnBlockVariance(stage,u)

and proves the SAME completed ratio kappa*R(2u)<=R(4u). It does not
produce the budget or justify a changing family.

The current forward estimate is
`BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.original_block_sourceDerivative_cost_relative_tolerance`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.lean:448`.
Its actual unsplit conditional square is defined by
`lastStepSourceDerivative` and `lastStepSourceDerivativeBudget` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:65`
and `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:73`.
The useful joint comparison remains unsupplied; a rate calibration is
not a replacement for this same-source estimate.

The concrete tested-mode reserve already exists in
`BF4DyadicWilsonSquareLoopModeReserve.paddedSquare_own_block_cost_loop_reserve`
at `lean/YMGap/Continuum/BF4DyadicWilsonSquareLoopModeReserve.lean:217`.
It retains the actual own-centered filtered b, both partitions and the
tested overlaps ell(b), ell(b*f). It does NOT construct a useful magnitude
of this reserve relative to Z1*ell(b^2) on a changing family. The new
obstruction explains why positive overlap alone cannot fill that omission.

The actual smoothing theorem
`BF4WilsonAllNomeTimeDefectTail.mixedMoment_column_bound` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:87` bounds
M_x(k+n,l+1) by M_x(k,l)/(n+1), not by the later surviving norm.
`BF4WilsonAllNomeResponseLower.response_step_lower` at
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:102` and
`BF4WilsonAllNomeBlockResponseLower.response_shifted_block_step_lower` at
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:104`
propagate a SUPPLIED relative floor; they do not construct it.

Execution consequence: continue seeking the COMPLETE normalized signed
window estimate, or an actual quantitatively sufficient selected-source
overlap estimate. Do not open a new branch that assumes slow-rate
compatibility or generic preimage smoothing alone supplies survival.
No new assumed-input bundle or changed canonical field is introduced.

## Verification boundary

Final focused check, exit 0:

    python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 \
      --check-worker-limit-gib 20 --status-seconds 300 \
      --log-file /tmp/ym-two-mode-survival-20261003-2.log \
      --check lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean \
      --check-output lean/.lake/build/lib/lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.olean

All 16 public printed gates are within {propext, Quot.sound}; the log has
no error or warning. An independent source/math review passed; its strict
rate documentation suggestion was implemented using the existing helper.
The first focused check also passed, before that strict lemma was added.

- Final source SHA-256: `d3dd9e4c2ba343523141456939b7fab414c27b14909a6916faf10275b013a025`.
- Final log SHA-256: `a4fea603c1abc2a95fbc033aaa6a66d2f4bffb7f9bec7f078cd1ba7ec7ddb385`.
- Dynamic preflight: 64 GiB host, 75% free at final launch, zero swap,
  no existing Lean worker; one serialized worker with a 12 GiB reserve.
- Root import is registration only. Full-root/full-tree/audit/guard NOT run.
- No sorry added or discharged, no axiom, classical shortcut, weakened
  frontier field, CI change, or exact displayed chart claim changes.

The actual signed window budget, conditional Jensen/action debt, justified
spatial/spacing/coupling family, continuum survival, physical calibration,
full QFT, every-group theorem and Clay closure remain OPEN.
