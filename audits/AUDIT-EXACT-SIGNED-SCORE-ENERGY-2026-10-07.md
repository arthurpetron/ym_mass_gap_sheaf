# Exact signed score reassembly (2026-10-07)

Whole-project goal unchanged and OPEN: nontrivial continuum Yang--Mills on
R^4 for every compact simple group, SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap, under the constructive Lean axiom gate.

Previous goal turn: PROGRESS. Commit `adec0fc8` constructed an original-action
full-noise obstruction and proved exact score/signed-bulk null cancellation.
This continuation uses that evidence, not an unproved noise-payment arrow.

## Mathematical decision and actual consumer

The next identity reassembles the TWO signed Taylor terms into genuine
original energy before estimating. Its consumer is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:324`,
`original_block_exact_score_cost_relative_tolerance`: the displayed bulk is
the remaining term in its complete cleared Rayleigh-cost ceiling.

Available inputs:

- `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:95`,
  `reciprocal_score_cleared_derivative`, pins the literal finite derivative
  `A*D(G*b)=G*S+e`, `S=A*Db-b*DA`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:71`,
  `projected_terminal_source_pin`, pins `q=Vbar*A` coefficientwise; `:283`,
  `blockConditionalRatio_fringe_independent`, removes only inactive output
  derivatives after a genuine transfer step.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:132`,
  `energy_taylor_angular`, pins the combined Taylor expression to ORIGINAL
  temporal energy, with the original spatial action and terminal message.

Prediction: an exact square expansion gives a signed reciprocal correction,
not another positive conditional-noise ceiling. Decisive algebraic check:
retain the mixed pairing's sign and the NEGATIVE correction square. Do not
drop either, replace `G` by an exact inverse, or replace `q` by Haar density.
Budget: two serialized focused checks, no full build/audit or numerical sweep.
Revise if the equality changes any source, action, normalization or time.

## Checked identity

All angular sums below run over the actual active links and six planes.
At output `n+r+1`, with the same finite reciprocal degree k, write

```
b=T^(r+1)(g_n*psi), A=g_(n+r+1), phi=G*b,
S=A*Db-b*DA, e=reciprocalScoreCorrection(A,b,k),
L0=sum H[Vbar^2*G^2*S^2],
J =sum H[Vbar^2*(G*S)*e],
E =sum H[Vbar^2*e^2],
Debt=sigma*L0-2*J-E,  Z0=ell[A^2],  ell[p]=H[V*p].

exactScoreAngularBudget = weightedAngularEnergy(q,phi)+Debt,
exactScoreSignedBulk = Z0*(energy(A,phi)+(1-w)*Debt).
```

- `lean/YMGap/Continuum/QuaternionHaarExactScoreEnergySplit.lean:34`,
  `reciprocal_score_weighted_energy_split`, proves the signed square
  expansion with arbitrary polynomial weight and rational sigma. No support
  or positivity premise, absolute value, or square triangle is needed.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy.lean:86`,
  `exactScoreReciprocalDebt`, is the literal signed correction above.
  `:106`, `exactScoreAngularBudget_energy_split`, sums every original plane;
  `:170`, `exactScoreSignedBulk_energy_split`, joins BOTH signed remainders
  to the same original energy.

The original-action joins retain `0<w<1`, `relativeCutoff w 32<=K`, positive
carrier size and supported psi. Sigma is arbitrary because these are
equalities; the existing cost ceiling still requires sigma>0. No canonical
field or older theorem statement is changed. All nome, cutoff, width, depth,
source and degree dependence remains explicit. No uniform estimate is claimed.

## Next estimate and boundaries

CONTINUE with the cleared selected-source estimate

```
Z0*(energy(A,phi)+(1-w)*Debt) <= c_cost*(Z1*B),
Z1=ell[A*T(A)], B=ell[b^2].
```

Here c_cost denotes a proposed COST coefficient, not bare lattice coupling;
it is NOT constructed by this identity. No partition is cancelled. The
signed cross term is indefinite; no smallness or favorable sign is inferred.
The existing reciprocal error onsets do not by themselves bound original
interacting energy or the remaining score contribution along the AF family.

This one-step cost upper estimate serves selected-state survival. It is not
the all-vector relative RG dissipated-form comparison, whose direction and
coarse action/map still require a separate proof. AF survival, actual RG
comparison and its useful budget, spatial/spacing calibration, continuum QFT
and every-group realization remain OPEN. Do not close a chart node from this
finite reassembly; the broad canonical chart is unchanged and not reprinted.

## Verification

Final checks completed 2026-10-07, 18:38 UTC: the generic leaf and the original
leaf pass all 1+3 printed axiom gates within `{propext, Quot.sound}`, with no
errors or sorryAx. The generic focused check emitted its .olean for the
downstream leaf. One monitored worker, mandatory 20-GiB ceiling, 12-GiB OS
reserve, fresh process/memory preflights and zero swap. No competing compiler
or runner was found. Earlier path/namespace/elaboration failures were repaired,
not counted as verification. No heartbeat raise, hole, new axiom or classical
input. No full-root/tree build/audit or baseline refresh. Root imports are
registered separately, not whole-root checked.

Final logs and SHA-256:

- `/private/tmp/ym-oct7-exact-score-energy-split.log`:
  `2ae6ab7e118f588e4b25fee20f823fd6d9cbc2f112653dd5041187f5b4df9695`.
- `/private/tmp/ym-oct7-original-signed-score-energy.log`:
  `61acbf2757c93ab55822b73b0414989ef61526318efe2cda782130a953de4294`.

An independent read-only source review confirmed the correction signs,
active/inactive split, original source pin, both Taylor terms and outer
`Z0*(1-w)` factor. Review and proof establish an identity, not the missing
quantitative estimate.
