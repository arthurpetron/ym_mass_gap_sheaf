# Quantitative damping of the original signed baseline

Two focused checks and independent frozen-source review passed. The whole
project target remains OPEN: nontrivial continuum Yang--Mills on R^4 for
every compact simple group, SAME-theory full QFT axioms, and a finite positive
physical Hamiltonian mass gap. This is a fixed-parameter estimate.

## Forward proof and backward finite-source join

On the ORIGINAL completed Wilson carrier put D=I-T,
M_x(k,l)=<x,T^k D^l x>, r=mixFraction and q=mixRate=1-r.
For every vacuum-orthogonal x and every defect degree l, apply the existing
defect gap to T^t x. Commutation and the original time/inner-product pins give

```
r*M_x(2t,l) <= M_x(2t,l+1)
M_x(2t+1,l) + M_x(2t,l+1) = M_x(2t,l)
M_x(2t+2,l) <= M_x(2t+1,l)
M_x(2t,l) <= q^t*M_x(0,l).
```

Taking l=1 and the ACTUAL centered Wilson vector makes the existing joint
limit expression
G_t=(Joint(2t)-Joint(2t+1))-q^t*(Joint(0)-Joint(1)) nonpositive.
No new analytic input is assumed. This quantitative estimate follows from
the already proved fixed-carrier gap; it does not improve that gap's parameter
dependence or construct a surviving excitation.

For the literal original finite source T^t(g_n*(f-c_n)), write

```
d0 = centeredPair(n,2t,f,c_n) - centeredPair(n,2t+1,f,c_n)
d1 = centeredPair(n+t,0,f,c_n) - centeredPair(n+t,1,f,c_n)
S  = normalizedSignedMultiplicationCost(n,t,f)
S  = d0-d1                             (existing exact original pin)
S + (1-q^t)*d1 <= epsilon              (new, at computed late onsets).
```

BOTH original partitions remain in S. The SAME depth-n OWN center c_n is
retained at depth n+t; it is not replaced by a stationary or later OWN mean.
Finite d1 is a SIGNED baseline drop: its positivity is not asserted or
needed. Zero states and t=0 are covered. Strict negative finite payment
would require a separately proved positive baseline and late-error control.

The existing onsets suffice, with delta=epsilon/16. Weighted centering errors
cost at most 2*delta, four raw-joint errors at most 4*delta, and representative
regularity plus eventual G_t<=0 at most 5*delta. Thus 11*delta<=epsilon.
The published cutoff, depth and representative onsets remain Type-valued;
no erased eventual-order witness is extracted to compute an onset.

| Declaration | Source | Role |
| --- | --- | --- |
| `mixedMoment_evenTime_shift` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectGeometric.lean:60` | SAME time/defect pin at T^t x. |
| `mixedMoment_evenTime_step` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectGeometric.lean:86` | Two-step contraction for every defect degree. |
| `mixedMoment_evenTime_geometric` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectGeometric.lean:108` | q^t times the initial SAME moment. |
| `dampedDropLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeSignedMultiplicationLimit.lean:381` | Expression in EXISTING original joint limits. |
| `dampedDropLimit_nonpositive` | `lean/YMGap/Continuum/BF4WilsonAllNomeSignedMultiplicationLimit.lean:387` | Completed quantitative bound with actual centered-vector pin. |
| `dampedDropLimit_representative_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSignedMultiplicationLimit.lean:445` | Computed delta.den onset and 5*delta representative error. |
| `original_signed_baseline_damping` | `lean/YMGap/Continuum/BF4WilsonAllNomeSignedMultiplicationLimit.lean:470` | Direct SAME finite-source damping, without a sign premise on d1. |
| `signedCostCutoffOnset`, `signedCostDepthOnset`, `signedCostRepresentativeOnset` | `lean/YMGap/Continuum/BF4WilsonAllNomeSignedMultiplicationLimit.lean:219`, `:227`, `:238` | Existing independent onsets reused, not enlarged or assumed. |

## Remaining meet

Nome, width, loop and smoothing lag remain fixed. No spacing/volume-uniform
rate, useful changing-family signed-cost/variance budget, or justified scaling
trajectory is supplied. In particular the input to
`aggregate_window_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`, and its original
finite-source consumer `original_window_budget_macro_ratio` at `:245` remain
uninhabited by this result. The full curvature/error/leading-term comparison,
continuum survival, physical calibration, SAME OS/QFT passage, every-group
construction and Clay remain OPEN. Partial A03 support only; the exact
canonical chart claims do not change.

## Verification boundary

Accepted logs, each exit 0 with no warnings/errors and only permitted axioms:

- `/private/tmp/ym-time-defect-geometric-20261004-2.log`: three printed gates;
  SHA256 `49b1397cb7399b187537e1b916b26ec462179373d70d08da5a2e5715d8e81f85`.
- `/private/tmp/ym-signed-baseline-damping-20261004-1.log`: fourteen printed
  gates, four new; SHA256
  `397e6e162140103f8206e47c06cfca43ce8ae96d64a0b37d8cf52aa8289e831e`.

Frozen source SHA256:

- `BF4WilsonAllNomeTimeDefectGeometric.lean`:
  `afddeae3a1821e743873af8d9ca8c838e7597e3ce2335bfea62f28214276d26e`.
- `BF4WilsonAllNomeSignedMultiplicationLimit.lean`:
  `940989e05e68231e2641b8334f752ee1f576a487df8601d331e3cc76b90b9b4d`.

The first producer check failed on opaque time-zero reduction and is rejected
evidence. Existing `completedTime_zero` repaired it; no resource/heartbeat
increase. Each accepted check used ONE monitored 20-GiB worker, a 12-GiB
reserve and fresh process/pressure/swap preflight; swap was zero. Independent
review verified frozen source/log hashes and mathematical scope. No new sorry,
axiom, classical/native_decide/noncomputable declaration, analytic premise or
weakened frontier. Root import registration is NOT root verification. No
full/root build, broad audit, guard or metrics run; CI stays off. No ASCII or
paper-list reprint.
