# Literal dyadic Wilson squares and SAME reflected time moments — 2026-09-24

## Scope and causal consumer

Baseline: `ea7f6fd`. This milestone constructs an actual changing-size Wilson
word family and connects its existing original-action scalar increment bound
to a reflected form at the SAME literal spatial width. It adds no analytic
hypothesis, completion, physical coupling trajectory, or continuum claim.
Canonical A03 and J02 remain OPEN; no chart marker or label changes.

The new endpoint is
`BF4WilsonAllNomeLoopTimePin.dyadic_reflected_loss_bound`
(`lean/YMGap/Continuum/BF4WilsonAllNomeLoopTimePin.lean:84`). For the actual
padded square x of side L=2^s it proves

```
2 * (F(x,x) - F(x,advance L x)) <= 384 * L^3 * (1-w).
```

F is the ORIGINAL fixed-width joint-limit reflected form constructed below,
not the old face-span completed inner product. The inequality is absolute,
not relative to centered variance. Its cubic inverse-spacing cost is retained.

## Literal geometry and assigned spacing

- `BF4ExactSlabFixedSpatialWilsonSquare.squareLoop`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSquare.lean:301`)
  returns a `SourceLoop side`: the ordered east/north/west/south boundary
  word has proved endpoint compatibility, closure and membership in the
  existing spatial-link carrier. Side zero is allowed; dyadic members have
  strictly positive side.
- `BF4ExactSlabFixedSpatialWilsonSquare.squareEdges_endpoints_inSquare`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSquare.lean:241`)
  bounds both endpoints in the displayed square. Direction-specific strict
  origin bounds justify each positive-link endpoint; an origin bound alone
  would have been insufficient.
- `BF4DyadicWilsonSquare.spacingModulus` and `.spacing_small`
  (`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:51`, `:53`) supply the
  explicit epsilon-to-scale threshold `epsilon.den` for spacing=(1/2)^s.
- `BF4DyadicWilsonSquare.unit_side` and `.unit_perimeter`
  (`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:62`, `:68`) prove
  spacing*L=1 and spacing*wordLength=4 as exact rational equivalences.
  The reused `ThermodynamicDyadicEnergy.half_power_normalizes` is scalar
  arithmetic only; its older carrier is not used in the construction.
- `BF4DyadicWilsonSquare.paddedSquare_edges`
  (`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:84`) proves that enlarging
  the room witness with spatial shift zero leaves the literal word unchanged.
  The strictly larger width is the actual width of the expectation; equality
  of expectations at different widths is NOT asserted.
- `BF4DyadicWilsonSquare.unitTimeIncrement_bound`
  (`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:115`) instantiates
  `BF4WilsonAllNomeTimeIncrement.padded_timeIncrement_nome_bound`
  (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeIncrement.lean:131`). Since
  wordLength=4L and elapsed lattice steps=L, its existing
  `24*n*wordLength^2*(1-w)` bound becomes `384*L^3*(1-w)`.
- `BF4DyadicWilsonSquare.cubic_spacing_calibration`
  (`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:125`) proves that multiplying
  this bound by spacing^3 gives exactly `384*(1-w)`. This identity is NOT a
  field renormalization prescription or a justified nome/spacing relation.

## Reflected form on the literal original action

`BF4WilsonAllNomeReflectedForm.commonForm`
(`lean/YMGap/Continuum/BF4WilsonAllNomeReflectedForm.lean:112`) is literally

```
originalJointLimit hw0 hw1 (2*H) (.mul (mirror H e) f) ...
```

at the SAME `width` parameter as e and f. An initial draft's spatial collar
was removed before acceptance: no `centeredExpression`, shifted loop or
enlarged-width action is substituted here. Assumptions are only `0<w<1`
and the explicit temporal-window support guards; no small-nome/entropy
condition is used.

The limit and its explicit approximation data are the existing
`BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJointLimit`,
`.jointModulus`, and `.originalJoint_approx`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:118`,
`:57`, `:131`). No new limit or erased modulus is chosen.

`BF4WilsonAllNomeReflectedForm.originalWindowScalar_reflected_symm`
(`lean/YMGap/Continuum/BF4WilsonAllNomeReflectedForm.lean:64`) uses original
selected-chain reflection and the exact finite window-ratio normalization.
`.commonForm_symm` and `.commonForm_nonnegative` (`:137`, `:149`) transport
the actual finite symmetry and reflection positivity to that joint limit.
`.commonForm_shift` (`:120`) removes simultaneous temporal padding using the
existing joint-limit identity, without changing the spatial width or action.

`.intrinsicForm` and `.intrinsicForm_chart` (`:154`, `:163`) use the existing
radius-tagged Wilson syntax and prove independence of the chosen valid common
temporal chart. `.intrinsicForm_symm` and `.intrinsicForm_nonnegative`
(`:182`, `:190`) give symmetry and diagonal positivity. This milestone does
not yet supply its all-nome seminorm completion or completed transfer.

## Exact SAME-observable time realization

`BF4WilsonAllNomeLoopTimePin.loopState`
(`lean/YMGap/Continuum/BF4WilsonAllNomeLoopTimePin.lean:40`) is the literal
fundamental Wilson expression of radius zero. `.time_pairing_lag` (`:45`)
proves, for EVERY natural m,n,

```
F(advance m x, advance n x) = lagMoment(loop,m+n).
```

At common center H=max(m,n), the reflected insertion is at H+m and the
other at H-n. Their lag is m+n, not |m-n|. The existing original joint
padding law removes the unused window and retains the same expectation.
`.norm_pin` (`:64`) is its zero-lag specialization.

`.timeIncrement_reflected_pin` (`:72`) combines these identities with the
existing original-state polarization to prove

```
timeIncrement(loop,n) = 2 * (F(x,x) - F(x,advance n x)).
```

The dyadic inequality at the beginning is the direct consumer of this exact
pin. No map into a different Hilbert space is used or assumed.

## Remaining joins and next work

The existing `BF4ExactSlabFixedSpatialJointPhysicalTime.JointCompletion`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPhysicalTime.lean:111`)
uses face-span syntax. An arbitrary closed Wilson word has NOT been mapped
into that completion here. In particular, this milestone does not supply
the input to `BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:112`).
The older enlarged Wilson `Completion`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonCompletedInner.lean:109`)
has different small-nome/spatial-limit hypotheses; it is not silently reused.

Next carrier work: extend the literal all-nome reflected form through its
actual rational algebra, squared-seminorm completion and time operator,
retaining these loop-moment pins. This addresses the missing observable
domain, not the analytic survival bound. Any use of the old face-span gap
requires a proved same-form/carrier bridge, not just the two APIs' similarity.

A03 still requires useful control relative to the SAME centered variance
on a justified scaling family, or a direct nonzero response bound. Assigned
spacing alone selects neither a physical coupling trajectory nor a spatial
volume schedule and proves no cross-scale convergence. Nonzero centered
norm survival, EVERY-state decay through scaling, SAME thermodynamic and
continuum limits, full QFT/YM/UV structure, physical time/Hamiltonian/mass,
and every compact simple group remain OPEN.

## Verification boundary

Four final narrow serialized checks used `scripts/safe_lean_build.py --jobs 1`,
a 2 GiB worker cap, unchanged 12 GiB OS reserve and default elaboration limits.

| File under `lean/YMGap/Continuum/` | Final log in `/tmp/` | Printed gates |
|---|---|---|
| `BF4ExactSlabFixedSpatialWilsonSquare.lean` | `ym-gap-wilson-square-check-4.log` | 5 |
| `BF4DyadicWilsonSquare.lean` | `ym-gap-dyadic-wilson-square-check-2.log` | 13 |
| `BF4WilsonAllNomeReflectedForm.lean` | `ym-gap-wilson-all-nome-form-check-2.log` | 9 |
| `BF4WilsonAllNomeLoopTimePin.lean` | `ym-gap-wilson-loop-time-pin-check-1.log` | 6 |

All 33 final printed dependencies lie within `{propext, Quot.sound}`;
some computational declarations have no axioms. The form has one harmless
unused-support-argument warning. Earlier geometry simplification introduced
`Classical.choice`; that development result was rejected. Explicit side-bound
and endpoint constructors removed the dependency. Earlier syntax, list
association, projection and dependent-rewrite errors were repaired without
raising limits. No forbidden dependency or failed elaboration was accepted.

No new `sorry`, axiom, analytic premise, canonical-field weakening or safety
stop. No full-root build/audit/guard or progress-metric run was performed.
The semantic-root import is recorded, not claimed freshly root-compiled.
Schema 1 snapshot 9 updates evidence only; its fenced chart is unchanged.
