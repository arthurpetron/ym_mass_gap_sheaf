# Local commutator control of original disjoint face cross energy

The original mixed temporal energy now has an exact second-order expression
and a sharp bound after subtraction of its complete signed cubic/cutoff debt.
The estimate uses two local commutator squares instead of four global source
Casimir-square budgets. It neither controls that debt nor compares these
squares with the interacting OWN variance on a changing family.

## Mathematical argument and original consumer

Write h=1-w, a for the ACTUAL projected original endpoint source, f and g
for the two signed singleton spatial spans, and Z for the original odd mass.
All terms share w, K, width, terminal depth, coefficients and normalization.
Let C be the literal full angular Casimir and define

```
B(a,f) = a*C(f) - 2*Gamma(a,f)
Err(f) = sourceCubic(a,f) - sourceOmitted(a,f)
Err_mix = Err(f+g) - Err(f) - Err(g).
```

The existing `SU2QuaternionCyclicSecondOrder.sourceRemainder_secondOrder`
(`lean/YMGap/Continuum/SU2QuaternionCyclicSecondOrder.lean:197`) and
`SU2QuaternionSecondOrderCancellation.sourceSecondMoment_cancellation`
(`lean/YMGap/Continuum/SU2QuaternionSecondOrderCancellation.lean:118`) retain
the complete source and both signed spectral debts.

Literal link-disjointness makes the angular square additive before weighting.
Apply `DisjointFaceEnergy.weightedAngular_pair`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceEnergy.lean:173`)
under a*a, a*C(a), and a*(P(a)-a), respectively. The mixed first-order,
quadratic source-flux and signed angular-weight-defect terms all cancel.
Linearity of B and its square polarization leave

```
Z*E_mix = -h^2*H[B(a,f)*B(a,g)] + Err_mix
(Z*E_mix - Err_mix)^2 <= h^4*H[B(a,f)^2]*H[B(a,g)^2].
```

The inequality is ordinary Haar Cauchy--Schwarz on these ACTUAL auxiliary
polynomials, not a claimed physical OS norm. Source derivatives in Gamma(a,f)
only act on the observable's incident links; a itself retains dependence on
all original variables. No source independence or density factorization is
asserted. The omitted term is not assigned a favorable sign or declared
uniformly higher order.

## Declarations

All new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceSecondOrder.lean`,
namespace `YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceSecondOrder`.

| Declaration | Line | Exact role |
| --- | --- | --- |
| `sourceCommutator`, `sourceCommutator_pair` | 174, 178 | Actual original-source polynomial and coefficientwise pair linearity. |
| `sourceDebt`, `mixedDebt` | 197, 201 | Explicit signed cubic-minus-omitted quantities. |
| `commutatorCross`, `commutatorSquare` | 207, 211 | Same-source raw Haar pairing and squares. |
| `angularWeightDefect_pair` | 216 | Exact mixed cancellation under the signed change-of-weight density. |
| `signedRemainder_pair` | 328 | Complete original mixed remainder equals the signed commutator cross plus full debt. |
| `mixedEnergy`, `mixedEnergy_mass_pin` | 361, 379 | Unchanged original normalized energy and partition consumer. |
| `commutatorCross_square_bound` | 393 | Sharp Haar Cauchy--Schwarz. |
| `corrected_mixedEnergy_square_bound` | 404 | Sharp corrected original mixed-energy bound. |

The physical consumer requires 0<w<1, strict spatial padding, literal face
membership, link-disjointness and the ORIGINAL head cutoff. It requires no
additional `sufficientCutoff` guard. The earlier finite Wilson-window consumer
`DisjointFaceEnergy.finite_mixed_increment` (its module, line 270) still pins
twice the mixed remainder to the original cutoff/depth schedule. No completed
or changing-parameter inequality is inferred from this finite result.

## Verification

The accepted focused command exited zero:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceSecondOrder.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceSecondOrder.olean \
  --log-file /tmp/ym-disjoint-face-second-order-20261002-second.log
```

All twelve public gates report only {propext,Quot.sound}; the accepted log has
no error, warning, sorryAx or disallowed axiom. The first draft check failed on
polynomial scalar encoding and intermediate-term elaboration; it is NOT
accepted evidence. Independent Sol mathematical review passed the signs,
factor, cancellations, original partition and bound. Luna checked source/gate
coverage and documentation scope separately.

| Artifact | SHA-256 |
| --- | --- |
| source | `e1dbbb308b521965f02823b252fa576fa863d435428a70c7c5e7310bf5ceef7c` |
| accepted log | `f886887d45659596841e767ac315c567ded695f6646d4287d5d2ca0fbca9ae0a` |

The root alone compiled with ONE 20-GiB worker and unchanged 12-GiB reserve.
Preflight found no competing compiler/runner/test and zero swap. Free-memory
pressure readings were 86 percent before the accepted run and 85 percent after.
Post-run swap was also zero.
One semantic-root import is registered, not aggregate-checked. No broad build,
audit, guard, progress metric, literature scan or heavy evaluation ran. No new
sorry, axiom, analytic premise, frontier weakening, safety limit or CI change.

## Remaining mathematical input

Control the combined original signed margin: interacting OWN covariance,
these local source-commutator terms, the exact mixed debt, and the diagonal
margins must jointly give useful slack exceeding the existing common cutoff
allowance on a JUSTIFIED changing family. No such slack or favorable original
instance is supplied here. Spatial/spacing control, every-state scaling decay,
nonzero continuum survival, physical mass, full QFT, every compact simple group
and Clay remain OPEN. No exact displayed status-chart claim changed; its
fenced blocks are preserved and no ASCII chart is reprinted.
