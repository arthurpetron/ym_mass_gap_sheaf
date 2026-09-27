# Original completed block-pair algebra

Date: 2026-09-27 UTC. Starting commit: `584b0f7`.
Whole-project target remains open: nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT structure and positive
physical Hamiltonian mass gap within the constructive axiom gate.

## Exact remote commutation

`conditionalProjection_commute` at
`lean/YMGap/Continuum/BF4ExactSlabBlockNonneighborCommutation.lean:142`
proves `Q_S Q_T x = Q_T Q_S x` for EVERY vector of the original full-action
completion. The operators are the actual constructed block conditionals,
not freely chosen reference projections. Hypotheses: rational `0<w<1`,
`K>=headCutoff(w)`, finite in-range physical link lists S,T, and

```
LinksDisjoint T (faceLinks extent (collar extent S)).
```

Only this one collar-separation condition is assumed. There is no extra
S/T-disjointness or reverse-separation hypothesis, no nonempty/nodup premise,
and no small-nome restriction. A selected link with no incident action factor
need not be excluded. No action factor is deleted from either operator.

The short proof is explicit in the same module:

| Declaration | Line | Role |
| --- | --- | --- |
| `collarHeat_independent_of_separated` | 46 | Literal plaquette support omits each selected T coordinate. |
| `approximateInverse_preserves_independent` | 64 | Polynomial inverse iteration preserves any coordinate absent from both source and normalizer. |
| `conditionalRep_preserves_independent` | 90 | The supplied original Cauchy sequence retains T independence. |
| `conditionalProjection_preserves_exterior` | 105 | Q_S sends T-exterior polynomial states into the fixed space of Q_T. |
| `conditionalProjection_invariant_dense` | 117 | Q_T Q_S Q_T = Q_S Q_T on embedded dense states. |
| `conditionalProjection_invariant` | 132 | The same identity on every completed vector. |
| `conditionalProjection_commute` | 142 | Self-adjointness turns range invariance into commutation. |
| `remote_residual_pair_nonnegative` | 152 | Remote mixed residuals contribute nonnegatively to the original energy sum. |

The completion steps reuse `fixed_of_cauchy_terms`,
`fixed_of_cauchy_images` and `invariant_range_of_dense` in
`lean/YMGap/Continuum/GNSDenseFixedPoint.lean`, and
`commute_of_invariant` in `lean/YMGap/Continuum/GNSProjectionCommutation.lean`.
No representative of an arbitrary quotient is selected by choice.

## Nested tower and actual schedule-family input

`blockFamily` at `lean/YMGap/Continuum/BF4ExactSlabBlockTower.lean:44`
instantiates the existing projection-family interface with the actual original
operators, indexed by finite in-range physical link lists. It supplies no gap
hypothesis. It is consumed by both new mixed-residual nonnegativity proofs and
is available to the existing schedule/neighbor algebra.

In that same module, `slots_subset_of_links_subset` (`:55`) carries literal
link inclusion into slot inclusion. For A contained in B, `tower_dense`
(`:71`), `tower` (`:89`), and `reverse_tower` (`:101`) prove
`Q_A Q_B = Q_B = Q_B Q_A` first densely and then on EVERY completed vector.
`nested_commute` (`:117`) and `nested_residual_pair_nonnegative` (`:125`)
give the exact pair consequence. The reverse composition is proved by
self-adjointness, not by falsely declaring the smaller-block output exterior
to the larger block. These are ordinary weighted-L2 conditional identities.

## Signed interacting estimate: review, not a new proof

The parallel mathematical review separates exact projection algebra from the
missing analytic estimate. For nested blocks, conditional tower identities
are available from exterior fixation. For general overlapping blocks, the
union's exterior projection is fixed by both block projections; this does
NOT imply that the block projections commute or that their product equals
the union projection.

Writing R_A=I-Q_A, E_A=||R_A x||^2, polarization gives the equivalent
prediction-difference form of the proposed signed estimate:

```
<R_A x,R_B x> >= -eta*(E_A+E_B)
    iff
||Q_A x-Q_B x||^2 <= (1+2*eta)*(E_A+E_B).
```

This paragraph records the reviewed algebraic target, not a newly checked
Lean declaration or a supplied analytic bound. Removing the common exterior
mode does not bound the angle between the remaining interacting ranges.
The current near-Haar comparison cannot simply be extended by invoking a
tower identity.

For a fixed polynomial source p, actual inverse approximants a_n,b_m give
the exact signed rational test `F.B (F.sub p a_n) (F.sub p b_m)`, with F the
SAME original full-action datum. All spectator factors remain present.
The recurrence uses the two actual normalizers; it does not license a
polynomial expression with pointwise reciprocals `1/(D_A*D_B)`.
An explicit original-norm approximation bound could bracket that test's
completed pairing. Such a certificate for one source is not an all-vector
angle bound. The existing L/U approximation constants deteriorate with
nome and block size; convergence of the numerical inverse is not mixing.

The targeted review found NO uniform finite-dimensional/degree-tail reduction
for this actual fullData block-pair problem. Modules searched:
`BF4ExactSlabBlockConditionalApproximation`, `BF4ExactSlabStarVariationalApproximation`,
`SU2QuaternionGroupedHarmonicTail`, `BF4ExactSlabFixedSpatialActualSeedNorm`,
and `ThermodynamicUniformPolynomialLinear`, under `lean/YMGap/Continuum/`.
The relative inverse cutoff controls iteration error, not the input's
polynomial degree: a finite iteration operator is not a finite matrix.
The next analytic producer must cover every supported polynomial, or provide
a genuine high-degree tail bound before using a finite-matrix lower margin.

## Consumer and remaining work

Remote commutation removes remote commutator errors. Its mixed residual
terms are nonnegative squares, not zero in general. Nested-block algebra
likewise does not supply the interacting non-nested estimate.
The ordered-pair consumer is `neighboringCross_lower` at
`lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142`;
`energy_contract` at
`lean/YMGap/Continuum/GNSResidualGeneratorDescent.lean:112`
requires the resulting genuine generator-square lower bound.

A useful actual block schedule still needs its cover, row/column counts,
propagation geometry and signed interacting estimate. The single-link
degree 25, loss 625 and sixteen-layer cone are not block constants.
The intended physical rate must be calibrated on a justified scaling family
with nonzero finite-physical-time survival. Ordinary weighted-L2 conditional
dynamics is not the reflected OS transfer or physical Hamiltonian.
Selected-face boundary/thermodynamic control, same-theory scaling/OS/QFT,
nontriviality, physical mass and every-group Clay remain open.

## Verification boundary

Both files passed focused checks: all 15 printed axiom gates lie within
`{propext, Quot.sound}`. One missing proof-only binder was corrected before
the remote file's successful run. All compiler invocations used the safe
launcher with one worker and a 20 GiB ceiling; no concurrent compiler ran.
Sol supplied the tower proof and analytic review; Luna reviewed the minimal
geometric premise and edge cases. No heavy verification was delegated.
No new sorry, axiom, analytic bundle or weakened canonical field was added.
No full build, root build, audit, guard, progress-metric run or CI was run.
The canonical chart's displayed claims and markers are unchanged.
