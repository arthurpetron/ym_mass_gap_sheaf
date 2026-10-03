# Actual angular Bochner square and finite heat composition

## Result and scope

Four new leaf modules construct local SU(2) curvature and actual finite
head-heat composition. No Bochner bound, Casimir centrality, conditional
Poincare inequality, or signed-window estimate is supplied as a hypothesis.
These extend the bracket/endpoint results recorded in
`audits/AUDIT-FINITE-HEAT-FLOW-ANGULAR-BRACKETS-2026-10-03.md`.

The unchanged Clay target remains OPEN: a nontrivial SAME continuum theory
on R^4 for EVERY compact simple group, with full required QFT structure and
a finite positive physical Hamiltonian gap. None of those conclusions is
claimed by these local identities.

## Actual Casimir centrality

The existing literal rotations are D_ij=x_i*partial_j-x_j*partial_i. Their
six-square Laplacian L and energy Gamma are `angularLaplacian` and
`angularSquare`, `lean/YMGap/Continuum/QuaternionHaarLinearAngularEnergy.lean:47`
and :50. No new Laplacian replaces them.

`angularLaplacian_angularDerivative_carrier`,
`lean/YMGap/Continuum/SU2QuaternionAngularCasimirCentrality.lean:309`, proves
L(D_ij p)=D_ij(Lp) as HaarCarrierEqv for blocks>0, i,j<4, and arbitrary p.
The equality holds under EVERY original Haar insertion; other blocks remain
shared spectators. No support restriction on p is added to this identity.

Overlapping square commutators cancel in pairs using the actual brackets.
`same_left_planes_reorder` (:53) and `shared_middle_planes_reorder` (:74)
in that file expose the two signed reorderings. Disjoint and own squares
commute; finite explicit coordinate cases identify the ordered Casimir with
the original six-plane sum. The final accepted proof uses explicit false
elimination in impossible coordinate cases, not a classical tactic fallback.

## Complete Hessian square, with the commutator factor retained

In `lean/YMGap/Continuum/SU2QuaternionAngularHessianSquares.lean`,
`field` (:38) enumerates 01,02,03,12,13,23. `commutatorSquare` (:229),
`hessianSquare` (:235), and `symmetricSquare` (:239) contain ALL 36 ordered
field pairs. Writing X_ab=D_a D_b p, the two checked identities are:

```text
sum_(a,b) (X_ab-X_ba)^2 = 4*Gamma(p)
Hessian(p)-Gamma(p) = (1/4)*sum_(a,b) (X_ab+X_ba)^2.
```

They are `commutator_square_carrier` (:245) and `hessian_margin_carrier`
(:280) in that file, as HaarCarrierEqv for blocks>0 and arbitrary p.
Each output field occurs four times in the ordered commutator table.
The integer-reflected matrix identity is 4*Hessian=commutatorSquare+
symmetricSquare; rational scaling by 1/4 is then handled separately.
Reflection never expands the input's raw derivative lists to certify a
particular sample: it normalizes a finite identity in 36 opaque entries.

`hessian_curvature_certificate` (:313) constructs a Certificate of the
margin when p is supported in the original blocks. Its witness contains
the actual supported symmetric squares, addition, nonnegative scaling and
carrier transport. No constructor from an asserted analytic inequality
is used; see `Certificate`,
`lean/YMGap/Continuum/QuaternionHaarSquareCertificate.lean:62`.

## Actual Gamma2, not a Hessian-defined substitute

`mixedGamma` and `gamma2`,
`lean/YMGap/Continuum/SU2QuaternionAngularBochner.lean:41` and :45, define
the polarized energy and the ORIGINAL iterated energy:

```text
Gamma(p,q) = sum_a (D_a p)*(D_a q)
Gamma2(p) = (1/2)*L(Gamma(p)) - Gamma(p,Lp).
```

`gamma2_hessian_carrier` (:98) proves Gamma2(p)=Hessian(p), retaining
every insertion. The proof applies `angularLaplacian_square`,
`lean/YMGap/Continuum/QuaternionHaarExposedFundamentalEnergy.lean:137`,
to each first derivative, sums using `angularLaplacian_six`,
`lean/YMGap/Continuum/QuaternionHaarAngularLaplacianLinear.lean:176`, and
uses actual centrality to cancel the mixed first-order terms. A finite
coefficient identity exchanges the two Hessian index orders.

`bochner_curvature_certificate` (:117) constructs Gamma2-Gamma's square
certificate, without a curvature premise. `weighted_bochner_nonnegative`
(:126) proves nonnegative Haar value after multiplication by ANY supplied
Certificate of positive ORIGINAL output W. W may overlap spectator
coordinates; independence is not assumed.

The curvature coefficient ONE is local to this bare angular Laplacian on
the concrete SU(2) quaternion carrier. This is not a curvature bound for
the full interacting/drift generator, the OS transfer, or the physical
Hamiltonian; no beta- or spacing-uniform physical mass is asserted.

## Actual shared-spectator finite heat composition

The original map is `headMap`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:247`, defined by
conditionalHeat(copy(p)) with a distinct heated input and shared spectators.
It is NOT being identified with the completed Yang--Mills transfer T.

In `lean/YMGap/Continuum/SU2QuaternionHeadHeatSemigroup.lean`,
`headMap_carrier` (:49) transports carrier equality through that actual
map with both input supports retained. `headMap_harmonic` (:83) identifies
its retained OR omitted harmonic attenuation under EVERY surviving test.
`headMap_semigroup` (:173) proves, for supported p:

```text
headMap u K (headMap v K p) = headMap (u*v) K p
```

as HaarCarrierEqv on tail+1. The inclusive cutoff K is the SAME on both
steps. It need not contain every input degree: an omitted mode stays zero.
No nome positivity, finite-kernel positivity or saturation is assumed for
this algebraic identity. Spectators are never resampled independently.

## Forward/backward join still to construct

The next missing result is the actual conditional reference angular
variance estimate. Its required source remains ORIGINAL Q_K, not Q_L:
`projectedReferenceVariance`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:83`.
The already checked near-unit cutoff consumer is
`projected_variance_cutoff_weighted_le` (:133) there. Only its auxiliary
conditional kernel changes cutoff; the original action/transfer/source do not.

Unpaid seams are nome-generator differentiation, constructive endpoint
order, intermediate positive-prefix transport, and any needed particular
fresh-output/unit-block identification. Nome-one reproduction is not kernel
positivity at one. Arbitrary Haar insertions are not a diagonal delta.
No generic rational mean-value theorem is assumed available.

The backward consumer remains `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`. Its
eventual COMPLETE original signed-window budget on a JUSTIFIED scaling
family is still missing. Signed action/Taylor terms and the SAME surviving
norm must be retained. Local curvature or an unweighted smoothing estimate
does not fill that hypothesis. Physical calibration, continuum survival,
OS/QFT/scaling/every-group/Clay closure remain OPEN.

## Focused verification and reproducibility

Each accepted source was checked through `scripts/safe_lean_build.py` with
one worker, a 20 GiB worker cap, 12 GiB reserve and five-minute status
interval. Checks were serialized; process/swap/memory preflight was fresh
at every launch. Accepted final preflights reported 77% free system memory
and zero swap. No safety stop occurred. Only finite-reflection recursion/
heartbeat limits are locally scoped in the proof source; worker/reserve
limits were not raised. Independent mathematical reviews found no sign,
factor, index-order, spectator or scope defect.

Four final checks passed, with 12 public axiom outputs ALL exactly
{propext, Quot.sound}. No sorryAx, Classical.choice or new axiom was accepted.
Earlier compile/gate failures were repaired, not counted as checks.
Root imports are registration only; no full root build, full axiom audit or
Clay-frontier guard was run. No .lean sorry, axiom or classical declaration
was added or discharged. The canonical displayed chart's claims are unchanged.

| Accepted leaf | Accepted log in /tmp | Source SHA256 | Log SHA256 |
| --- | --- | --- | --- |
| SU2QuaternionAngularCasimirCentrality.lean | ym-angular-casimir-centrality-20261003-8.log | 9f399902c09be3e3df163c37ce2b7da2366a1502c98f8e0f33038866f49142eb | 0243d3c4d3ebea0caf9259fd282f287416f189d821c451d5b7c208f93ad0111a |
| SU2QuaternionAngularHessianSquares.lean | ym-angular-hessian-squares-20261003-3.log | 8d3960de52ec78cedc44a7aa81b3afb8e2c1e1f8310538954b8cadd8aeeb4711 | c48a163ddc789919a3d23cab48148885dea34c9a6454f691237c2a6b35e61d92 |
| SU2QuaternionAngularBochner.lean | ym-angular-bochner-20261003-3.log | 172eb95fe48f37a2e5550c9f2281744a918d6d49f62c1c2f493932e19faf117b | 55cd38bd4f1edae3555087e411b08ff4ce5ec7542f9d3c9bb647c58cc90b82ec |
| SU2QuaternionHeadHeatSemigroup.lean | ym-head-heat-semigroup-20261003-2.log | c87c8acca3b25425b87790a6fe069aaefed093028640b22ef84590af50f35083 | 5c1a82a3cdc3f93c190d3c499a2362f6b15f6952567ca62e4aed077b17ca103f |
