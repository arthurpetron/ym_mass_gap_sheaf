# Clay resolution target: clause-to-carrier inventory

Status: Phase A session-5 corrected architecture inventory, 2026-07-17.

This document maps every clause of `docs/ym_mass_gap_prompt.md` to the
strongest current Lean carrier and records the exact repair needed before a
canonical `ClayResolutionTarget` can honestly represent the terminal theorem.
It is a design input, not a proof and not a frontier-closing claim.

## Governing rule

The canonical target is rooted in one Schwinger functional, its ordinary
ambient state GNS datum, and its separate completed reflected positive-time OS
reconstruction.  The group, lattice approximants, continuum limit,
translations, transfer semigroup, Hamiltonian, spectrum, local fields, OPE, and
stress tensor must all be pinned to that same root.  A collection of separately
inhabitable structures is not sufficient.

The target must not be inhabited by any of the repository's deliberately
available toy objects:

- `localCurvatureFields_triv`, `stressTensor_triv`, or `ope_triv`;
- `afShortDistance_su2` without a correlator pin;
- `GNSData.idTransfer` or `trivialSpectralGapData`;
- the abstract `OSReconstruction` `Unit` witnesses with freely selected law
  propositions;
- `PentagonRelation.numericShapeWitness`;
- `SpectralLocalizationCrux.trivialLocalization`;
- the legacy true-margin or bounded-functional-calculus generic witnesses.

## Clause inventory

| Prompt clause | Strongest current carrier | Adequacy verdict | Required canonical field or repair |
|---|---|---|---|
| Every compact simple `G` | `RG.CartanType`, `MassGap.AllSimpleTypes.IsSimpleRank`, `repDataOf`, `admissible_of_cartanType` | Classification-facing Casimir data exist, but a Cartan type does not determine the global form (`SU(n)` vs `PSU(n)`, `Spin(n)` vs `SO(n)`), allowed representations, bundles, or line operators. The physical measure, observable algebra, and character tails are not indexed by one actual group. | Parameterize by a computable compact global group/root datum and chosen faithful lattice action; derive `T : CartanType` as a projection. Pin all representation, heat-kernel, lattice, AF, and tail data to that group, including descent through the center and short-root normalization. |
| Four-dimensional pure Yang--Mills lattice family | `ContinuumMeasure.ProjectiveSystem`, finite-volume Wilson/character modules, `CanonicalOSRoot.ReferenceWeightStageFamily` | `ContinuumMeasure` stores a consistent thread of arbitrary values, while bare Wilson measures at different spacings are not exact block marginals. The new two-parameter stage interface records spacing, volume, weights, and support certificates but is not yet group/action-pinned. | Add a `PinnedWilsonLatticeFamily G` containing link/plaquette geometry, the global group/action, bare Wilson weights, normalized functionals, and comparison maps. Treat exact projective consistency only as an effective-RG theorem, not as a law of the bare family. |
| Thermodynamic limit `T^4 -> R^4` | `ContinuumLimitData.cluster`; `ContinuumMeasure` inverse-limit thread | The inverse-limit thread is not a thermodynamic probability-functional limit. `ContinuumLimitData` gives masses and a modulus but is not pinned to the Wilson family or Schwinger functional. | Carry a volume-directed functional limit with an explicit modulus; prove all local correlators converge uniformly on bounded support and that the limit equals the canonical Schwinger functional. |
| Continuum limit `a -> 0` | `FunctionalContinuumTarget.scaling`, `ScalingLimitModulus`, `ContinuumLimitData.continuumModulus` | Genuine modulus interfaces exist, but their functionals/masses are not tied to the same lattice family and reconstructed spectrum. | One two-stage or joint limit object, pinned to the lattice family and canonical functional, transporting OS laws, local correlators, and the gap. |
| OS0 regularity/temperedness | `OSAxioms.IsOS0`; `OSAxiomAudit.GJ_OS1_Regularity` | Present predicates are heat-kernel normalization bounds, not full continuum distributional regularity or tempered Schwinger growth. `IsOS0` does not use `mu_inf`. | State constructive test-function spaces, multilinear Schwinger functionals, continuity/growth moduli, and the regularity theorem for the canonical functional. |
| Euclidean translations and full `O(4)` | `IsOS1HypercubicTranslation`, `IsOS1HypercubicH4`, `O4RestorationContent` | Current actions are single freely supplied endomorphisms. They do not encode a group action, the full Euclidean group, strong continuity, or identity with the canonical functional. | Carry an `E(4)` action with identity/composition/inverse laws, covariance of every Schwinger function, and continuity; pin its lattice dense-subgroup restriction to the lattice symmetries. |
| Permutation/symmetry axioms | `IsOS3Symmetry` | A single equivariant endomorphism is weaker than all Schwinger permutation, reflection, and covariance laws. | State the complete family of symmetry laws on the canonical `n`-point functionals. |
| Reflection positivity | `IsOS2ReflectionPositivity`; `CanonicalOSRoot.PositiveTimeOSRoot.reflectedForm`; many Z4 RP modules | Strong cutoff ingredients exist, but the legacy OS bundle is detached from the limiting functional. The older `PositiveTimeCompression` additionally equates the ordinary and reflected norms and has a finite-mode positivity certificate, so it is not the generic continuum OS root. | Prove the positive-time form `E(star (Theta a) * b)` for the canonical continuum functional and identify it only with `PositiveTimeOSRoot.positive.B`; use the ordinary Wilson form solely as ambient Euclidean data. Derive transfer positivity from OS geometry/Markov identities or an infinite certificate with convergence modulus. |
| Clustering/ergodicity | `IsOS4ClusterProperty`, `UniformClusterBound`, located spectral models | Current OS4 is finite spectral-model decay and may be populated independently of the continuum functional. | State connected canonical correlator decay uniformly in volume/spacing; derive uniqueness/ergodicity and transport it into the limit. |
| Constructive GNS Hilbert space | `WilsonGNSData.toGNSData`, `CanonicalOSRoot.PositiveTimeOSRoot.positive`, `CompleteGNSHilbertGeneral` | The ordinary Wilson datum is a sound ambient state GNS substrate, but `PositiveIsometricTimeNoGo` forbids using its invariant time action as nontrivial physical transfer. The standard reflected root is now stated without the false ordinary-norm equality, but has no 4D inhabitant. The completion exposes a carrier/inner product and arbitrary-modulus completeness, but not yet canonical completed vector operations. | Pin the ordinary Wilson datum to the canonical functional as ambient data; construct the physical datum directly on geometrically certified half-space observables and use `positive.gnsComplete_general`. Prove support density/essential surjectivity, then add completion add/smul/zero and show the embedding and transfer are linear before generator work. |
| Time translations/transfer semigroup | `CanonicalOSRoot.PositiveTimeOSRoot.completedTransfer`; `GNSDynamics.TransferOperator`; `AdditiveTransferOperator` | The standard root now descends a pinned one-step transfer and derives a nonzero unit vacuum plus completed form laws, but its representative self-adjointness/positivity/contraction are named 4D obligations and no continuous-time semigroup exists. The legacy finite weighted-Gram compression cannot be the generic infinite-dimensional time-one map. | Derive the three representative laws from half-space reflection/Markov geometry and prove the exact `Nat` semigroup. For continuous time, construct and pin a Euclidean action on observables for every rational/dyadic time, with composition and a Type-level continuity modulus; `U(1)=completedTransfer` alone is insufficient. |
| Positive self-adjoint Hamiltonian | abstract `OSReconstruction.SelfAdjointOp`; `SelfAdjointHamiltonian` form infrastructure | The former is law-witness data; the legacy bounded functional-calculus residual is generically inhabited and a bounded logarithm is generally false at zero spectrum. | Use a densely defined closed positive quadratic form, resolvent, or strongly continuous contraction semigroup to construct an unbounded positive self-adjoint generator. Pin its semigroup to the descended time translations. |
| Vacuum and `H Omega = 0` | `CanonicalOSRoot.PositiveTimeOSRoot.physicalVacuum`; abstract reconstruction vacuum | The new generic root derives a normalized nonzero unit vacuum and transfer invariance, but no 4D Yang--Mills positive-time realization or generator domain has been constructed. | Define `Omega` as the completed positive-time class of the actual algebra unit; derive normalization/nonzero/fixedness from the common reflected form, then prove generator-domain membership and `H Omega = 0` from strong continuity. |
| Vacuum uniqueness | No adequate canonical carrier found | Missing from the present Clay targets. Finite spectral separation alone does not identify the vacuum eigenspace as one-dimensional. | State and prove that every invariant/zero-energy vector is constructively equivalent to a scalar multiple of `Omega`, derived from clustering/ergodicity. |
| Positive-energy Poincare representation | abstract OS prose and Euclidean actions | No complete strongly continuous representation or spectrum-cone statement is pinned to the GNS Hilbert space. | Reconstruct the Poincare representation from full OS data; carry representation laws, continuity, and joint spectrum in the forward cone. |
| Finite positive mass gap | `LocatedSpectralGap`, `SpectralGapData`, `ContinuumLimitData` | `SpectralGapData` admits identity transfer plus an empty spectral model. Its model is not a spectral representation of `op`; an arbitrary positive exclusion interval does not prove a finite excited threshold. | Define the mass as a located infimum of the actual generator form on normalized vacuum-orthogonal domain vectors. Carry positive lower brackets and finite-energy near-edge witnesses, proving `0 < m < infinity`, and pin all brackets to the uniform continuum scaling limit. |
| Uniformity in volume and spacing | `UniformClusterBound`, `RubricUniformInCoupling`, `TrueRGComparison` | Interfaces exist but are not tied end-to-end to the actual Wilson operators and scale relation. | State one uniform estimate over volumes and spacings, derive the physical scale conversion, and prove preservation by both limits. |
| Gauge-invariant curvature fields | `LocalCurvatureFields` and `GaugeInv` syntax | `mu_inf` is phantom; `A` and `E` are freely selected; the one-point algebra is an inhabitant. | Require `curvature.A = bundle.A`, `curvature.E = bundle.E`, and identify realized fields as limits of renormalized lattice curvature observables with locality/support and covariance. |
| Nontrivial/interacting theory | `FourDExistence.NontrivialityContent`; `ContinuumOSCarrier.nontrivial` | Witness spectral models/correlations are selected independently of the canonical functional. A positive one-point correlation does not exclude a trivial or Gaussian theory. | Give an actual separated connected correlator or higher cumulant computed from canonical local fields and prove it is nonzero; exclude Wick factorization for the same functional. |
| Stress tensor | `LocalCurvatureFields.StressTensor` | Only expectation-level symmetry and one divergence expectation are required; the trivial realization inhabits it. | Construct a renormalized local tensor on the canonical field algebra; prove locality, covariance, symmetry, conservation as an operator-valued distribution, Ward identities, and that its charges generate translations. |
| Operator product expansion | `LocalCurvatureFields.OPE` | Coefficients and a nonnegative bound are free data; no equation relates the product of actual operators to the expansion. The zero OPE inhabits it. | State the OPE as an asymptotic equality of canonical correlation functionals for every spectator insertion, with singular coefficient laws and an explicit remainder modulus. |
| Asymptotic freedom/perturbative short distance | `AFRateModulus`, `AsymptoticFreedomShortDistance`, `invRunningCoupling` | Correct one-loop sign and a freely selected rate are proved, but neither is linked to actual correlators, renormalized coupling, or all-group character tails. | Define the renormalized coupling from canonical observables; prove its beta-function asymptotics and the predicted OPE/correlator coefficients for each `T`. |
| Pentagon/associator input | signed `SixJRacahCReal`, `BiedenharnEverettGeneral`, `BEDougallCore`; current `PentagonNumericCore` | `PentagonNumericCore` is trivially inhabited and does not state the pentagon. Unguarded Dougall is false outside admissible data. | Introduce a guarded admissible signed Biedenharn--Elliott/Dougall residual and prove its equivalence to the associator used by the actual fusion calculation. |
| Block-spin spectral comparison | `SpectralLocalization`, `EdgeShiftResidual`, `TrueRGComparison` | Post-move spectra are free variables; trivial localization is available. | Define the blocked Wilson functional/operator first and state comparison estimates only for its derived transfer/form/resolvent data. |
| Physical gap recursion | `singleStep`, legacy `TrueMarginRecursion` | The constructive defect spine is valuable, but the legacy margin type omits the equation tying lattice masses to spacings. | Pin `Delta_k = m_lat(k)/a_k`, derive the scale ratio from the actual blocking/AF trajectory, and connect its positive limit to `spec(H)`. |

## Root object proposed for the Lean target

The strongest existing root begins with the functional/GNS stack, not the
abstract `OSReconstruction` record, but the ordinary state GNS space is only the
AMBIENT Euclidean space.  `PositiveIsometricTimeNoGo` proves that invariant time
is isometric on `E(a* b)` and therefore cannot be the nontrivial positive
physical transfer.  The corrected root is:

1. an actual computable compact gauge group with global form and faithful action;
2. its derived `T : CartanType`, `hT : IsSimpleRank T`, and classification pin;
3. a group/action-pinned two-parameter Wilson lattice family, without assuming
   false exact marginal consistency between bare cutoffs;
4. one limiting observable algebra `A` and probability/Schwinger functional
   `E`, obtained with an explicit thermodynamic/continuum modulus;
5. `W : WilsonGNSData A` with `W.E = E.E`, used to define the ordinary AMBIENT
   datum `D_amb := W.toGNSData`;
6. an actual positive-time observable carrier, reflection `Theta`, and a
   reflected physical datum `D_phys` satisfying only
   `B_phys(a,b) = E(star (Theta a) * b)`, with physical Hilbert space
   `H_phys := D_phys.gnsComplete_general`;
7. a normalized nonzero unit vacuum and a normalized vacuum-orthogonal probe
   with a strict Rayleigh bracket, both pinned to actual observables;
8. a strongly continuous semigroup with `U(1)` equal to the descended physical
   one-step transfer, followed
   by its densely defined positive generator and located form infimum;
9. local operators and correlators built on the same Schwinger functional and
   physical reconstruction;
10. exact pins from the physical gap and local correlators back to the uniform
   lattice estimates.

The existing `ClayTargetPinned` can be a legacy projection of this target, but
must not be embedded as its semantic foundation: it retains weak O(4), finite
spectral-model, and abstract-reconstruction slots.

## New prerequisite interfaces

Before `ClayResolutionTarget` can be useful rather than another wrapper, the
following semantic carriers are required:

1. `ComputableCompactGaugeGroup` — global form, group laws, Haar/character
   algorithms, and a chosen faithful lattice action; Cartan type is a projection.
2. `PinnedWilsonLatticeFamily G` — the same group/action, plaquette weight,
   reference functional, and normalized bare functional at every two-parameter
   volume/cutoff stage; effective blocking is a theorem, not an assumed bare
   marginal law.
3. `CanonicalSchwingerLimit family` — observable-by-observable thermodynamic and
   spacing approximation estimates with separate Type-level moduli, tied to the
   ambient-GNS metric and expectation of the same limit functional.
4. `EuclideanSchwingerAxioms limit` — full E(4), symmetry, regularity, RP, and
   clustering on actual `n`-point functionals.
5. `PositiveTimeOSRoot limit` — ambient Wilson datum plus a
   geometry-derived Type-valued half-space support carrier, reflected form only,
   equivalence-reflecting representative map, essentially-surjective observable
   realization, and normalized physical vacuum/probe. The legacy finite
   compression is an optional cutoff specialization, not this root.
6. `PositiveOSSemigroup reconstruction` — rational/constructive-real
   strongly-continuous contraction semigroup pinned at time one to the derived
   reflected positive-time transfer.
7. `PositiveSemigroupGenerator semigroup` — dense domain, resolvent/closed-form
   data, and difference-quotient pin to the semigroup.
8. `PhysicalSpectralGap generator family` — located positive finite infimum of
   the generator form on the vacuum-orthogonal unit sphere, with near-edge
   witnesses and uniform-limit pins.
9. `CanonicalLocalOperatorContent limit reconstruction` — local curvature
   fields, nontriviality, stress tensor, OPE, and AF equations for actual
   correlators.

Each interface must expose data or equations sufficient to prevent its known toy
inhabitants.  An opaque `law_witness : Prop` chosen by the caller is not a
semantic implementation.

## Adequacy theorem shape

After these carriers exist, the only accepted frontier census is the hypotheses
of a total theorem:

```lean
def revisedFrontierDAG_to_clayResolution
    (G : ComputableCompactGaugeGroup)
    (d : RevisedFrontierDAG G) :
    ClayResolutionTarget G :=
  ...
```

The theorem must introduce no additional hypothesis, select no unrelated model,
and use every load-bearing field. A legacy projection may then be proved:

```lean
def ClayResolutionTarget.toLegacyPinned :
    ClayResolutionTarget G -> ClayTargetPinned muInf
```

The converse must not exist unless the legacy statements are first strengthened.

## Immediate implementation order

1. Define the missing global compact-group/action datum; do not treat a Cartan
   type as a global group.
2. Realize `PinnedWilsonLatticeFamily` and `CanonicalSchwingerLimit` with their
   object-identity and two-parameter approximation pins. Do not impose exact
   projective consistency on bare Wilson actions; either prove convergence
   estimates directly or construct exact effective RG measures and separately
   prove their origin from the bare action.
3. Inhabit the existing positive-time support carrier and
   `PositiveTimeOSRoot` from actual stage support/reflection geometry; add explicit
   fences against the additive-zero vacuum, identity transfer, zero transfer,
   false ordinary/reflected norm equality, finite-rank transfer certificates,
   and adjoined toy sectors.
4. Derive the physical completed one-step operator, then its exact `Nat`-indexed discrete
   semigroup.  Do not call this strongly continuous.
5. Construct the rational/constructive-real `C0` semigroup with a Type-level
   continuity modulus and time-one pin.  Only then define the generator.
6. Define the located finite positive form edge with near-edge witnesses, rather
   than a free finite `SpectralModel` or an arbitrary exclusion interval.
7. Define full Euclidean/OS and local-operator interfaces against the same
   Schwinger functions.
8. Assemble `ClayResolutionTarget`, then immediately start its adequacy theorem.
9. Derive the revised frontier list from the holes in that theorem; do not copy
   the legacy seven-atom list.
