# Clay resolution target: clause-to-carrier inventory

Status: Phase A.1 architectural inventory, 2026-07-17.

This document maps every clause of `docs/ym_mass_gap_prompt.md` to the
strongest current Lean carrier and records the exact repair needed before a
canonical `ClayResolutionTarget` can honestly represent the terminal theorem.
It is a design input, not a proof and not a frontier-closing claim.

## Governing rule

The canonical target is rooted in one Schwinger functional and its completed
constructive GNS reconstruction.  The group, lattice approximants, continuum
limit, translations, transfer semigroup, Hamiltonian, spectrum, local fields,
OPE, and stress tensor must all be pinned to that same root.  A collection of
separately inhabitable structures is not sufficient.

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
| Every compact simple `G` | `RG.CartanType`, `MassGap.AllSimpleTypes.IsSimpleRank`, `repDataOf`, `admissible_of_cartanType` | Classification-facing Casimir data exist, but the physical measure, observable algebra, and character tails are not indexed by the same `T`; the operating-point `eta_max` is explicitly nonphysical. | Parameterize the target by `T : CartanType` and `hT : IsSimpleRank T`; pin all representation, heat-kernel, lattice, AF, and tail data to `repDataOf T`. Carry the group-specific physical tail estimate, including short-root normalization. |
| Four-dimensional pure Yang--Mills lattice family | `ContinuumMeasure.ProjectiveSystem`, finite-volume Wilson/character modules | `ContinuumMeasure` currently stores a consistent thread of arbitrary stage values, not the Wilson action, probability laws, volumes, spacings, or gauge group. | Add a `PinnedWilsonLatticeFamily T` containing volumes, spacings, link/plaquette configuration carriers, normalized Wilson functionals, blocking maps, and exact pins to the selected action and group. |
| Thermodynamic limit `T^4 -> R^4` | `ContinuumLimitData.cluster`; `ContinuumMeasure` inverse-limit thread | The inverse-limit thread is not a thermodynamic probability-functional limit. `ContinuumLimitData` gives masses and a modulus but is not pinned to the Wilson family or Schwinger functional. | Carry a volume-directed functional limit with an explicit modulus; prove all local correlators converge uniformly on bounded support and that the limit equals the canonical Schwinger functional. |
| Continuum limit `a -> 0` | `FunctionalContinuumTarget.scaling`, `ScalingLimitModulus`, `ContinuumLimitData.continuumModulus` | Genuine modulus interfaces exist, but their functionals/masses are not tied to the same lattice family and reconstructed spectrum. | One two-stage or joint limit object, pinned to the lattice family and canonical functional, transporting OS laws, local correlators, and the gap. |
| OS0 regularity/temperedness | `OSAxioms.IsOS0`; `OSAxiomAudit.GJ_OS1_Regularity` | Present predicates are heat-kernel normalization bounds, not full continuum distributional regularity or tempered Schwinger growth. `IsOS0` does not use `mu_inf`. | State constructive test-function spaces, multilinear Schwinger functionals, continuity/growth moduli, and the regularity theorem for the canonical functional. |
| Euclidean translations and full `O(4)` | `IsOS1HypercubicTranslation`, `IsOS1HypercubicH4`, `O4RestorationContent` | Current actions are single freely supplied endomorphisms. They do not encode a group action, the full Euclidean group, strong continuity, or identity with the canonical functional. | Carry an `E(4)` action with identity/composition/inverse laws, covariance of every Schwinger function, and continuity; pin its lattice dense-subgroup restriction to the lattice symmetries. |
| Permutation/symmetry axioms | `IsOS3Symmetry` | A single equivariant endomorphism is weaker than all Schwinger permutation, reflection, and covariance laws. | State the complete family of symmetry laws on the canonical `n`-point functionals. |
| Reflection positivity | `IsOS2ReflectionPositivity`; `WilsonGNSData.E_self_nonneg`; many Z4 RP modules | Strong constructive ingredients exist, but the OS bundle's RP predicate is a fixed heat-kernel theorem and is not pinned to the continuum functional or limiting Wilson action. | Prove the positive-time Schwinger quadratic form for the canonical continuum functional and identify it with the Wilson GNS form used below. |
| Clustering/ergodicity | `IsOS4ClusterProperty`, `UniformClusterBound`, located spectral models | Current OS4 is finite spectral-model decay and may be populated independently of the continuum functional. | State connected canonical correlator decay uniformly in volume/spacing; derive uniqueness/ergodicity and transport it into the limit. |
| Constructive GNS Hilbert space | `WilsonGNSData.toGNSData`, `CompleteGNSHilbert` | This is the strongest real substrate. It is preferable to the abstract `OSReconstruction.HilbertSpace`, but must be fed the canonical continuum functional rather than a toy/reference functional. | Root reconstruction at one `WilsonGNSData bundle.A`; pin `wilson.E = bundle.E.E`; use `wilson.toGNSData.gnsComplete` as the physical Hilbert space. |
| Time translations/transfer semigroup | `GNSDynamics.TransferOperator`; `AdditiveTransferOperator` | `TransferOperator` has an identity inhabitant and no pin to time translation. The abstract `ContractionSemigroup` is `Unit`-backed. | Construct translations on the observable algebra, descend them through the GNS quotient, extend to completion, prove the semigroup law/strong continuity, and define the target's transfer operator to be that descended action. |
| Positive self-adjoint Hamiltonian | abstract `OSReconstruction.SelfAdjointOp`; `SelfAdjointHamiltonian` form infrastructure | The former is law-witness data; the legacy bounded functional-calculus residual is generically inhabited and a bounded logarithm is generally false at zero spectrum. | Use a densely defined closed positive quadratic form, resolvent, or strongly continuous contraction semigroup to construct an unbounded positive self-adjoint generator. Pin its semigroup to the descended time translations. |
| Vacuum and `H Omega = 0` | `TransferOperator.vacuum`; abstract reconstruction vacuum | Existing vacua are not pinned to the GNS class of the unit observable; identity transfer makes the equations vacuous. | Define `Omega` as the completed GNS image of `bundle.A.one`; prove normalization, invariance, domain membership, and generator annihilation. |
| Vacuum uniqueness | No adequate canonical carrier found | Missing from the present Clay targets. Finite spectral separation alone does not identify the vacuum eigenspace as one-dimensional. | State and prove that every invariant/zero-energy vector is constructively equivalent to a scalar multiple of `Omega`, derived from clustering/ergodicity. |
| Positive-energy Poincare representation | abstract OS prose and Euclidean actions | No complete strongly continuous representation or spectrum-cone statement is pinned to the GNS Hilbert space. | Reconstruct the Poincare representation from full OS data; carry representation laws, continuity, and joint spectrum in the forward cone. |
| Finite positive mass gap | `LocatedSpectralGap`, `SpectralGapData`, `ContinuumLimitData` | `SpectralGapData` admits identity transfer plus an empty spectral model. Its model is not a spectral representation of `op`. The margin `1-sep` is not yet the physical energy `-log sep`. | Add a constructive spectral-resolution/form theorem identifying the model or spectral exclusion with the actual generator. Carry `0 < Delta < infinity` and `spec(H) intersect (0,Delta) = empty`, with `Delta` pinned to the continuum scaling limit. |
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

The strongest existing root is the functional/GNS stack, not the abstract
`OSReconstruction` record:

1. `T : CartanType`, `hT : IsSimpleRank T`;
2. a group-pinned Wilson lattice family for `repDataOf T`;
3. one limiting observable algebra `A` and probability/Schwinger functional
   `E`, obtained with an explicit thermodynamic/continuum modulus;
4. `W : WilsonGNSData A` with the pin `W.E = E.E`;
5. `D := W.toGNSData` and `H := D.gnsComplete` definitionally, rather than
   independently selected `gnsData` and `CompleteGNSHilbert` fields;
6. translations, transfer semigroup, generator, vacuum, spectral theorem, local
   operators, and correlators all constructed from `A`, `E`, `W`, and `H`;
7. exact pins from the physical gap and local correlators back to the uniform
   lattice estimates.

The existing `ClayTargetPinned` can be a legacy projection of this target, but
must not be embedded as its semantic foundation: it retains weak O(4), finite
spectral-model, and abstract-reconstruction slots.

## New prerequisite interfaces

Before `ClayResolutionTarget` can be useful rather than another wrapper, the
following semantic carriers are required:

1. `PinnedWilsonLatticeFamily T` — same group/action/functional at every stage.
2. `CanonicalSchwingerLimit family` — volume and spacing limit with moduli.
3. `EuclideanSchwingerAxioms limit` — full E(4), symmetry, regularity, RP, and
   clustering on actual `n`-point functionals.
4. `CanonicalGNSReconstruction limit` — completed Wilson GNS with descended
   time translations and vacuum pinned to the unit.
5. `PositiveSemigroupGenerator reconstruction` — unbounded generator package.
6. `PhysicalSpectralGap generator family` — actual spectral exclusion and
   uniform-limit pins.
7. `CanonicalLocalOperatorContent limit reconstruction` — local curvature
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
    (T : CartanType) (hT : IsSimpleRank T)
    (d : RevisedFrontierDAG T hT) :
    ClayResolutionTarget T hT :=
  ...
```

The theorem must introduce no additional hypothesis, select no unrelated model,
and use every load-bearing field. A legacy projection may then be proved:

```lean
def ClayResolutionTarget.toLegacyPinned :
    ClayResolutionTarget T hT -> ClayTargetPinned muInf
```

The converse must not exist unless the legacy statements are first strengthened.

## Immediate implementation order

1. Define `PinnedWilsonLatticeFamily` and `CanonicalSchwingerLimit` with their
   object-identity pins.
2. Refactor the strongest existing GNS constructions so the continuum functional
   supplies `WilsonGNSData` directly.
3. Define the semigroup-generator and physical-gap interfaces over that exact
   completed GNS carrier.
4. Define full Euclidean/OS and local-operator interfaces against the same
   Schwinger functions.
5. Assemble `ClayResolutionTarget`, then immediately start its adequacy theorem.
6. Derive the revised frontier list from the holes in that theorem; do not copy
   the legacy seven-atom list.
