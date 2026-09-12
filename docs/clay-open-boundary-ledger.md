# Clay Open-Boundary Ledger

**Integrity statement for the Yang–Mills mass-gap formalization.**

This ledger is the project's honest accounting of the Clay Millennium
boundary: for each requirement and each existence carrier, what is now
**PROVED in Lean** (named theorem), what remains **GENUINELY OPEN** (one
precise sentence), and whether the open part is **open research mathematics**
or **engineering / wiring**.

The deliberate policy here is to **underclaim, not overclaim**. Yang–Mills
existence and the mass gap on ℝ⁴ is an open problem. Nothing in this
repository closes it. What the repository contains is a body of genuine
finite / lattice-level theorems, an explicit and content-bearing statement
of the continuum existence hypothesis (assumed, never proved), and a
current boundary marking where the open analysis begins.

**Controlling correction (2026-07-17).** The R1--R3 sections, carrier summary,
continuum-limit entry, and reconstruction entry below have been re-audited
against `docs/clay_resolution_target_inventory.md` and
`Continuum/CanonicalOSRoot.lean`.  They supersede stronger interpretations in
the dated historical addenda.  In those addenda, words such as "actual",
"physical", "continuum mass", and "frontier" describe only the literal legacy
finite/scalar carrier unless an explicit bridge to the canonical two-parameter
Wilson functional, reflected half-space reconstruction, full time semigroup,
generator, and spectral pin is stated.  No older scorecard or fixed-spacing
construction is an exhaustive Clay frontier.

Axiom convention: "axiom-clean" below means the theorem's `#print axioms`
reports at most `propext` and `Quot.sound` (both MLTT/HoTT-valid), with no
`Classical.*`, no `sorryAx`, no `native_decide`. See `lean/AGENTS.md`.

### Live finite-volume frontier update (2026-09-11)

- **PROVED, SU(2) at the fixed anchor and every cutoff `K >= 1`:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity` proves that
  the normalized production source weight is bounded by the actual symmetric
  OS joint capacity of the first edge
  `sourceLower -> commonRight`, and the normalized production target weight is
  bounded by the second edge `commonRight -> targetLower`.  The proof uses the
  exact fine-intertwiner physical disintegration and the literal common
  boundary summand; the resulting certificate is axiom-clean.
- **PROVED next normalization:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSNormalizedFlow` proves
  that the selected normalized source traffic has total mass at least
  `41/425`, and that every compiled-target fiber's incoming traffic is at most
  `globalInwardMateTransportCost` times the actual second OS joint edge.
- **PROVED first-edge aggregation:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad` partitions
  the complete source family by its actual first OS edge and injects every
  fiber into that edge's literal boundary--fine-intertwiner summands.  Hence
  the total traffic of each fiber is at most the normalized OS joint capacity,
  with no source-collision cardinality factor.
- **PROVED second-edge aggregation and completeness:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad` first
  partitions every selected source into its exact production-target class,
  then partitions those classes by the literal second OS edge.  Both
  partitions preserve the total traffic exactly.  Distinct target atoms over
  one edge inject into its literal boundary--intertwiner summands, giving load
  at most `globalInwardMateTransportCost` times the actual normalized OS joint
  capacity.
- **PROVED one-observable demand and first-edge Dirichlet embedding:** one
  concrete demand is proved by
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand`: the parity
  of central lower face zero changes between every source and target, and its
  Boolean value changes on exactly one of the two path edges.  Hence the two
  selected parity-gradient energies sum exactly to the selected traffic and
  are at least `41/425`.
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy`
  partitions the first energy by literal OS edge, applies the proved aggregate
  capacity bound, and injects distinct realized edges into the complete
  Cartesian half-state square.  Thus the selected first-edge parity energy is
  bounded by the full physical OS Dirichlet form, without a cardinality loss.
- **PROVED second-edge Dirichlet embedding:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy`
  first factors the parity gradient through exact production-target classes,
  then through exact second-edge classes.  It applies the proved congestion
  estimate and injects distinct realized second edges into the Cartesian
  half-state square.  Thus the selected second-edge energy is bounded by
  `globalInwardMateTransportCost` times the full physical OS Dirichlet form.
- **PROVED explicit one-observable Dirichlet floor:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity`
  combines both edge embeddings with the lossless `41/425` demand identity.
  At every cutoff `K >= 1`, the full physical OS Dirichlet energy of
  central-face parity is at least the explicit positive rational
  `(41/425) / (1 + globalInwardMateTransportCost)`.
- **PROVED non-vacuous strict form channel:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap` centers the
  same Boolean parity by its exact stationary mean, preserves the Dirichlet
  floor through constant shifting and deletion of zero-marginal rows, and
  converts it by the exact physical Dirichlet/transfer identity into
  `|<f,Tf>| <= q <f,f>` with
  `q = 1 - (1/2) * (41/425) /
  (1 + globalInwardMateTransportCost)` and `0 <= q < 1`.  Its certificate also
  proves the centered physical norm is bounded below by the positive margin.
- **PROVED arbitrary-observable edge compiler:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy`
  generalizes both aggregate edge embeddings beyond parity.  For every
  rational observable its selected source-to-target squared oscillation is at
  most `2 * (1 + globalInwardMateTransportCost)` times the full physical OS
  Dirichlet energy.  `GlobalInwardMateUniformEndpointCoverage` names, but does
  not inhabit, the remaining cutoff-independent centered-norm comparison.
- **PROVED conditional all-vector compiler:**
  `BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler`
  converts any inhabitant with floor `kappa > 0` into the explicit rate
  `4(1 + globalInwardMateTransportCost) /
  (4(1 + globalInwardMateTransportCost) + kappa) < 1`, valid for every
  centered physical coefficient and every cutoff `K >= 1`.  No coverage
  inhabitant is supplied.
- **PROVED full-carrier coverage obstruction:**
  `BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction` constructs
  the XOR parity of central-cube faces `0` and `39`.  Every selected six-face
  mate preserves it, so its stationary-centered selected endpoint energy is
  exactly zero.  Vacuum and the independently proved positive transverse
  single-face state give different raw values, and the centered physical norm
  is strictly positive at cutoff one.  Therefore
  `no_globalInwardMateUniformEndpointCoverage` proves that the proposed
  full-positive-carrier coverage structure is uninhabited.
- **OPEN next edge:** restrict the flow and observable norm to the existing
  exact finite vacuum connected component, then construct a translated or
  component-adapted move family which separates that sector with a
  cutoff-uniform weighted congestion bound.  The one-observable estimate and
  the conditional algebra do not imply an all-vector Poincare inequality,
  finite-volume spectral gap, continuum limit, or Clay theorem.

---

## The three Jaffe–Witten requirements

### R1 — Mass gap for ALL compact simple gauge groups

- **PROVED precursor in Lean (CONDITIONAL on a supplied OS reconstruction).**
  The Cartan-type / simple-Lie-algebra Casimir reduction to the A₁ floor is
  assembled axiom-clean for the repository's representative `RepData`:
  `YMGap.MassGap.SimpleGroup.mass_gap_simple_group_of_osReconstruction`
  (renamed from `mass_gap_simple_group` per the 2026-06-21 audit so the name
  signals the OS-reconstruction hypothesis; the global minima `h∨ = 2`,
  `Δ = 3/4` are attained at SU(2) = A₁; the rep-theory floor for all
  fundamental weights and all N is in `RG/SUNWeylData.lean`).  The SU(2) leaf
  is `YMGap.MassGap.SU2.mass_gap_SU2_of_osReconstruction`.  The spectral
  conjunct is genuine: the supplied `OSReconstruction` now carries
  `gapBound < 1` structurally (`gapBound_lt_one`), so `HasSpectralGap`
  entails a real geometric decay (`HasSpectralGap.clustering`), not a
  vacuous `gapBound = 1`. This proves a conditional theorem about
  Cartan/Lie-algebra Casimir representatives; it does **not** yet quantify over
  fully specified compact gauge groups or their physical Wilson theories.
- **GENUINELY OPEN.** Supply an actual compact simple group (including its
  global form), a group action/Haar structure and lattice action
  representation, prove that the representation used by the Wilson action
  descends to that global form, and tie all of these data to the same canonical
  lattice/continuum OS root. The physical heat-kernel/character-tail estimate
  must then be proved for each group with the correct normalization (including
  short-root effects for non-simply-laced types). A Cartan type alone does not
  distinguish, for example, `SU(n)` from `PSU(n)` or `Spin(n)` from `SO(n)`,
  and a fundamental representation need not descend to a quotient group.
  Consequently the claim that the physical all-group problem is reduced to an
  SU(2) worst case remains open until the group-specific tail and descent
  theorems are proved.
- **Open-part character:** open research mathematics plus substantial
  foundational formalization; the existing finite Cartan/Casimir enumeration
  is a precursor, not a closure of R1.

### R2 — Continuum existence on ℝ⁴ via OS reconstruction

- **PROVED precursor in Lean.** The legacy OS-axiom interface is not literally
  `True`, and exact finite heat-kernel/reflection-positivity theorems such as
  `reflectionPositiveSchwinger_holds` are useful cutoff results.  However,
  `OSAxiomBundle mu_inf` does not pin its predicates to `mu_inf` or to one
  limiting Schwinger functional; its OS0/OS2 predicates are fixed heat-kernel
  statements, OS1/OS3 admit identity maps, and OS4 uses detached finite spectral
  data.  These are precursors, not the full continuum OS theorem.  The abstract
  reconstruction quintuple and existence hypothesis are stated in
  `YMGap.Continuum.FourDExistence.ContinuumYMExistence` /
  `ContinuumYMWithGap`, consumed as a hypothesis by
  `ym_mass_gap_of_existence`.
- **GENUINELY OPEN.** Construct the two-parameter thermodynamic/continuum
  Schwinger-functional limit of the actual group/action-pinned Wilson family,
  prove the full OS axioms on that same functional, and build its reflected
  positive-time quotient/completion.  A sigma-additive point-set measure is
  optional downstream packaging; neither the functional limit nor the physical
  OS reconstruction is currently constructed.
- **Open-part character:** open research mathematics (this is the dominant
  open frontier; it is the Clay problem itself).

### R3 — Mass gap Δ_G > 0

- **PROVED precursor in Lean.** Finite-model gap ⇒ clustering content is proved:
  `YMGap.Continuum.SpectralGap.decay_of_spectralGap_corr0` (gap ⇒ geometric
  clustering) and the located finite transfer-operator gap
  (`LocatedSpectralGap.lean`); the √-bridge `m = √σ̂` and `σ̂∞ > 0`
  machinery are in the continuum track. `ym_mass_gap_of_existence` projects a
  positive gap from an assumed existence-with-gap hypothesis; it does not
  construct or spectrally identify that gap.
- **GENUINELY OPEN.** Transporting the finite-volume / finite-transfer-operator
  spectral gap to a strictly positive gap of the continuum OS-reconstructed
  Hamiltonian requires the continuum spectral theorem for the reconstructed
  (unbounded) Hamiltonian, which is unbuilt (and Mathlib-free constructive
  spectral theory for general bounded operators is itself obstructed — only
  the LOCATED 2nd-eigenvalue of the compact finite transfer operator is
  constructively available).
- **Open-part character:** open research mathematics (continuum spectral
  theory), riding on R2.

---

## The four Yang–Mills existence carriers

Each carrier is a content-bearing `Prop` over the continuum measure
(`FourDExistence.lean`). The "precursor" column is the strongest honest
finite / lattice-level fact now in Lean feeding that carrier. The
"continuum remainder" is the genuinely-open step.

### Carrier 1 — UV asymptotic freedom (`UVAsymptoticFreedomContent`)

- **PROVED in Lean (genuine, not non-vacuity-only).**
  - `FourDExistence.betaZero_pos` — the one-loop coefficient
    `β₀ = (11/3)·C₂(adj) > 0` at the dual-Coxeter floor (correct
    asymptotically-free sign).
  - `FourDExistence.invRunningCoupling_strictMono` — the inverse coupling
    `u(k) = u₀ + β₀·k` is strictly increasing (`g²` decays toward the UV).
  - `FourDExistence.uv_asymptotic_freedom_su2` /
    `CarrierPrecursors.uv_asymptotic_freedom_genuine` — the carrier holds at
    the SU(2) data with no open input (`β₀ = 22/3 > 0`).
  - These are real finite constructive order facts, division-free, axiom-clean.
- **GENUINELY OPEN (continuum remainder):** that the true nonperturbative
  continuum running coupling actually vanishes logarithmically in the UV,
  beyond the one-loop linear law.
- **Open-part character:** open research mathematics.

### Carrier 2 — Gauge generation (`GaugeGeneratedContent`)

- **PROVED in Lean (genuine upgrade onto real heat-kernel data).**
  - `CarrierPrecursors.gauge_generated_on_charAlg` — the gauge-averaging
    factorization (idempotent projection `P` with `E(P a) = E a`) holds for
    the genuine SU(2) character `*`-algebra `RGTransport.charAlg` and the
    diagonal heat-kernel functional `RGTransport.charFunc`, with `P = id`:
    characters ARE the class functions = gauge-invariant observables, so the
    character algebra already is the gauge-invariant subalgebra and gauge
    averaging is the identity on it.
  - `CarrierPrecursors.gauge_witness_functional_nonconstant` — the witnessing
    functional is genuinely non-constant (`E χ_0 = 1`, `E χ_2 = 3/256`), so
    this rests on real, non-degenerate single-edge heat-kernel data, not on
    the trivial one-point algebra used by the earlier
    `FourDExistence.gauge_generated_inhabited`.
  - **Honest flag:** the projection is the identity on the *already
    gauge-invariant* character algebra; this is a genuine fact about a real
    algebra/functional, but it does not construct a non-trivial gauge-group
    averaging map on a larger non-invariant algebra.
- **GENUINELY OPEN (continuum remainder):** the construction of the continuum
  gauge-invariant observable algebra of Wilson loops on `SU(2)^E` and the
  action of the continuum gauge group on it (`charAlg` is the single-edge
  character lattice model, not the continuum gauge orbit space).
- **Open-part character:** open research mathematics.

### Carrier 3 — Nontriviality / interacting (`NontrivialityContent`)

- **PROVED precursor in Lean (finite surrogate diagnostic only).**
  - `CarrierPrecursors.heatKernelSpectralModel` — a two-mode spectral model
    whose transfer eigenvalues are the ACTUAL SU(2) heat-kernel weights
    `λ_s = w^{C₄(s)}` at the genuine Casimir exponents `C₄(s) = s(s+2)`
    (`RGTransport.c4`, `= 4·C₂(s)`), with `w = 1/2`: `λ_0 = 1`, `λ_1 = 1/8`.
  - `CarrierPrecursors.nontrivial_from_heatKernel` — this model violates the
    exact surrogate equality `G(1) = G(0)²`:
    `corr(1) = 1 + 1/8 = 9/8 ≠ 4 = corr(0)²`.
  - **Honest correction:** this is not a Wick-theorem test. A Gaussian
    theory's two-point function need not satisfy `G(1) = G(0)²`; Wick's
    theorem constrains higher-point functions by sums over pairings. Likewise,
    a nonconstant reference weight or strictly positive variance is compatible
    with a Gaussian theory and is insufficient for Clay-facing
    nontriviality. These Lean results remain useful exact finite diagnostics,
    but they do not certify interaction.
- **GENUINELY OPEN (continuum remainder):** construct gauge-invariant local
  observables in the **canonical** Schwinger limit and prove a nonzero connected
  cumulant which violates Wick factorization for that same functional. A
  suitable target is a centered local observable `O` and separated test
  insertions for which the canonical connected four-point cumulant
  `κ₄(O₁,O₂,O₃,O₄)` is apart from zero, where `κ₄` is the actual
  four-point Schwinger functional minus the three two-point pairings (with the
  lower-cumulant corrections included if the observables are not centered).
  The witnesses, separation/support data, and nonzero modulus must all be tied
  to the group/action-pinned continuum functional; a freely selected spectral
  model, reference weight, or variance cannot discharge this field.
- **Open-part character:** open research mathematics.

### Carrier 4 — O(4) rotation restoration (`O4RestorationContent`)

- **PROVED in Lean (HONEST: only the identity-rotation precursor; the
  boundary is sharpened, not crossed).**
  - `CarrierPrecursors.o4_restoration_on_charAlg` — the equivariance property
    `E(r a) = E a` holds for the genuine character algebra and heat-kernel
    functional under the identity rotation `r = id` (the always-present group
    element), upgrading the witness off the trivial one-point algebra used by
    `FourDExistence.o4_restoration_inhabited`.
  - `CarrierPrecursors.heatKernel_not_equivariant_under_collapse` — proves the
    equivariance constraint is REAL, not vacuous: the genuine non-identity
    vacuum-projection `*`-hom `RGTransport.collapseHom` does NOT leave the
    heat-kernel functional invariant (`E(collapse χ_2) = 1 ≠ 3/256 = E χ_2`).
    So a genuine rotation must satisfy a real constraint that arbitrary maps
    fail.
  - **Honest flag — most important in this ledger:** there is **no genuine
    non-trivial rotation precursor**. The only functional equivariance proved
    in the repository is under the identity. No non-identity discrete
    hypercubic `H₄` rotation `*`-hom under which the heat-kernel functional is
    invariant has been constructed. The witnesses use the identity rotation;
    they establish non-vacuity on a real algebra and that the bar is real,
    nothing more.
- **GENUINELY OPEN (two nested steps):**
  1. (discrete, lattice-level) a non-trivial hypercubic `H₄` rotation action
     on the lattice observable algebra under which the Schwinger functional is
     invariant — not yet constructed in Lean;
  2. (continuum) restoration of the full `O(4) ⋉ ℝ⁴` Euclidean group in the
     continuum limit (Magnen–Rivasseau–Sénéor).
- **Open-part character:** step 1 is plausibly constructible
  engineering/wiring (the lattice genuinely has `H₄` symmetry; building the
  permutation `*`-hom and proving functional invariance is finite work that
  is simply not yet done here); step 2 is open research mathematics and is
  among the hardest pieces of 4D YM existence.

---

## The continuum-limit interface

- **PROVED in Lean.** The projective / inverse-limit functional machinery is
  constructed and the Daniell–Kolmogorov coarsening is proved at the
  functional level: `ObservableMeasure.ProbFunctional.restrict` (restriction
  preserves positivity and normalization), `ObservableMeasure.continuumMeasure`
  with `pushforward_limit_eq`, `RGTransport.charContinuumMeasure` on genuine
  SU(2)-character data, and `ObservableMeasure.expectation_stable` /
  `RGTransport.charExpectation_stable` (exact per-observable stabilization).
  These theorems validate the abstract machinery and stationary character
  examples; they do not show exact projective consistency of the bare Wilson
  family.
- **GENUINELY OPEN.** Construct the canonical group/action-pinned Schwinger
  functional by one of two honest routes:
  1. use the bare Wilson functionals `E_{a,L}` and prove explicit
     two-parameter approximation/Cauchy estimates (volume `L → ∞` and spacing
     `a → 0`) for every bounded-support local observable, with moduli and a
     common limiting functional; or
  2. construct an exactly projective family of **effective RG measures/actions**
     and separately prove that each effective object is the pushforward of, or
     has a quantified approximation to, the corresponding bare Wilson theory.

  Exact restriction consistency of bare Wilson measures across lattice
  spacings is not a generally valid target: integrating out fine variables
  generates additional interactions and does not normally return the same
  bare Wilson action at the coarse scale. A stationary character tower or an
  arbitrary consistent thread cannot substitute for the two physical limits.
  A σ-additive point-set measure remains optional downstream packaging once
  the canonical functional and all required OS/local-correlation properties
  are constructed.
- **Open-part character:** open research mathematics (the actual continuum
  limit of the YM lattice family), with engineering only after the required
  approximation or effective-RG theorems exist.

---

## The interacting-operator construction (OS reconstruction)

- **PROVED interface precursor in Lean.** The abstract OS-reconstruction
  interface and its conditional consumption are in place:
  `YMGap.Continuum.OSReconstruction` (the abstract reconstruction
  quintuple `(H_∞, Ω_0, U(t), H_op)` with `H_op ≥ 0`, `H_op Ω_0 = 0`,
  `U(t) = exp(−t H_op)`), and
  `FourDExistence.ym_mass_gap_of_existence` (existence ⇒ positive spectral
  gap, a pure projection out of the hypothesis, axiom-clean). The
  finite-volume ordinary GNS construction and located finite-model datum are in
  `FiniteVolumeGNS.lean` / `LocatedReconstruction.lean`.  These do not yet
  construct the standard reflected half-space Hilbert space.
- **The four reconstruction laws are HONEST OBLIGATIONS, not `True`.** Per the
  2026-06-21 audit (`docs/clay-requirements-audit-2026-06-21.md`), the four
  reconstruction laws `VacuumNormalized`, `HamiltonianNonneg`,
  `VacuumAnnihilated`, `SemigroupGenerated` — formerly `def _ : Prop := True`
  vacuous stubs — are now GENUINE abstract `Prop` predicates read off the
  carriers (`law_witness` / `nonneg_law` / `annihilation_law` /
  `generation_law` fields). A caller of `os_reconstruct_su2` must SUPPLY a
  proof of each; nothing reads as `True`-content. These are the paper-level
  Pour-El–Richards boundary carried as explicit obligations.
- **GENUINELY OPEN.** Construct geometry-derived half-space support and the
  reflected form on the canonical Schwinger limit; derive the positive
  contraction semigroup; construct its unbounded positive self-adjoint
  generator; and identify its located finite positive spectral/form edge.
  Merely inhabiting the abstract carrier/law bundle is insufficient.
- **Open-part character:** open research mathematics, riding on R2 and R3.

---

## Summary table

| Item | Proved-in-Lean precursor (theorem) | Open remainder | Open-part character |
|---|---|---|---|
| R1 | Cartan/Lie-algebra Casimir precursor and `mass_gap_simple_group_of_osReconstruction` (conditional on supplied OS recon) | actual compact global group/action, representation descent, group-pinned Wilson/OS root, and physical group-specific character tails | open research math + foundational formalization |
| R2 | legacy `OSAxiomBundle`, cutoff `reflectionPositiveSchwinger_holds` | canonical two-parameter Schwinger limit + full OS laws + reflected half-space reconstruction | open research math |
| R3 | `decay_of_spectralGap_corr0`, located finite gap | continuum spectral theorem for `H_op` | open research math |
| UV freedom | `betaZero_pos`, `invRunningCoupling_strictMono` | nonperturbative continuum running | open research math |
| Gauge | `gauge_generated_on_charAlg` (+ nonconstant) | continuum gauge-invariant algebra + gauge action | open research math |
| Nontriviality | `nontrivial_from_heatKernel` (exact finite surrogate inequality; not a Wick test) | nonzero canonical connected higher cumulant for gauge-invariant local fields, excluding Wick factorization for the same Schwinger functional | open research math |
| O(4) restoration | `o4_restoration_on_charAlg` (id only) + `heatKernel_not_equivariant_under_collapse` | (1) non-trivial `H₄` rotation `*`-hom; (2) continuum O(4) restoration | (1) engineering; (2) open research math |
| Continuum-limit interface | abstract `ProbFunctional.restrict`, `continuumMeasure`, `expectation_stable` machinery | two-parameter bare-Wilson approximation estimates, or exact effective-RG measures separately tied to the bare action; common canonical functional (sigma-additive extension optional) | open research math (+ later wiring) |
| Interacting-operator construction | abstract `OSReconstruction`, conditional `ym_mass_gap_of_existence` | construct reflected carrier, `C0` semigroup, unbounded `H_op`, and located finite edge on the same limit | open research math |

## Addendum (2026-06-21): honesty-hardening of the four audited blemishes

The full-tree audit (`docs/clay-requirements-audit-2026-06-21.md`) flagged four
honesty blemishes where a claim outran its content. All four are now fixed as
non-breaking refactors (no new mathematics; the build stays green and
axiom-clean, `propext`/`Quot.sound` only):

1. **Spectral conjunct strengthened.** `OSReconstruction` now carries
   `gapBound_lt_one : gapBound < 1` as a structural field (mirroring the
   `LocatedReconstruction`/`FiniteVolumeReconstruction` path). With `μ < 1` the
   bound `G(n) ≤ G(0)·μⁿ` (`HasSpectralGap.clustering`) is a REAL geometric
   decay, and `HasSpectralGap.gapBound_lt_one` surfaces the positive gap. The
   former wiring admitted `gapBound = 1` (no decay).

2. **Four `Prop := True` stubs removed.** `VacuumNormalized`,
   `HamiltonianNonneg`, `VacuumAnnihilated`, `SemigroupGenerated` are now
   genuine abstract `Prop` predicates read off carrier fields
   (`law_witness`/`nonneg_law`/`annihilation_law`/`generation_law`), supplied
   by the caller — honest open obligations, not vacuous content.

3. **Degenerate cluster witnesses relabeled.** The constant-margin
   `UniformClusterBound` inhabitants are renamed
   `ClusterBoundInstance.degenerateConstClusterBound` and
   `SigmaGroundedFloor.degenerateSigmaGroundedClusterBound`, with loud
   `⚠ DEGENERATE PLACEHOLDER` doc banners. They inhabit the TYPE via a constant
   `sep`, `tailConst = 0` family (the tail vanishes trivially); the genuine
   strong-coupling cluster-EXPANSION instance remains OPEN. The prose no longer
   claims cluster physics.

4. **Headline theorems renamed for honest conditionality.**
   `mass_gap_SU2 → mass_gap_SU2_of_osReconstruction` and
   `mass_gap_simple_group → mass_gap_simple_group_of_osReconstruction`, matching
   the `constructive_YM4_gap_conditional` convention so the NAME signals
   "conditional on a supplied OS reconstruction." All references updated.

None of this discharges any Clay obligation; it makes the claims match the
content.

## Addendum (2026-06-17): the constructive `RegularCReal` continuum pipeline

A constructive substrate for continuum-limit bookkeeping was built (4 phases,
all axiom-clean), recasting a supplied model as a positive linear functional
with real-number expectations and routing its supplied finite-model gap through
a compact transfer operator. The 2026-07-17 canonical-root audit supersedes the
older interpretation that this was already the physical Yang–Mills continuum
construction: it is an algebraic pipeline, not the reflected OS reconstruction
of the bare Wilson family.

- **`RegularCReal`** (`Constructive/RegularCReal.lean`) — a regular Bishop real with the
  Cauchy modulus carried as canonical Type-level DATA (choice-free; the existing one-slack
  `CReal.le` is genuinely non-transitive for lack of a regularity field). `le_trans` PROVED.
- **Arithmetic + completeness** (`Constructive/RegularCRealArith.lean`) — `add`/`sub`,
  rational scaling `qmul`, and `completeLimit` (modulus-Cauchy sequence ⇒ limit), with
  bound-passing.
- **Positive (linear) functional** (`Continuum/RegularFunctional.lean`) —
  `RegProbFunctional` (RegularCReal-valued, positive, normalized; concrete SU(2)
  char inhabitant `regCharFunctional`); `RegLinearFunctional` on an enriched additive
  algebra with **additivity & homogeneity PROVED** (linearity is now a theorem, enabled by
  the new arithmetic).
- **Algebraic capstone** (`Continuum/RegularContinuumPipeline.lean`) —
  `regContinuumGapRate`, `ConstructiveContinuumYM`, and the hypothesis-free,
  axiom-clean model inhabitant `concreteContinuumYM` at the freely selected
  separator `1/1000`. This is an unconditional inhabitant of the scaffold, not
  an unconditional infinite-volume Wilson theory or a Clay-facing gap.

**Conditional boundary (corrected again by the 2026-07-17 audit).** The selected
model's fixed-spacing positive gap + functional bundle is unconditional, but
its identification with the infinite-volume bare Wilson theory is not. The
scaling limit (`a→0`) includes the named obligation
`RegScalingLimitModulus`, now in its physically-correct **dimensional-transmutation**
form: the dimensionless lattice gap `m_lat(a_j)` is allowed (indeed must) vanish as the
spacing `a_j→0`, while the PHYSICAL gap `Δ(a_j) = m_lat(a_j)/a_j` carries a two-sided
spacing-UNIFORM bound `0 < physGapMin ≤ Δ(a_j) ≤ physGapMax` plus a spacing-uniform
convergence modulus. (The earlier interface — a uniform positive *lattice-unit* floor —
was the wrong shape: it describes an infinite-mass/trivial continuum, not YM; it has been
removed.) The genuine open content is `physGapMin > 0` (the gap surviving `a→0` in
physical units) — **no inhabitant** for 4D YM. The conditional theorem
`scaling_continuum_physGap` builds the continuum physical gap as a positive `RegularCReal`
from this; continuum clustering is stated at the physical rate. The no-go results (Cubitt
et al. = family decision problem; Pour-El–Richards = low-regularity artifact) do not bind a
fixed-theory proof; the missing piece is a genuine spacing-uniform estimate, not a logical
obstruction. Also fixed: `HasSpectralGapAt rec m_0` now genuinely binds its rate
(`SpectralGapBound ∧ m_0 ≤ ofQ'(1 − sep)`), no longer ignoring `m_0`; the rate-to-margin
relation, where not internally derivable, is carried as an explicit OS4 obligation.
**This does not close the Clay problem.** Nor is that modulus the only remaining
obligation: the same model must first be tied to the two-parameter bare-Wilson
limit (or to exact effective-RG measures with a proved bare-action bridge), the
canonical reflected half-space OS reconstruction, and its actual generator.
The convergence-modulus half is provable for scalar φ⁴ in d=2,3 (Bauerschmidt–Dagallier) —
the realistic proof-of-concept target (φ⁴ has a tunable bare mass, so it exercises the
spacing-uniform convergence machinery but NOT YM's dimensional-transmutation gap
generation, which is the genuinely open part).

**Bottom line.** The UV and gauge carriers have exact finite precursors tied to
SU(2) heat-kernel / Casimir data. The current nontriviality result is only a
finite surrogate inequality, not a Wick test; Clay-facing interaction requires
a nonzero canonical connected higher cumulant. Cutoff reflection-positivity
theorems carry real proved content, but are not yet pinned to the canonical
continuum Schwinger functional and reflected half-space Hilbert space.
The O(4)-restoration carrier has **no genuine non-trivial precursor** — only
the identity-rotation witness, with the boundary made explicit by proving the
equivariance constraint is non-vacuous. The continuum limit, the full-measure
OS construction, and the interacting continuum Hamiltonian remain open
research mathematics. This repository proves real finite facts and states the
open problem honestly; it does not close it.

## Addendum (2026-06-25): the π-free node-free Wall-1 reduction + Turok artifacts

A focused campaign reduced the **all-order SU(2) heat-kernel character Gram
PSD** ("Wall-1") to THREE named analytic atoms via a π-free, node-free route,
and added two finite Turok-template scaffolds. This addendum records the result
honestly. **Wall-1 is REDUCED, not closed.** The Clay problem remains open; the
continuum (`a → 0`) frontier is untouched. A companion capstone is
`wall1-reduction-campaign-2026-06-25.md`.

### (a) Wall-1 reduced to three named atoms (the π-free node-free route)

The all-order Gram PSD is the predicate `GramRed.MomentSquarePos M`:
`momentSquare M c N ≥ 0` for EVERY order `N` and coefficient vector `c`. The
campaign supplies a SECOND route to it (independent of the earlier
`UniformGramSOS` / P_N-wall route in `MomentSquarePSD.lean`), going through the
Chebyshev-`U` orthogonality matrix and the R-projection of the moment integral.

- **CAPSTONE (CONDITIONAL).** `MomentIntegralPSD.wilson_momentSquare_nonneg`
  (and its general form `momentSquare_nonneg`): `SOSIntegral M ⇒ MomentSquarePos
  M`, specialized to the SU(2) heat-kernel moments `wilsonMoments t ht`. The
  downstream PSD form is `MomentIntegralPSD.wilson_gramPSD_of_sosIntegral`.
  Axiom-clean (`propext`/`Quot.sound`).

- **The reduction is to EXACTLY these three named atoms** (all explicit
  hypotheses, nothing hidden):
  1. `ChebOrthoMatrix.OffDiagClosed` — the even off-diagonal √-weighted FTC
     atom that closes the orthogonality matrix `∫U_cU_d√ = semiInt·δ_{cd}`. It
     is a `Prop` (`∀ e ≥ 1, ConvergesTo (seqOrth e) czero`), derivable from
     `ChebOrthoBudget.cellBoundExists` for even `e ≥ 2` (the summed
     midpoint-quadrature error estimate; `cellBoundExists`/`BudgetExists` are
     `Prop`-∃ obligations).
  2. `MomentIntegralPSD.RProjection a` — the R-series sum-integral interchange
     `∫U_e R √ = semiInt·r_e` per edge, carried as a **Type-level `structure`**
     with the genuine per-edge integral `edgeIntegral : Nat → CReal` and its
     value identification.
  3. `MomentIntegralPSD.SOSIntegral M` (definitionally `=
     MomentSquarePSD.UniformGramSOS M`, via `sosIntegral_eq_uniformGramSOS`) —
     the SOS-integrand moment-integral identity plus the Riemann convergence of
     the proved-nonnegative SOS sums, packaged as a **Type-level `×'`** uniform
     nonnegative certificate.

  All three are genuine analytic convergence/interchange obligations — the same
  flavor as the proved semicircle convergence in (b). They are NOT proved.

- **The supporting STRUCTURE is genuinely PROVED, axiom-clean** (the chain
  around the atoms):
  - `ChebOrthoMatrix.orthMatrix` — the orthogonality matrix `[∫U_cU_d√]_{cd} =
    semiInt·I` (manifestly PSD via `orthMatrix_diag_nonneg : semiInt ≥ 0`),
    CONDITIONAL only on `OffDiagClosed`; the pointwise fusion
    (`chebU_fusion`, GENERAL `U_c·U_d = Ufusion c d`, proved here) and the
    `ConvergesTo` linearity lemmas (`convergesTo_add`/`_csum`/`_congr_seq`,
    built from scratch) are UNCONDITIONAL.
  - `MomentIntegralPSD.momentIntegral_entry` — the per-entry identity
    `∫U_pU_q R √ = (semiInt·2a)·gram(p,q)`, with the fusion / `r_e = 2a·m_e`
    (`RCoeffReproduction.rCoeff_eq_two_a_moment`) / gram algebra UNCONDITIONAL,
    CONDITIONAL only on the per-edge `RProjection`.
  - `ChebOrthoOffDiag.orthInt_odd_converges` — the ODD off-diagonal vanishing,
    **UNCONDITIONAL**.
  - `ChebUDClosure.Bderiv_identity_uncond` — the polynomial antiderivative
    identity feeding the FTC, **UNCONDITIONAL**.

  Net: the ENTIRE orthogonality → moment-integral → PSD structure is proved;
  only the three named analytic atoms remain open.

### (b) The semicircle constructive Riemann integral (UNCONDITIONAL)

`SemicircleBoundClosed.semiInt` is the integral `∫_{−1}^1 √(1−x²)` realized as a
constructive real with a **hypothesis-free** convergence certificate
(`semiInt_converges`) and the proved enclosure `0 ≤ semiInt ≤ 2`
(`semiInt_nonneg`, `semiInt_leRat_two`) — the first fully-rigorous constructive
Riemann integral in the library, built from the proved Cauchy rate
(`semiRateB_mono`) and the two-sided refinement bound (`semiLeRatBound`).
π-FREE: `semiInt` is used throughout as an abstract positive constant; its exact
value π/2 is NOT proved (and is not needed — the Machin-π route is deliberately
avoided). All axiom-clean.

### (c) Two Turok-template artifacts (honest about scope)

- **Krein–OS reconstruction scaffold** (`KreinOS.lean`). `krein_os_reconstruction`
  packages an indefinite-metric (Krein/BRST) datum with Θκ-positivity +
  compatibilities ⇒ a positive physical sector + (gap datum ⇒) a strictly
  positive finite-volume gap; `kreinReconstructionExample` is a NON-VACUOUS
  2-dimensional inhabitant (so the lemma is not vacuously true). This is
  Stage-1 SCAFFOLDING / a structural generalization of the repo's GNS
  reconstructions. **OUT OF SCOPE (named open):** the projection of *pure*
  Yang–Mills onto this template. Note the positive-metric Wilson OS2 is already
  unconditional (`ReflectionPositivity.lean`), so this Krein layer is off the
  pure-YM critical path. Axiom-clean.

- **Bakry–Émery 2nd-gap proof** (`BakryEmeryGap.lean`). `be_to_poincare`
  derives the Poincaré/variance inequality from the slacked finite-regulator
  Bakry–Émery hypothesis (the genuine BE chain at finite regulator); `be_gap`
  gives the strictly-positive finite-volume gap `ρ` as an `IsPositive` witness;
  `beDatumExample` is a non-vacuous inhabitant (symmetric two-state walk, ρ=2).
  **HONEST SCOPE:** this is a SECOND, independent proof of the **fixed-spacing**
  gap; the `a → 0` continuum use is explicitly NOT claimed (the carré-du-champ
  functional is the wrong form in the continuum limit). Axiom-clean.

### (d) Wall-2: m ≤ 3 done, m ≥ 4 6j open

`LoopyLinkIntegral.lean` extends the abstract↔real partition identity beyond the
tree geometry. The `m`-fold shared-link Haar integral is PROVED for `m = 2` (the
orthogonality kernel δ) and `m = 3`
(`tripleCharInt_eq_fusionInd : ∫χ_aχ_bχ_c = N_{abc}`, the single-6j fusion
multiplicity), by Clebsch–Gordan-then-orthogonality. The general `m`-fold link
integral for `m ≥ 4` (the genuine `(m−2)`-fold SU(2) 6j network) and the
per-link `LinkCollapseData` it feeds remain NAMED-open. Closing it would upgrade
the fixed-spacing gap from the tree geometry to the general loopy lattice with
no change to the abstract Dobrushin/Kotecký–Preiss tail. Axiom-clean.

### What is and is NOT closed

PROVED unconditionally (real prior result, unchanged): the fixed-spacing
tree-scoped infinite-volume mass gap
`TreeFixedSpacingGap.tree_fixed_spacing_mass_gap` (axiom-clean,
geometrically-restricted to ≤ 2-shared-link geometry; the continuum `a → 0`
limit is NOT addressed).

NOT closed by this campaign: Wall-1 is REDUCED to the three named atoms
{`OffDiagClosed`, `RProjection`, `SOSIntegral`}, not proved; the Turok artifacts
are honest-scope scaffolds (Krein-OS: pure-YM projection out of scope;
Bakry–Émery: fixed-spacing only); Wall-2 `m ≥ 4` is open. The whole library
builds clean (289 jobs) and every load-bearing declaration is axiom-clean
(`propext`/`Quot.sound` only). The Clay problem remains OPEN.

---

## Addendum 2026-06-27 — off-diagonal CLOSED; bond-moving route FALSIFIED; pivot to cluster expansion

**New unconditional results (axiom-clean, build green, ~3432 theorems):**
- **Off-diagonal Chebyshev orthogonality `∫U_e√(1−x²)=0` (∀e≥1) is now PROVED
  unconditionally** (`ChebOrthoOffDiagFinal.offdiag_orthogonality_unconditional`),
  cascading to the **unconditional orthogonality matrix
  `∫U_cU_d√ = semiInt·δ_{cd}`** (`ChebOrthoMatrixUncond.orthMatrix_unconditional`).
  This discharges Wall-1 atom (1) `OffDiagClosed`.
- Wall-1 atoms (2)/(3) (`RProjection`/`SOSIntegral`) bottom out in
  `JTPIdentity.DiffJTP` (the heat-kernel Chebyshev expansion κ=Σr_f U_f), a deep
  theta-function wall — and Wall-1 is OFF the OS2 critical path anyway (OS2 is
  proved unconditionally via `ReflectionPositivity`).

**OS2-critical-path attempt (bond-moving RG) — FALSIFIED:**
- The bond-moving full-mode defect chain (`GenuineResidualDefect`,
  `BondMovingRelResidual`, `CrudeMomentBound`) aimed to inhabit the cluster bound
  via the RG bond-move. Its load-bearing obligation `FusionRelResidualBound` was
  found **FALSE**: (i) a normalization bug (`rrelFix(0)=bmc(0)−1→158` at w=.99),
  and (ii) fundamentally the bond-moving (pointwise-product `K_w^p`) defect is
  **linear `O(1−w)`, not quadratic** (per-step defect `≈0.4374·(1−w)`, power 1.00,
  exact-arithmetic numerics) — so `Σ_k d_k ~ Σ1/k` diverges and the product floor
  → 0: **no gap**. Root cause: pointwise product of heat kernels is not a heat
  kernel (deviation `O(1−w)`); only the full Migdal–Kadanoff step (bond-move +
  decimation) could be quadratic, and MK is uncontrolled in d>1. Those three files
  carry ⚠️ DEPRECATED banners; their `Q'`-arithmetic lemmas remain reusable.

**Still genuinely PROVED on the critical path (unchanged, valid):**
OS2 reflection positivity (unconditional); `ClusteringImpliesGap` (clustering ⇒
located finite-volume gap, division-free); `ClusterGapReduction` (cluster bound ⇒
continuum mass m_∞>0); `FourDExistence.ym_mass_gap_of_existence` (the end
implication). The single genuine missing input is an inhabited
`ClusterGapReduction.UniformClusterBound` (an ORACLE).

**Path forward (in progress):** inhabit `UniformClusterBound` via the STANDARD
strong-coupling polymer / cluster expansion (Kotecký–Preiss / Mayer; literature:
Osterwalder–Seiler, Shen–Zhu–Zhu), which yields the fixed-spacing exponential
clustering with volume-independent constants — bypassing both DiffJTP and the dead
bond-moving route, and feeding the proved `clustering ⇒ gap ⇒ continuum mass`
chain. Scope: a Kotecký–Preiss convergence lemma + the activity-smallness input at
strong coupling. This yields a genuine fixed-spacing strong-coupling gap (NOT the
continuum Clay result — `a→0` + O(4) restoration remain the open frontier). The
Clay problem remains OPEN.

---

## Addendum 2026-06-27 — the cluster-expansion path-forward, EXECUTED (fixed-spacing)

The "path forward" above (inhabit `UniformClusterBound` via the standard
strong-coupling polymer/cluster expansion) has now been carried out genuinely and
axiom-clean (`[propext]`/`[Quot.sound]` only), as a sequence of merged loops.
**The Clay problem remains OPEN** — what follows is the *fixed-spacing,
strong-coupling* sub-result, not the continuum gap.

**Now genuinely PROVED (unconditional, finite-volume / fixed-spacing):**
1. **Combinatorial cluster count — UNCONDITIONAL.** The lattice-animal predicate is
   the genuine one (`IsClusterThrough` = internally-connected, `Nodup` plaquette
   set, `connectedIn`/`ChainIn`). The full chain `adjSpanningTreeInternal`
   (constructive BFS spanning-tree build; boundary-crossing by `ChainIn` induction;
   `insertUnder` preserving adjacency/`Nodup`) → `AdjSpanningTree` (choice-free
   `reindex` to faithful `nbrs`-indices) → `SpanningTreeExists` → `decode_tour_sound`
   → `DecodeComplete` → `overcount_of_complete` is HYPOTHESIS-FREE. `animalCount` is
   the real `|enumPolys|` cardinality (not free data), `count_le : animalCount n ≤
   ((D+1)²)^n` proved. (Files: `PolymerModel`, `BddLatticeAnimal`, `DecodeComplete`,
   `DecodeTourSound`, `SpanningTreeBuild`, `AdjSpanningBuild`.) The old
   `ClusterCount.toyClusterCountBound` (`deg^{2n}` free data) is retired off the path.
2. **KP convergence on the genuine count.** `kp_criterion_of_count` (proved,
   parametric) applied to the genuine `zChainClusterCountBound` at strong coupling
   `w=1/6`: threshold `kpRatio = 16·(1/108)·3 = 4/9 ≤ 1/2` by real computation ⇒
   `genuineKP_sum_le_two : Σ kpTerm ≤ 2`. (`GenuineKP.lean`.)
3. **Mayer clustering ⇒ a located gap from the REAL correlator.**
   `clusterSpanSum_decay : ≤ 2·ρ^d` (consumes `connected_spanning_size_ge`, the
   spanning-size ≥ d engine). `reconTransfer_located_gap : LocatedSpectralGap` of the
   ACTUAL reconstructed single-edge transfer operator, `sep = ρ = 2·(1/6)³`, with
   `hcluster` = the real `wilsonG_decay` (character double-sum, via
   `wilsonG ≃ corr(reconTransfer)`) and `hdead` = real Casimir monotonicity
   (`coeffW_excited_le_one`). (`MayerClustering.lean`.)
4. **Positive infinite-volume mass on the real gap.** `realCorrUniformClusterBound`
   (an inhabited `UniformClusterBound` whose `located Λ` IS `reconTransfer_located_gap`
   — `rfl`) ⇒ `realCorr_continuum_mass_isPositive : realContinuumRate.IsPositive`
   (margin `107/108` for all Λ), via the proved `clusterBound_continuum_mass_isPositive`.
   (`RealCorrMass.lean`.)
5. Side result: the capstone's clustering tie was DE-CIRCULARIZED — `genuineCorrLink`
   replaces the `eqv_refl` `wilsonCorr` with the real `wilsonG` (domination
   `wilsonG w 2 n ≤ (sep Λ)^n`, honest `w ≤ 1/4`). (`GenuineCorrLink.lean`.)

So `ClusterGapReduction.UniformClusterBound` (the single ORACLE flagged above) is
now inhabited TWO ways — `genuineUniformClusterBound` (real geometric Λ-tail,
synthetic closed-form margins) and `realCorrUniformClusterBound` (real
Wilson-correlator margins, trivial Λ-tail) — COMPLEMENTARY, neither yet the full
physical object.

**Still OPEN (the honest frontier — unchanged in kind):**
- **Multi-plaquette Mayer/Ursell.** `MayerUrsellIdentity` (connected correlator =
  spanning-cluster sum) is DISCHARGED for the single-line chain only; the
  multi-plaquette / loopy generalization is the wall (believed TRUE; standard for
  convergent polymer expansions; constructive proof open). This is also what a
  `UniformClusterBound` with BOTH real margins AND real Λ-variation needs.
- **Uniform-in-`w`** (results are at the single weight `w=1/6`).
- **Continuum `a→0`** (dimensional transmutation + O(4) restoration + Prokhorov
  tightness) — the R2 frontier, untouched by the fixed-spacing cluster expansion.
- 4D Yang–Mills mass gap = the Clay target: **OPEN.**

---

## Addendum 2026-06-28 — scorecard, RG-landing, R1/R2/R3, vacuum-stability loop, weak-coupling object

Continues the 2026-06-27 addendum. All work axiom-clean (`propext`/`Quot.sound` only), full build
green, audit at 3666 theorems. **The Clay problem remains OPEN**; this records the sharpened
proved-vs-open boundary.

### The external rubric is now a compile-checked scorecard
Pulled + AUDITED external formalizations (`docs/external-formalization-rubric.md`,
`reference/leanmillennium-pinned/`): the canonical Clay-in-Lean (`lean-dojo/LeanMillenniumPrizeProblems`)
is a STATEMENT (unproven `∃`, bounded-Hamiltonian proxy); the publicized "complete proof"
(`Shariq81/yang-mills-mass-gap`, Coq) is an OVERCLAIM — its own frontier doc admits YM₄ is open at an
admitted Balaban hypothesis (48 `Admitted`, 83 `Axiom`); HepLean/PhysLean is HEP math, not a gap
proof. `lean/YMGap/Rubric/ClayScorecard.lean` transcribes each Clay clause constructively: the MET
clauses (fixed-spacing gap, clustering, OS2, nontriviality, positive infinite-volume mass) are
inhabited by REAL theorems (`reconTransfer_located_gap`, `wilsonG_decay`, `realCorr_continuum_mass_isPositive`,
`reflectionPositiveSchwinger_holds`); `clay_fixed_spacing_met` is PROVED. `ClayTarget` (fixed-spacing
∧ the three continuum obligations) is DELIBERATELY UNINHABITED — producing a term without
sorry/axiom IS the open problem. `make lean-rubric` checks it every build. **OPEN-vs-CLOSED is now a
compile-checked fact, not prose.**

### Newly PROVED (fixed-spacing, strong-coupling)
- **Cluster-count completeness UNCONDITIONAL** over the genuine lattice-animal predicate: the whole
  chain (BFS spanning-tree build → AdjSpanningTree → decode-tour soundness → DecodeComplete →
  over-count) is hypothesis-free; `animalCount` is the real `|enumPolys|` cardinality.
- **KP convergence on the genuine count**, uniform on the strong-coupling INTERVAL `w ∈ [0, 1/6]`
  (`UniformCouplingGap`, via genuine cube-monotonicity) — not just the single weight.
- **Mayer clustering** extended from the single line to arbitrary **trees** (`treeWilsonG_decay`) AND
  single **cycles** (`CycleMayer.cycleWilsonG_decay`) — the loops sub-case of the loopy wall, with
  the honest finding that there is NO holonomy obstruction at the SU(2) character level.
- **A located gap in the fixed-spacing reconstruction surrogate** from the genuine `wilsonG` decay +
  Casimir monotonicity (`reconTransfer_located_gap`), and a positive correlator-mass precursor
  (`realCorr_continuum_mass_isPositive`).  Neither is yet identified with the generator edge of the
  canonical reflected continuum OS theory.
- The RG-landing target sharpened to a **dimensionless rational certificate** `q ≤ m/Λ_YM`
  (`RGLandingCertificate`, `q := prodFloor`), and a **non-degenerate `DefectGapRecursion`** from the
  real quadratic bond-moving defect with an unconditional product floor.

### The decisive conceptual finding (the R2(B) vacuum-stability loop, 4 iterations)
Attacking the physical-gap identification (does the survival-product margin equal the actual gap?):
1. The feared **vacuum-eigenvalue shift is NOT the obstruction** — the RG fusion step's
   normalization fixes the trivial-rep coefficient at 1 by construction (`VacuumStability`).
2. But the dominant-mode **"gap = 1 − leading character coefficient" margin is STRONG-COUPLING-ONLY**:
   `coeffW(w,1) = 2w³` is the SU(2) heat-kernel coefficient `2e^{−3t}`, which EXCEEDS the vacuum
   coefficient 1 for `w > 2^{−1/3} ≈ 0.794`. The margin `(1−c₁)²/(1+c₁²)` crosses ZERO at `c₁=1`
   (`NormExcitedDrift`), and this PERSISTS at N=2 (`FusionMarginScope`, machine-checked) — NOT a
   truncation artifact. The zero-crossing sits in the **intermediate-coupling region** = the same
   "middle" as the continuum problem.
   ⇒ the physical weak-coupling gap is a DIFFERENT object (the gauge-invariant spatial transfer
   operator's located gap / connected-correlator decay), and the character-coefficient margin cannot
   be carried into the continuum region.

### The weak-coupling gap object, reduced (not closed)
`WeakCouplingGap.lean`: the single-link character object is PROVEN to fail (`sep ≥ 1` at weak
coupling); the correct object `WeakClusteringBound` (spatial transfer operator + connected-correlator
decay) yields a real located gap via `clustering_implies_located` (`weakSpectralGap`, `sep = μ < 1`),
CONDITIONAL on the named clustering. Chain: **weak gap ⟸ weak clustering ⟸ strong clustering (PROVED,
uniform `[0,1/6]`) + `RGClusteringTransport`** (RG-flow preservation through the middle, a genuine
existential, UNINHABITED).

### The open boundary, now precise (= the continuum problem, three named obligations)
1. `WeakClusteringBound` — weak-coupling exponential clustering of the gauge-invariant spatial
   transfer operator.
2. `RGClusteringTransport` — carrying clustering from the proved strong window through the
   intermediate-coupling **middle** to weak coupling (the radius-overlap wall).
3. `RGLandingInput` — the dimensional-transmutation scale normalization `m/Λ_YM`.

All three are uninhabited; each is genuine research-open mathematics (Balaban-level RG control,
exponentially-small dimensionally-transmuted gap). The fixed-spacing strong-coupling story is proved
up to these doors; the doors are the continuum/4D problem. **Clay target: OPEN.**

### The two-sided radius-overlap program (formalized 2026-06-28)
`TwoSidedGap.lean` makes "the middle from both sides" precise. `CouplingWindow` = a clustering rate
`ρ<1` with geometric decay for all `w` in an interval. `strongWindow : [0, 1/6]` is PROVED (gap field
discharged from `uniform_rho_le_endpoint` + `uniform_cluster_decay`). `WeakWindow : [w_w, 1]` and
`WindowOverlap (w_w ≤ 1/6)` are UNINHABITED. `twoSided_covers` (interval case-split) + 
`twoSided_gap_all_couplings` PROVE: given the overlap, every coupling `w ∈ [0,1]` gets a clustering/gap
bound — the strong branch fully proved, the weak branch consuming only `WeakWindow` + `WindowOverlap`.
So the all-coupling (hence continuum, at the weak end) gap is reduced to the weak control reaching
DOWN to `w_w ≤ 1/6` to meet the proved strong window — the intermediate "middle." No such weak window
is known: that gap is `RGClusteringTransport` / `WeakClusteringBound`, the continuum wall.

### Pushing the windows together + the character ceiling (2026-06-28)
`CharacterWindowCeiling.lean`. The strong/character clustering window is genuinely PUSHED up from
`w ≤ 1/6` to `w ≤ 7/9 ≈ 0.778` (`rho_lt_one_ext`, `coeffW_excited_le_rho_ext` by genuine induction,
`wilsonG_decay_ext`; `strongWilsonWindowExt : WilsonWindow` at `hi = 7/9`). Honest mechanism note: the
KP `CouplingWindow` (TwoSidedGap) caps at `~0.17` (count overhead `K=16,e=3`); the sharper single-line
`wilsonG` decay is the mechanism whose ceiling is `2^{−1/3}`, so the push uses a parallel `WilsonWindow`
(no KP window faked). CEILING PROVED: for `w³ ≥ 1/2` (`w ≥ 2^{−1/3} ≈ 0.7937`) the rate `rho w = 2w³ ≥ 1`
(`character_rate_ge_one_at_ceiling`, witness `rho(4/5) ≥ 1`), so the clustering bound does not decay;
every `WilsonWindow` has `hi < 2^{−1/3} < 1` (`characterWindow_hi_lt_ceiling`). **The two-sided overlap
provably CANNOT close via the character mechanism — the strong radius is bounded at `2^{−1/3}`.** The
region `[2^{−1/3}, 1]` (weak/continuum, incl. the middle) has no character clustering; a window there is
the open continuum problem (`WeakClusteringBound`/`RGClusteringTransport`, uninhabited). Clay OPEN.

### Weak-region boundary no-go (2026-06-28)
`WeakRegionNoGo.lean` rigorously maps the open weak/continuum interval `[2^{−1/3}, 1]` (exactly
`1/2 ≤ w³ ∧ w ≤ 1`). PROVED: the character rate `rho w = 2w³` is `≥ 1` throughout (monotone 1→2,
real proof), so it never decays and no character `WilsonWindow` reaches the interval
(`character_window_excludes_weak`); and the approximate fusion-RG margin is nonpositive at the
in-interval witness `w=4/5` (`FusionMarginScope`). `weak_region_dichotomy` packages BOTH exclusions ⇒
the weak gap is necessarily NON-PERTURBATIVE. `NonPerturbativeWeakGap` records the precise missing
input (a clustering rate `μ < 1 ≤ rho w`), UNINHABITED. **The wall is now a theorem: the convergent
machinery provably cannot reach the weak region.** Closing it = constructing the gauge-invariant
spatial transfer operator's weak-coupling gap / Balaban-level RG control = the open continuum problem.
Clay OPEN.
