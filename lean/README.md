# Lean Formalization

This folder holds the Lean 4 formalization of the constructive
mathematical steps of the Yang–Mills mass gap program, instantiated
per gauge group [SU(2), SU(3), ...] with a uniform reduction toward
all compact simple groups.

The purpose is to make the program's **constructive law** —
"every existence claim returns an object, a witness, and a computable
modulus" (`docs/outline.md` §0.2) — *mechanically enforced* rather
than merely intended. A Lean proof that typechecks under the
discipline below is a machine-checked certificate that a given step is
genuinely constructive.

> **Read `AGENTS.md` before contributing.** It contains the
> non-negotiable constructivity rules. They are easy to violate by
> accident in Lean, because Lean and Mathlib are classical by
> default.

---

## Why Lean, given that Lean is classical

Lean 4 and Mathlib admit `Classical.choice`, excluded middle, and
non-constructive existence as axioms. Left unconstrained, Lean will
happily prove `∃ x, P x` with no extractable witness. That is exactly
what this program forbids.

We therefore work in a **constrained fragment**:

1. Every load-bearing theorem is checked with `#print axioms` to
   confirm it does **not** depend on `Classical.choice`,
   `Classical.em`, `Quot.sound`-via-choice, or `propext` used to
   erase computational content. The maintained baseline is
   `AXIOM_AUDIT.md` (auto-generated; CI fails on drift).
2. Existence is stated using `Σ` (sigma types) / constructive
   existence, not `∃` (`Exists`), wherever a witness is required.
   `∃` is permitted only for genuinely propositional side conditions
   that carry no computational content.
3. Real numbers and moduli use the project's constructive reals
   (`Constructive/Reals.lean` and the `CReal*` modules) with explicit
   Cauchy moduli, not Mathlib's `ℝ` (which is classical via
   Cauchy-sequence quotients plus choice for completeness). Exact
   rational arithmetic lives in the project's `Q'`
   (`Constructive/Rationals.lean`); Lean core's `Rat` was rejected for
   load-bearing use because `Rat.decEq` depends on `Classical.choice`.
4. Estimates return the witnessing constant, not just its existence.
   A bound `μ ≤ C · exp(...)` is formalized as a function returning
   `C` together with the proof, not as `∃ C, μ ≤ ...`.

This is the same discipline as Bishop-style constructive analysis,
mechanized. The `#print axioms` gate is the enforcement mechanism;
see `AGENTS.md`.

**Substrate: MLTT / HoTT.** Lean is the Calculus of Inductive
Constructions, an extension of Martin-Löf Type Theory. We hold ourselves
to what is valid in MLTT and its homotopy-type-theory extension: the
only permitted axioms are `propext` and `Quot.sound` (both HoTT-valid —
`propext` is univalence for mere propositions, `Quot` is the set-quotient
HIT); `Classical.choice`/LEM (invalid in MLTT/HoTT) and `native_decide`
(trusts the compiler, not a kernel reduction) are banned. Because the
proof's worth is its computational content, we prefer **canonicity**:
axiom-free, `decide`-checkable proofs, and witnesses carried as
`Type`-level data (`Σ`, functions `ε ↦ N`) rather than erased inside a
proof-irrelevant `Prop` `∃`. See `AGENTS.md` Rule 8.

**No external dependencies.** The library is Mathlib-free — the Lake
manifest has zero packages. Everything builds from Lean core
(`leanprover/lean4:v4.29.1`, pinned in `lean-toolchain`).

---

## Folder structure (as of 2026-07-03)

```
lean/
├── README.md                  # This file.
├── AGENTS.md                  # Constructivity contract — read first.
├── AXIOM_AUDIT.md             # Auto-maintained axiom-gate baseline (~3.8k tracked decls).
├── SORRY_LEDGER.md            # Every sorry, logged. Currently: library is sorry-free.
├── CLASSICAL_LEDGER.md        # Every quarantined classical input (Rule 4). Currently empty.
├── lakefile.toml              # Lake build configuration (no external packages).
├── lean-toolchain             # Pinned Lean version (v4.29.1).
├── YMGap.lean                 # Root import aggregator (annotates load-bearing vs excluded).
├── docs/                      # Lean-local design notes (KP limit, RG transport, ...).
└── YMGap/
    ├── Constructive/          # Group-independent constructive substrate (~70 modules):
    │                          #   Q' exact rationals; CReal with explicit moduli
    │                          #   (arithmetic, exp/log, sqrt/cbrt, trig, π, completion);
    │                          #   geometric/finite-sum machinery; SU(3) character-tail
    │                          #   factorization; soundness bounds.
    ├── RepTheory/             # Per-group representation data: SU2, SU3, Spin4 (+H₄
    │                          #   reflection data), CasimirData, RepData, SimpleGroup
    │                          #   (the compact-simple-G interface).
    ├── BufferShell.lean       # Single-plaquette buffer-shell tail bound (κ, β, C as data).
    ├── Sheaf/                 # Bound-witness sheaf framework: Site, BoundWitness
    │                          #   (flabby presheaf), Summability (KP certificates),
    │                          #   Gluing (domGlue_preserves_KP), PolymerDomination, SU2KP.
    ├── RG/                    # RG induction + the uniform-group reduction: BlockSpin,
    │                          #   InductiveState, PolynomialTree, production/directed
    │                          #   interface transports, stable-tail/dynamics certificates,
    │                          #   SigmaHatPilot(+UV), UniformBudget,
    │                          #   character-tail majorant/antitone chain, EtaPackaging,
    │                          #   SUNWeylData / WeylDimGeneral / RankCollapse.
    ├── MassGap/               # Headline composition theorems: SU2 (mass_gap_SU2),
    │                          #   SimpleGroup (mass_gap_simple_group).
    ├── Categorical/           # Site/presheaf/2-cell scaffolding; ScaleSheaf cocycles;
    │                          #   budget functors and closure transports.
    ├── Codynamic.lean         # Codynamic transfer template (EKF ↔ YM signature port).
    ├── HigherCategorical.lean # 2-categorical RG-flow packaging.
    ├── Continuum/             # The continuum campaign (~470 modules): finite-volume
    │                          #   functionals and partition positivity (S2–S6), KP
    │                          #   increment engine, reflection positivity (OS2 via
    │                          #   Osterwalder–Seiler), OS axioms + reconstruction
    │                          #   interfaces, complete GNS Hilbert space, transfer
    │                          #   calculus, spectral gap/localization, Bakry–Émery and
    │                          #   codynamic floors, Mayer/Ursell/tree-graph reductions,
    │                          #   6j/pentagon track, O(4)/H₄ restoration groundwork,
    │                          #   AF-rate calibration, and the Tier-0 frontier files
    │                          #   (Tier0Scorecard, ContinuumFrontierScorecard,
    │                          #   FourDExistence, ...). Many `*Progress`/`*Close`
    │                          #   modules are stepwise reductions of named frontier
    │                          #   atoms — check `YMGap.lean`'s annotations and the
    │                          #   scorecard docstrings for load-bearing status.
    ├── Rubric/                # Machine-checked transcription of the Clay rubric:
    │                          #   ClayScorecard (fixed-spacing line PROVED; ClayTarget
    │                          #   deliberately uninhabited), ContinuumScorecard,
    │                          #   Loop/Reconstruction scorecards.
    ├── PolyAtlas.lean         # Expository/design scaffolding — NOT load-bearing,
    ├── ModuliAlgebra.lean     #   excluded from the default aggregator (see YMGap.lean).
    └── ...
```

The dependency direction runs upward from `Constructive/` (depends on
nothing but Lean core) through `RepTheory/`, the lattice layers
(`Sheaf/`, `RG/`, `MassGap/`), into `Continuum/` and finally the
`Rubric/` scorecards. `YMGap.lean` is annotated: it states which
modules are load-bearing and which are deliberately excluded from the
default build to keep the axiom-audit surface honest.

---

## Relationship to the rest of the repository

The Lean formalization mirrors, but does not replace, the Python
`computations/` and the LaTeX `formal/`:

| Concern | Python `computations/` | LaTeX `formal/` | Lean `lean/` |
|---|---|---|---|
| role | compute explicit constants | state the argument for humans | machine-check constructivity |
| trust | numerical, regression-tested | peer-readable | kernel-verified |
| output | the numbers $(\kappa, \beta, C, \rho, K, \ldots)$ | the prose proof | the certified theorem |

The intended workflow per milestone:

1. `computations/` produces the explicit constants and a numerical
   sanity check.
2. `formal/` states the argument in prose with those constants.
3. `lean/` certifies that the argument's existence claims are
   constructive, using the constants as inputs.

A milestone's Lean obligation is **not** "formalize everything" — it
is "formalize the *constructivity-critical* existence claims," i.e.
the ones where a classical proof would be unacceptable. The
`AGENTS.md` file lists which claims those are per phase.

---

## Building

```sh
lake build                 # build everything (no external packages to fetch)
lake build YMGap.MassGap.SU2                    # just the SU(2) headline chain
lake build YMGap.Continuum.Tier0Scorecard       # just the frontier scorecard
lake build YMGap.PolyAtlas YMGap.ModuliAlgebra  # the excluded expository modules
```

Every PR-equivalent change must pass `lake build` and the axiom check
described in `AGENTS.md` (`make lean-audit` at the repo root; refresh
the baseline with `make lean-audit-update` only for deliberate,
reviewed changes).

---

## Current status (2026-07-03)

**Active BF4 milestone (2026-07-28).** The canonical retained spatial
carrier is now literal Lean data: 24 lower faces, 48 physical links, an
explicit 25-link tree, 23 chord coordinates, and the five transmitted chord
indices `{0,4,5,6,10}`.  Rational unit quaternions define the actual SU(2)
relative class coordinate and finite Cauchy--Schwarz proves its `[-1,1]`
range.  Complete source/target/path/factor locations, an explicit nonempty
identity carrier, and the 23-factor kinetic Harnack instantiation are in
`BF4CanonicalClassCoordinateCarrier`.

The closed-sheet route is now decisively classified.  The exact row-mass
budget makes binary-multicover existence constructively decidable, but
`BF4SU2OuterBinaryMulticoverNoGo` proves that the universal normality theorem
is false: a literal positive cutoff-two row has a four-link cocircuit
certificate excluding every binary multicover.  The same row is proved to
belong to the enumerated global joint carrier in
`BF4SU2OuterJointCarrierStrictEnlargement`.  Thus the live combinatorial
obstruction is not binary-sheet normality.

`BF4SU2OuterJointCarrierRawRowMass` identifies nonemptiness of the
four-preimage coarse carrier exactly with one scalar statement about that
specific BF4 row:
`wholeSlabJointCarrierCodes` has positive length if and only if the finite
sum of its nonnegative whole-slab recoupling weights is strictly positive.
The reverse implication is constructive: positive total mass selects a
positive coarse target, then positive face channels and shared-link fusion
witnesses.  It also constructs the literal normalized
`CoherentSlabRecouplingSource` and proves division-safe lower/upper order
transfer from raw numerator and partition bounds.
`BF4SU2OuterRawRowMassRetainedHarnack` conditionally feeds this scalar
certificate into the grouped retained Feynman--Kac floor.  The certificate
is not universal.  `BF4SU2OuterRawRowMassCounterexample` constructs a
positive cutoff-two fine row whose only nonvacuum coarse packet is
`(2,0,0,0)` and whose adjacent coarse packets are vacuum.  Every positive
face channel therefore produces the forbidden link word `(2,0,0)`.
Consequently the raw-row mass vanishes in the strict-order sense and
`SU2OuterRawRowMassPositive` is contradictory for the pinned geometry.

`BF4SU2OuterFineIntertwinerRetainedCarrier` makes the corrective pivot.
Before the lossy four-preimage projection, the literal finite fine
link-intertwiner carrier is canonically inhabited on every positive row.
`BF4SU2FineIntertwinerConditionalKernel` normalizes the exact unit-counting
Haar fiber on that carrier and proves partition positivity, nonnegativity,
strict member positivity, and row mass one.
`BF4SU2FineIntertwinerChoiCPOrder` then performs the all-label source/target
Choi contraction on the same retained carrier.  It proves exact conditional
expectation, finite and matrix-amplified Gram positivity, and lower/upper
Loewner domination from a pointwise window on the complete interior spatial
weight.  The collar row killing the old carrier is instantiated with row
mass one.
`BF4SU2FineIntertwinerPhysicalDisintegration` proves that this normalized
row is the conditional law of the literal production spin foam.  Its
partition is exactly the `Q'` image of the corrected-slab SU(2) link
multiplicity, the sum of the per-witness face contributions is the genuine
`SlabPhysicalData.physicalTerm`, and multiplying the conditional row by that
physical term recovers each unnormalized witness contribution.  Thus the
base Haar carrier and normalization are physically identified.

The fixed-plane grouped identification is now exact.
`BF4SU2FixedIntertwinerPhysicalChoi` identifies the source and target
half-amplitudes with `centralHalfAmplitude`, the interior insertion with the
fixed-plane heat factor, and the resulting Choi entry with the genuine
`centralPhysicalReflectedKernel`.
`BF4SU2FixedMagneticMehlerCarrier` then refines every spin-\(s\) fixed-face
channel by its literal \(s+1\) magnetic indices.  Conditional summation
recovers the representation dimension exactly, while each refined channel
carries only the heat eigenweight \(w^{C_4(s)}\).  Hence the physical and
reference spatial insertions have the spacing-independent pointwise window
\([1,1]\); the local magnetic tail is controlled by the proved heat
majorant.  This equality concerns the spatial insertion on the enlarged
carrier, not a completed Gaussian endpoint Mehler comparison.

Here “magnetic” is representation-theoretic: it is the full Peter--Weyl
matrix-index fiber on a face whose spin label is fixed during the
conditional sum.  It is not a restriction to a prescribed monopole,
center-vortex, background-field, or topological magnetic-flux sector.
The implementation sums this full fiber dynamically; fixing one magnetic
matrix index would fail to reconstruct the representation dimension.

`BF4SU2FixedMagneticPositiveKernelConvergence` identifies every normalized
kernel entry with a cutoff-stable lower/reflected-upper Yang--Mills cylinder
expectation.  The arbitrary-nome degree-thirteen envelope therefore gives
an executable two-cutoff modulus; degree thirteen pays the full link
intertwiner growth together with the magnetic dimension.
`BF4SU2FixedMagneticPhysicalHSCauchy` compensates the complete square
carrier dimension: on a base carrier of size \(N\), it requests entry
tolerance \(\varepsilon/N\) and proves exactly
\[
  \|J_{K_1}-J_{K_2}\|_{\rm HS}^2
  \le N^2(\varepsilon/N)^2=\varepsilon^2
\]
for all later cutoffs beyond the displayed modulus.

Finally, `BF4SU2FixedMagneticPhysicalMarkov` performs the physically correct
normalization of the symmetric joint law.  It filters precisely the
positive row marginals, proves discarded rows decouple, divides each
retained row by its own marginal, and obtains a nonempty reversible Markov
carrier with normalized stationary marginal.  Constants are fixed, the
marginal-weighted mean is preserved, and the corresponding physical
mean-zero subspace is invariant.  Its marginal vacuum projector is
constructed and removed exactly.  Uniform counting measure is no longer
substituted for the physical vacuum.  The exact marginal-weighted inner
product is also constructed, and finite Fubini plus detailed balance proves
that the physical conditional BF4 operator is self-adjoint in it, without
adjoining square roots of rational marginal weights.

The same-carrier HS route is now vacuum-correct.  In
`BF4NormalizedSameCarrierPerron`, normalized nonlinear and Mehler matrices
are compared after removing the same rank-one vacuum projector; raw
mean-zero eigenmodes are proved unchanged.  A cutoff-indexed convergence
datum with growing carrier dimension and explicit error modulus yields the
eventual `7/100` perturbation and `q ≤ 1/4` for an actual dominant finite
eigenmode.  The remaining analytic task is a distinct Gaussian endpoint
Mehler kernel on the same physical weighted carrier, with an interacting
physical-minus-Mehler entry estimate (not merely the now-exact spatial
insertion window), followed by a constructive contraction or dominant-mode
identification on the physical marginal-mean-zero subspace.  A raw
normalized matrix is deliberately never subjected to the false global
quarter bound because it contains the vacuum eigenvalue one.

The Peter--Weyl endpoint interface is now exact at the constructive
finite-dimensional level.  `BF4CentralPositivePeterWeylEndpoint` proves the
fundamental rational-complex \(\mathrm{SU}(2)\) Haar Schur table and exhibits
a negative matrix coefficient, then defines nonvacuous all-spin boundary and
double-Haar endpoint-projection targets on the literal physical labels.
`BF4FiveHolonomyNormalizedKernel` constructs the exactly Haar-normalized
finite product heat kernel on the five rational-unit-quaternion coordinates,
proves its endpoint symmetry, and supplies an inhabited expansion-level
all-spin character transform on the exact positive BF4 carrier.  Its
mixed-radix state mode is faithful, its one-term character expansions
synthesize pointwise, and the genuine all-mode \(\mathrm{SU}(2)^5\) Haar
Kronecker table proves normalization and orthogonality.  This is explicitly a
faithful character-coordinate realization: it does not yet identify those
characters with the geometric BF4 spin networks obtained after integrating
the eighteen non-transmitted chords.  The same module also proves that
`generalizedA = K^{-1}S` is not symmetric, so the coupled endpoint must retain
the symmetric pair `(kineticK24, spatialS24)` (or construct its symmetric
conjugate) rather than treating `generalizedA` itself as a scalar Hessian.
`BF4SymmetricReferenceOperatorComparison` therefore treats the projected
endpoint as the signed symmetric positive-semidefinite operator it naturally
is; its weighted quarter consumer does not require an entrywise-positive
endpoint law or a matching endpoint marginal.
`BF4AFUniformRowRelativeBudget` completes the cross-numerator,
numerator/partition, carrier-growth, marginal-floor, and AF-family algebra
feeding that consumer.  The unproved inputs are now purely analytic and
physical: the coupled normalized five-holonomy endpoint kernel, the geometric
BF4 spin-network identification of the constructed all-spin character
carrier, its spectral certificate, and uniform Yang--Mills estimates
inhabiting the displayed budgets.

`BF4CanonicalFiniteNumeratorPartitionBudget` now inhabits the complete
numerator/partition/marginal interface at every fixed finite physical BF4
scale for every signed symmetric endpoint.  Its tolerance is the executable
exact rational
\[
  \varepsilon_{\rm fin}
  = |S|\,\frac{\sum_{x\in S} b(x)}{\pi_{\min}},
\]
where each \(b(x)\) is formed from literal physical-minus-endpoint numerator
and partition differences.  The module also locates the vacuum row and
proves that the canonical order-one Cauchy--Schwarz rate is at least one.
Since \(\varepsilon_{\rm fin}\geq0\), that particular rank-one rate can never
satisfy \(r+\varepsilon\leq1/4\).  Thus the live spectral route must use
centered cancellation or the higher positive-Gram endpoint; the still-open
analytic task is spacing-uniform smallness of the exact physical comparison
budget for that sharper endpoint along the genuine AF trajectory.

`BF4CanonicalFiniteMehlerGramSpectralBudget` constructs that sharper
fixed-scale spectral datum.  It subtracts the exact physical vacuum joint
\(V(x,y)=\pi(x)\pi(y)\), proves its quadratic form vanishes on the physical
\(\pi\)-mean-zero carrier, and defines the executable centered Schur rate
\[
  r_{\rm cen}
  =\max_{x\in S}
    \frac{\sum_{y\in S}|M(x,y)-\pi(x)\pi(y)|}{\pi(x)}.
\]
Every denominator is positive by membership in `centralPositiveHalfStates`.
The resulting positive-Gram `MehlerGramEndpointSpectralData`, its raw
endpoint, and its complete exact finite comparison budget are unconditional
constructive definitions.  A further normalization audit proves
\[
  1-\pi(0)^2\leq r_{\rm cen}\pi(0).
\]
Consequently the previously proposed all-scale bound for
`matchedExactCenteredMehlerGramQuarterCostAt = r_cen + epsilon_fin`
would force \(\pi(0)>1/2\) at every scale, independently of the truncation
orders.  Neither `CubicMarginLaw` nor `PhysicalSpacingEnvelope` contains
such a stationary-marginal hypothesis.

`BF4VacuumCalibratedFiniteMehlerGramSpectralBudget` removes this artificial
obstruction.  It proves that square-scaling a raw endpoint preserves
symmetry, PSD, and the physical-mean-zero Rayleigh bound, then scales the
Mehler Gram by \(\pi(0)^2\).  The calibrated vacuum entry is exactly
\(\pi(0)^2\), and its certified spectral rate is no larger than the original
one.  On matched coordinates the corrected exact scalar is
`matchedVacuumCalibratedMehlerGramQuarterCostAt`.  Its spacing-uniform
quarter theorem is reduced without hidden finite data to the two genuine
Yang--Mills estimates: calibrated spectral rate at most \(1/8\), and exact
physical comparison tolerance at most \(1/8\).

The current grouped-action layer removes one of those hidden
identifications.  `BF4PhysicalBoundaryCommonKernelAction` uses the complete
fixed-interface carrier after the eighteen non-transmitted chords have been
integrated and constructs the literal activity
\[
  a_{\rm phys}(b)=W(b)B(b)/Z_{\rm phys}.
\]
It proves constructively that the vacuum boundary coordinate is strictly
positive and that the transposed physical half-amplitude acts on this
activity as the exact marginal:
\[
  \sum_b A(x,b)a_{\rm phys}(b)=\pi(x).
\]
For an exact grouped gluing
\(A(x,b)=\sum_m P(x,m)T(m,b)\), finite Fubini pushes this activity through
\(T\), producing a nonzero positive activity on the enlarged middle carrier
and identifying the common kernel \(P(x,m)\) with the same physical
marginal.  `BF4GroupedCommonKernelPerronAction` installs that theorem into
the scale-uniform Faraut/core-tail consumer; the physical activity and
physical action-identification fields are no longer assumptions.
`PhysicalBF4OneStepContractionGluingRow.toFarautBufferedRow` also turns an
exact one-step stationary density gluing on the literal retained carrier
into the full witness-bearing \(C_s^2q_s^{m-2}\) buffer, and the
scale-family producer forces that gluing to use definitionally the same
bit, depth, and nonlinear-rate schedule as the grouped profile.  The
remaining BF4 analytic inputs are now explicit: construct the genuine
grouped half-amplitude gluing and a positive primitive terminal
certificate, identify the calibrated Peter--Weyl activity on the same
middle carrier and prove its Perron remainder, and prove the actual
one-step stationary BF4 density gluing together with its endpoint and
\(q_s\le 1/4\) bounds.  Those Yang--Mills estimates are not yet inhabited.

**Ledger state.** The `YMGap` library builds sorry-free (`lake build`
reports zero `declaration uses 'sorry'`; see `SORRY_LEDGER.md`, whose
remaining entries are closure records and named-hypothesis
bookkeeping, not open holes). `AXIOM_AUDIT.md` tracks ~3,758
declarations, axiom-gated to `∅` / `[propext]` /
`[propext, Quot.sound]` — no `Classical.*`, no `sorryAx`, no
`native_decide`. `CLASSICAL_LEDGER.md` has zero entries (see the
Minlos caveat below).

**Proved — the fixed-spacing Clay line.**
`Rubric.ClayScorecard.clay_fixed_spacing_met` genuinely inhabits every
fixed-lattice-spacing clause of the transcribed Clay rubric, each
discharged by a concrete named theorem about a specific YM object:
positive located spectral gap of the reconstructed transfer operator,
geometric clustering of the real Wilson connected correlator,
nontriviality, OS2 reflection positivity (via the Osterwalder–Seiler
diagonalization `ReflectionPositivity.reflSchwinger_nonneg`, which
retired the previous P_N/product-form walls from the critical path),
and infinite-volume mass positivity. Supporting closed work includes
the constructive-reals substrate, the SU(2)/SU(3) KP-certificate
derivations, the S2–S6 finite/infinite-volume functional stages
(partition positivity, reweighted state, KP increment engine, limit
with modulus), the complete constructive GNS Hilbert space
(`GNSComplete`), and the uniform-group reduction
(`mass_gap_simple_group` via the proven character-tail majorant chain,
with SU(2)/SU(3) discharged end-to-end).

**Deliberately open — the machine-checked frontier.** The continuum
(`a → 0`) Clay problem is carried as *uninhabited* bundles, never
faked, in **two complementary enumerations** whose unification is
planned (`work_plan.md` Milestone 11.14). On the measure/RG side,
`Continuum.Tier0Scorecard` enumerates: Sub-wall A (loopy geometry:
(T′) tree-graph, (D1) Mayer–Ursell bridge, (D2) separation metric,
(A2) 6j pentagon), Sub-wall B (Balaban RG: the `SpectralMarginInput`
atoms `hlocalize` / `hbridge` / `hadd`), and the orthogonal
`CitedMinlosLift` (σ-additive continuum measure — note: this
cited-classical input is not yet processed through the Rule-4
quarantine, hence the empty classical ledger currently *understates*
the continuum chain's classical content; resolving this is
`work_plan.md` Milestone 11.9). On the operator/OS side,
`Rubric.ReconstructionScorecardFinal` names five open tokens:
`OpenNode1FiniteSMargin`, `OpenTrueMargin` (the genuine dimensionless
physical margin `Δ_k = m_lat(a_k)/a_k`, distinct from the proved
survival-product *surrogate* in the green line — see AGENTS.md
Rule 9(6)), `OpenPhysicalWilsonBridge`, `OpenBoundedHamiltonian`, and
`OpenContinuumMinlos`. `ClayScorecard.ClayTarget` additionally names
O(4) restoration, coupling-uniformity, gauge content, asymptotic
freedom, and nontriviality (`Continuum/FourDExistence.lean`); the
Jaffe–Witten local-field/stress-tensor/OPE layer is currently only
two bare `Prop` fields there and is scoped as Milestone 11.17.
`ContinuumFrontierScorecard` proves that the codynamic, curvature, and
OS-reconstruction continuum routes all converge on the single
uninhabited scalar `UniformSpacingFloor`.

The active Core-B reduction now reaches the canonical row-one origin
square-gap quotient.  `CoreBUniversalSquareGap` gives the exact all-index
factorization, `CoreBConsumerOrigin` and `Rubric/CoreBPhysicalBridge` give the
consumer composition, and `CoreBAtomwiseGapBounds` proves the parity content
floors, sharp coefficient maxima/reserves, endpoint degrees, adverse-chain
length bound, and homogeneous-chain endpoint estimate for all eleven bounded
selector families.  `CoreBCanonicalSquareShell` supplies the exact parity
four-square shell, and `CoreBLowGapBudget` kernel-checks the finite
coefficientwise envelope budget conditional on its explicitly transcribed
mass lists.  `CoreBCubicEvenTail` now proves the exact all-index cubic
even-gap tail `3311/884736`, with a nonnegative geometric remainder and an
explicit modulus; the comparison from actual adverse mass to that majorant
remains open.  `CoreBLowGapClassifier` closes the first actual classifier
fiber: for every stable odd length, the real bounded adverse endpoint-gap-two
atoms are equivalent to five explicit selector patterns, with a computable
Boolean classifier.  Summing those five actual contributions into the
transcribed `oddMass2Formula` remains open.  A parallel exact scout found
strictly positive Bernstein
coefficients cell-by-cell through canonical length eight after the physical
change of variable `u=4w²`.  `CoreBBernsteinConsumer` kernel-checks the direct
typed composition from an all-index actual-cell Bernstein family to the
row-one quotient certificate, and `Rubric/CoreBPhysicalBridge` carries that
family all the way to the guarded bridge.
`BernsteinSignedMonomialReconstruction` now closes the generic algebraic seam:
any finite integer-signed monomial ledger is computably compiled into one
common Bernstein row with an exact evaluation theorem.
`CoreBActualBernsteinRow` now closes the Core-B-specific enumeration seam: it
constructs the actual eleven-family integer row and proves exact signed-ledger
reconstruction, then reduces the physical cell certificate to coefficient
nonnegativity plus one explicit `u=4w²` scaling identity.  No all-index
Core-B-specific certificate family is yet inhabited, so Core B remains open
at those two final row obligations.

On the compact-dual lane, `CompactDualPinnedPhysicalData` pins the physical
coupling, cutoff, box, observable, packet graph, spin-foam data, and RG state.
`CompactDualBoundaryReflectionCone` closes the rational one-interface
reflection cone: every actual finite boundary packet has an exact rational
sum-of-squares Gram and an exact constructive-real equivalence to the existing
diagonal reflection form.  The rational weight
`ofQ'(w^(4*C₂(s)))` is not yet identified with the Schwinger weight
`exp(-t*C₂(s))`, and no RG block-map preservation theorem is claimed.

`CompactDualPositiveChannelDoor` records the supplied `(1,1,1,1)` rim
survival probe at the exact rational level.  Its twelve page-spin sectors are
carried as four exact permutation orbits with multiplicities `1,6,4,1`;
their nonnegative orbit contributions resum to
`1/4 + (9/2)s^16 + 6s^24 + (21/4)s^32` and feed a conditional
activity-times-square consumer.  This is a finite positive-channel candidate,
not a physical block theorem.  The module names the remaining all-label
source-dependent kernel obligation over the actual fine/coarse physical
labelling lists; no inhabitant, semantic Haar-network bridge, complete
channel decomposition, or overlap remainder is constructed.

The executable companion has since derived an all-label theorem for the
wheel topology: trivalent Haar projection writes each fixed-label wheel as a
positive dimension factor times a squared Clebsch--Gordan norm, so every
fixed-rim heat-kernel channel is coefficientwise nonnegative.  This analytic
identity is documented and independently regression-checked, but is not yet
formalized in Lean or identified with the pinned physical spin-foam fiber.
The canonical unit-rim manifest is exported by
`computations/dual_positivity_manifest.py`.

**Per-atom partial progress** (the scorecard docstrings may lag these;
Milestone 11.0 re-syncs them): (D2) has a sound, non-tight L¹
inhabitant (`SepLatticeZ4Close.SepLatticeZ4_witness`); (T′) is reduced
to three named legs, of which only the Penrose sign-domination is new
mathematics (`TreeGraphBoundProgress`, with the (P) leg under further
active reduction in `PenroseDomInduction`); the pentagon track has the
Level-1/Level-2 analysis and a refutation of the permutation surrogate
(`PentagonRelation`); `hbridge` has its wiring lemma
(`PinnedBridgeProgress.edgeShift_le_gradedDefect`); and the δ-loop
capstone (`DeltaFrontierLedger`) reduces the bond-moving obstruction to
the single vacuum-normalized bulk-shift residual `bulkCtrl` (= the
`hlocalize` content, open for `p ≥ 2`). Hygiene note: the library
carries exactly 9 `noncomputable` declarations (in `NormExcitedDrift`,
`DominantModeRecursion`, `UniformCouplingFromAF`), pending the
classification ledger required by the AGENTS.md Rule 1 addendum.

**Not claimed.** No inhabitant of `ClayTarget`, `Tier0Scorecard`, or
`UniformSpacingFloor` exists in this library. The Clay Yang–Mills
existence and mass gap problem is OPEN; what is machine-checked is the
fixed-spacing closure and the reduction of the remainder to the named
atoms above. The current campaign against those atoms is
`work_plan.md` Phase 11 (frontier mathematics) and Phase 12
(compliance, publication, hygiene).

---
