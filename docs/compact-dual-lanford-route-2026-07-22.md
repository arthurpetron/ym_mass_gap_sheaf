# Compact dual RG with positivity and a Lanford certificate

## Decision

The most novel high-leverage program is the conjunction

1. never linearize the compact gauge variables;
2. perform the block step in the exact character/fusion (spin-foam) dual;
3. carry reflection positivity as an invariant of the block map;
4. retain the adjacent-block correlation remainder instead of deleting it;
5. certify a cutoff-uniform contraction and landing statement by exact
   rational/interval arithmetic.

This is a parallel physical route, not a replacement for the active Core-B
closure.  Core B remains the nearest sharply isolated analytic milestone.
The compact-dual route is the candidate for the physical `singleStep` and
RG-I5--RG-I9 inputs after that local obstruction.

## What the repository already has

### Exact compact/dual algebra

The finite-box character expansion is no longer merely aspirational.

- `Z4ParametricArbitraryCutoffSpinFoamIdentity` constructs the literal
  coupling-parametric, arbitrary-physical-cutoff packet graph and proves its
  exact finite-box spin-foam identity.
- `Z4ExplicitPhysicalCutoffReduction` and
  `Z4ExplicitValenceFusionMultiplicity` eliminate auxiliary bookkeeping down
  to explicit face coefficients and local fusion-path cardinalities.
- `Z4ExplicitSpinFoamBounds` proves nonnegativity of every face factor,
  multiplicity factor, summand, and finite partition sum.
- The finite shared-link Haar/fusion modules prove local completeness through
  every four-dimensional link valence from zero through six.  The rational
  Temperley--Lieb/transvectant development supplies exact low-label
  recoupling data well beyond disjoint plaquettes.
- `Z4StrongCouplingParametricAnchor` gives a genuine finite-cutoff
  very-strong-coupling contraction anchor.

This closes the finite exact rewriting and a strong-coupling anchor.  It does
not construct an RG map through the crossover or remove the representation
cutoff.  It also does not contain a faithful signed all-label recoupling
theory: `racahPerm` is explicitly a nonphysical permutation surrogate and the
general Jones--Wenzl/pentagon carrier `JWTowerCoherence` remains open.

### Positivity

`ReflectionPositivity` proves the Osterwalder--Seiler reflection form as a
Schur-diagonal weighted sum of squares for every finite character packet.
The much larger `Z4HalfTimeReflection*` chain supplies finite-box geometric,
incidence, Fubini, and limiting infrastructure.

What is not yet proved is that a proposed dual block/decimation map sends the
relevant interacting reflection-positive boundary cone into the next cone.
Initial-scale OS2 is not the same statement as positivity preserved by every
intermediate RG step.  There is also a hard existing fence:
`cutoffZero_parityPushforward_ne_physical_coarseCube` proves that bare parity
pushforward is not the physical coarse weight.

### Overlap corrections

The adjacent-block remainder is not completely virgin territory.
`Z4BlockLocalityTensorObstruction` records an exact two-block covariance
obstruction and corrected density, while
`Z4ThreeBlockOverlapCumulantKernel` records the third-cumulant obstruction and
an exact positive normalized kernel at `epsilon = 1/8`.  These are finite
local prototypes.  The all-block connected norm, its stability under repeated
blocking, and its cutoff-uniform control are still open.

### The Lanford-shaped consumer

`RG/DirectedStableTailPresentation`,
`RG/StableDynamics`, and `RG/DirectedStableDynamics` already define the
constructive output expected from a computer-assisted RG theorem:

- a selected physical ray and forward normalization to a common interface;
- an exact rational `q < 1`;
- a Type-valued preserved admissible domain;
- a constructive landing scale and state;
- separate summable dynamic and interface distortions;
- geometric contraction and a finite spectral-gap consumer.

These modules are composition machinery.  Their Yang--Mills contraction,
landing, and summability fields remain uninhabited.

## The exact missing conjunction

Define a production dual block step whose state contains:

- the finite character packet/cutoff and retained boundary intertwiner data;
- the exact local fusion/Haar kernel;
- a reflection-positive boundary Gram/cone certificate;
- the adjacent-block overlap remainder as data;
- the relevant-coordinate projection and observable transport;
- a norm and interval enclosure suitable for a derivative/Jacobian bound.

For one step, prove simultaneously:

1. **exactness:** the output plus the retained remainder equals the original
   finite-volume character sum;
2. **cone preservation:** the reflected boundary Gram stays nonnegative;
3. **no amputation:** the overlap remainder is transported and bounded, never
   replaced by zero;
4. **cutoff control:** the retained packet and discarded character tail have
   an explicit modulus;
5. **interface control:** the step instantiates a forward
   `ProductionCarrierMap` with a computed discrepancy;
6. **contractive enclosure:** on a preserved rational ball, the transported
   derivative norm is at most an explicit `q < 1` over the certified
   crossover window, or supplies an accumulated scale-dependent contraction
   with summable defects.

Only this conjunction may instantiate the physical
`DirectedStableDynamicsCertificate`.

The first production-facing interface should have the shape

```text
SpinFoamRPBlockRemainder

D_* mu_fine = mu_coarse + R_overlap
sum R_overlap = 0
reflection intertwining / Gram-cone compatibility
norm(R_overlap) <= c * (1 - w)^2
```

and its principal theorem should be an exact
`parametricSpinFoam_block_pushforward_decomposition`.  The block kernel must
be source-dependent, positive, row-normalized, supported on genuine fine
spin-foam configurations, and parameterized by the physical coupling/cutoff
schedule.  An adapter from this object to
`DirectedStableDynamicsCertificate` is the shortest route that actually joins
the exact algebra to the Lanford consumer.

As of 2026-07-23 these remain declaration and theorem **targets**:
`SpinFoamRPBlockRemainder` is not yet defined in `lean/YMGap`.  The exact-Haar
dual-positivity probe has opened a finite positive-channel door: the twelve
`(1,1,1,1)` rim page-spin sectors form four positive permutation orbits whose
activity resums to
`1/4 + (9/2)s^16 + 6s^24 + (21/4)s^32`.
`CompactDualPositiveChannelDoor` kernel-checks that orbit ledger and exposes
the all-label physical-kernel obligation, but does not identify the probe with
the pinned physical term or construct a block remainder.  The exact scope and
semantic bridge are recorded in
`docs/dual-positivity-survival-cd2-map-2026-07-23.md`.

The same probe now has an analytic all-label upgrade at the wheel topology.
The trivalent Haar projector factors every fixed-label wheel into a positive
dimension prefactor times a sum of Clebsch--Gordan amplitude squares.  Hence
every fixed-rim heat-kernel channel is coefficientwise nonnegative for all
labels.  This does not apply to the unanchored slab and is not yet a theorem
about `CompactDualPhysicalData.physicalTerm`.  The executable translation
boundary is pinned by `computations/dual_positivity_manifest.py`, whose
canonical unit-rim certificate has SHA-256
`f7ad2fd06add0c8e5bc51e4aa340bdb0e86687f52d664d3ce3397f21be5d2e52`.

## Required theorem order

### CD-0 — Crosswalk and pinning **[STRUCTURAL PINNING CLOSED]**

Pin the physical objects shared by the exact spin-foam identity, the
reflection form, and the RG state.  In particular, the coupling, finite box,
physical cutoff, face enumeration, link incidence, and observable packet must
be definitionally the same data.  No detached surrogate state is accepted.

`CompactDualPinnedPhysicalData` now supplies this shared object.  One
`CompactDualPhysicalData` value definitionally fixes the rational coupling,
physical cutoff, box, observable packet, physical face/link enumeration,
fusion-complete packet graph, spin-foam term/partition, algebraic
Schur-diagonal reflection form, and the corresponding `RGInterface`/`RGState`
indices.  The generic norm, certificate, and error carriers remain explicit
inputs; the construction manufactures no analytic witness.

The first exact mismatch is now visible rather than hidden.  The spin-foam
packet uses rational weights `w^(4*C₂(s))`, while `reflSchwinger` uses
constructive-real weights `exp(-t*C₂(s))`.  Identifying the two requires a
genuine representation/approximation theorem for `w = exp(-t/4)`; it is not
definitional data.  CD-1 must either construct that bridge with a modulus or
state the RP cone directly over the pinned rational Schur weights.

### CD-1 — Dual boundary state and reflection cone

Define the finite boundary packet/intertwiner carrier and its reflected Gram.
Prove equivalence with the already-closed Schur-diagonal reflection form in
the one-interface case.

### CD-2 — One exact RP-preserving dual block

Construct the smallest nontrivial overlapping block map directly from the
finite packet-graph identity.  Prove exact Fubini/link elimination, output
packet support, reflection-cone preservation, and an equality defining the
overlap remainder.  The named target is
`parametricSpinFoam_block_pushforward_decomposition`, returning a
`SpinFoamRPBlockRemainder` rather than a bare partition-function equality.

The first falsification target is two adjacent plaquettes sharing one link.
It is large enough to detect the known failure of naive shared-link
factorization and small enough for exhaustive rational checking.

### CD-3 — Remainder norm and cutoff modulus

Give the retained overlap remainder a norm tied to the same dual boundary
state.  Bound it uniformly in volume and construct a representation-cutoff
tail modulus.  A bound that grows with the cutoff is diagnostic failure, not
a certificate.

### CD-4 — Lanford enclosure

Represent the transported dual RG map on a concrete weighted coefficient
ball.  Use exact rational interval/Taylor enclosures to prove:

- self-mapping of the ball;
- cone preservation throughout the enclosure;
- a uniform derivative bound `q < 1`;
- or, if the true one-step ratio approaches one along the ultraviolet
  harmonic flow, an accumulated scale-dependent contraction with a summable
  defect ledger;
- separate dynamic and interface-error caps.

### CD-5 — Constructive crossover landing

Construct the scale at which the physical ultraviolet trajectory enters the
certified dual ball.  This is the nonperturbative crossover theorem; a
proposition asserting eventual entry is insufficient.

### CD-6 — Stable dynamics and physical consumers

Instantiate `DirectedStableDynamicsCertificate`, then supply the physical
Wilson readout, volume-uniform floor/modulus, spacing conversion, and
continuum/OS bindings.  Only here may the finite contraction feed a physical
mass-gap statement.

## Falsification gates

The route is abandoned or revised if any of the following occurs.

1. The exact dual block map fails to preserve the chosen reflection cone.
2. The overlap remainder has no cutoff-uniform weighted norm.
3. Oscillatory recoupling signs survive every Gram/squared-kernel
   representation and prevent a cone-compatible enclosure.
4. The certified derivative lower bound reaches or exceeds one on every
   physically reachable crossover ball and no accumulated scale-dependent
   contraction is available.
5. The representation cutoff required by the crossover grows faster than the
   constructed tail modulus can pay.
6. A roughening singularity intersects the mass-gap channel used by the
   contraction, rather than only the string-tension observable.

## Important non-shortcuts

- Compactness removes the chart-created “large field” region, but it does not
  by itself give a usable dual norm or contraction.
- Nonnegative heat-kernel character coefficients and initial OS2 do not prove
  that an arbitrary block map preserves reflection positivity.
- The finite spin-foam identity is exact at every fixed cutoff; the
  continuum/UV character limit is not obtained by setting `w = 1`, where the
  strong-coupling character expansion is known in this repository to diverge.
- The raw character activity is not a continuum contraction norm: its
  elementary rate already exceeds one beyond the character crossover.  A
  usable dual Lanford norm must be renormalized and scale-dependent.
- A fixed `q < 1` cannot describe the true deep-ultraviolet harmonic flow,
  whose one-step ratio tends to one.  The fixed contraction belongs to a
  finite crossover enclosure unless an accumulated contraction theorem
  replaces it.
- Termwise positivity is not assumed for faithful nonabelian recoupling.
  Reflection positivity must be carried at the Gram/quadratic-form level.
- A hierarchical or Migdal--Kadanoff recursion is admissible only with its
  deleted overlap term restored as an explicit remainder.
- Roughening is not represented by a proved repository object.  The route
  must target the mass-gap/reflection channel directly rather than import
  strong-coupling string-tension analyticity through a possible roughening
  singularity.
- The stable-dynamics structures are consumers of a physical certificate, not
  evidence that such a certificate exists.

## Immediate implementation step

CD-0 and the direct rational CD-1 cone are structurally pinned, and the
positive wheel channel now has both an all-label squared-norm derivation and
a machine-readable exact certificate.  The next step is the semantic
geometry theorem identifying the manifest's oriented wheel with the
corresponding physical finite fiber, followed by a Lean formalization of the
all-label squared-norm identity.  Then test the complete CD-2
two-plaquette/one-shared-link boundary decomposition.  Its output must still
be an exact

`input partition = blocked packet contribution + overlap remainder`

together with a reflection-cone preservation decision and a complete
rational diagnostic when preservation fails.
