# Constructive Yang--Mills mass-gap formalization

> **Research status (2026-09-11): this repository does not prove the Clay
> Yang--Mills existence and mass-gap theorem.** It contains kernel-checked
> finite-lattice and strong-coupling results, explicit proof compilers, and an
> honest ledger of the bridges that remain open.

This project is a Mathlib-free Lean 4 formalization of a constructive route
from four-dimensional lattice gauge theory to continuum quantum Yang--Mills.
The active physical model is SU(2) BF4 lattice data. Existence statements are
required to carry witnesses and explicit moduli; numerical exploration is not
part of the trusted proof.

## Whole-project goal

The Clay target requires a non-trivial quantum Yang--Mills theory on
`R^4`, satisfying suitable QFT axioms, with an isolated vacuum and a uniform
mass gap `Delta > 0` for every compact simple gauge group. The repository is
currently pursuing SU(2) as the concrete non-abelian construction; a valid
all-group lift remains separate work.

```text
WHOLE-PROJECT GOAL / CLAY TARGET
Continuum 4D Yang--Mills exists + QFT axioms + isolated vacuum + Delta > 0
                                  |
                    EXPAND into causal obligations
                                  v
finite 4D SU(2) lattice measure and exact representation data       [PROVED]
  |                   FIX w=1/400 AND slab extent=1
  +-> OS Gram -> physical transfer -> exact vacuum component -----+
  |   and sector event contains the weight-one vacuum    [PROVED] |
  +-> complete-source conservation + target-weighted contraction -+
  |   internal bad mass <= (384/425) * sector mass       [PROVED] |
  `-> degree-13 Casimir majorant -> exact finite Fubini -----------+
      full partition <= 65/64, for every spin cutoff     [PROVED] |
                                                                 v
                     AND: all three inputs on the same ensemble
                                                                 |
       outside physical mass <= 1/64                             |
         -> escaping bad mass <= (6/425) * sector mass   [PROVED] <+
         -> successful mass >= (7/85) * sector mass      [PROVED]
         -> same normalized OS traffic >= 448/5525       [PROVED]
                                  |
                 + zero extension -> exact sector energy [PROVED]
                 + restricted move energy <= C * energy [PROVED]
                 -> positive sector-parity energy floor [PROVED]
                 AND centered norm <= move energy / kappa [OPEN]
                 (all-K exact cube/parity sector + positive
                  OS vacuum orbits: PROVED; weighted coverage: OPEN)
                                  v
  -> cutoff-uniform all-vector non-abelian Poincare estimate           [OPEN]
  + exact raw-entry saturation + stable positive Gram               [PROVED]
  + normalized norm/transfer compatibility -> completed gap         [OPEN]
  + volume-uniform estimates -> controlled thermodynamic limit       [OPEN]
  + spacing control -> continuum limit and OS/Wightman reconstruction [OPEN]
  -> extension from SU(2) to every compact simple gauge group        [OPEN]
                                  |
                 CONTRACT only through checked bridges
                                  v
Continuum 4D Yang--Mills exists + QFT axioms + isolated vacuum + Delta > 0
WHOLE-PROJECT GOAL / CLAY TARGET
```

`PROVED` means kernel-checked at exactly the displayed scope. It does not mean
that downstream arrows have been proved. `PARTIAL` means concrete objects and
useful theorems exist but a required bridge is missing.

## Current frontier

The present bottleneck is a cutoff-uniform gap for the **exact finite vacuum
component of the actual physical SU(2) BF4 transfer**, not the reducible full
positive-row carrier and not an abstract spectral theorem.

**Latest result:** at slab extent one, the full raw OS kernel on cube-supported
states now has an exact heat-weight/Boolean-overlap formula. For each half, its 48 production
links reduce to twelve SU(2) triangle tests and twelve boundary-zero tests;
the fixed part contributes eight corner triangles. The original weights and
boundary enumeration are retained, with no auxiliary multiplicity left.

If both endpoint label bounds are `R`, the raw kernel entry stops changing
exactly at every cutoff `K >= 2R`. A computed cutoff gives each pair an explicit
stable rational entry. Every finite quadratic form of this single stable
kernel is realized by the original physical OS Gram at a computed common
cutoff and is nonnegative for `w >= 0`.

This is raw-entry compatibility and a positive algebraic finite-span form,
not convergence of normalized rows, Hilbert norms, or completed transfer
operators. Those constructions and a cutoff-uniform gap remain open.

**Exact sector:** at slab extent one, every positive rational weight parameter
`w` and every spin cutoff `K >= 1`, the canonical vacuum sector is **exactly**
the bounded six-face cube labellings with common parity. The constructive
inward-mate orbit stays in that sector and reaches vacuum within `K + 1`
genuine positive OS moves.

The key construction puts `|a-b|` on the boundary face between cube labels
`a` and `b`. All source, mate and fixed-link multiplicities are exactly one;
the complete production summand becomes an explicit positive heat-coefficient
product below the original OS kernel. Together with the earlier singleton
pins and parity constraints, this proves both directions of the classification.
The sector sets are nested in `K` and unchanged by positive `w`; their weights
are not. Every mate-invariant observable on the sector is constant.

The edge weights depend explicitly on the state and `w`. Successful-source
traffic coverage and a cutoff-independent norm-to-move estimate remain open;
positive connectivity does not establish either. Sector-set nesting alone
also does not establish norm or operator compatibility across cutoffs; the
new raw-entry saturation theorem supplies a separate, strictly weaker result.

The preceding quantitative result remains: the normalized sector OS flow carries at
least `448/5525` total traffic. Exact source-block Fubini connects it to the
proved `7/85` raw sector-demand fraction. Together with the same-object sector
energy embedding, this gives the positive central-face-parity Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost)` on the exact vacuum component.
These estimates are uniform in spin cutoff `K >= 1` at fixed coupling `1/400`
and slab extent one.
The missing reverse estimate must control every centered sector norm by move
energy with a positive cutoff-independent floor.

The latest checked path is already on that actual OS object.  Every successful
six-face inward-mate source gives a supported two-edge path in the normalized
symmetric OS joint kernel.  Its selected source traffic has total mass at
least `41/425`; exact production-target fibers have congestion bounded by
`globalInwardMateTransportCost`; and all complete sources that forget to the
same first OS edge now inject into distinct literal boundary--intertwiner
summands of that edge.  Consequently their **aggregate** first-edge traffic is
at most the actual OS joint capacity, without a volume- or cutoff-cardinality
loss.  The second edge is now complete too: exact production-target classes
partition all selected source traffic, those classes partition again by their
actual second OS edge, and the resulting loads sum exactly to the original
traffic.  Each second-edge load is bounded by
`globalInwardMateTransportCost` times its OS capacity.

For one concrete observable the answer is now positive.  The parity of
central lower face zero is reversed by every selected inward mate, and because
the intermediate parity is also Boolean, exactly one of the two path edges
changes it.  Lean proves without a triangle-inequality loss that the two
selected parity-gradient energies sum to the selected traffic and are
therefore at least `41/425`.  The complete first-edge energy is now embedded
in the full physical OS Dirichlet form: exact first-edge fibers make the
parity gradient constant, their aggregate traffic is bounded by the matching
OS capacity, and distinct realized edges inject into the Cartesian half-state
square.  The second-edge energy is now embedded as well.  Its exact
production-target and OS-edge partitions contribute no loss; only the already
proved `globalInwardMateTransportCost` congestion factor remains.  The active
contraction is now complete: the explicit cutoff-independent positive floor

```text
(41/425) / (1 + globalInwardMateTransportCost)
```

is bounded by the full physical OS Dirichlet energy of central-face parity at
every cutoff `K >= 1`.  Lean now centers that same Boolean observable with its
exact stationary mean, proves that deleting zero-marginal rows and columns
does not change its Dirichlet energy, and applies the exact
Dirichlet/transfer identity.  The centered vector has a strictly positive
physical norm and obeys the explicit one-observable form estimate

```text
|<f,Tf>| <= q <f,f>,
q = 1 - (1/2) * (41/425) / (1 + globalInwardMateTransportCost),
0 <= q < 1.
```

This is a real cutoff-uniform strict channel of the actual finite physical
transfer, but it is not an all-vector Poincare inequality.  For arbitrary
observables, the selected source-to-target oscillation is at most
`2 * (1 + globalInwardMateTransportCost)` times the actual physical OS
Dirichlet energy.  The proposed Type-level full-carrier coverage input is now
proved impossible.  The XOR parity of central-cube faces `0` and `39` is
unchanged by every simultaneous six-face inward mate, but after exact
stationary centering it has strictly positive physical norm already at cutoff
one (vacuum value zero, proved transverse-face value one).  Its selected
endpoint energy is exactly zero.  Hence
`GlobalInwardMateUniformEndpointCoverage` has no inhabitant.

This obstruction cleanly repoints the proof.  The full positive-row carrier
is already known to be reducible at cutoff two.  Lean now proves the first
sector bridge: a positive raw OS edge cannot leave the exact finite vacuum
component, so whenever an inward-mate source endpoint is in that component,
its common hub and mate endpoint are there too.  A finite-support Boolean
classifier now filters the global source enumeration exactly to those paths;
the resulting Type-level list is duplicate-free and its membership theorem is
an iff, not an assumed selector.  Restricting the partition-normalized traffic
to this list preserves nonnegativity and both proved OS edge-capacity bounds,
including the second-edge congestion factor. The global `41/425` demand floor
does not follow merely by restriction; the new sector bound is `7/85`.
The branch decomposition has now been localized
at the right level: over the exact finite list of full physical fields whose
lower restriction is in the vacuum component, all-target mass plus
first-stretched mass equals the genuine BF4 physical mass exactly.  The
bad-target support argument now needs no equality of boundary labels: the raw
OS kernel sums over those labels, so each field supplies its own positive
boundary summand.  A target preserving the reflected upper state therefore
has a two-edge path from the source lower state.  A target preserving the
lower state stays in the sector directly.  The resulting exact decomposition is
`sector physical mass = successful mass + one-sided bad mass + two-sided bad mass`.
The two-sided residual changes both half-states and is contained in the older
boundary-or-upper crossing list; no strict positive mass reduction is claimed.
The weighted localization is now proved too: every nonnegative function of the
actual lowered target passes through the inverse-fiber and target/root/size
sums, preserving the factor `384/425`.  Taking the exact sector indicator
bounds all internal bad mass by `384/425` of sector physical mass.  Exact
branch conservation then proves
`(41/425) * sector mass <= successful mass + escaping bad mass`.
The escaping mass counts only sources in the sector whose lowered targets
leave it.  Every such source is proved two-sided; two-sided targets that
remain inside the sector are already covered by the contraction.
That escaping mass is now absorbed. The physical degree-thirteen face
majorant has successive ratio at most `2/15625` at the anchor, hence its
all-cutoff one-face sum is at most `15625/15623`. Exact finite Fubini and
the corrected slab's embedding in the 96-face ambient corner box give
`Z <= (15625/15623)^96 <= 65/64`. Since the weight-one vacuum lies in the
sector, outside physical mass is at most `1/64`. Applying the same weighted
contraction to the complementary target event gives
`escaping bad mass <= (6/425) * sector mass`. Subtracting this from the
previous demand bound proves
`successful mass >= (7/85) * sector mass > 0`.
This is a fixed-volume, fixed-coupling result, not uniformity in beta or
lattice spacing.

The sector Dirichlet embedding is now proved without recounting any fibers.
Zero extension of a sector observable adds no physical energy: the exact
component has no crossing OS kernel entries, and zero-marginal rows vanish.
The full half-state energy of this extension equals the already-defined
canonical indexed sector energy. On every restricted path, the extension
agrees with the original observable at all three vertices. Thus the first
edge, second edge, and endpoint estimates restrict with their original
factors `1`, `globalInwardMateTransportCost`, and
`2(1 + globalInwardMateTransportCost)`.

The exact normalization handoff is now proved as well. The sector test is
constant within each fixed-physical source block, so filtering commutes with
the complete-source Fubini sum. The existing production source weights agree
termwise with the raw source weights, yielding
`sector total traffic = successful sector mass / Z`. Thus the traffic is at
least `7/85` times the partition-normalized sector-event mass and, using
`sector mass >= 1` and `Z <= 65/64`, at least `448/5525` absolutely.
The Boolean parity identity says its two path-edge energies sum exactly to
this traffic, giving the sector Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost) > 0`, without a factor-two
triangle-inequality loss. No source list, physical kernel, or normalization
has been changed.

The geometric test now has a checked answer at cutoff two. In
[`BF4PhysicalVacuumSectorInwardMateOrbits.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateOrbits.lean),
`targetLower_eq_mate_sourceLower` identifies the literal source endpoint map;
`cubeInwardOrbit_even_eq_parityCore` proves its all-cutoff parity reduction;
`cubeInwardOrbit_rootTime_eq_zero` gives an explicit vacuum-hitting time for
cube-supported common-parity states. On the canonical cutoff-two sector at
coupling `1/2`, `canonicalCutoffTwo_mate_invariant_constant` proves every
potential-mate invariant is constant. This is a geometric statement, not a
new weighted OS estimate at the anchor coupling.

The all-cutoff physical support implication is now proved in
[`BF4PhysicalHalfCubeSupport.lean`](lean/YMGap/Continuum/BF4PhysicalHalfCubeSupport.lean)
and
[`BF4PhysicalVacuumSectorCubeContainment.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorCubeContainment.lean).
`sharedBoundaryOfKernelNeZero` returns a witnessing nonzero boundary as data.
`vacuumSector_cubeSupportedCommonParity` propagates the singleton pins and
relative parities along the actual canonical component.
`vacuumSector_inwardOrbit_reaches_zero` applies the existing orbit formula to
every sector state; `vacuumSector_cubePairParity_zero` eliminates the
pair-parity obstruction there for every cutoff. These are fixed-geometry
support statements for arbitrary nonnegative `w`, not uniform spectral bounds.

Next: establish physical support and successful-source traffic on the required
potential moves, then prove quantitative norm-to-move coverage at arbitrary
cutoff. The converse inclusion of the entire common-parity cube family in
the canonical sector is not proved here. The orbit formula alone does not
establish weighted coverage or congestion bounds.
The Poincare compiler's algebra remains useful: a correctly formulated
sector-local coverage theorem with floor `kappa > 0` produces the rate shape

```text
q_all = 4(1 + globalInwardMateTransportCost)
        / (4(1 + globalInwardMateTransportCost) + kappa) < 1
```

uniformly for every cutoff `K >= 1`.  No such sector-local uniform coverage
theorem is presently claimed.

See
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean).
The two-level second-edge partition is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean).
The exact Boolean observable identity is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean).
The checked first-edge Dirichlet embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean).
The checked two-level second-edge embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean).
The resulting explicit positive Dirichlet floor is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean).
The stationary centering, positive-norm certificate, exact transfer identity,
and strict one-observable form rate are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean).
The arbitrary-observable two-edge estimate and exact all-vector coverage
frontier are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean).
The conditional coverage-to-uniform-Poincare contraction is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean).
The exact XOR counterexample refuting its full-carrier coverage input is in
[`BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean).
Positive raw-edge closure of the exact vacuum component and its application to
both inward-mate path edges are in
[`BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean).
The exact finite-support classifier and duplicate-free sector-local source list
are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean).
The restricted partition-normalized traffic and its inherited first- and
second-edge capacity bounds are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean).
The exact physical-field sector event and its localized good-plus-bad branch
conservation identity are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean).
The stronger support theorem, allowing arbitrary boundary changes whenever
either half-state is preserved, is in
[`BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean).
The exact three-way mass identity and residual containment are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean).
The contraction against any nonnegative physical target function is in
[`BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean).
Its sector specialization and exact escaping-mass demand bound are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean).
The sharp physical partition ceiling is in
[`BF4PhysicalAnchorPartitionCeiling.lean`](lean/YMGap/Continuum/BF4PhysicalAnchorPartitionCeiling.lean).
The complementary-event comparison, leakage absorption, and positive `7/85`
sector demand are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemand.lean).
The exact zero-extension identity for the canonical indexed sector is in
[`BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean).
The three unconditional restricted observable-energy comparisons are in
[`BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean).
The exact raw-to-normalized traffic identity, positive traffic floor, and
sector-parity Dirichlet consequence are in
[`BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean).

The current verified frontier joins a multiplicity-exact finite enumeration
of the root-first SU(2) cube source to a fixed-target contraction for every
certified first-stretched strand source.  Lean compiles the complete two-root
component union into three finite words:

- one connected rooted `Z^4` animal word in a carrier of size `625^n`;
- one exact physical strand-multiplicity word in a carrier of size `4^n`;
- one complete auxiliary-drop row word in a carrier of size at most `4096^n`.

At fixed root, peel size `n`, and lowered presented target, those words
reconstruct the source physical field and raw auxiliary assignment.  Thus any
explicit duplicate-free fixed-target source family has at most
`10240000^n` members.  Combining that injectivity with the exact per-source
anchor payment `anchorFaceCoefficient^n = (1/32000000)^n` gives the checked
finite-fiber estimate

```text
source fiber weight <= (8/25)^n * target weight.
```

See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean),
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean),
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean).

The classifier domain is now also a literal duplicate-free heterogeneous
product over the twelve cube incidences.  SU(2) fusion-path permutation
invariance proves that every root-first local fiber has the same cardinality
as its production-order fiber.  Hence the complete function-valued source
enumeration, and its injective target-or-first-stretched image, have exactly
`cubeInwardMateSourceBoundaryProduct K physical` members.

The target and first-stretched branches are now extracted as separate
duplicate-free lists whose lengths add back to the exact production
cube-boundary multiplicity.  The off-cube completion no longer starts from a
full background that would later discard twelve cube coordinates.  Instead,
it explicitly filters the complete slab-link list to the complement of the
twelve cube links, enumerates only those production fibers, and combines them
piecewise with the certified root-first cube data.  Cube and off-cube lookup
laws prove that every coordinate comes from exactly its intended source.

The remaining immediate bridge is to enumerate the Cartesian product of the
first-stretched list and this off-cube list injectively, partition the result
by common lowered target, root, and peel size, and sum those fibers.  The
Cartesian family itself is now explicit, duplicate-free, and has exact length

```text
first-stretched cube count * off-cube production multiplicity.
```

Every member canonically compiles to a complete presented source and its raw
auxiliary payload.  That compiler is now proved injective on the enumerated
family: equality on cube coordinates recovers the certified classifier input,
while equality off the cube reconstructs the complement assignment.  The
resulting physical/raw source list remains duplicate-free.  The active edge is
now to attach each member's deterministic lowered target, root, and peel size,
then partition this list into the fixed fibers consumed by the existing
`(8/25)^n` contraction theorem.  That attachment is now explicit and
duplicate-free: every entry retains its upstream source as an injective key,
projects the existing flat inverse record, and has peel size at least two.
Reapplying the older defensive cube override is also proved to leave the raw
complete source unchanged.  The live edge is the actual dependent target/root/
size partition and its fixed-fiber witness compiler.  The lossless decidable
partition key is now proved: it records the root, size, lowered physical word,
every local face-order word, and every local lowered-auxiliary word.  Equal
keys reconstruct literal equality of the lowered physical function and
heterogeneous equality of the dependent presented assignment.  The live edge
was therefore the realized representative fibers and their
`PresentedAdaptiveRemovalWitness` compiler.  That compiler is now checked as
well: each realized fiber is duplicate-free, has size at most
`10240000^n`, and its complete anchor weight is at most `(8/25)^n` times
the representative's lowered-target weight.  The live edge is the exact
representative-fiber Fubini sum followed by contraction of the resulting
distinct lowered-target weights against the pure mate product.  The exact
Fubini step is now checked and the full first-stretched source weight is
bounded by the strict-rate-weighted sum of its realized lowered targets.  The
live mathematical edge is the target-side congestion/injection that contracts
this distinct target sum against the pure mate product.
The theorem does **not** yet give a physical transfer minorization, a
posterior-variance fraction, an OS transfer gap, or a continuum result.

Earlier in the same causal chain, the Casimir/heat payment for an inward mate
at the physical nome `w = 1/2` established that a parity-uniform six-face cube
has a non-vacuum even source heat product at most `64` times its inward mate's
heat product, while an odd source is at most `1/4096` times its inward mate.

These are
`sixHeatProduct_evenInwardMate_le_sixtyFour` and
`sixHeatProduct_oddInwardMate_le_oneOver4096` in
[`BF4PhysicalVacuumSectorInwardMateHeatBound.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateHeatBound.lean).

The local SU(2) fusion debt is now also exact and kernel-checked. Lowering two
positive incident labels preserves their Clebsch--Gordan ladder except for
its stretched top channel. At the production link-multiplicity level, every
source path is bounded by the inward-mate path count plus one explicit
stretched-channel continuation. See
[`BF4PhysicalVacuumSectorInwardMateFusionSupport.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionSupport.lean).

The local comparison now also transports across arbitrary physical incident
spin orderings, provided the two geometric permutation witnesses are supplied.
This is
`explicitValenceMultiplicity_physical_inwardMate_of_permutations` in
[`BF4PhysicalVacuumSectorInwardMateFusionReordering.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionReordering.lean).
The generic finite-box incidence step is now closed as well:
`incidentPhysicalSpinsTwoFacePermutations` constructively moves any two
distinct incident plaquette IDs to the front of the source and mate words with
one shared residual word, and
`incidentPhysicalSpinsTwoFaceInwardMateLeAddStretched` immediately feeds
those witnesses into the production multiplicity inequality. See
[`BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean).

The cube-specific geometry is now closed too.  The twelve-entry production
table is compiled into exact corrected-slab numerical incidence: at every
cube-boundary link the two recorded selected face IDs occur, are distinct, and
exhaust the selected six-face support.  Thus the global six-face mate restricts
to the proved local two-face mate, yielding the actual corrected-slab
multiplicity bound with one explicit stretched continuation.  See
[`BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean).

Those twelve local certificates now form one explicit global debt profile.
Lean proves that every link outside the cube boundary is unchanged and that
the boundary products obey
`product(source) <= product(mate + stretchedDebt)`.  See
[`BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean).
This deliberately does not absorb the debts independently.

That finite product is now expanded exactly over Boolean words aligned with
the twelve attached links.  The all-target word is the pure mate product; all
nonempty stretched words sum to the named
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean).

Every summand in that remainder now has a canonical constructive root.  Lean
computes the first stretched choice, proves its index lies in the attached
twelve-link incidence list, returns the corresponding geometric incidence as
data, and proves the root bit is `true`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean).

The natural-number remainder is no longer opaque cardinality either.  Each
stretched local factor is the length of a literal accepted SU(2) auxiliary
fiber; Boolean words choose target or stretched fibers link by link; and the
flattened finite carrier has length exactly
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean).

The raw expansion has now been sharpened at its mathematical source.  The
SU(2) ladder proof shows that if either changed face label is zero, every
source channel survives and the additive debt is exactly zero.  The active
remainder therefore retains a stretched fiber only when both incident cube
faces are positive; it again has an exact finite-carrier cardinality theorem.
See
[`BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean).

Every member of that active carrier now retains its assignment-membership
certificate, its first active position, the actual auxiliary labelling stored
there, and proofs that both incident physical face labels are positive.  Thus
the root required by the strand compiler is Type-level data rather than a
propositionally extracted witness.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean).
The two positive root faces are now also realized as distinct literal
slot-zero strand-copy vertices on their common recorded link; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean).
For the stretched SU(2) vertex itself, the canonical resolution is now exact:
no strand joins the two input legs, while their strands occupy two disjoint
segments of the summed internal leg.  See
[`SU2StretchedTrivalentStrandContinuation.lean`](lean/YMGap/Continuum/SU2StretchedTrivalentStrandContinuation.lean).
The cube-root specialization now sends both literal face copies through those
canonical mates to distinct summed-channel ports and certifies the stored
auxiliary on the exact collapsed word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean).
The resulting collapsed auxiliary can now be lifted constructively back across
the stretched vertex.  For every source word of length at most six,
`stretchedFusionWitnessLift_mem` inserts the forced first channel, shifts the
remaining internal coordinates, and proves that the resulting auxiliary is
accepted on the ordered source word; see
[`SU2StretchedFusionWitnessLift.lean`](lean/YMGap/Continuum/SU2StretchedFusionWitnessLift.lean).
That compiler is now specialized to every active cube-root carrier:
`rootSourceAuxiliary_mem_orderedSourceSpins` provides the literal accepted
source auxiliary, and `rootProductionSpins_perm_orderedSourceSpins` retains
the exact permutation from the physical production order; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean).
The corresponding root-first order of literal plaquette IDs is now retained
as data as well.  It is duplicate-free, permutes the production incidence
list, and maps exactly to the accepted ordered spin word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean).
The canonical ordered-chain termination and fixed-point-free terminal mate now
work for any such certified face presentation.  The generic compiler reindexes
every terminal to a literal incident plaquette and proves its mate lies on a
different face; see
[`CompactDualSlabOrderedLinkPhysicalStrandPairing.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkPhysicalStrandPairing.lean).
The one-element physical half-edge fiber now gives a constructive terminal at
any specified face position and strand slot.  At the active cube root this
produces two literal slot-zero terminals whose occurrences are exactly the two
previously named positive root copies; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean).
Those selected terminals are now identified as full dependent ports at the
first canonical trivalent vertex, not merely by face ID.  The first channel is
proved to carry exactly the SU(2) stretched spin sum; its strand counts are
`ab = 0`, `bc = right`, and `ca = left`.  Consequently the two selected local
mates both land on the third leg but in distinct slots (`right` and `0`).  See
[`CanonicalLinkFirstVertexPorts.lean`](lean/YMGap/Continuum/CanonicalLinkFirstVertexPorts.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean).
The outgoing channel is now constructively classified as physical at valence
three or genuinely internal at valence four through six.  Both root strands
are fed to the exact stop-or-same-slot-advance compiler; their complete paths
to physical endpoints are retained as data, and those endpoints are proved
distinct.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean).
Those endpoint terminals are now reindexed to the presentation-independent
global `(faceId, slot)` carrier.  Each root copy is proved to be the exact
source of a global strand edge, and the two retained path endpoints remain
distinct as literal global copies.  See
[`CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean).
The global edge compiler now also accepts a different certified face order and
fusion witness at each link.  It enumerates every local physical terminal,
forgets every endpoint to the common global carrier, and concatenates the
result into one heterogeneous edge list.  Replacing the root entry of any
explicit complete background assignment by the actual root-first witness puts
both retained root edges literally in that list.  See
[`CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean).
An ordinary accepted source assignment now embeds canonically into this
presented interface.  More generally, a rooted component of any heterogeneous
presented graph pulls back to exact partner closure at each ordered link.  For
the active debt root, Lean constructs the two rooted components generated by
the left and right stretched-channel strands and takes their Boolean union.
That union contains both literal root copies and is closed across every edge,
without asserting that the two components coincide.  See
[`CompactDualSlabPresentedFaceStrandSeedComponent.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandSeedComponent.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean).
That ordered partner closure now compiles all the way through the existing
Kirchhoff strand-removal theorem.  At every link, the canonical edge drop is
proved equal to the global selected-copy count on the literal face occupying
that ordered position.  Consequently the two-root union constructs one common
lowered physical field and a complete accepted heterogeneous auxiliary
assignment over it; both distinct root-face labels decrease strictly.  See
[`CompactDualSlabPresentedFaceStrandComponentDrop.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDrop.lean).

The source-side local decomposition is now witness-faithful rather than only
an inequality of natural-number dimensions.  For any root-first ordered word
through valence six, Lean reads the actual first SU(2) channel of an accepted
source witness.  If it survives the inward mate, the same auxiliary is
accepted in the mate fiber.  Otherwise Lean deletes the unique stretched
first vertex, retains the resulting accepted collapsed witness and both
positive-spin proofs, and proves that reinsertion recovers the source exactly.
The resulting `inwardMateFusionWitnessPartition` is injective.  See
[`SU2InwardMateFusionWitnessPartition.lean`](lean/YMGap/Continuum/SU2InwardMateFusionWitnessPartition.lean).

That abstract partition is now specialized to every literal cube-boundary
link.  One certified face order exposes the two incident cube faces first; its
residual literal faces are proved unchanged by the global six-face mate.  Lean
therefore maps the actual ordered source fiber injectively into either the
actual ordered mated fiber or an accepted collapsed stretched witness, and it
packages every surviving target as a presented mated-link witness.  Exact
recovery still returns the original auxiliary.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean).

The dependent twelve-link product is now constructed too.  A complete source
is a function whose coordinate type is the accepted root-first fiber of that
literal incidence.  Lean classifies all coordinates, recovers all original
auxiliaries pointwise, proves the complete classifier injective, and packages
the original tuple as one accepted presented cube family.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean).

That product now has a constructive global dichotomy.  A structural scan either
returns all twelve accepted mated witnesses or the first stretched incidence
with its actual positive two-face debt witness.  Forgetting the branch
reconstructs the complete classified assignment, so the source-to-branch map
remains injective.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean).

The classifier's source-image invariant is now explicit rather than implicit
in its construction.  Every local output retains proof that its exact decoder
is accepted in the source fiber; the dependent product reconstructs a common
presented cube source.  The strengthened first-stretched branch keeps this
entire certified product and proves that its root output is exactly the stored
debt witness.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean).

The certified cube family now extends to a complete slab presentation whenever
an explicit accepted full-slab background for the same physical field is
supplied.  A constructive finite lookup finds the unique recorded incidence
of each cube link, overwrites exactly those twelve entries with the certified
source witnesses, and leaves all off-cube entries unchanged.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean).

At the certified first-stretched incidence, the retained positivity data now
constructs slot-zero terminals on the first two faces of that same root-first
witness.  Their terminal-pair edges have exactly the two literal cube-face
copies as sources, and both edges are proved members of the single completed
presented slab graph.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean).

Those two edges now seed a complete accepted peel.  Lean takes the Boolean
union of their constructive rooted components, proves it closed under the
actual partner at every independently presented link, and compiles the common
selection to a lowered physical field plus a complete accepted presented
assignment.  Both root-face labels decrease strictly; no connectivity claim
between the two roots is assumed.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean).

That accepted drop now has an exact physical serialization and pointwise
weight payment.  Every endpoint of the heterogeneous presented graph is
proved to lie on a displayed physical face; the selected-copy multiplicities
form a legal repeated-face peel with an exact physical left inverse; and the
certified two-root word has length at least two.  At the production anchor,
the actual completed source entry is bounded by one
`anchorFaceCoefficient` factor for every word letter.  See
[`CompactDualSlabPresentedFaceStrandComponentWeight.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentWeight.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean).

The auxiliary drop is now serialized as well.  The lowered target retains each
certified face order, so the finite code pays no extra order coordinate.  Its
physical word plus link-local internal-drop words reconstruct the complete
source `(physical, raw auxiliary)` entry exactly, and every local word has
width at most three independently of cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDropCode.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean).

Zero internal-drop rows can now be erased and recovered exactly.  Every
retained row is charged injectively to a selected physical strand copy and one
of its four boundary links, so there are at most `4 * peelSize` nonzero rows.
More sharply, the complete volume-indexed row table inhabits a link-adaptive
Cartesian carrier: local conservation bounds every entry by the selected
physical mass incident on that link, all widths are at most three, and the
total incident mass is exactly `4 * peelSize`.  Consequently the auxiliary
carrier has size at most `4096^peelSize`, uniformly in slab volume and spin
cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean),
[`CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean),
and
[`CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean).

The physical geometry, multiplicity, and auxiliary inverse are now joined in
one adaptive code.  Its fixed-target injectivity and weighted fiber contraction
are checked, including component overlap without double counting.  What is
still open is the global regrouping: construct the actual finite enumeration
of certified first-stretched routes, partition it by the common lowered target,
root, and peel size, and sum those fibers into a cutoff-independent multiple
of the pure mate product.  The older coarse mixed target/debt Cartesian carrier
still does not itself provide a common accepted source presentation and is not
used as one.  Closing this regrouping would feed a genuine physical
mate-transition floor and then a rooted-subtree Hardy--Poincare or posterior
conditional-variance estimate.

An earlier plan tried to bound the whole new-cutoff self-return trace by a
small constant. Exact exploratory computation found that plan false already
at cutoff four: a single state has self-return about `0.71428`, and six
symmetric copies make the positive trace exceed four. This computation is a
route-selection diagnostic only; no floating-point value enters a theorem.

For the detailed live dependency map, see [`work_plan.md`](work_plan.md).
For the source-based group audit, see
[`audits/AUDIT-GROUP-DEPENDENCE.md`](audits/AUDIT-GROUP-DEPENDENCE.md). That
audit found that the strand machinery is hard-coded to the SU(2)
Clebsch--Gordan rule and that no source dependency bridge currently connects
the component chain to the generic `singleStep` obligation. Accordingly, this
README makes no claim that group dependence is closed.

## Trust and constructivity rules

The Lean development is intentionally stricter than ordinary Lean code:

- no Mathlib dependencies;
- no `Classical.choice`, excluded-middle shortcut, or `native_decide` in
  load-bearing proofs;
- constructive reals carry explicit Cauchy moduli;
- witness-bearing existence claims use data-bearing structures or sigma
  types;
- load-bearing declarations are inspected with `#print axioms`; the permitted
  project gate is `propext` and `Quot.sound` only;
- unproved obligations and conditional interfaces are recorded in
  [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md), rather than being described
  as completed physics.

Python and Rust may perform expensive searches or generate compact exact
certificates. They are **untrusted producers**: Lean must parse the resulting
finite data and independently check every semantic condition and inequality.

Read [`lean/AGENTS.md`](lean/AGENTS.md) before modifying any Lean file.

## Repository guide

| Path | Role |
| --- | --- |
| [`lean/`](lean/) | Lean 4 formalization and constructivity/axiom gates |
| [`lean/YMGap.lean`](lean/YMGap.lean) | Root import aggregator |
| [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md) | Open obligations and milestone evidence |
| [`work_plan.md`](work_plan.md) | Current causal roadmap and status |
| [`docs/outline.md`](docs/outline.md) | Technical specification |
| [`docs/context.md`](docs/context.md) | Mathematical motivation and constructive rationale |
| [`audits/`](audits/) | Read-only source audits of important claim boundaries |
| [`computations/`](computations/) | Untrusted Python/Rust exploration and certificate generation |
| [`tests/`](tests/) | Tests for computational tooling |
| [`formal/`](formal/) | Human-readable LaTeX development |
| [`visualizations/`](visualizations/) | Generated diagrams and exploratory figures |

## Building safely

Lean is pinned by [`lean/lean-toolchain`](lean/lean-toolchain). Builds must use
the monitored launcher; bare `lake build` and bare `lake env lean` bypass the
repository's crash safeguards.

```bash
# Full monitored Lean build
make lean-build

# Narrow target (preferred while developing)
python3 scripts/safe_lean_build.py --jobs 1 -- +YMGap.Continuum.ModuleName:olean

# Check one source and emit only its importable olean (parent directory exists)
python3 scripts/safe_lean_build.py --check lean/YMGap/Continuum/ModuleName.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/ModuleName.olean

# Monitored axiom audit
make lean-audit
```

See [`docs/lean-build-safety.md`](docs/lean-build-safety.md) for memory and
worker limits.

The auxiliary Python tools require Python 3.11 or newer:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
make test
make lint
```

Other common targets are `make figures` and `make paper` (the latter requires
a working LaTeX installation with `latexmk`).

## How to evaluate a claim in this repository

Check all four of the following:

1. the exact theorem statement and its parameter range;
2. its printed axiom dependencies;
3. whether its hypotheses have concrete inhabitants, rather than only a
   conditional compiler;
4. whether the next bridge in [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md)
   is still open.

A finite-cutoff theorem, a fixed-coupling clustering estimate, or a compiler
of the form “if certificate `C`, then gap” is valuable progress, but none is
by itself a continuum Yang--Mills mass-gap theorem.
