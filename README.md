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
  -> reflection positivity and finite OS Gram                       [PROVED]
  -> concrete finite physical vacuum-sector transfer                [PARTIAL]
  -> cutoff-uniform non-abelian transition / Poincare estimate       [ACTIVE]
  -> completed physical vacuum-complement gap                        [OPEN]
  -> thermodynamic limit with uniform estimates                      [OPEN]
  -> continuum limit and OS/Wightman reconstruction                  [OPEN]
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

The present bottleneck is a cutoff-uniform gap for the **actual physical SU(2)
BF4 vacuum-sector transfer**, not an abstract spectral theorem.

The most recent proved step is the Casimir/heat payment for an inward mate at
the physical nome `w = 1/2`. For a parity-uniform six-face cube, Lean proves:

- a non-vacuum even source heat product is at most `64` times its inward
  mate's heat product;
- an odd source heat product is at most `1/4096` times its inward mate's heat
  product.

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

The next causal step is to adapt that certified root to the exact two-root
component peel, extend the cube family with accepted off-cube
witnesses into one complete slab presentation, and serialize the resulting
drop into a multiplicity-faithful peel/weight certificate.  The older coarse mixed
target/debt Cartesian carrier still does not itself provide that source
background and is not used as one.  The resulting source-partition sum must
ultimately be bounded by a cutoff-independent multiple of the pure mate
product.
This avoids mistaking a change of fusion basis for a pointwise permutation of
basis witnesses.  The resulting fixed-boundary intertwiner comparison would
feed a genuine physical mate-transition floor and then a rooted-subtree
Hardy--Poincare or posterior conditional-variance estimate.

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
