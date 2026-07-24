# Compact-dual spacing-uniform gap closure spine

## Outcome

The compact-dual program is on a logically complete route to spacing-uniform
continuum gap survival, but it has not yet crossed the first analytic gate.
The exact sign work establishes that the dual coordinate remains viable.  It
does not establish the physical block map or any uniform estimate.

`computations/compact_dual_continuum_route.py` now makes the whole dependency
chain executable and fail-closed.  Its current-route constructor contains the
pinned finite sign evidence and no analytic witness, so its first open gate is
exactly:

```text
CD-2 physical block and overlap remainder
```

No census count, nonnegative finite Gram, or local sign law can change that
answer.  A gate closes only when its physical witness data are present and
compose with all earlier gates.

## Dependency-complete route

| Gate | Required constructive output | What cannot substitute for it |
|---|---|---|
| CD-2 | Source-indexed positive row-normalized kernel on the actual fine/coarse physical labellings; exact pushforward; complete reflected channels; computed overlap remainder; reflection intertwining. Zero total mass then follows automatically from finite normalization. | A positive scalar channel, a detached stochastic matrix, or entrywise fixed-channel positivity |
| CD-3 | Norm of that exact CD-2 remainder; `c(1-w)^2`-type cap; cutoff-independent constant; volume-uniform bound; explicit representation-tail modulus | Any norm of a surrogate remainder or a constant growing with cutoff/volume |
| CD-4 / RG-I7 | A pinned self-mapping physical coefficient ball; reflection-cone preservation; either `q<1` or an explicit accumulated contraction envelope | Positivity, compactness, or an unquantified stable-manifold statement |
| CD-5 / RG-I8 | Computed scale and computed physical state entering exactly the CD-4 enclosure | Eventuality, subsequence compactness, or entry of an unpinned trajectory |
| RG-I9 | Separate summable block-remainder, dynamic, and interface ledgers with exact tail moduli and a physical comparison theorem | Per-scale convergence without a summable modulus |
| Continuum survival | Physical Wilson/gap readout; volume-uniform modulus; spacing conversion; OS binding; a strict exact floor after every certified loss | A fixed-spacing gap or a limit statement with no quantitative positive margin |

The final acceptance inequality is explicit.  If `m_latt` is the pinned
fixed-spacing gap, the route returns a continuum certificate only when

\[
  m_{\rm latt}
  - E_{\rm block}
  - E_{\rm dyn}
  - E_{\rm int}
  - E_{\rm vol}
  - E_{\rm spacing}
  > 0,
\]

where every `E` is computed from a constructive geometric tail modulus at its
certified start scale.  Equality to zero fails the gate.

## Exact current position

The finite evidence object records:

- 100 complete four-cube binary-pair orbits;
- 65 complete six-valent pair orbits;
- 14 exact first-branching nonzero-defect channel orbits;
- nonnegativity of every tested complete sum;
- the combined cycle/branch local sign law.

Its `analytic_gates_discharged` value is definitionally zero.  This is the
program-distance firewall in executable form.

The current missing CD-2 fields are the same ones isolated by the exact
manifest audit:

1. pin the wheel/rim geometry to
   `CompactDualPhysicalData.faceEdges` and `enumeratedLinks`;
2. prove the exact-Haar integrator equals the corresponding finite fiber sum
   of `CompactDualPhysicalData.physicalTerm`;
3. pin `s` to the physical rational coupling and its `4*C₂` exponent;
4. map every reflected boundary channel, not just the positive rim channel;
5. construct the physical source-dependent kernel;
6. compute and retain the overlap remainder.

Only after these six items may `SpinFoamRPBlockRemainder` be inhabited.  The
next work step is therefore the physical geometry/integrator semantic bridge,
not a larger sign census.

### First semantic slice closed

`computations/dual_positivity_coordinate_bridge.py` now closes the exact
coupling/cutoff coordinate slice of this list.  For every one of the twelve
unit-rim sectors it proves computationally that

\[
  W(j;m)\prod_i
    \left[(j_i+1)s^{j_i(j_i+2)}\right]
  =
  c_{j,m}s^{\sum_i j_i(j_i+2)},
\]

and it verifies that the sector ledger, compressed four-monomial activity,
and independent exact-Haar contraction agree at an arbitrary pinned rational
coupling.  It also catches a support distinction that matters physically:
cutoff one supports the fixed rim labels, but cutoff two is required for the
complete induced page-spin sum.

The executable semantic frontier therefore closes manifest integrity,
coupling coordinate, boundary support, and page-cutoff completeness.  Its
first open field remains `geometry_pinned`, followed by integrator semantics,
complete reflected channels, the physical kernel, and the overlap remainder.
The parent CD-2 gate remains open.

### Physical four-page carrier pinned; full wheel geometry still open

`computations/dual_positivity_geometry_bridge.py` corrects a dimensional
ambiguity in the phrase “four-page interior-link wheel.”  A physical interior
link in four dimensions has six incident plaquettes, not four.  At the first
interior direction-zero link of the production extent-two box, the exact
physical face identifiers are

```text
(66, 79, 86, 90, 91, 92).
```

The `01` and `02` transverse planes give the four active pages
`(66,79,90,91)`; the `03` pair `(86,92)` must be in the vacuum
representation.  Their local positions in the production
`incidentPlaqIds` order are active `(0,1,3,4)` and vacuum `(2,5)`.
Exhaustive exact fusion checks through doubled spin three verify that the
six-valent invariant with those two vacuum labels equals the corresponding
four-valent invariant.

This pins the wheel's physical page carrier and removes a possible detached
four-valent surrogate.  It does **not** yet embed the four cyclic rim words
`X_i X_(i+1)^-1` into the reflected boundary packet or pin their half-time
reflection orientation.  The geometry frontier therefore stops at
`cyclic_rim_words_embedded`; the aggregate `geometry_pinned` field remains
false.

### Boundary carrier must be upgraded before the rim map

The rim audit also found that the current CD-1 `DualBoundaryState` has arity
one, whereas the wheel requires four ordered rim slots.  The coincident unit
labels `(1,1,1,1)` do not remove this provenance: the all-label squared-norm
uses the cyclic neighbors `m_(i-1),m_i` separately at every page.

`computations/dual_boundary_carrier_gap.py` now pins the abstract four-slot
cyclic carrier and proves that the one-interface carrier is insufficient.
The next physical field is `physical_half_time_slot_ids_pinned`, followed by
the reflection permutation and intertwiner basis.  The required Lean carrier
upgrade is specified in
`docs/compact-dual-boundary-carrier-gap-2026-07-23.md`.  This upgrade is a
prerequisite to the full `geometry_pinned` and integrator-semantic fields,
not a new analytic gate.

### Reflection-closed physical datum correction

The geometry audit found a stricter obstruction.  The legacy
`CompactDualPhysicalData.physicalTerm` uses `boxPlaquettes n`, and the Lean
theorems `not_physicalFaceReflectionClosed` and
`no_physicalFaceReflectionReindex` prove that this face list is not closed
under physical half-time reflection at any nonzero extent.  Consequently the
legacy term cannot be the direct carrier of an RP-preserving CD-2 block.

`computations/dual_half_time_reflection_route.py` mirrors the corrected
boundary-complete slab, constructs its exact face reflection involution, and
pins the reflected partner of the central four-active/two-temporal page
carrier.  A deeper audit found that the production Lean development already
contains the complete corrected-slab physical term and partition, their
reflection invariance, the weighted-Gram identity, exact Cartesian coverage,
and nonnegativity of the independently defined full physical reflection
quadratic.

`CompactDualSlabPhysicalData.lean` packages this as the corrected CD-2
physical datum.  The finite reflection route is therefore closed without a
legacy-box bridge.  The immediate open object is the fine-to-coarse physical
block kernel and its exact retained remainder; `reflection_intertwines` must
be proved for that kernel, not re-proved for the already closed single-scale
measure.

`CompactDualFiniteBlockRemainder.lean` now closes the finite algebra around
that missing kernel.  The corrected source and target laws are normalized;
for every source-dependent, positive, row-normalized,
reflection-intertwining slab kernel, the retained pushforward remainder is
defined and its total mass is proved exactly zero.  Its universal
cutoff/volume-independent `L¹` bound is `2`.  This removes zero-mass
cancellation as an independent obligation, but the bound `2` has no vanishing
RG factor and therefore does not close CD-3.  The executable frontier in
`computations/compact_dual_cd2_frontier.py` also records the first exact
overlap correction.  `Z4AdjacentCubeCancellationActivity.lean` proves that
the closed symmetric-difference carrier of two adjacent cubes has ten faces,
incidence two at every touched link, and exact activity
`coeffW(w,1)^10`; equivalently the product of the two independent cube
powers is `coeffW(w,1)^2` times the glued activity.  This converts the
qualitative positive adjacent carrier into a quantitative gluing law.

The first open subgate remains genuinely overlapping shared-link *kernel*
assembly: the theorem does not yet provide a source-indexed joint
normalization, all-cutoff recoupling, or a physical Gibbs pushforward.
Those precede the all-cutoff whole-slab kernel and physical pushforward
identification.

## What this advances

This gate does not prove a new analytic estimate.  It closes a serious
program-control ambiguity: all remaining work now has a typed quantitative
consumer, and the present exact evidence is unable by construction to
overstate its distance to the continuum theorem.  It also fixes the order of
attack.  CD-3 cannot be explored honestly until CD-2 returns the actual
remainder; RG-I7 cannot be claimed until that same norm is used; and the
continuum floor cannot be returned unless every infinite error ledger is
strictly paid from the physical gap anchor.
