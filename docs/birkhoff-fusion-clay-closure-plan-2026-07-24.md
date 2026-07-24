# Birkhoff–fusion route to Clay closure

Date: 2026-07-24

## Terminal theorem

The program is complete only when it constructs, for every compact simple
gauge group \(G\), one nontrivial quantum Yang–Mills theory on
\(\mathbb R^4\), verifies axioms at least as strong as
Osterwalder–Schrader/Wightman for that same theory, and proves that its
Hamiltonian has no spectrum in \((0,\Delta_G)\) for explicit
\(\Delta_G>0\).

A lattice contraction, a continuum correlation rate, or an abstract
Hamiltonian model is not by itself the terminal theorem.

## Simplification-ledger correction

The dependency and counterfactual audit in
`docs/the-simplification-ledger-2026-07-24.md` changes the execution order,
but not the terminal theorem.  The highest-leverage work is no longer
“enlarge the multiplicity census” in isolation.  It is to preserve three
pieces of data that earlier reductions discarded:

1. the positive physical Haar boundary tensor before it is split into signed
   Peter--Weyl channels;
2. the actual fusion-tree/intertwiner maps, phases, and \(F/R\) symbols before
   they are decategorified to multiplicity vectors;
3. one exact plaquette-coupled Gibbs object from fine-to-coarse pushforward
   through projective contraction, continuum construction, and OS spectral
   identification.

The corrected contraction target also remains scale-dependent:
\(q_a=1-ma+o(a)\), grouped over a fixed physical distance.  A microscopic
spacing-independent \(q<1\) is not the target.

These become **data-preservation invariants** for every gate:

- **P1 — physical object:** every estimate names the exact Haar/Gibbs object
  on which it acts;
- **P2 — coherent boundary data:** no carrier closure or block-map claim may
  retain only masks or multiplicities when the missing map depends on
  intertwiner bases or phases;
- **P3 — complete physical grouping:** signs are adjudicated only after all
  channels with their actual heat weights have been grouped;
- **P4 — shared-object transport:** a witness on an abstract polymer gas,
  finite transfer matrix, single-edge character model, or finite fusion
  category is not silently substituted for the Yang--Mills object;
- **P5 — physical-distance uniformity:** cutoff-uniform means a grouped
  exponent over fixed physical length, with located scale and volume moduli;
- **P6 — all-groups honesty:** SU(2) may be used as a pilot, but not as the
  all-groups theorem until monotonicity is proved on the physical carrier.

## Critical path

| Gate | Deliverable | Exit certificate | Hard failure signal |
|---|---|---|---|
| BF1. Physical carrier | Finite **intertwiner-resolved boundary-tensor basis** on corrected slabs | Direct unfused Haar integral equals the coherent fusion-tree contraction, independently of basis; complete heat activity is nonnegative | A negative complete physical heat family, basis dependence, or failure of exact resummation |
| BF2. Dual positivity | General theorem (DP), a reflected-Gram/SOS theorem, or a precisely enlarged positive carrier | Nonnegative activity for every complete physical generator at every cutoff and coupling | Exact counterexample surviving the complete physical sum |
| BF3. Physical block map | Exact fine-to-coarse pushforward of the plaquette-coupled Haar Gibbs law on the BF2 carrier | Mass preservation, reflection compatibility, joint coarse-intertwiner transport, and an explicit remainder identity | Coarse data leave the carrier or require unrecorded signed/coherent cancellation |
| BF4. Projective geometry | Birkhoff--Hopf estimate on the reflected physical block kernel over a fixed physical distance | Exact cross-ratio/diameter bound with \(q_a=1-ma+o(a)\) and grouped rate \(<1\), uniform in volume and cutoff | Infinite grouped diameter or no positive physical decay exponent |
| BF5. Graded stability | Perturbative comparison for branched/intersection sectors | Explicit \(C\kappa^{64}\) bound and summable grouped distortion | Graded contribution is unsummable or changes the cone order |
| BF6. RG-I7–I9 | Contraction, landing, and summable distortion on the **same exact Yang--Mills Gibbs trajectory** | One witness-bearing RG certificate with physical-distance, volume, and cutoff moduli | Any certificate applies only to a surrogate law, a fiducial constant, or a fixed cutoff |
| BF7. Continuum theory | Infinite-volume and \(a\to0\) Schwinger functional/measure obtained from the BF6 trajectory | Located convergence/tightness moduli, sigma-additive realization or adequate functional construction, non-Gaussianity, locality, covariance, and AF normalization | Limit is trivial, Gaussian, nonunique, non-covariant, or detached from the RG trajectory |
| BF8. OS reconstruction and gap | OS axioms and reconstruction on the **same BF7 object** | Physical Hilbert space, vacuum, Hamiltonian, and \(\operatorname{spec}H\cap(0,\Delta)=\varnothing\) derived from its grouped decay | Correlation decay cannot be identified with the reconstructed Hamiltonian |
| BF9. All compact simple groups | Per-group physical carriers and estimates, or a uniform lift proved on those carriers | Concrete per-group representation/heat-kernel/intertwiner data plus a proved physical worst-case reduction | An uninhabited representation-data interface or scalar-only monotonicity remains |
| BF10. Clay assembly | Shared-object final theorem | `ClayTargetPinned`-strength inhabitant and independent assumption audit | Any clause refers to a different or surrogate object |

## BF1: current tranche

The carrier candidate is a multiset of closed labelled surface strands.
Overlap faces retain all irreducible channels and all fusion-path
multiplicities. The implementation must satisfy four checks:

1. every strand has zero mod-two edge boundary;
2. union stays in the carrier;
3. direct unfused Haar integration equals the complete channel ledger;
4. the label-dependent heat-weighted activity is tested exactly for sign.

Current exact certificate:

- corrected slab: extent one, 72 faces, 116 edges;
- complete family: two intersecting closed fundamental surfaces;
- fusion ledger: 16 channels, including four negative fixed channels;
- direct and resummed amplitude: \(31/331776\);
- physical heat activity:
  \(w^{48}(1+12w^8+6w^{16}+12w^{24}+w^{32})>0\).

The first bounded-orbit campaign now extends this from one family to every
intersecting pair on the unit four-cube:

- 7,997 raw pairs in 100 symmetry orbits;
- all 100 physical heat polynomials coefficientwise positive;
- six orbits contain negative fixed-face channels;
- 77 distinct heat polynomials, with minimum positive coefficient \(1/6561\).
- all 127 diagonal duplicate-surface families are structurally positive:
  \(A_{S,S}(w)=\prod_i(1+3^{\chi_i}w^{8F_i})\).

The finite \(SU(2)_k\) central-monad campaign is also adjudicated. Fixed
low-spin fusion, the degree-zero adjunction, and pure-fusion module transport
stabilize. The full central vacuum carrier grows with rank \(k+1\), physical
heat weighting is not an ordinary module morphism, and multiplicity vectors
do not retain the counit/multiplication maps on intertwiner spaces. Central
induction is therefore a coherence envelope, not the positive RG cone.

BF1 is not closed by one example.  The simplification audit changes the next
BF1 work units to:

1. add embedded fusion trees, orthonormal intertwiner indices, orientations,
   and exact phase data to the carrier **before** enlarging the census;
2. construct the first three-strand family where fusion-path multiplicity is
   nontrivial, then compare direct Haar, coherent recoupling, and the complete
   physical heat polynomial;
3. test reflected Gram/SOS positivity on that complete family;
4. carry the same boundary data through one exact corrected-slab,
   unnormalized Haar pushforward;
5. only then enlarge to all three-strand orbits, higher labels, and larger
   corrected slabs;
6. construct the heat-twisted central-module comparison as an explanatory
   coherence envelope, not as the carrier itself;
7. state the minimal general positivity lemma surviving that falsification
   campaign.

## Closed milestone — BF1.5: intertwiner-resolved three-strand pushforward seed

**Closed 2026-07-24 by the negative route.**  The minimal sector has 96
explicit fusion paths over 64 output channels.  Direct Haar, left/right
coherent path sums, signed Racah transport, and the positive heat activity
all agree exactly.  The path-to-channel unnormalized Haar pushforward is
explicit.  However, the one-sided reflected Gram form on the closed
full-slab surface generators has leading \(3\times3\) principal minor
\(-1/65536\).  Because those generators cross the reflection plane, this is
not an OS-positivity counterexample; it proves that the proposed
closed-surface carrier is not the positive-half reflection cone.  See
`notes/bf1-5-three-strand-pushforward.md`.

This is the next milestone to execute.

### Goal

Construct one minimal, genuinely four-dimensional three-strand corrected-slab
sector in which fusion-path multiplicity occurs, retain its full boundary
intertwiner data, and compute both its complete physical heat activity and
one exact unnormalized fine-to-coarse Haar pushforward.

This milestone deliberately bridges BF1 and BF3.  A larger
multiplicity-only census would not test the data that the block map needs.

### Required mathematical object

For every boundary state in the selected sector, record:

- the closed surface-strand multiset and oriented face labels;
- a canonical fusion tree on each multiply occupied face;
- an orthonormal basis index for every non-bivalent edge invariant space;
- exact signed/unitary \(F/R\)-symbol data for changes of tree or ordering;
- the dimension and Casimir heat exponent of every physical output channel;
- the reflected partner needed to form the candidate Gram pairing.

The multiplicity ledger is a derived view of this object, never its source of
truth.

### Work units

1. **Carrier model.** Implement the intertwiner-resolved boundary-state type
   and deterministic canonicalization under slab symmetries.
2. **Minimal physical sector.** Locate and pin the smallest three closed
   fundamental surfaces whose overlap produces nontrivial fusion-path
   multiplicity and genuinely four-dimensional intersection data.
3. **Three-way equality.** Compute:
   - the direct unfused quaternion-Haar network;
   - the coherent fusion-tree/\(F\)-symbol contraction;
   - the complete heat-weighted physical activity.
   Prove the first two agree and that the third resums every channel.
4. **Basis/coherence audit.** Change the internal fusion tree and verify that
   the complete activity is unchanged with the exact signed
   Biedenharn--Elliott/Racah transport.
5. **Reflected positivity test.** Build the finite reflected Gram matrix for
   the sector and either give an exact PSD/SOS factorization or isolate its
   first exact negative principal minor.
6. **Pushforward seed.** Integrate every fine internal link for one selected
   boundary-to-coarse-boundary block, returning the unnormalized kernel,
   total mass, coarse intertwiner map, and literal residual outside the
   selected carrier.
7. **Regression and prose certificate.** Pin all exact values and record
   precisely which clauses are proved, falsified, or still open.

### Exit certificate

BF1.5 closes only when one of the following mutually decisive certificates
exists.

**Positive exit**

- direct Haar \(=\) coherent recoupling for every state in the selected
  sector;
- basis changes leave the complete heat activity invariant;
- every selected complete heat activity is nonnegative for its full physical
  coupling domain;
- the reflected Gram matrix is exactly PSD;
- the one-block unnormalized pushforward, its coarse-intertwiner transport,
  total mass, and remainder identity are explicit.

**Negative exit**

- a minimal complete physical heat family is exactly negative; or
- a basis/coherence inconsistency survives exact signed recoupling; or
- the exact pushforward requires boundary data outside the proposed enriched
  carrier.

Any negative exit is progress: it supplies BF2/BF3 with the first exact
coordinate of failure and specifies the necessary carrier enlargement.

### Anticipated artifacts

- `computations/intertwiner_resolved_carrier.py`;
- `computations/three_strand_corrected_slab.py`;
- `tests/test_intertwiner_resolved_carrier.py`;
- `tests/test_three_strand_corrected_slab.py`;
- `notes/bf1-5-three-strand-pushforward.md`.

Names may be adjusted to the existing module layout, but the mathematical
payload and exit test may not be weakened.

### Dependencies already present

- exact quaternion Haar integration and corrected-slab geometry;
- pair-orbit and diagonal physical heat census;
- exact signed/squared Wigner--Racah \(6j\) machinery;
- Biedenharn--Elliott coherence interfaces;
- the finite \(SU(2)_k\) audit identifying precisely why multiplicities are
  insufficient.

### Explicit non-goals

BF1.5 does not claim general (DP), cutoff-uniform Birkhoff contraction,
RG-I7--I9, continuum existence, the all-groups lift, or the Clay theorem.
Its purpose is to decide whether the first carrier rich enough for the
physical block map is positive and closed in the first genuinely
multiplicity-bearing sector.

## Closed milestone — BF1.6: reflection-cut half-surface carrier

**Closed 2026-07-24 by the positive finite-sector route.**  The three BF1.5
strands cut into loops of lengths four and six with four four-valent and two
bivalent cut vertices, giving a 16-dimensional invariant boundary-index
space.  Exact temporal-gauge half-tensor gluing reconstructs the BF1.5
amplitude \(83/5184\).  The first nontrivial two-state positive-half Gram has
determinant \(1/331776\) and positive \(LDL^{\mathsf T}\) pivots
\((41/648,1/20992)\).  A spacing-two, cutoff-two Haar disk block embedded in
the corrected slab has coarse modes \(1,2s^{12},3s^{32}\), Haar mass one,
and zero outside-carrier remainder.  See
`notes/bf1-6-reflection-cut-half-surface.md`.

BF1.5 identifies the datum still missing before BF2/BF3: a closed surface
must be cut into two open half-surface packets, and the exposed cut-edge
intertwiner indices must be retained rather than contracted away.

### Goal

Construct the minimal positive-half carrier whose gluing reconstructs every
BF1.5 closed state, identify the corrected-slab reflected kernel as its exact
Gram matrix, and carry that carrier through one genuinely
spacing-changing, unnormalized Haar block.

### Exit test

The gate closes when either:

- the reconstructed minimal reflected kernel has an exact PSD/SOS
  factorization and the geometric block pushforward remains inside the
  half-surface carrier with explicit mass and remainder; or
- an exact negative minor, gluing inconsistency, or outside-carrier
  pushforward term identifies the next datum that must be retained.

### Required actions

1. split the three BF1.5 strands at the half-time reflection plane;
2. canonicalize open surface boundaries and oriented cut loops;
3. attach an orthonormal invariant-basis index at every cut edge;
4. implement reflection and gluing with exact signed \(F/R\) transport;
5. recover the closed BF1.5 Haar amplitudes by summing shared cut indices;
6. build and factor the physical one-sided Gram matrix on positive-half
   states;
7. perform one actual lattice-spacing-changing corrected-slab Haar
   pushforward and return its kernel, mass, and outside-carrier remainder.

## Next milestone — BF2.1: general reflection-cut positivity carrier

BF1.6 proves that the corrected coordinate system is the positive-half
boundary tensor, not the closed-surface scalar.  BF2.1 must decide whether
that finite success extends to the fusion-closed physical carrier.

### Goal

Construct the general finite-cutoff reflection-cut carrier on corrected
slabs and prove its complete physical weighted Gram blocks nonnegative, or
isolate the first exact coherent counterexample.

### Required actions

1. enumerate cut signatures and invariant bases through the next cell and
   label cutoffs;
2. retain complete magnetic/intertwiner tensors and signed \(F/R\) transport;
3. group states by boundary signature before testing positivity;
4. build every weighted Gram block from the exact plaquette-coupled Haar
   law;
5. sweep the complete heat-weighted blocks for negative principal minors;
6. identify a fusion-closed cone stable under the spacing-two block, or
   return the first exact outside-cone term;
7. formulate the minimal general reflected-Gram/SOS lemma supported by the
   census.

### Exit test

The gate closes with either a theorem/certificate covering every generator
at the stated cutoff and geometry, together with a proved enlargement
scheme, or a complete physical counterexample retaining all coherent
boundary data.

## BF2–BF4: contraction engine

The Birkhoff map will not be the raw one-face fusion matrix: its support has
zero holes and infinite Hilbert diameter. The candidate is the reflected
physical block kernel on BF2-positive generators.

For lattice spacing \(a_n\), the target is scale-dependent:

\[
q_n=1-m a_n+o(a_n),
\qquad
\quad
\prod_{n\in I(L)}\left(q_n+C\kappa_n^{64}\right)
\le e^{-m_*L}<1
\]

for every group of steps spanning a fixed physical distance \(L\). Required
certificate data are the positive cone, an interior comparison point, lower
and upper cross-ratio bounds, the physical block length, and the graded
distortion budget.

## BF5–BF6: physical RG closure

The exact pushforward identity must split into:

- the unbranched positive carrier map;
- a \(\kappa\)-graded branched sector;
- an actual remainder measured in the same projective norm;
- scale-dependent contraction and summable distortion;
- landing in the domain where the estimates reproduce under iteration.

This package is RG-I7, RG-I8, and RG-I9 only when its measure is the exact
Haar-network Gibbs law, not the multiplicity-product surrogate.

The Bałaban-shaped small-/large-field bounds must therefore be re-extracted
or reproved in the normalization of that exact law.  Literature-shaped
fiducials remain pilots, not RG exit certificates.

## BF7–BF10: from RG to the Clay theorem

The RG certificate must construct located infinite-volume and continuum
Schwinger limits on a gauge-invariant local observable algebra. The same
object must carry reflection positivity, Euclidean covariance, symmetry,
regularity, clustering, locality, nontriviality, and asymptotic-freedom
normalization.

OS/GNS reconstruction must then identify the physical time translations and
show that the grouped correlation exponent supplies a spectral exclusion
\((0,\Delta_G)\) for the reconstructed Hamiltonian. Finally, every
representation-theoretic input must be constructed for each compact simple
group, and all fields must assemble on the one shared stack required by
`ClayTargetPinned`.

Finite witnesses for reflection positivity, nontriviality, a transfer gap,
or identity covariance remain valuable tests, but they do not compose into
BF7--BF10 unless their maps into this shared object are explicit.

## Evidence and commit policy

Every completed gate requires:

- an exact computation or proof artifact;
- regression tests;
- a prose statement distinguishing proved results from open inputs;
- constructive Lean certificates for witness-bearing reductions where
  applicable;
- an assumption/axiom audit;
- a focused commit that does not absorb unrelated worktree changes.
