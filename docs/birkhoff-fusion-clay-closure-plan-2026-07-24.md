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

## Closed milestone — BF2.1: general reflection-cut positivity carrier

**Closed 2026-07-24 by the enlarged reflected-Gram route.**  The exact
heat-kernel Gibbs reflection form has a general Gram/SOS factorization on
the complete fusion- and intertwiner-resolved boundary Hilbert space.
Exact Haar blocking acts on its PSD cone by a completely positive Kraus
map.  On the unit four-cube, all 64 binary half-surfaces form 32 boundary
blocks; their 128 ordered gluings biject with every closed binary surface.
All 32 one-strand and all 528 two-strand coherent blocks have exact
nonnegative \(LDL^{\mathsf T}\) pivots.  See
`notes/bf2-1-general-reflection-positive-carrier.md`.

This closes reflected positivity and identifies the cone needed by the
Birkhoff program.  It does not prove entrywise (DP), strict projective
contraction, or invariance of a selected finite carrier under the whole
physical block map.

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

## Closed milestone — BF3.1: whole corrected-slab Kraus kernel

**Closed 2026-07-25 at physical representation cutoff one.**  The smallest
whole corrected slab has 72 faces.  Its complete binary physical sector
gives 32 exact rank-one Kraus blocks on a 64-state half-boundary carrier and
an independently reconstructed mass polynomial.  All 512 spacing-two
binary Wilson words have explicit 128-channel affine Haar fibres, including
four- and six-valent intertwiner packets.  The first non-vacuum fibre is
fully evaluated and has a nonzero signed normalized remainder.  Exact
leading terms in all four \(P/Q\) blocks show that every finite
representation cutoff leaks.  See
`notes/bf3-1-whole-corrected-slab-kraus.md`.

The older multiplicity-product conditional kernel remains a useful formal
normalization scaffold but is not identified with this coherent Haar map.
All-label summability and a physical vanishing-remainder estimate remain
open.

BF2.1 fixes the carrier and its order.  BF3.1 must now inhabit the map rather
than infer it from complete positivity.

### Goal

Construct the exact, unnormalized, plaquette-coupled Haar pushforward for
one whole corrected slab as a Kraus/Stinespring map between the complete
BF2 boundary spaces.  Return its mass, reflection transport, joint
coarse-intertwiner action, and the literal coherent remainder at a finite
representation cutoff.

### Required actions

1. enumerate the complete fine and coarse boundary fusion/intertwiner bases
   for the smallest whole corrected slab extending the BF1.6 disk;
2. factor the exact physical heat-kernel block density into half-kernel
   features without truncating the measure;
3. integrate every internal Haar link and return the exact Kraus matrices;
4. verify mass preservation after normalization and covariance under the
   slab reflection;
5. compute joint coarse-intertwiner transport, including signed \(F/R\)
   basis changes;
6. for a finite boundary projection \(P\), return all four blocks
   \(P\Phi P\), \(P\Phi Q\), \(Q\Phi P\), and \(Q\Phi Q\);
7. decide the exact closure condition \(QK_rP=0\) for every Kraus index, or
   exhibit the first outside-carrier coherent term;
8. pin the complete kernel with independent direct-Haar and recoupled
   reconstructions.

### Exit test

The gate closes only with an explicit whole-slab physical kernel.  A generic
CP-map theorem, the BF1.6 disk, a scalar mass ledger, or a map on
multiplicity vectors is not an exit certificate.

## Closed milestone — BF3.2: all-label kernel and vanishing remainder

### Goal

Upgrade the BF3.1 cutoff-one affine Haar fibres to the full heat-kernel
representation field and prove that the coherent normalized remainder has a
cutoff- and volume-uniform vanishing modulus in the same PSD boundary-kernel
norm.

### Required actions

1. construct the all-label fusion/intertwiner fibre over every coarse Wilson
   word, retaining all signed \(F/R\) transport;
2. give a summable heat-tail envelope uniform in the finite slab volume;
3. control \(P\Phi Q\), \(Q\Phi P\), and \(Q\Phi Q\) without deleting their
   coherence;
4. evaluate or enclose the actual normalized Haar remainder, not the older
   multiplicity-product surrogate remainder;
5. return an explicit cutoff modulus and a volume-uniform norm bound that
   tends to zero at the required blocking scale;
6. identify the exact all-label kernel passed to BF4.

### Exit test

BF3.2 closes only when the same exact Haar map constructed in BF3.1 has an
all-label, cutoff-uniform completion and a vanishing physical remainder.
The universal probability bound two, zero vacuum coefficient, or a
finite-cutoff table is not sufficient.

**Closed 2026-07-25 at paper level.**  The repository's axiom-clean Lean
transport remains open at the differentiated infinite Jacobi identity.

### Completion

Every nine-word coarse Wilson coefficient of the 72-face BF3.1 Haar network
now has a literal finite-cutoff approximant and an explicit all-label Cauchy
modulus.  The character estimate

\[
  (n+1)s^{n(n+2)}|\chi_n|\le(n+1)^2s^{n(n+2)}
\]

gives a super-geometric one-plaquette tail and the exact fixed-slab envelope
\(72H_N^{71}T_N\).  Dividing by the product of external representation
dimensions makes this coefficient bound uniform in all coarse labels.  A
constructive coupling-dependent cutoff schedule is implemented.

In the elementary strong-coupling positivity corridor this also gives a
normalized bound on the actual plaquette-coupled Haar Gibbs density.  At
\(s=1/2\), cutoff \(N=11\) is the least cutoff certified by this estimate to
put the normalized \(L^1\) tail below \(10^{-2}\).

Conditioning on the exterior of one corrected slab cancels every disjoint
plaquette factor.  The same 72-face estimate is therefore uniform in the
ambient finite volume and boundary holonomies inside the certified
strong-coupling corridor.

The strong-coupling restriction is removed at paper level by a new exact
Jacobi-product floor.  If

\[
 P_M(s)=\prod_{n=1}^M(1-s^{2n})(1-s^{2n-1})^2,\qquad
 \delta_M(s)=\frac{s^{2M+2}+2s^{2M+1}}{1-s^2}<1,
\]

then the differentiated Jacobi triple product gives

\[
 K_s(x)\ge
 \frac{P_M(s)(1-\delta_M(s))}{(1+s)^2}>0
\]

for every \(x\in[-1,1]\).  Combining this with the character tail constructs
a coupling-dependent cutoff making the truncated plaquette kernel positive
and the normalized local conditional tail arbitrarily small at every
rational \(0<s<1\).  The finite rational certificate is executable; the
repository's existing `HeatKernelPos*.lean` frontier still lacks the
infinite differentiated Jacobi identity.

The representation tail itself is now identified with the BF2 trace-class
boundary-kernel norm.  The heat-weighted Peter--Weyl evaluation vector on
nine coarse holonomies has squared norm at most \(H_N(s)^9\), so a normalized
local Gibbs \(L^1\) tail \(\varepsilon_N\) gives

\[
 \lVert\delta G_N\rVert_1\le H_N(s)^9\varepsilon_N.
\]

The independent boundary-feature tail is
\(D_N=9H_N(s)^8T_N(s)\).  It bounds \(QGQ\), while the two coherent corners
are bounded by \(\sqrt{H_N(s)^9D_N}\), with an exact rational square-root
enclosure in the certificate.  Signed orthonormal recouplings preserve all
these trace norms.  Thus the open-boundary Gram is a trace-norm Cauchy
object retaining magnetic and intertwiner data.

Combining the density and boundary-feature tails gives a constructive total
trace-norm cutoff modulus.  At \(s=1/2\), \(N=18\) is the least cutoff
certified by the implemented bound to put the complete coherent error below
\(10^{-2}\).  The exact all-label local Haar kernel, coupling-dependent
cutoff, ambient-volume-uniform conditional normalization, full magnetic and
intertwiner feature field, and all coherent \(P/Q\) trace tails therefore
satisfy the BF3.2 exit test.

This closes the representation-cutoff remainder, not the later
fine-pushforward-versus-coarse-ansatz RG remainder.  The latter requires a
named landing/reference rule and remains open before RG-I7--I9.  Nor can
trace convergence be promoted directly into BF4: an exact heat-spectrum
witness has trace norm tending to zero while its relative-order norm remains
one.
The existing
`Z4FixedCutoffNaiveTailFence` rules out a volume-uniform additive
independent-plaquette repair.  The remaining route must use a localized or
connected norm.  BF3.2 now bounds every cutoff \(P/Q\) block; the later
fine/coarse cylinder mismatches remain part of the RG landing/remainder
problem.  See
`notes/bf3-2-all-label-whole-slab-frontier.md`.

## Closed diagnostic milestone — BF3.3: Birkhoff handoff admissibility

**Closed 2026-07-25 by the exact obstruction route, in advance of BF3.2.**
This gate adjudicates the currently available shortcuts from positivity to
Birkhoff contraction; it does not skip BF3.2 or open BF4.

The BF3.1 reflected density is a direct sum of 32 positive rank-one blocks.
Every block has projective rate zero, but the full support has no
cut-signature mixing and therefore has infinite global projective diameter.
The local reflected fusion Gram is strictly positive inside each parity
sector at every finite cutoff, but an explicit spin-\(2\)/spin-\(4N\)
cross-ratio obeys

\[
 \Theta_N\ge
 \frac{(N+1)(3N^2+7N+1)}{18N}
 \ge\frac{N^2}{6}.
\]

Hence both the rational certificate rate and the sharp Birkhoff--Hopf
diameter rate tend to one with the cutoff. Finally, at
\(s_N=1-1/(2(N+1)(N+3))\), the first outside-cutoff heat feature is at
least \((N+2)/2\), so no cutoff-only tail modulus is uniform in the
coupling.

### Exit result

BF3.3 closes as a rejection certificate for these three candidate
handoffs. A valid BF4 input must instead provide the exact all-label
physical kernel, an invariant positive carrier, retained signed
intertwiners, global or fixed-distance grouped mixing, the physical
projective norm, a fixed-distance diameter bound, coherent-remainder
domination in that norm, a coupling-dependent cutoff schedule, and
volume-uniform constants.

At the time of this diagnostic closure, only the signed-intertwiner field
was available.  BF3.2 has subsequently closed at paper level and the
fixed-coupling physical minorization now closes the support/mixing field.
The historical obstruction remains the reason BF4 targets fixed physical
distance rather than the raw local Gram. See
`notes/bf3-3-birkhoff-handoff-admissibility.md`.

## BF2–BF4: contraction engine

The Birkhoff map will not be the raw one-face fusion matrix: its support has
zero holes and infinite Hilbert diameter. The candidate is the reflected
physical block kernel on BF2-positive generators.

The full infinite-cutoff PSD trace-class cone is the correct order carrier
but has empty trace-norm interior, so it is not itself the quantitative
Birkhoff cone.  BF4 must prove that the grouped physical image lies in a
reference-order part.  For a faithful trace-one heat reference \(R_a\), the
new exact target is

\[
  \alpha_a\ell(A)R_a
  \preceq\Phi_{a,L}(A)
  \preceq\beta_a\ell(A)R_a.
\]

This single two-sided operator estimate implies

\[
  q_{a,L}\le
  \frac{\beta_a-\alpha_a}{\beta_a+\alpha_a}
\]

independently of boundary-space dimension.  The abstract exact-rational
Loewner-order certificate and the trace-cone interior-collapse witness are
complete.  The sharp heat-relative reference-cone invariance and
physical-distance coherent-remainder domination are open.  The cutoff-one
BF3.1 map cannot
satisfy a positive lower minorization because all 32 components are rank
one.  See `notes/bf4-reference-order-cone-gate.md`.

Equivalently, center the normalized physical output at \(R_a\):

\[
 E_A=\Phi_{a,L}(A)/\ell(A)-R_a.
\]

The single relative-order estimate

\[
 -\delta_aR_a\preceq E_A\preceq\delta_aR_a
\]

gives \(\alpha_a=1-\delta_a\), \(\beta_a=1+\delta_a\), and therefore the
dimension-free rate \(q_{a,L}\le\delta_a\).  This is the precise remaining
physical theorem.

The first physical all-label minorization is now also constructed at every
fixed rational coupling.  The Jacobi floor \(L_s\) and character ceiling
\(H_s\) give, for the 72 active plaquettes and every exterior boundary
condition,

\[
 (L_s/H_s)^{72}\lambda
 \le \mu_b\le
 (H_s/L_s)^{72}\lambda.
\]

The deterministic coarse pushforward preserves this comparison.  Therefore
the completely grouped physical conditional family has a finite,
cutoff-independent and ambient-volume-independent diameter at fixed
coupling.  This closes the support/mixing field rejected by BF3.3.

It does not close BF4's physical-distance rate: the certified values of
\(1-q_s\) are already about \(10^{-216}\) at \(s=1/2\) and deteriorate as
\(s\to1\).  The next BF4 action is to replace this global worst-holonomy
comparison by a fusion/heat-local grouped estimate with
\(q_a=1-ma+o(a)\), or directly a fixed-distance rate \(<1\).

### Intuitionistic BF4 normal form (2026-07-25)

The finite contraction algebra no longer needs to wait for a constructive
formalization of logarithmic Hilbert geometry.  An explicit grouped
refresh decomposition

\[
  \Phi_{a,L}
  =
  \varepsilon_{a,L}\Omega_{R_{a,L}}
  +(1-\varepsilon_{a,L})\Psi_{a,L},
  \qquad
  \Omega_R(A)=\ell(A)R,
\]

with positive mass-preserving residual \(\Psi_{a,L}\), contracts the base
norm by \(1-\varepsilon_{a,L}\).  The finite exact-rational theorem is
machine checked in
`lean/YMGap/Continuum/ConstructiveRefreshContraction.lean`.
For square grouped kernels,
`lean/YMGap/RG/ConstructiveRefreshStableDynamics.lean` exports the result
as the existing RG-I7 `UniformContractionCertificate`.

The lower half of the existing relative-order target already has this
form: \(-\delta R\preceq E_A\) gives
\(\Phi(A)\succeq(1-\delta)\ell(A)R\), hence
\(\varepsilon=1-\delta\) and contraction rate \(\delta\).  The upper
Loewner estimate is not needed for this base-norm route.

The physical target should be imposed on the map grouped over a fixed
physical distance, not obtained by multiplying the catastrophic
microscopic Haar floors.  The new preferred BF4 exit witness is therefore

\[
  \varepsilon_{a,L}\ge\varepsilon_L>0,
  \qquad
  q_L=1-\varepsilon_L<1,
\]

uniformly in spacing, representation cutoff, and ambient volume.  Complete
positivity of the residual is preferred so that the certificate survives
boundary ancillas and coherent intertwiner transport.  The exact grouped
physical refresh packet and its spacing-uniform mass remain open.  See
`notes/bf4-intuitionistic-proof-routes.md`.

The first all-label grouping experiment is now positive.  The exact central
heat corridor satisfies \(K_s^{*m}=K_{s^m}\), and the complete character
tail gives the rational common Haar floor
\[
 K_{s^m}\ge\frac{1055}{2272}
 \quad\text{when}\quad s^m\le\frac12.
\]
A finite \(r\)-corridor cover would therefore carry common mass
\((1055/2272)^r\), before the physical domination coefficient.  This
identifies the remaining BF4 constructor: prove that the normalized
interacting corrected-slab grouped map CP-dominates such a corridor cover
with \(\eta_{a,L}\ge\eta_L>0\), and prove
\(s(a)^{\lceil L/a\rceil}\le1/2\).  The resulting physical packet has mass
at least \(\eta_L(1055/2272)^r\).

The nine canonical filling disks are now pinned exactly.  They use 30
disjoint faces and 27 disjoint internal links, but every internal link also
meets two transverse plaquettes, refuting literal product-semigroup
factorization.  Exact Haar leaf elimination removes 21 of the 42 transverse
faces and leaves a pinned 21-face core.  Its connected 15-face component has
1024 admissible cutoff-one fillings.  Their coherent partial Haar tensors are
now constructed as 1024 distinct canonical trace-word records with rational
scalar coefficients, soluble orientation constraints, and maximum trace-word
length seven.  Distinctness here is syntactic after the stated word
canonicalizations, not functional independence modulo every \(SU(2)\) trace
identity.  This is a finite fundamental-sector result, not the needed
all-label order theorem.  The next comparison must lift the compact
trace-word family through the complete recoupling tower and prove a
spacing-uniform CP lower bound with a summable cutoff modulus.

The cumulative-heat condition controls the local bare heat-kernel mode.
With \(\rho=s^3\), it implies
\[
 (1-\rho(a))/a\ge7/(16L)
\]
for \(a\le L\).  This is not yet the physical gap: identifying this bare
Fourier multiplier with the interacting gauge-invariant transfer separator
is a separate open bridge, and bare asymptotic freedom may make the displayed
ratio diverge.  BF4 must derive the bare scale estimate on the actual
trajectory and the interacting CP comparison; BF6--BF8 must perform the
shared-object physical transfer and OS promotion.

This audit also sharpens the BF3.2 handoff language.  BF3.2 has the
all-label local reflected Gram and its trace-class Cauchy modulus.
Constructing a source-indexed kernel that composes across consecutive
physical scales, including the shared coarse-intertwiner field, remains
part of BF4.  See `notes/bf4-grouped-all-label-haar-kernel.md`.

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
