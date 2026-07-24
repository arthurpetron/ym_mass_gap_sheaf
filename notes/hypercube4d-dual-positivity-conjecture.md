# SU(2) dual positivity: resolved-channel signs and physical-sum survival

**Date:** 2026-07-23
**Exact engine:** `computations/exact_haar_network.py`
**Four-cube survey:** `computations/hypercube4d_survey.py`
**Crossing kernel:** `computations/four_strand_crossing_kernel.py`
**Binary Gram:** `computations/hypercube4d_surface_gram.py`
**Regression pins:** `tests/test_hypercube4d_dual.py`,
`tests/test_hypercube4d_survey.py`,
`tests/test_four_strand_crossing_kernel.py`,
`tests/test_hypercube4d_surface_gram.py`

## Result and scope correction

Universal nonnegativity of every **resolved fixed-face channel** is false.
It already fails on the two-skeleton of the boundary of one four-cube at
doubled-spin cutoff two.
The smallest symmetry-orbit representative found by the complete exact scan
is

```text
(2,1,1,1,1,2,0,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,1,0)
```

in the deterministic face order of `hypercube4d_survey.py`.  It is locally
admissible at every trivalent edge.  Its 16 physical vertex-\(6j\) signs
contain nine negatives and no zeros, and direct quaternion-Haar integration
gives

\[
  A_{\partial I^4}(j)=-\frac1{196608}.
\]

Because every edge of this resolved complex is trivalent, its invariant
space is zero- or one-dimensional.  There is no omitted intertwiner
cancellation inside this fixed-face channel.

This does **not** refute the program conjecture (DP), because a physical
intersecting-surface amplitude retains and sums every induced fusion channel
and edge intertwiner.  The witness occurs as a negative internal channel
inside genuine intersecting pairs, but the complete four-strand sum over
\(\operatorname{Inv}((\tfrac12)^{\otimes4})\) remains positive in every
four-cube physical pair orbit tested below.

## Two statements that must not be conflated

Let \(X\) be a finite connected oriented two-complex with closed faces \(F\)
and integrated edges \(E\).  For doubled SU(2) face labels
\(j=(j_f)_{f\in F}\), define the basis-independent fixed-face Haar
coefficient

\[
  A_X(j)
    := \int_{\mathrm{SU}(2)^E}
         \prod_{f\in F}\chi_{j_f}\!\left(\operatorname{Hol}_f(U)\right)
         \prod_{e\in E}dU_e .
\]

The stronger resolved-channel statement tested and refuted in this note is:

> **Cubical fixed-face positivity.** If \(X\) is a closed physical cubical
> complex, then \(A_X(j)\ge 0\) for every admissible SU(2) face labelling
> \(j\), after the complete edge-intertwiner fiber has been summed.

The explicit four-cube channel refutes that fixed-\(j\) statement.  The
program-level conjecture is instead:

> **(DP): physical dual positivity.** The SU(2) dual amplitude of a physical
> surface complex is nonnegative after summing the complete set of face
> fusion channels and edge intertwiners induced by that complex.

Thus a negative \(A_X(j)\) is a required signed ledger entry, not a
counterexample to (DP), unless \(j\) itself exhausts the physical complex's
complete fusion/intertwiner fiber.  The exact pair calculations below show
the distinction operationally: negative fixed-face entries cancel inside
positive complete physical sums.

For an open complex the integral is a boundary tensor or kernel, not a
scalar.  The meaningful analogue is positive-semidefiniteness of the
reflected boundary form, or a Gram decomposition.  Entrywise sign in a
phase-dependent intertwiner basis is neither invariant nor the desired
reflection-positivity statement.

Face reversal does not change the scalar because SU(2) characters satisfy
\(\chi_j(g^{-1})=\chi_j(g)\).  Edge reversal is the Haar change of variables
\(U_e\mapsto U_e^{-1}\).  Thus the scalar conjecture is independent of the
orientation choices used to evaluate it.

## What “intertwiner-summed” excludes

Expanding every edge Haar integral as its orthogonal invariant projector,

\[
  P_e
    = \sum_{\iota_e\in
        \operatorname{ONB}\operatorname{Inv}(H_e)}
        |\iota_e\rangle\langle\iota_e|,
\]

gives

\[
  A_X(j)=\sum_{\iota} A_X(j,\iota).
\]

The positive edge-normalization factors do not make the individual vertex
spin-network evaluations positive.  Wigner \(6j\), cubic \(18j\), and
four-dimensional \(48j\) recoupling terms can carry signs.  Hence

* fixed-intertwiner nonnegativity is false;
* a negative term \(A_X(j,\iota)\) does not refute the conjecture when the
  invariant space has dimension greater than one;
* a counterexample must include the complete sum over the intertwiner fiber.

This distinction is already present in the exact duality of Oeckl--Pfeiffer,
which performs the group integrations and produces representation and
intertwiner data, and in the three-dimensional cubic dual amplitudes of
Cherrington--Christensen--Khavkine:

* <https://arxiv.org/abs/hep-th/0008095>
* <https://arxiv.org/abs/0705.2629>

The latter paper's negative \(18j\) terms establish a fixed-intertwiner sign
problem.  They do not, by themselves, exhibit a negative value of the
plaquette-only coefficient after every intertwiner has been summed.

## Exact four-cube reconstruction

`brick_complex_nd((1,1,1,1))` constructs the oriented two-skeleton of the
unit four-cube without a topology-specific amplitude table.  It has

* 16 vertices;
* 32 edges;
* 24 square faces;
* 17 co-tree integration variables after maximal-tree gauge fixing; and
* three incident faces at every edge.

The GF(2) edge-face incidence kernel has dimension seven, in agreement with
the eight cubical three-cell boundaries and their one relation.  Its 128
binary closed surfaces have support census

| number of faces | Euler characteristic | number of surfaces |
|---:|---:|---:|
| 0 | 0 | 1 |
| 6 | 2 | 8 |
| 10 | 2 | 24 |
| 12 | 2 | 40 |
| 12 | 4 | 4 |
| 14 | 2 | 48 |
| 16 | 0 | 3 |

These split into nine orbits under the 384 symmetries of the four-cube.
The four size-12, Euler-characteristic-four sectors are disconnected pairs
of spheres; the remaining positive-Euler-characteristic sectors in the
table are spheres.  The three size-16 coordinate sectors are Clifford tori.
The exact spin-1 amplitude is \(2^{\chi-F}\); in particular the connected
representative pinned at each support size has

\[
\begin{array}{c|rrrrrr}
F&0&6&10&12&14&16\\ \hline
A&1&1/16&1/256&1/1024&1/4096&1/65536.
\end{array}
\]

The disconnected size-12 pair has amplitude \(1/256\).  In general this is
the two-dimensional Yang--Mills formula \((j+1)^{\chi-F}\), so
binary-surface positivity is a theorem for these sectors rather than an
unexplained finite pattern.

## Highest-channel projection of intersecting surfaces

For two distinct binary surfaces \(S,T\), assign doubled spin one to a face
covered once and doubled spin two to an overlap face.  This produces a
\(\{0,1,2\}\)-valued admissible labelling and selects only the highest fusion
channel on every overlap.  It is a useful resolved channel, but it is **not**
the complete pair observable: coincident fundamental strands have already
been fused to spin one, so the geometric edge remains trivalent.

There are \(\binom{128}{2}=8{,}128\) raw unordered pairs.  Exactly 7,997
intersect and 131 are disjoint.  At every four-cube edge the invariant space
is zero- or one-dimensional, because precisely three faces meet there and
SU(2) fusion is multiplicity-free.  Therefore “intertwiner-summed” and
“fixed-intertwiner” coincide on this complex.  Up to positive edge
normalizations, the sign is the product of the 16 local tetrahedral \(6j\)
symbols.

At a lattice vertex \(x\), write \(n_{ab}(x)\) for the incident face in
coordinate plane \(a<b\).  The physically wired local symbol is

\[
  \left\{\begin{matrix}
  n_{01}&n_{02}&n_{03}\\
  n_{23}&n_{13}&n_{12}
  \end{matrix}\right\}.
\]

Its four triangle triples are
\((01,02,03)\), \((01,13,12)\), \((23,02,12)\), and
\((23,13,03)\), exactly the three-face stars of the four primal edges at
that vertex.  This incidence check is essential: grouping
\((01,02,12)\) as a triangle instead attaches a symbol to a boundary
three-cell and gives a false zero screen.

The complete exact sign census of the 7,997 intersecting pairs is:

| negative local \(6j\)'s | zero local \(6j\)'s | raw pairs |
|---:|---:|---:|
| 0 | 0 | 1,485 |
| 2 | 0 | 2,456 |
| 4 | 0 | 2,372 |
| 6 | 0 | 720 |
| 8 | 0 | 820 |
| 10 | 0 | 96 |
| 12 | 0 | 48 |

Every pair channel is nonzero, and no admissible pair has an odd number of
negative vertex symbols.  Hence all 7,997 global amplitudes are strictly
positive.  The counts are raw pair counts, not symmetry-orbit counts.

The 7,997 pairs reduce to 100 hyperoctahedral orbits.  Direct quaternion-Haar
evaluation of representative channels provides an independent normalization
and wiring check on the faster \(6j\)-sign factorization.  For example, the
pair of masks `0x1cefc0` and `0x39dc0b` has supports 12 and 12, overlap six,
and exact Haar amplitude \(1/186624\).  The incorrect three-cell wiring
assigns local zeros to this same channel, so this value is also a regression
against that tempting incidence error.

Grouped by the same negative-symbol counts \(0,2,4,6,8,10,12\), the 100
orbits have multiplicities \(29,20,27,6,16,1,1\), respectively.

The even sign is structural, not merely a 7,997-case observation.  At one
four-cube vertex, a binary closed surface restricts to an Eulerian subgraph
of \(K_4\): the empty graph, one of four triangles, or one of three
four-cycles.  The exact \(8\times8\) local table says that the superposed
symbol is negative precisely when one local surface state is empty and the
other is nonempty.  Hence

\[
  N_- = |V(S)\mathbin{\triangle}V(T)|,
\]

where \(V(S)\) is the set of four-cube vertices touched by \(S\).
Every binary surface touches an even number of vertices.  Indeed it is a
closed cubical surface embedded in the boundary three-sphere and hence is
orientable, so its Euler characteristic is even.  Also \(E=2F\) by
bivalence, so \(\chi=V-F\), and \(F\) is even because every surface is a
symmetric difference of six-face three-cell boundaries.  Thus \(V\) is
even, \(N_-\) is even, and the global sign is positive.

This is an all-pair theorem for the highest-channel projection, but not an
all-assignment theorem and not yet the genuine four-strand pair theorem.  The
full cutoff-two scan below shows that leaving this projected cone changes the
fixed-face answer.

## Genuine intersecting pairs and the four-strand sum

The genuine pair retains two separate fundamental character factors on every
overlap face:

\[
  A(S,T)
   =\int \left(\prod_{f\in S}\chi_1(U_f)\right)
           \left(\prod_{f\in T}\chi_1(U_f)\right)dU .
\]

At a crossing edge, the two bivalent sheets contribute four fundamental
strands and Haar integration projects onto the two-dimensional space

\[
  \operatorname{Inv}
    \left((\tfrac12)^{\otimes4}\right).
\]

Equivalently, applying \(\chi_1^2=\chi_0+\chi_2\) on every overlap face
expands the pair into **all** zero/spin-one fusion choices, not just the
highest choice used in the preceding section.

The 7,997 raw intersecting pairs reduce to 100 four-cube symmetry orbits.
The exact complete fusion sum is strictly positive on all 100.  The smallest
orbit value is

\[
  \min A(S,T)=\frac1{16384}.
\]

The calculation is interference-sensitive.  Across the 100 representative
fusion ledgers there are 696 positive, 108 negative, and 19,548 vanishing
fixed-face terms.  Six pair orbits require genuine signed cancellation:

| negative terms | positive terms | pair orbits |
|---:|---:|---:|
| 4 | 12 | 3 |
| 16 | 48 | 2 |
| 64 | 192 | 1 |

For the representative masks `0x4ab33` and `0x6bc6ad`, four fusion channels
have amplitude \(-1/196608\), but the complete exact sum is

\[
  A(S,T)=\frac{31}{331776}>0.
\]

Direct duplicate-character Haar contraction agrees exactly with the
independent sum of the resolved \(6j\) channels.  This is the first probe here
that genuinely exercises the four-valent intertwiner sum described by the
binary-surface conjecture.  It is an exhaustive cutoff-one pair result on one
four-cube boundary, not yet an all-complex theorem.

### Why the six signed ledgers are positive

The six cancellation-requiring orbits are not unrelated numerical
exceptions.  They contain 147 raw pairs, their symmetric difference is
always one of the coordinate Clifford tori, and their overlap plaquettes
split into two complementary coordinate-plane families.  The associated
interaction graph is respectively

\[
  K_{2,2},\qquad K_{2,4},\qquad K_{4,4}.
\]

In the zero/triplet face-fusion basis, every resolved channel has the exact
form

\[
 A_x=2^{-16}\prod_{ij\in E(K_{m,n})}W_{x_i x_j},
 \qquad
 W=\begin{pmatrix}1&1\\[2pt]1&-\frac13\end{pmatrix}.
\]

The negative triplet--triplet entry is the local source of the signed
resolved ledger.  Summing the complete channel fiber gives

\[
 Z_{m,n}
   =\sum_{r=0}^{m}\binom mr
      \left(1+\left(-\frac13\right)^r\right)^n>0.
\]

Every summand in the last expression is positive.  After the finite
four-cube orbit classification, this proves analytically the positivity of
all six signed ledgers.  Their complete amplitudes are

\[
\begin{array}{c|c}
K_{2,2}&31/331776\\
K_{2,4}&1837/6718464\\
K_{4,4}&5115985/11019960576.
\end{array}
\]

The other 94 pair-orbit ledgers are termwise nonnegative.  Thus the
100-orbit result is now a finite structural proof on \(\partial I^4\), not
merely a list of 100 positive totals.  The limitation is equally precise:
the proof uses the Clifford-torus/complementary-plane classification of the
four-cube and does not automatically extend to arbitrary complexes.  Local
projector positivity alone is insufficient, because both the rational
\(6j\) table and the diagram-basis inverse Gram contain negative entries.

### Complete binary-surface Gram

For every one of the 128 closed binary surfaces, set

\[
 O_S(U)=\prod_{f\in S}\chi_1(\operatorname{Hol}_f(U)),\qquad
 G_{S,T}=\int O_S(U)O_T(U)\,dU .
\]

The full exact \(128\times128\) matrix has 8,256 unordered entries, 118
pair orbits, and 80 distinct rational values.  All entries are strictly
positive.  The orbit split is 100 distinct intersecting, nine distinct
disjoint, and nine diagonal orbits.  This also resolves the earlier
`108 of 109` bookkeeping:

* 108 is 100 distinct intersecting orbits plus the eight nonempty diagonal
  surface orbits;
* 109 distinct-pair orbits are the 100 intersecting plus nine disjoint
  orbits; and
* the complete Gram has all of those plus nine diagonal orbits, for 118.

More strongly, \(G\) is strictly row-diagonally dominant.  If

\[
 r_S=G_{S,S}-\sum_{T\ne S}G_{S,T},
\]

then all 128 exact residuals are positive, and

\[
 G=\sum_S r_S e_Se_S^{\mathsf T}
   +\sum_{S<T}G_{S,T}(e_S+e_T)(e_S+e_T)^{\mathsf T}.
\]

This is an explicit rank-one factorization with nonnegative coordinates.  It
proves positive definiteness and full rank independently of a modular
determinant check, which gives
\(\det G\bmod 1{,}000{,}000{,}007=897{,}767{,}826\ne0\).
The componentwise diagonal formula is

\[
 G_{S,S}=\prod_{C\subset S}\left(1+3^{\chi(C)-F(C)}\right).
\]

In particular a coordinate Clifford torus has diagonal
\(1+3^{-16}=43046722/43046721\), while two distinct coordinate Clifford
tori have Gram entry \(5115985/11019960576\).  Centering the observables also
leaves an acute nonconstant basis: the upper triangle has 8,124 positive
covariances and 132 zeros, with no negatives.

This Gram certificate closes the complete binary sector of one four-cube.
It does not prove (DP) for general complexes, and its row diagonal dominance
is not an RG contraction estimate.

### First six-valent interior-link probe

The next gluing test uses the minimal anisotropic brick
\([0,1]\times[0,2]^3\).  It has 54 vertices, 135 links, and 126 plaquettes.
Its distinguished direction-zero interior link is incident to all six
transverse plaquettes.  Duplicate surface observables are evaluated with
separate fundamental-character factors; no coincident face is silently
replaced by its highest fusion channel.

The 12 elementary three-cube boundaries through that link give 66 unordered
pairs in four stabilizer orbits.  All complete amplitudes are positive, with
values \(1/128\) and \(1/256\), and direct duplicate-character contraction
agrees with the independent
\(\chi_1^2=\chi_0+\chi_2\) face-channel expansion.

Taking symmetric differences of two elementary boundaries gives 66
two-cube composite surfaces.  Their 2,145 unordered pairs reduce to 65
stabilizer orbits.  The complete exact census found 2,145 positive, zero
zero, and zero negative amplitudes, with minimum \(1/65536\).  Ten orbits,
covering 252 raw pairs, activate all six plaquettes at the distinguished
link; all ten are pinned positive.  Two of these put exactly one fundamental
strand on each incident plaquette and have value \(1/32768\).

The complete \(66\times66\) Gram of this family has a stronger exact
certificate.  Its diagonal values are

\[
  \frac{6562}{6561}=1+3^{-8}
  \quad\hbox{and}\quad
  \frac{6724}{6561}=(1+3^{-4})^2,
\]

while the largest of all 2,145 off-diagonal entries is \(31/3888\).
Consequently every row has diagonal-dominance residual at least

\[
 \frac{6562}{6561}-65\frac{31}{3888}
   =\frac{50587}{104976}>0.
\]

Thus the six-valent family has the explicit nonnegative-coordinate
factorization

\[
 G=\sum_i r_i e_i e_i^{\mathsf T}
   +\sum_{i<j}G_{ij}(e_i+e_j)(e_i+e_j)^{\mathsf T},
 \qquad r_i>0.
\]

The compact orbit census is regression-pinned, and an opt-in slow gate
recomputes every one of the 65 representatives from the exact Haar
integrator.  The complete rederivation passes.

This is the first probe here that passes through a geometrically six-valent
interior link, but it is still a generated subfamily.  The brick's full
binary-surface kernel has dimension 44, far larger than the 66 composite
surfaces.  More immediately, the 12 elementary boundaries are independent
and generate 4,096 binary surfaces; the present family is only their
weight-two shell.  The uniform ceiling argument itself can certify at most
126 observables, since it first fails at dimension 127.  Extension therefore
needs a sharper orbitwise/weighted row-sum or a true local gluing identity,
not just a larger uniform Gershgorin bound.  The result is a finite
six-valent Gram-cone theorem, not a general six-valent theorem and not a
proof of (DP).

The next-shell scope is exact before any new amplitude scan.  Generator
weight three contains 220 surfaces in nine surface orbits and 24,090
unordered pairs in 568 pair orbits.  A bounded attempt to contract the first
weight-three diagonal did not finish after sustained multi-minute
intermediate growth and was stopped without assigning a sign.  The exact
quaternion engine already chooses a greedy link-elimination order; the
failure is representation width at the duplicated high-valence circuit.
The next implementation must therefore contract the central Haar projector
in a fusion-tree invariant basis and expose only its boundary channel
indices.  Reproducing the complete weight-two certificate is the required
semantic regression before using that engine on weight three.

The first local projector identity is now executable.  For link-linear
fundamental factors \(f_i(q)=c_i\mathbin{\cdot}q\), normalized \(S^3\)
measure gives

\[
 \int\prod_{i=1}^{2m}f_i(q)\,dq
 =\frac{1}{4\cdot6\cdots(2m+2)}
   \sum_{\text{pairings}}\prod_{(i,j)}
   (c_i\mathbin{\cdot}c_j).
\]

Exact tests agree with generic Haar integration when the coefficient vectors
are themselves polynomials on the other links.  But expanding the
eight-strand, 105-pairing answer back into one coordinate polynomial remains
too large.  The required next object is therefore a factorized
14-dimensional invariant-block carrier, not another expanded-polynomial
formula.

## Complete cutoff-two falsification

On any closed trivalent complex, every edge invariant space is zero- or
one-dimensional.  A negative fully summed amplitude is therefore equivalent
to an admissible global face labelling for which

1. every local tetrahedral \(6j\) is nonzero; and
2. an odd number of those local \(6j\)'s is negative.

This gives a cheap exact prefilter before invoking the slower quaternion-Haar
integrator.  The complete local constraint problem with labels in
\(\{0,1,2\}\) has 38,151 admissible assignments and 369 orbits under the
384 four-cube symmetries.  There are 31,447 positive and 6,704 negative raw
assignments; no amplitude vanishes.  Thirty-three of the 369 orbits have an
odd vertex-\(6j\) sign product and therefore have negative amplitudes.

The smallest negative orbit has the literal face labels displayed in the
Result section.  Equivalently, its odd-label mask is `0x6f6d9e` and its
label-two mask is `0x21`.  The orbit has size 48 and total doubled spin 20,
which is minimal among the negative orbits.  Only two faces carry label two;
the odd support is a 16-face, Euler-characteristic-zero Clifford torus.  Its
exact local signs are

```text
(+,+,+,+,+,-,-,-,+,-,-,-,+,-,-,-)
```

and the direct integral is \(-1/196608\).  This is not a superposition of two
binary surfaces with every overlap forced into the highest channel.  It does
occur as a resolved channel inside genuine pair fusion ledgers, where the
other intertwiner channels restore a positive total.  The witness is small
enough to serve as a permanent regression pin against any future claim of
universal fixed-face positivity.

The exhaustive binary-pair reachability audit now sharpens this boundary.
Only three of the 33 negative fixed-face orbits can occur in any fusion
ledger of two closed binary surfaces:

```text
(0x6f6d9e, 0x21)      orbit size 48
(0x6f6d9e, 0x261)     orbit size 96
(0x6f6d9e, 0x108261)  orbit size 48
```

These account for 192 negative raw assignments.  All three have the same
Clifford-torus odd support; their selected label-two faces have odd parity
in each of its two complementary coordinate-plane families.  They are
exactly the \(q=ab=1\) channels of the spin-structure ledger.  The remaining
30 negative orbits (6,512 raw assignments) cannot occur in a two-binary-
surface fusion ledger and have Euler-characteristic-two odd supports.
They remain relevant to wider higher-label or multi-surface questions, but
they are not counterexamples to the exact binary-pair quadratic-refinement
law.

The first actual two-four-cube gluing test also preserves this structure.
In the `2 x 1 x 1 x 1` brick, a clean 24-face product torus splits into two
12-face cylinders.  Six raw overlap plaquettes give 64 formal channel
choices, but edge-invariant admissibility is equivalent to cancellation of
the relative boundary defect on the shared three-face.  Exactly 16 channels
survive, organized as four global caps with `K_(2,2)` intersection graph.
The two caps spanning the interface acquire positive subdivision factors
`1/3`; the crossing kernel and quadratic sign remain unchanged.  The
complete exact result is

\[
 2^{-24}\sum_{r=0}^2 {2\choose r}3^{-r}
       \left(1+(-1/3)^r\right)^2
 =\frac{101}{382205952}>0.
\]

This is a relative-gluing theorem for the clean product-torus orbit, not for
the spanning surfaces that contain plaquettes in the shared three-face.
The first such interface-bearing scout already locates the new datum: three
selected spin-one faces can meet at one interface edge with a unique
trivalent invariant even though their mod-two boundary defect is nonzero.
Its exact amplitude is positive, \(1/18874368\), but it proves that ordinary
relative homology alone cannot carry all physical channels.  The gluing
state must retain the branch intertwiner.

## Revised work order

The negative witness closes the universal resolved-sign question, while the
crossing resummation and full Gram close the four-cube binary-pair milestone.
The productive next work is now:

1. enlarge the now-proved branch-free product-torus carrier to a decorated
   relative spin network retaining trivalent interface intertwiners, as
   forced by the exact three-strand obstruction;
2. test the first genuinely higher-valent interior-link complexes using
   duplicate fundamental factors and the complete Haar projector;
3. characterize the maximal positive subcone containing reflection doubles,
   bivalent surfaces, wheels, and complete two-surface sums;
4. use the completed reachability split—3 torus orbits in binary-pair
   ledgers, 30 sphere-supported orbits outside them—to determine which can
   enter the actual reflected boundary channel used by CD-2 and verify
   cancellation in its complete intertwiner ledger;
5. replace any planned entrywise-positive block kernel by a signed channel
   ledger plus an explicit positive-semidefinite reflected Gram;
6. retain the 2x2x1 unanchored slab, 2x2x2 core, and first four-dimensional
   slab as full-sum tests of the restricted reflected cone;
7. seek a structural criterion, not a larger cutoff table, for when local
   \(6j\) signs cancel after the complete four-valent projector sum.

## Current boundary

The strongest proved positive classes are:

* reflection doubles, by an explicit squared norm;
* bivalent uniform closed surfaces, by the Euler/dimension formula;
* the all-label wheel, by its Clebsch--Gordan squared-norm identity;
* every binary surface on the four-cube boundary;
* the highest-channel two-surface family there, by the even-sign theorem; and
* the complete four-strand two-surface family there, by termwise positivity
  on 94 orbits and the complete-bipartite resummation theorem on the six
  signed orbits.

All-label **resolved fixed-face** positivity on the four-cube is refuted.
(DP) for complete physical complexes remains open and is supported by every
complete sum evaluated here.  The exact full binary Gram is a finite
positive-definite certificate, not a cutoff-independent contraction or a
continuum-gap estimate.  This also does **not** refute reflection
positivity of the original lattice gauge measure: a signed character
coefficient is not the same object as a reflected Gram quadratic.  It does
refute any CD-2 strategy that requires every resolved fixed-face amplitude or
recoupling channel to be nonnegative.  CD-2 must keep a complete reflected
channel sum and an explicit signed overlap ledger; none of the positive
subclasses above yet supplies the normalized block pushforward or overlap
remainder required for closure.
