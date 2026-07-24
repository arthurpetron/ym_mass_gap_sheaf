# BF1.5 — Intertwiner-resolved three-strand pushforward

**Date:** 2026-07-24  
**Disposition:** closed by an exact negative reflection-carrier certificate

## Result

BF1.5 has a decisive outcome.

The minimal genuinely four-dimensional three-strand sector is positive and
coherent before reflection:

- its direct unfused Haar amplitude equals both explicit left- and
  right-associated fusion-path sums;
- the signed Racah change of basis is exactly orthogonal;
- its complete physical heat activity is coefficientwise positive; and
- its path-to-channel unnormalized Haar pushforward is explicit and has zero
  residual outside the selected fusion carrier.

But the one-sided reflected Gram form on the closed full-slab surface
generators is not positive semidefinite.  Its first negative leading
principal minor is

\[
  \det G_{\{1,O_1,O_2\}}=-\frac1{65536}.
\]

This is not a counterexample to Osterwalder--Schrader reflection positivity.
The \(O_i\) are closed surfaces crossing both halves of the slab, not
observables supported in the positive-time half.  It is instead a carrier
obstruction: closed full-slab strands, even when enriched by all their
fusion paths and edge invariant indices, are not the reflection-positive
boundary cone needed by BF2/BF3.  The next carrier must contain open
half-surfaces and the intertwiner data exposed where they meet the reflection
cut.

## 1. Minimal sector

The unit four-cube has 128 mod-two closed surfaces including the vacuum.  The
search examines triples of distinct nonempty surfaces and requires:

1. a triple-occupied face, so
   \(\chi_{1}^{3}=2\chi_1+\chi_3\) has a genuine path multiplicity;
2. use of all six coordinate two-planes, excluding a coordinate
   three-dimensional reduction;
3. minimum total strand area, then minimum union area, then minimum sorted
   area profile.

There are 192 co-minimizers.  The lexicographically first is

\[
  (0x8938,\;0x4220b,\;0x8c96d),
\]

with strand areas \((6,6,10)\), total area \(22\), and union area \(15\).
After embedding in the extent-one corrected slab, its face occupancy census
is

\[
  N_0=57,\qquad N_1=9,\qquad N_2=5,\qquad N_3=1.
\]

At the slab edges, the number of fundamental legs is distributed as

\[
  n_0=91,\qquad n_2=10,\qquad n_4=11,\qquad n_6=4.
\]

Consequently the invariant-space dimensions are \(1\) on 101 edges, \(2\)
on 11 edges, and \(5\) on four edges.  This is the first selected sector in
which an edge multiplicity count is visibly not an intertwiner basis.

## 2. Intertwiner-resolved carrier

`computations/intertwiner_resolved_carrier.py` retains:

- each oriented strand incidence at each corrected-slab edge;
- a deterministic left- or right-associated fusion path on every face;
- every sequential invariant path at every edge;
- the classical \(SU(2)\) exchange signs for two fundamentals; and
- exact signed quadratic-radical Racah matrices.

For three fundamentals with total doubled spin one, the exact change of
association is

\[
 F_{1/2}=
 \begin{pmatrix}
 -\frac12 & \frac{\sqrt3}{2}\\[2mm]
 \frac{\sqrt3}{2} & \frac12
 \end{pmatrix},
 \qquad
 F_{1/2}F_{1/2}^{\mathsf T}=I.
\]

For total doubled spin three, \(F_{3/2}=(1)\).  The two-fundamental exchange
phases are \(-1\) in the singlet and \(+1\) in the triplet.  Forgetting the
explicit face paths produces exactly the prior fusion ledger: 96 paths over
64 output assignments.

## 3. Haar and heat certificates

The exact direct unfused corrected-slab integral is

\[
  A_{\mathrm{direct}}=\frac{83}{5184}.
\]

Summing all 96 explicit left-associated paths and summing all 96 explicit
right-associated paths give the same value:

\[
  A_{\mathrm{direct}}
  =A_{\mathrm{left}}
  =A_{\mathrm{right}}
  =\frac{83}{5184}.
\]

All 64 fixed output channels in this sector are nonnegative.  In the
repository heat coordinate \(s\), the complete activity is

\[
  8s^{30}+24s^{38}+24s^{62}+8s^{70}+32s^{82},
\]

so it is strictly positive on \(0<s<1\).  Both fusion associations resum to
this identical polynomial.

This is a finite-sector theorem.  It does not prove dual positivity for
arbitrary corrected slabs or arbitrary labels.

## 4. Exact reflected obstruction

Let the generator packet be \((1,O_1,O_2,O_3)\), and let \(\theta\) be the
corrected-slab time involution.  The one-sided candidate reflection form

\[
  G_{ij}=\int \theta(O_i)\,O_j\,d\mu_{\mathrm{Haar}}
\]

is

\[
G=
\begin{pmatrix}
1 & \frac1{16} & \frac1{16} & \frac1{256}\\
\frac1{16} & \frac{82}{81} & \frac1{128} & \frac{41}{648}\\
\frac1{16} & \frac1{128} & \frac1{256} & \frac1{768}\\
\frac1{256} & \frac{41}{648} & \frac1{768} & \frac{6562}{6561}
\end{pmatrix}.
\]

Its leading principal minors begin

\[
  1,\qquad \frac{20911}{20736},\qquad -\frac1{65536}.
\]

The exact unpivoted \(LDL^{\mathsf T}\) diagonal begins

\[
  1,\qquad \frac{20911}{20736},\qquad
  -\frac{81}{5353216}.
\]

Thus the form is not PSD.  The failure is conceptually diagnostic:
reflection positivity applies to a positive-half algebra, while a nontrivial
closed surface generally straddles the reflection cut.  The scalar
closed-surface carrier erased precisely the open boundary legs required to
state the correct half-slab Gram theorem.

## 5. Unnormalized Haar pushforward seed

For completeness, the selected local fusion-block transport is also
explicit.  The fine carrier consists of the 96 face fusion-path assignments.
The coarse map forgets intermediate paths but retains all 64 physical
face-spin outputs.  Each coarse fiber is listed by its fine path indices.
After all corrected-slab links are Haar integrated, the unnormalized coarse
weight includes the exact channel amplitude, fusion multiplicity, dimensions,
and Casimir heat exponent.

The total mass is exactly

\[
  8s^{30}+24s^{38}+24s^{62}+8s^{70}+32s^{82}.
\]

The corrected-slab reflection involution transports all 64 fibers and
weights exactly, and the literal residual outside this selected fusion
carrier is zero.

This map is a fusion-block pushforward, not yet a lattice-spacing-changing
RG block map.  It supplies the algebraic seed requested by BF1.5 but does not
close BF3.

## 6. Gate accounting

| BF1.5 clause | Outcome |
|---|---|
| Intertwiner-resolved carrier | complete |
| Minimal genuinely 4D multiplicity sector | complete |
| Direct Haar = coherent left/right path sums | complete |
| Exact signed basis/coherence audit | complete |
| Complete heat activity | positive |
| Reflected Gram/SOS test | **negative exact minor** |
| Unnormalized path-to-channel pushforward | complete |
| Geometric scale-changing physical pushforward | not claimed |

BF1.5 therefore closes through its negative route.  The result changes the
next action rather than the program's final status.

## 7. Next milestone: BF1.6

Construct the reflection-cut carrier:

1. split every selected closed strand into positive- and negative-half open
   surface packets;
2. record oriented cut loops and an orthonormal cut-edge intertwiner basis;
3. define reflection as an antilinear map between the two half-carriers;
4. reconstruct each closed BF1.5 state by gluing its two halves and summing
   the shared cut indices;
5. reproduce the corrected-slab physical reflected kernel as a Gram matrix
   on this half-carrier;
6. obtain an exact PSD/SOS factorization for the minimal three-strand packet
   or isolate the next missing datum;
7. carry the half-carrier through one actual spacing-changing unnormalized
   Haar block pushforward.

Only after that gate should the project attempt the general positive cone
and its Birkhoff projective-diameter bound.

## Reproduction

The executable certificate is exposed by
`computations.three_strand_corrected_slab.bf15_certificate()`.  Regression
pins are in:

- `tests/test_intertwiner_resolved_carrier.py`;
- `tests/test_three_strand_corrected_slab.py`.

