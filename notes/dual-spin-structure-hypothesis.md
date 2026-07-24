# Dual sign geometry: the spin-structure hypothesis

**Date:** 2026-07-23
**Executable algebra:** `computations/four_strand_crossing_kernel.py`
**Regression pins:** `tests/test_four_strand_crossing_kernel.py`

## Exact result on the four-cube

Each of the six cancellation-requiring binary-pair orbits has a coordinate
Clifford torus as symmetric difference.  Its overlap plaquettes lie in two
complementary coordinate-plane families and have interaction graph

\[
  K_{2,2},\qquad K_{2,4},\qquad\text{or}\qquad K_{4,4}.
\]

For a resolved zero/triplet channel assignment
\(x\in\mathbf F_2^{m+n}\), the exact channel weight is

\[
 A_x=2^{-16}\prod_{ij\in E(K_{m,n})}W_{x_i x_j},
 \qquad
 W=\begin{pmatrix}1&1\\1&-1/3\end{pmatrix}.
\]

Therefore its sign is

\[
 \operatorname{sgn}(A_x)=(-1)^{q(x)},\qquad
 q(x)=\sum_{ij\in E(K_{m,n})}x_ix_j.
\]

Writing

\[
 a(x)=\sum_{i\in L}x_i,\qquad
 b(x)=\sum_{j\in R}x_j
 \quad\text{in }\mathbf F_2,
\]

gives the exact reduction

\[
 q(x)=a(x)b(x).
\]

All redistributions within one plane family lie in the radical.  The sign
therefore descends to the two-dimensional quotient with coordinates
\((a,b)\).  Its polarization is

\[
 B(x,y)=q(x+y)+q(x)+q(y)
       =a(x)b(y)+b(x)a(y),
\]

the standard nondegenerate alternating form on a hyperbolic
\(\mathbf F_2\)-plane.  Algebraically, \(q(a,b)=ab\) is its even quadratic
refinement.

The geometric identification is now exact on the six orbits, not just
suggestive.  If the complementary overlap planes are \(A\) and \(B\), the
symmetric-difference mask is exactly

\[
 T_{A,B}=\partial I_A^2\times\partial I_B^2.
\]

Its cellular mod-two Betti numbers are \((b_0,b_1,b_2)=(1,2,1)\).  The
boundary of every overlap plaquette parallel to \(A\) is the class
\((1,0)\), and every one parallel to \(B\) is \((0,1)\), in the product
basis of \(H_1(T_{A,B};\mathbf F_2)\).  Every complementary pair of these
representative cycles meets in exactly one vertex.  Consequently the
computed polarization \(B\) is precisely their mod-two geometric
intersection form.  The product basis is canonical from the coordinate
plane split, up to its harmless exchange.

There is also a coordinate-free formulation of the carrier.  If \(D_x\) is
the mod-two 2-chain of overlap plaquettes selected into the triplet channel,
then its edge boundary lies on the symmetric-difference surface \(T\), and
the exact sign law is

\[
 \operatorname{sgn}(A_x)
 =(-1)^{q_T([\partial D_x])}.
\]

The tests reduce actual edge-chain boundaries modulo the span of the 16
torus-face boundaries.  Every two selections with the same plane parities
give the same class in \(H_1(T;\mathbf F_2)\), and the sign depends only on
that class.  This is the first coordinate-independent form of the candidate:
the channel data enter through the homology class of the boundary of their
selected overlap 2-chain.

The regression suite checks this geometry, the sign formula, and the
polarization on every channel of all three crossing graphs.

## Four-sector resummation

Let \(Z_{ab}\) be the sum of the positive channel magnitudes with plane
parities \((a,b)\).  Then

\[
 Z=Z_{00}+Z_{01}+Z_{10}-Z_{11}.
\]

For \(K_{2,2}\), the exact sector ledger is

\[
 (Z_{00},Z_{01},Z_{10},Z_{11})
 =\left(\frac{244}{81},\frac{20}{9},
        \frac{20}{9},\frac43\right),
\]

so \(Z=496/81\), and the physical normalization gives
\(2^{-16}Z=31/331776\).  Exact four-sector ledgers are also pinned for
\(K_{2,4}\) and \(K_{4,4}\), and they resume to the previously proved
positive binomial formula.

Thus positivity is not obtained by deleting the negative sector.
It follows because the complete physical fusion sum supplies positive
sector magnitudes whose untwisted quadratic-refinement combination remains
positive.

The full torus transform is now also exact.  For
\(\alpha,\beta\in\mathbf F_2\), define

\[
 P_{\alpha\beta}
 =\sum_{a,b\in\mathbf F_2}
   (-1)^{ab+\alpha a+\beta b}Z_{ab}.
\]

These are the four quadratic refinements of the same polarization, with

\[
 \operatorname{Arf}(ab+\alpha a+\beta b)=\alpha\beta.
\]

The regression pins all four \(P_{\alpha\beta}\) on every crossing graph
and verifies the character identity

\[
 \frac12\sum_{\alpha,\beta}
 (-1)^{\alpha\beta}P_{\alpha\beta}
 =\sum_{a,b}Z_{ab}.
\]

This distinction matters.  The Arf-weighted half-sum reconstructs the
**unsigned magnitude ledger**.  The physical SU(2) amplitude computed here
is the single untwisted sector \(P_{00}\).  The transform therefore gives an
exact topological Fourier organization of the signs, but does not by itself
prove positivity of the physical amplitude.

## What an orientation can and cannot do

A change of discrete orientation/spin structure changes a quadratic
refinement by a linear form.  It cannot change the polarization \(B\).
Here \(B\ne0\): if \(e_L,e_R\) are the two parity generators, then

\[
 q(e_L)=q(e_R)=0,\qquad q(e_L+e_R)=1.
\]

Consequently no single linear channel rephasing can make every resolved
sign positive.  It can only redistribute the negative parity sectors.  The
three even refinements have one negative sector, while the odd refinement
has three.  This is the torus rather than planar situation: one should
expect controlled four-sector bookkeeping, not one globally positive
Pfaffian chart.

This matches the established two-dimensional picture.  Kasteleyn
orientations on a genus-\(g\) surface form the discrete spin structures,
and the dimer/Ising partition function uses \(2^{2g}\) Pfaffian or Kac--Ward
sectors with Arf coefficients:

* <https://arxiv.org/abs/math-ph/0608070>
* <https://arxiv.org/abs/0704.0273>
* <https://arxiv.org/abs/1101.5559>

The analogy is structural, not yet a reduction of SU(2) Yang--Mills to free
fermions.  The positive magnitudes contain \(1/3\) recoupling weights and,
beyond the four-cube, general \(6j\)/higher-intertwiner data.  No Pfaffian or
Kac--Ward determinant for the physical gauge-dual amplitude has been
constructed.

## Exhaustive cutoff-two reachability audit

The 33 negative fixed-face orbits do not all test this two-surface
spin-structure mechanism.  An encoding \((o,t)\), with odd-label mask \(o\)
and label-two mask \(t\), occurs in a binary-pair fusion ledger exactly when
there are closed binary surfaces \(L,R\) with

\[
 L+R=o,\qquad t\subseteq L\cap R.
\]

The exact audit gives:

* only 3 of the 33 negative orbits are binary-pair reachable, accounting
  for 192 of the 6,704 negative raw assignments;
* their representatives are
  `(0x6f6d9e, 0x21)`, `(0x6f6d9e, 0x261)`, and
  `(0x6f6d9e, 0x108261)`;
* every one has the same coordinate-Clifford-torus odd support and has odd
  selected-channel parity in both complementary plane families, hence
  \(q=ab=1\);
* the other 30 negative orbits, accounting for 6,512 raw assignments, are
  not reachable from two binary surfaces.  Their odd supports are
  Euler-characteristic-two spheres with 10, 12, or 14 faces.

Thus the quadratic-refinement law captures **every negative fixed-face
orbit that can actually enter the binary-pair fusion problem**.  It says
nothing yet about the remaining sphere-supported assignments; those belong
to a wider multi-surface/higher-label sign problem and cannot be counted as
failures of the torus law.

## First relative gluing theorem

The first two-cell gate is now closed on the clean product-torus family.
The `2 x 1 x 1 x 1` brick has three transverse-axis-related 24-face tori
which span both four-cubes and avoid the six plaquettes in their shared
three-face.  Each torus splits into two 12-face cylinders, with cellular
Betti numbers

\[
 (1,2,1)\longrightarrow (1,1,0)\cup(1,1,0).
\]

A representative physical surface pair has six raw overlap plaquettes.
Four of them form two two-plaquette strips crossing the interface; the other
two are one-plaquette caps.  If \(D_x\) is an arbitrary raw selected overlap
chain, define its relative interface defect by

\[
 \delta(x)=\partial D_x\pmod{C_1(T;\mathbf F_2)}.
\]

This defect is supported entirely in the shared three-face.  Exhaustively,

\[
 \operatorname{Inv}_{SU(2)}(x)\ne0
 \quad\Longleftrightarrow\quad
 \delta(x)=0.
\]

Thus the 64 raw plaquette selections reduce to exactly 16 admissible
selections.  The two halves of each spanning strip have the same nonzero
interface defect, so they must be selected together and their defects
cancel.  The 16 survivors are precisely the unions of four global caps.
Their boundary classes form two homologous pairs in
\(H_1(T;\mathbf F_2)\), and the cap-intersection graph is again
\(K_{2,2}\).

Subdivision introduces no new sign.  Schur convolution contributes one
positive factor \(1/\dim(2)=1/3\) for each selected two-face strip.  With the
two strip caps indexed first, the exact channel law is

\[
 A_x
 =2^{-24}\,3^{-(x_1+x_2)}
   \prod_{ij\in E(K_{2,2})}W_{x_i x_j},
 \qquad
 W=\begin{pmatrix}1&1\\1&-1/3\end{pmatrix}.
\]

Consequently the sign still factors through the global class
\([\partial D_x]\):

\[
 \operatorname{sgn}(A_x)=(-1)^{ab}.
\]

The complete glued ledger is

\[
 \begin{aligned}
 Z_{\rm glue}
 &=2^{-24}\sum_{r=0}^2 {2\choose r}3^{-r}
     \left(1+(-1/3)^r\right)^2 \\
 &=2^{-24}\frac{3232}{729}
 =\frac{101}{382205952}>0.
 \end{aligned}
\]

The generic quaternion-Haar integrator directly checks the vacuum, both
one-face caps, one spanning strip, and that strip with zero, one, or two
crossings.  The remaining entries follow from transverse reflection and the
exact character-convolution identity.  All three spanning-torus
orientations are one orbit under permutations of the transverse axes.

This closes relative gluing for a clean subdivided product torus: interface
matching projects out the half-cap sectors, and the surviving spin
structure acquires only positive propagation weights.  It does **not** yet
cover surfaces containing plaquettes in the shared three-face,
non-product topology, or the higher-valent invariant blocks of a general
four-dimensional brick.

The first interface-bearing torus immediately shows why that qualification
is essential.  There is an exact physical channel with

```text
surface           0x31ad1b6d9e
surface pair      0x10886c4055, 0x2125772dcb
selected overlap  0x240001
```

for which \(\partial D_x\) has one uncancelled interface edge outside the
torus.  Nevertheless three doubled-label-two faces meet there, and

\[
 \dim\operatorname{Inv}(V_1\otimes V_1\otimes V_1)=1.
\]

Every edge invariant is admissible and the complete exact Haar amplitude of
this resolved channel is

\[
 \frac{1}{18874368}>0.
\]

Thus the clean-family equivalence

\[
 \text{admissible}\Longleftrightarrow\delta(x)=0
\]

fails as soon as an interface three-strand branch is available.  This is an
exact obstruction to extending the carrier as ordinary mod-two homology
alone.  It is not a negative-amplitude obstruction and does not refute the
quadratic law on cycle sectors.  It says the global carrier must be enlarged
from \(H_1(T;\mathbf F_2)\) to a **decorated relative spin network** which
retains trivalent invariant vertices; the ordinary spin-structure sector is
its branch-free subspace.

### The first decorated interface ledger

The required carrier has now been constructed exactly on this first
interface-bearing orbit.  At each edge in the shared three-face it records

1. the literal incident face strands, doubled-spin labels, and orientations;
2. the relative mod-two boundary defect; and
3. every path in a canonical left-associated fusion tree which ends in the
   trivial representation.

The last item is essential.  The same five-face overlap ledger contains both
the trivalent packet

\[
 \dim\operatorname{Inv}(V_1^{\otimes 3})=1
\]

with nonzero relative defect and a defect-free four-valent packet

\[
 \dim\operatorname{Inv}(V_1^{\otimes 4})=3.
\]

It also contains mixed interface packets with invariant dimension two.
Consequently neither the defect chain nor the strand valence alone is a
complete gluing state.

All \(2^5=32\) overlap choices have now been classified and the admissible
ones evaluated by the generic exact Haar integrator.  Eight choices have a
zero edge-invariant space.  The remaining 24 are all strictly positive, with
exact census

\[
\begin{array}{c|c}
\text{multiplicity} & \text{amplitude}\\ \hline
2  & 2^{-22}\\
12 & (3\cdot 2^{22})^{-1}\\
8  & (9\cdot 2^{21})^{-1}\\
2  & 7/(27\cdot 2^{22}).
\end{array}
\]

Their sum is

\[
 Z_{\mathrm{branched}}=\frac{7}{3538944}
 =2^{-22}\frac{224}{27}>0.
\]

An independent integral of the two unfused fundamental surface observables
gives the same rational exactly, so the channel ledger is complete.  The
pinned obstruction and its five-face ledger generate a six-element orbit
under permutations of the three transverse axes.

This closes construction and sign testing of the decorated carrier on the
first interface-bearing symmetry orbit.  It does not prove that every
decorated carrier has positive contraction, nor that its possible signs are
still governed by a quadratic refinement.  The next falsification gate is
the orbit census over all interface-bearing genus-one surface pairs in the
two-cell brick, with the fusion-tree packet retained rather than projected
to mod-two homology.

## Higher-dimensional status

It would be too strong to say that spin-structure technology has literally
never appeared beyond two dimensions.  Higher-dimensional bosonization and
Wu-structure state sums use quadratic refinements and higher-form
intersection pairings:

* <https://arxiv.org/abs/1607.01396>
* <https://arxiv.org/abs/2508.20167>

What is absent from the cited exact non-Abelian lattice duality and explicit
four-dimensional SU(2) vertex-amplitude work is a demonstrated
spin/Wu-structure organization of the physical Yang--Mills dual signs:

* <https://arxiv.org/abs/hep-th/0008095>
* <https://arxiv.org/abs/0808.3624>

The present computation supplies a concrete candidate for that missing
bridge on the smallest signed physical family.

## Falsifiable extension program

The hypothesis to test is:

> On a complete physical SU(2) surface/fusion complex, the parity of the
> resolved recoupling sign descends, after radical directions are quotiented,
> to a quadratic refinement of a mod-two intersection pairing carried by the
> physical surface complex.

The next gates are:

1. **Geometric semantic bridge.**  **DONE on the six four-cube orbits and
   the first clean two-cell gluing.**
   The two plane parities are the product basis of
   \(H_1(T^2;\mathbf F_2)\), and the computed polarization is their
   geometric intersection form.  The coordinate-free local carrier is
   \([\partial D_x]\in H_1(T;\mathbf F_2)\).  On the clean spanning torus,
   the relative interface defect vanishes exactly on the admissible
   channels and the two cylinder classes glue correctly.  **OPEN
   generally:** include interface plaquettes and non-product surface
   patches.
2. **Orientation covariance.**  **DONE locally.**  All four shifts
   \(q\mapsto q+\ell\) and their Arf coefficients are exact and
   regression-pinned.  **OPEN globally:** determine whether these shifts
   arise from actual orientation/spin-structure changes under physical
   four-cube gluing.
3. **Gluing law.**  **DONE for the clean subdivided product torus.**
   Relative-defect cancellation, global \(H_1\) recovery, the unchanged
   quadratic refinement, and the positive \(1/3\) subdivision weights are
   exact.  **FIRST GENERALIZATION OBSTRUCTION FOUND:** an interface-bearing
   torus admits a three-spin-one branch with nonzero mod-two boundary defect
   but a one-dimensional SU(2) invariant.  **DONE on the first branched
   orbit:** the decorated carrier retains oriented strands and a complete
   fusion-tree basis; all 24 admissible channels are exactly positive and
   resum to the unfused pair amplitude.  **OPEN next:** classify every
   interface-bearing genus-one pair orbit and determine whether a universal
   decorated sign law survives.
4. **Negative-orbit audit.**  **DONE for binary-pair reachability.**  Exactly
   3 of 33 negative orbits enter this lane, and all three obey \(q=ab=1\).
   **OPEN beyond this lane:** determine the appropriate carrier for the 30
   sphere-supported orbits under complete multi-surface/higher-label fusion.
5. **Higher-valent audit.**  Carry the parity quotient through the
   factorized six-valent invariant block.  Do not infer it from expanded
   quaternion signs.
6. **Physical-sector resummation.**  Seek a Gram/Pfaffian-like
   representation of the *untwisted* physical sector \(P_{00}\).  The
   Arf-weighted combination instead reconstructs the unsigned ledger, so it
   cannot be substituted for the physical SU(2) amplitude.

Either result is useful.  Successful gluing would turn the apparent
recoupling sign problem into finite topological sector bookkeeping.  Failure
would locate the first genuinely non-spin-structural SU(2) sign and provide
the exact coordinate where a different mechanism is required.

## Program boundary

Even a complete proof of this hypothesis would establish sign organization,
not RG contraction.  It supplies no cutoff-independent norm, ultraviolet
landing theorem, summable distortion estimate, or continuum-gap survival.
It is a candidate construction of the arena floor under (DP), not progress
through RG-I7--RG-I9.
