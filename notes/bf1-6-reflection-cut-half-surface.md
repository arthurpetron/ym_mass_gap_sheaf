# BF1.6 — Reflection-cut half-surface carrier

**Date:** 2026-07-24  
**Disposition:** positive exit on the selected finite \(SU(2)\) sector

## Result

BF1.6 repairs the exact obstruction found by BF1.5.

The closed BF1.5 surfaces are cut at time \(1/2\) into positive- and
negative-half packets.  The cut carrier retains:

- every lower, fixed-cut, and upper face occurrence;
- each oriented cut segment;
- each canonical cut loop;
- a canonical orthonormal fusion-path index at every cut vertex;
- exact reflection transport on those indices; and
- the signed \(F/R\) data required to change the canonical ordering or
  association.

The complete BF1.5 amplitude is reconstructed from the resulting exact
half-boundary tensors.  The first nontrivial two-state half-carrier Gram is
positive definite with an explicit rational \(LDL^{\mathsf T}\) sum of
squares.  Finally, a literal \(2\times2\) spatial Haar block embedded in the
extent-three corrected slab changes the lattice spacing by two and remains
inside the cutoff-two half-surface carrier with zero remainder.

This is a finite selected-sector result.  It does not prove general dual
positivity, a cutoff-uniform cone theorem, or a physical RG contraction.

## 1. The cut geometry

Write the three raw unit-four-cube masks as

\[
 S_1=0x8938,\qquad S_2=0x4220b,\qquad S_3=0x8c96d.
\]

Reflection across time \(1/2\) fixes \(S_1\) and \(S_3\).  The sphere \(S_2\)
lies entirely in the lower slice and is sent to

\[
 \theta S_2=0x2111c0.
\]

The lower/fixed/upper face counts are

\[
\begin{array}{c|ccc}
 & \text{lower} & \text{cut} & \text{upper}\\ \hline
S_1&1&4&1\\
S_2&6&0&0\\
S_3&2&6&2.
\end{array}
\]

A temporal plaquette intersects the reflection plane in a spatial segment.
The ten temporal strand occurrences form two canonical cut loops:

- a four-edge loop from \(S_1\);
- a six-edge loop from \(S_3\).

Their union has six cut vertices.  Four vertices carry four fundamental
legs, so

\[
 \dim\operatorname{Inv}\bigl((\tfrac12)^{\otimes4}\bigr)=2.
\]

The remaining two vertices are bivalent and have a one-dimensional
invariant space.  The full canonical boundary-index space therefore has
dimension

\[
 2^4=16.
\]

Reflection fixes the cut graph pointwise and pairs each oriented leg with
its dual.  In the canonical invariant bases its transport matrix is the
identity.  Changes of tree and ordering use the exact signed matrices from
BF1.5, including

\[
F=
\begin{pmatrix}
-\frac12&\frac{\sqrt3}{2}\\
\frac{\sqrt3}{2}&\frac12
\end{pmatrix},
\qquad FF^{\mathsf T}=I,
\]

and the fundamental exchange phases \((-1,+1)\) on the singlet/triplet
channels.

## 2. Exact half-tensor reconstruction

Temporal gauge sets the eight links crossing the cut to the identity.  A
fundamental temporal plaquette then has the exact real Peter--Weyl split

\[
 \chi_1(g_-g_+^{-1})
 =2\sum_{\mu=0}^{3}(g_-)_\mu(g_+)_\mu .
\]

The executable certificate verifies this as equality of quaternion
coordinate polynomials, not numerically.

A deterministic spanning tree is then fixed in the lower spatial cube.
After exact Haar integration:

- the BF1.5 family has ten boundary legs;
- the lower feature tensor has ten nonzero component words;
- the reflected upper tensor has 194,560 nonzero component words;
- exactly ten words overlap; and
- their weighted coefficient pairing is

\[
 \frac{83}{5184}.
\]

This agrees both with a direct temporal-gauge contraction and with the
original gauge-fixed BF1.5 Haar integral:

\[
 A_{\rm half\ glue}
 =A_{\rm temporal\ gauge}
 =A_{\rm direct}
 =\frac{83}{5184}.
\]

The three individual closed strands reconstruct to

\[
 A(S_1)=\frac1{16},\qquad
 A(S_2)=\frac1{16},\qquad
 A(S_3)=\frac1{256},
\]

and the common-boundary packet \(P_{13}\) made from the \(S_1,S_3\) halves
has norm

\[
 \langle P_{13},P_{13}\rangle=\frac{41}{648}.
\]

## 3. The physical half-carrier Gram

Use the two positive-half states

\[
 e_0=P_{13},\qquad e_1=S_2P_{13}.
\]

The upper partner of \(S_2\) is \(\theta S_2\).  Complete fusion-path
resummation with the exact four-cube vertex \(6j\) amplitudes gives

\[
G=
\begin{pmatrix}
\frac{41}{648}&\frac{83}{5184}\\[1mm]
\frac{83}{5184}&\frac{85}{20736}
\end{pmatrix}.
\]

The off-diagonal entry is precisely the BF1.5 three-strand amplitude.  The
determinant is

\[
 \det G=\frac1{331776}>0.
\]

More explicitly,

\[
G=L\,D\,L^{\mathsf T},
\qquad
L=
\begin{pmatrix}
1&0\\
\frac{83}{328}&1
\end{pmatrix},
\qquad
D=
\begin{pmatrix}
\frac{41}{648}&0\\
0&\frac1{20992}
\end{pmatrix}.
\]

Thus for rational \(x,y\),

\[
\begin{pmatrix}x&y\end{pmatrix}
G
\begin{pmatrix}x\\y\end{pmatrix}
=
\frac{41}{648}
  \left(x+\frac{83}{328}y\right)^2
+\frac1{20992}y^2\ge0.
\]

This is the sought finite reflected Gram/SOS certificate.  It also explains
the BF1.5 negative minor: the closed full-slab observables used there were
not elements of this positive-half algebra.

## 4. A genuine spacing-changing Haar pushforward

Four fine plaquettes in a \(2\times2\) spatial disk are embedded in the
lower half of the extent-three corrected slab.  Their reflected partners
are the corresponding four upper faces.  The eight-link boundary is treated
as one coarse loop, so the block changes lattice spacing by a factor of two.

At cutoff two, every internal disk link is Haar integrated exactly.  The
coarse character projections are

\[
\begin{array}{c|c}
\text{coarse doubled label}&\text{unnormalized mode}\\ \hline
0&1\\
1&2s^{12}\\
2&3s^{32}.
\end{array}
\]

This is the exact four-time heat-kernel semigroup.  The coarse intertwiner
transport is label preserving:

\[
0\mapsto0,\qquad1\mapsto1,\qquad2\mapsto2.
\]

The Haar total mass is \(1\).  At the identity the unnormalized activity is

\[
 1+4s^{12}+9s^{32}.
\]

Projections to labels three and four vanish exactly, so the literal
remainder outside the selected cutoff-two carrier is zero.

The label-two output is important.  A fundamental-only half-carrier would
already fail this first spacing-changing block.  BF1.6 therefore closes on
the fusion-closed cutoff-two carrier, not on the original binary-only
packet.

## 5. Gate accounting

| BF1.6 clause | Outcome |
|---|---|
| Split all three BF1.5 strands | complete |
| Canonical open boundaries and oriented loops | complete |
| Cut-edge invariant basis indices | complete; boundary dimension 16 |
| Reflection and signed \(F/R\) transport | complete |
| Recover BF1.5 Haar amplitudes | complete |
| Exact physical half-carrier Gram/SOS | positive definite |
| Actual spacing-changing Haar block | complete |
| Coarse mass and intertwiner map | explicit |
| Outside-carrier remainder | exactly zero at cutoff two |

BF1.6 therefore has a positive exit on its selected finite sector.

## 6. What remains

The result does **not** establish:

- (DP) for every physical \(SU(2)\) complex;
- positivity for all labels or all corrected-slab boundary packets;
- closure uniformly in cutoff or volume;
- the full plaquette-coupled Gibbs pushforward on a general block;
- a finite projective diameter or Birkhoff contraction;
- RG-I7--I9;
- continuum construction, OS reconstruction, or the mass gap.

The next gate is BF2.1: replace this selected 16-dimensional boundary packet
by the general fusion-closed reflection-cut carrier.  Its first exact tasks
are to enumerate all cut signatures at the next label/cell cutoff, construct
their weighted Gram blocks, and decide whether every complete physical
activity is nonnegative after coherent grouping.

## Reproduction

The executable artifacts are:

- `computations/reflection_cut_half_surface.py`;
- `computations/reflection_cut_haar_block.py`;
- `tests/test_reflection_cut_half_surface.py`;
- `tests/test_reflection_cut_haar_block.py`.

The combined certificate is
`computations.reflection_cut_haar_block.bf16_certificate()`.

