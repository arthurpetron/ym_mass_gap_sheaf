# BF3.1: whole corrected-slab Kraus kernel

Date: 2026-07-25

Status: **closed at physical representation cutoff one**.  The all-label
kernel and a vanishing, cutoff-uniform remainder estimate are BF3.2.

## 1. Scope and result

BF1.6 integrated one isolated \(2\times2\) disk.  BF2.1 identified the
positive carrier as the PSD cone of complete reflected boundary kernels.
BF3.1 now constructs the smallest whole corrected slab containing that disk
and carries its physical cutoff-one Haar law into the spacing-two coarse
Wilson basis.

The result has four layers.

1. The complete cutoff-one reflected kernel is an explicit direct sum of 32
   rank-one Kraus blocks.
2. Its unnormalized mass is computed independently from every closed binary
   surface and from the Kraus blocks.
3. Every one of the 512 binary spacing-two coarse Wilson words has an exact
   finite definition as a sum over its complete 128-state affine Haar fibre.
4. The first non-vacuum coarse mode is evaluated completely.  It has a
   literal nonzero coherent remainder after normalization, so the isolated
   BF1.6 zero remainder does not survive the whole slab.

The implementation retains all four \(P/Q\) blocks.  It also proves that no
finite representation cutoff is invariant under the full heat-kernel
factor: \(P\Phi Q\) and \(Q\Phi P\) have explicit positive leading terms.

This is a finite-cutoff construction theorem, not an RG estimate.  No
cutoff-uniform remainder norm, contraction, landing theorem, or continuum
claim is made.

## 2. Whole corrected-slab geometry

The smallest slab has extent one and contains:

| datum | exact count |
|---|---:|
| plaquettes | 72 |
| lower spatial plaquettes | 24 |
| temporal plaquettes | 24 |
| upper spatial plaquettes | 24 |
| links | 116 |
| links after maximal-tree gauge fixing | 65 |
| spacing-two coarse Wilson faces | 9 |

The six spatial coarse loops have length eight; the three temporal loops
have length six.  The slab reflection is an exact involution.

Although there are \(2^{72}\) formal binary face words, edge Haar
admissibility has rank seven.  Therefore the complete physical cutoff-one
closed sector has only

\[
 2^7=128
\]

assignments.  Their union uses exactly 24 of the 72 fine plaquettes: the
embedded boundary two-skeleton of the central unit four-cube.  The other
fine plaquettes become active when coarse Wilson boundaries are inserted,
which is why they cannot be removed from the pushforward geometry.

## 3. Exact reflected Kraus kernel

Cutting the 128 closed binary assignments at half time gives 32 cut
signatures and two lower fillings for each signature.  For one signature
\(\gamma\), let \(x_0^\gamma,x_1^\gamma\) be its fillings and define

\[
 K^\gamma_{ab}(s)
 =
 2^{F(x_a\#_\gamma x_b)}
 s^{3F(x_a\#_\gamma x_b)}
 A(x_a\#_\gamma x_b).
\]

Here \(A\) is the exact unfused Haar amplitude.  Every block factors as

\[
 K^\gamma(s)=v_\gamma(s)v_\gamma(s)^{\mathsf T}
\]

with an exact integral-monomial vector.  The vector census is:

| vector \(v_\gamma\) | multiplicity |
|---|---:|
| \((1,4s^{18})\) | 1 |
| \((2s^9,2s^{21})\) | 5 |
| \((2s^{15},2s^{21})\) | 8 |
| \((2s^{18},2s^{18})\) | 4 |
| \((4s^{18},s^{24})\) | 2 |
| \((2s^{21},2s^9)\) | 1 |
| \((2s^{21},2s^{15})\) | 4 |
| \((2s^{21},2s^{21})\) | 6 |
| \((s^{24},4s^{18})\) | 1 |

Thus the complete boundary dimension is 64 and the Kraus rank is 32.
Reflection transposes each block and leaves it unchanged.

Summing all matrix entries gives

\[
 Z_1(s)
 =
 1+32s^{18}+96s^{30}+224s^{36}+192s^{42}+3s^{48}.
\]

An independent sum over all 128 closed surfaces, using their exact Haar
amplitudes, produces the same polynomial.  This is both the mass check and
the independent reconstruction required by the gate.

## 4. Complete spacing-two boundary fibres

The coarse cutoff-one boundary basis has nine binary Wilson-face
generators, hence 512 words.  For a coarse mask \(c\), its fine fillings
satisfy the exact mod-two equation

\[
 \partial f=\partial c.
\]

Every coarse word is solvable, and each solution set is an affine translate
of the rank-seven closed-surface kernel:

\[
 {\cal F}_c=f_c+Z_2,\qquad |{\cal F}_c|=128.
\]

The complete map therefore contains

\[
 512\times128=65536
\]

coherent Haar channels.  This is an executable finite definition:

\[
 M_c(s)
 =
 \sum_{f\in{\cal F}_c}
 2^{|f|}s^{3|f|}
 \int
 \left(\prod_{p\in f}\chi_1(U_p)\right)
 \left(\prod_{C\in c}\chi_1(U_{\partial C})\right)dU.
\]

`exact_coarse_face_mode(c)` evaluates this formula without replacing any
Haar projector by a product of invariant dimensions.

The boundary packets are genuinely intertwiner-bearing:

| maximum edge valence | channels |
|---:|---:|
| 0 | 1 |
| 2 | 1,420 |
| 4 | 31,731 |
| 6 | 32,384 |

Their largest local invariant-space dimensions are respectively 1, 2, and
5:

| maximum invariant dimension | channels |
|---:|---:|
| 1 | 1,421 |
| 2 | 31,731 |
| 5 | 32,384 |

There are 1,159 distinct edge-packet profiles.  Consequently the physical
pushforward cannot be reconstructed from parity, homology, or
multiplicity-free fusion alone.  The complete fusion paths are part of the
mode definition.

The missing ordering transport is also explicit.  In the canonical
sequential fusion bases, adjacent fundamental-leg swaps give one \(1\times1\)
matrix at valence two, three signed \(2\times2\) matrices at valence four,
and five signed \(5\times5\) matrices at valence six.  The nontrivial entries
include

\[
\begin{pmatrix}
\frac12&\frac{\sqrt3}{2}\\[2pt]
\frac{\sqrt3}{2}&-\frac12
\end{pmatrix},
\qquad
\begin{pmatrix}
\frac13&\frac{2\sqrt2}{3}\\[2pt]
\frac{2\sqrt2}{3}&-\frac13
\end{pmatrix}.
\]

Exact quadratic-radical arithmetic verifies every involution relation,
every adjacent braid relation, and every distant-swap commutation relation.
These generators transport any leg ordering, so the 65,536 fibres carry the
joint signed intertwiner map rather than only its dimension.

## 5. First actual whole-slab remainder

For the first lower spatial coarse face, the isolated BF1.6 disk gives

\[
 M_{\rm disk}(s)=2s^{12}.
\]

The complete 128-channel whole-slab Haar fibre gives

\[
\begin{aligned}
M_{\rm whole}(s)
={}&2s^{12}+4s^{24}+48s^{30}+20s^{36}\\
 &+176s^{42}+280s^{48}+177s^{54}+4s^{60}.
\end{aligned}
\]

The raw whole-slab correction is therefore

\[
4s^{24}+48s^{30}+20s^{36}+176s^{42}
+280s^{48}+177s^{54}+4s^{60}.
\]

The physical normalized coefficient is \(M_{\rm whole}/Z_1\).  Comparing it
with the naive spacing-two target \(2s^{12}\), the exact remainder is

\[
\frac{R_1(s)}{Z_1(s)}
\]

with numerator

\[
R_1(s)
=4s^{24}-16s^{30}+20s^{36}-16s^{42}
-168s^{48}-207s^{54}-2s^{60}.
\]

This sign-changing numerator is the first literal whole-slab physical
distortion in the corrected carrier.  Positivity of the reflected kernel
does not imply positivity of the RG remainder, and the BF1.6 zero remainder
was a property of the isolated disk rather than the whole law.

The vacuum mode satisfies

\[
M_0(s)=Z_1(s),
\qquad
M_0-Z_1=0,
\]

so normalization preserves total mass exactly.

## 6. Full \(P/Q\) coherence and finite-cutoff failure

Let \(P_N\) project onto boundary representations with doubled label at most
\(N\), and \(Q_N=1-P_N\).  One physical heat factor contains

\[
(N+2)s^{(N+1)(N+3)}\chi_{N+1}.
\]

Acting on the vacuum, this supplies the following exact leading terms:

\[
\begin{array}{c|c}
\text{block} & \text{leading term}\\
\hline
P\Phi P & 1\\
P\Phi Q & (N+2)s^{(N+1)(N+3)}\\
Q\Phi P & (N+2)s^{(N+1)(N+3)}\\
Q\Phi Q & (N+2)^2s^{2(N+1)(N+3)}.
\end{array}
\]

For cutoff one the outside label is two:

\[
P\Phi Q=3s^8+\cdots,\qquad
Q\Phi Q=9s^{16}+\cdots.
\]

Thus \(QK_rP\ne0\) for the exact heat law at every finite cutoff.  A finite
carrier compression is PSD, but it is not invariant.  Both off-diagonal
coherence blocks must ride in the BF3.2 remainder.

## 7. Relation to the older formal kernel

The repository already contains axiom-free Lean theorems defining a
cutoff-one normalized whole-slab conditional kernel and a zero-total,
\(L^1\le2\) remainder.  Those theorems are retained as valuable normalization
and finite-kernel scaffolding.

They are **not** used here as the exact Haar identification.  Their fine
summand is the product of heat coefficients and local invariant
multiplicities.  It does not contain the global coherent Haar contraction
computed above.  Promoting that surrogate would reintroduce simplifications
S01--S03 from the Simplification Ledger.

The exact physical object in BF3.1 is instead the affine-fibre Haar formula
`exact_coarse_face_mode`.  The old formal remainder norm does not bound this
new physical remainder.  Establishing such a norm is an explicit BF3.2
obligation.

## 8. Gate adjudication

| BF3.1 action | Result |
|---|---|
| complete fine/coarse bases | 128 fine closed states, 64 half states, 512 coarse Wilson words |
| exact physical half features | 32 monomial Kraus vectors |
| integrate internal Haar links | exact lazy 128-channel fibre for every coarse word; first non-vacuum word fully evaluated |
| mass and reflection | exact \(Z_1\), independent reconstruction, reflection symmetry |
| joint coarse intertwiners | signed \(1\times1\), \(2\times2\), and \(5\times5\) adjacent-swap generators satisfy all symmetric-group relations |
| all four \(P/Q\) blocks | explicit; both coherence blocks nonzero |
| finite-carrier closure | falsified for every cutoff by the label-\(N+1\) witness |
| independent reconstruction | direct 128-surface Haar sum equals the Kraus mass |

The milestone closes because the complete finite-cutoff map and its literal
remainder are now constructed.  It does not close the all-label or uniform
analytic problem.

## 9. What remains

The next milestone is **BF3.2: all-label kernel and vanishing remainder**:

1. replace the cutoff-one fibres by a summable all-label
   fusion/intertwiner field;
2. evaluate or bound every coherent \(P/Q\) block in one physical norm;
3. prove a cutoff- and volume-uniform tail modulus;
4. prove that the normalized physical remainder vanishes at the required
   scale, rather than merely having zero vacuum component;
5. only then pass the actual kernel to BF4's grouped projective diameter.

Nothing here proves BF4 contraction, BF5 graded stability, RG-I7--I9,
continuum existence, OS reconstruction, or a mass gap.

## 10. Reproduction

- `computations/whole_corrected_slab_kraus.py`;
- `tests/test_whole_corrected_slab_kraus.py`;
- `computations/general_reflection_cut_carrier.py`;
- `lean/YMGap/Continuum/CompactDualCutoffOnePhysicalPushforward.lean`
  (typed surrogate scaffold, not the Haar identification).

The aggregate finite certificate is
`computations.whole_corrected_slab_kraus.bf31_certificate()`.
