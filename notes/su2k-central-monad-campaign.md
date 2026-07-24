# Finite SU(2)_k central-monad campaign

Date: 2026-07-24

## Verdict

The finite-category technology helps with **fusion coherence**, but it does
not provide the positive, cutoff-uniform Birkhoff carrier.

At the Grothendieck/multiplicity level, the campaign constructs the exact
central induction, proves its degree-zero adjunction with the current fusion
ledger, and shows that pure fusion transport is a module morphism. It also
produces two exact obstructions:

1. physical heat weighting breaks ordinary module naturality;
2. object multiplicities do not determine the comonad counit or monad
   multiplication on intertwiner spaces.

Finally, ordinary low-spin fusion stabilizes as \(k\to\infty\), while the
central carrier itself does not: the central induction of the vacuum already
has rank \(k+1\).

## Finite carrier

Let \(\mathcal C_k=SU(2)_k\), with simples \(0,\ldots,k\). Its fusion rule is

\[
 a\otimes b
 =
 \bigoplus_{\substack{|a-b|\le c\le
 \min(a+b,\,2k-a-b)\\a+b+c\ {\rm even}}} c .
\]

Since \(\mathcal C_k\) is modular, its Drinfeld center is equivalent at the
simple-object level to
\(\mathcal C_k\boxtimes\mathcal C_k^{\mathrm{rev}}\). Write a central simple
as \((a,b)\). The forgetful functor and its left adjoint have multiplicities

\[
 U(a,b)=a\otimes b,\qquad
 [F(V):(a,b)]=\dim\operatorname{Hom}(a\otimes b,V).
\]

The executable carrier is `central_induction(level, physical)`. The central
monad and associated comonad are represented on objects by

\[
 Z=UF,\qquad G=FU.
\]

This is an exact finite integer model of objects and Hom dimensions. It is
not a model of the actual linear maps in the Hom spaces.

## Degree-zero comparison

For physical multiplicity vector \(V\) and central vector \(M\), direct
finite-sum rearrangement proves

\[
\begin{aligned}
\dim\operatorname{Hom}_{Z}(F(V),M)
 &=\sum_{a,b,c}V_c\,N_{ab}^{c}\,M_{ab}\\
 &=\dim\operatorname{Hom}_{\mathcal C_k}(V,U(M)).
\end{aligned}
\]

Thus the complete face fusion ledger used by
`fusion_closed_surface_carrier.py` is exactly the physical degree-zero input
to central induction. For a word of labels whose total doubled spin is at
most \(k\), the affine reflection wall cannot occur, so the \(SU(2)_k\)
ledger agrees exactly with ordinary SU(2).

In particular, every face of the two-fundamental-surface witness uses either
`()`, `(1)`, or `(1,1)`. Its ledger \(\{0:1,2:1\}\) is stable for every
\(k\ge2\).

## Local block transport

Fusion by a label \(x\) acts on the physical ring. On the central side it
acts on the left factor:

\[
 x\triangleright(a,b)=(x\otimes a,b).
\]

Associativity, rigidity, and Frobenius reciprocity give

\[
 F(x\otimes V)\cong x\triangleright F(V).
\]

The implementation verifies the corresponding exact multiplicity identity
for every label through level nine. This means the **pure fusion part** of
unnormalized local block transport has a canonical central-module lift.

The physical heat coefficient does not share this naturality. At level
\(k\ge1\), act by label one on the vacuum at \(w=1/2\). Weighting after fusion
gives

\[
 D_w(1)=2w^3\,1=\frac14\,1,
\]

whereas weighting the vacuum first and then fusing gives \(1\). Therefore

\[
 D_w(x\otimes V)\ne x\otimes D_w(V).
\]

The actual block map is not an ordinary central-module morphism. It would
need a heat-twisted/lax module structure whose coherence constants carry the
physical weights.

## Counit and multiplication test

For the first crossing central simple \((1,1)\),

\[
 U(1,1)=0\oplus2.
\]

Consequently \((1,1)\) appears twice in

\[
 G(1,1)=F(U(1,1)).
\]

The comonad counit must choose a linear functional from this
two-dimensional multiplicity space to the simple \((1,1)\). The
Grothendieck vector records the number two but contains no basis, phase,
F-symbol, or functional. The same information loss affects
\(\mu:Z^2(V)\to Z(V)\).

Therefore the central monad/comonad **categorically** contains the desired
joint coarse-intertwiner transport, but the finite multiplicity carrier does
not compute it. A full realization must add explicit unitary F/R symbols and
the coend dinatural maps. Ocneanu rigidity guarantees qualitative coherence
once such finite-category data exist; it does not construct the physical
map from multiplicities.

## Stable versus finite-only

Stable as \(k\to\infty\):

- the fusion ledger of any fixed word once \(k\ge\sum_i j_i\);
- the degree-zero adjunction identity for fixed low labels;
- pure-fusion module naturality as an algebraic identity;
- the current pair-family heat polynomial, whose face outputs are at most
  label two.

Not stable, or not supplied uniformly:

- the central carrier: \(F_k(0)=\bigoplus_{a=0}^{k}(a,a)\), of rank \(k+1\);
- normalized cointegrals and Ocneanu-rigidity contractions, which use the
  full finite category;
- counit/multiplication matrices on growing intertwiner spaces;
- any positive cone or projective-diameter bound;
- physical heat-weighted module naturality.

## Consequence for BF1

Do not replace the physical surface/fusion carrier by the entire central
monad carrier: it grows before any physical excitation is inserted. Use
central induction as a **coherence envelope** for bounded local fusion words,
then project back to the physical heat-weighted carrier. The next relevant
object is a heat-twisted central-module comparison, not an appeal to
Ocneanu rigidity alone.
