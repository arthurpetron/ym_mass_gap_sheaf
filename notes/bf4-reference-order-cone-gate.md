# BF4 gate — reference-order cone and dimension-free minorization

Date: 2026-07-25

Status: **BF4 target corrected and its dimension-free abstract lemma
constructed; the physical minorization remains open**.

## 1. The BF2 cone is an order carrier, not yet the Birkhoff cone

BF2 identifies positive trace-class boundary kernels as the complete
infinite-cutoff order carrier.  That is the correct space on which exact
Haar blocking is completely positive.  It is not a solid cone in trace norm.

Indeed, let \(R\) be a positive trace-class operator on an
infinite-dimensional boundary Hilbert space.  Its eigenvalues
\(\lambda_n\) tend to zero.  For any \(\varepsilon>0\), choose
\(\lambda_n<\varepsilon/2\) and set

\[
  R'=R-2\lambda_n|e_n\rangle\langle e_n|.
\]

Then

\[
  \lVert R-R'\rVert_1=2\lambda_n<\varepsilon,
\]

but \(R'\) has eigenvalue \(-\lambda_n\).  Every trace-norm neighborhood of
\(R\) therefore leaves the positive cone.  The cone has empty interior.

The executable finite-cutoff witness uses the normalized heat spectrum.  Its
smallest eigenvalue gives an exact rank-one subtraction at trace distance
twice that eigenvalue, and those distances collapse as the cutoff grows.
This is the finite shadow of the general argument.

This does not invalidate Hilbert's projective metric.  It says that BF4 must
select one comparability part of the cone quantitatively; complete positivity
alone does not select it.

## 2. Reference-order replacement

Fix a faithful positive reference kernel \(R_a\) with
\(\operatorname{Tr}R_a=1\) at lattice spacing \(a\).  Let
\(\ell(A)>0\) be the mass of a nonzero positive input.  The missing physical
estimate has the form

\[
  \alpha_a\,\ell(A)R_a
  \;\preceq\;
  \Phi_{a,L}(A)
  \;\preceq\;
  \beta_a\,\ell(A)R_a
  \tag{DOEBLIN}_{a,L}
\]

for the exact grouped Haar block over physical distance \(L\), for every
admissible input \(A\).

If \(X=\Phi_{a,L}(A)/\ell(A)\) and
\(Y=\Phi_{a,L}(B)/\ell(B)\), the two bounds imply

\[
  \frac{\alpha_a}{\beta_a}Y
  \preceq X
  \preceq
  \frac{\beta_a}{\alpha_a}Y.
\]

Hence

\[
  d_H(X,Y)
  \le
  2\log\frac{\beta_a}{\alpha_a}.
\]

Birkhoff--Hopf then gives

\[
  q_{a,L}
  \le
  \tanh\!\left(
    \frac12\log\frac{\beta_a}{\alpha_a}
  \right)
  =
  \frac{\beta_a-\alpha_a}{\beta_a+\alpha_a}.
\]

This is the desired dimension-free formula.  The dimension of the boundary
space, the representation cutoff, and the ambient volume do not occur.
They enter only through the obligation to prove common physical constants
\(\alpha_a,\beta_a\).

The repository now checks this theorem in exact Loewner order for arbitrary
finite rational witness families.  The sample envelope

\[
 R=\begin{pmatrix}1/2&0\\0&1/2\end{pmatrix},\quad
 X_\pm=\begin{pmatrix}2/3&0\\0&1/3\end{pmatrix}^{\!\pm},
 \quad
 \alpha=2/3,\quad\beta=4/3
\]

has exact rate \(q=1/3\).  Alternating diagonal families in dimensions
\(2,4,10\) give the same rate \(q=1/2\) from the same
\(\alpha=1/2,\beta=3/2\), explicitly pinning the dimension independence.

These are theorem tests, not Yang--Mills data.

### Centered remainder form

Once \(R_a\) and the mass functional \(\ell\) are fixed, the actual
projective remainder has a canonical definition:

\[
 E_A
 =
 \frac{\Phi_{a,L}(A)}{\ell(A)}-R_a.
\]

If

\[
 -\delta_aR_a\preceq E_A\preceq\delta_aR_a,
 \qquad 0\le\delta_a<1,
\]

then the reference envelope holds with

\[
 \alpha_a=1-\delta_a,\qquad
 \beta_a=1+\delta_a,
\]

and the dimension-free Birkhoff rate simplifies exactly to

\[
 q_{a,L}\le\delta_a.
\]

The repository checks this centered form in exact Loewner order.  This is
the desired graded Perron--Frobenius interface: the entire analytic problem
is concentrated in one relative-order remainder bound.

### Trace norm is not enough

The BF3.2 representation tail is small in trace norm, but trace smallness
does not imply a reference-order bound at growing cutoff.  Let
\(R_N=\operatorname{diag}(\lambda_0,\ldots,\lambda_N)\) be a normalized heat
reference, let \(\lambda_N\) be its smallest eigenvalue, and let
\(\lambda_0\) be its largest.  The centered diagonal error

\[
 E_N
 =
 \lambda_N|e_N\rangle\langle e_N|
 -
 \lambda_N|e_0\rangle\langle e_0|
\]

has

\[
 \operatorname{Tr}E_N=0,\qquad
 \lVert E_N\rVert_1=2\lambda_N\longrightarrow0,
\]

while

\[
 \inf\{\delta:-\delta R_N\preceq E_N\preceq\delta R_N\}=1
\]

for every \(N\).  Thus it supplies no strict lower minorization.  The exact
finite witnesses are executable.  BF4 needs a heat-relative tail estimate,
not only a Schatten/trace tail.

## 3. Why BF3.1 cannot inhabit the estimate

The BF3.1 cutoff-one density consists of 32 disconnected rank-one
\(2\times2\) blocks.  A faithful reference \(R\) has positive quadratic form
in every direction.  A rank-deficient output cannot satisfy

\[
  \alpha R\preceq X
\]

for any \(\alpha>0\).  The missing cut-signature mixing gives the same
obstruction globally.  Thus the all-label or fixed-distance grouped map must
be positivity improving before a reference-order certificate is possible.

This is stronger and more useful than merely observing an infinite
cross-ratio: it states exactly which operator inequality grouping must
repair.

## 4. Updated BF3.2-to-BF4 handoff

| BF4 field | Current state |
|---|---|
| exact all-label Haar-network block kernel | the local reflected boundary Gram has a heat-weighted Peter--Weyl trace-norm Cauchy name; the actual fine-to-coarse versus coarse-Gibbs remainder remains open |
| invariant positive carrier | BF2 PSD trace-class order carrier proved; invariance of a quantitative reference-order subcone is open |
| signed intertwiner transport | closed at BF3.1 finite cutoff |
| global or grouped mixing | absent at BF3.1; open for the all-label grouped map |
| physical projective norm | corrected candidate: Hilbert order relative to \(R_a\); not yet inhabited by the physical map |
| fixed-distance diameter | abstract formula complete conditional on \((\mathrm{DOEBLIN})_{a,L}\); physical constants open |
| coherent representation-tail domination | complete in BF2 trace norm; actual fine/coarse RG remainder open |
| coupling-dependent cutoff | all-coupling rational Jacobi-floor schedule constructed; the differentiated identity's Lean transport is open |
| volume uniformity | local conditional truncation is ambient-volume uniform at every rational coupling; physical remainder and minorization constants are open |

BF4 is therefore reached as a precisely formulated gate, not opened as a
proved contraction milestone.

## 5. The next theorem

The highest-leverage theorem is now:

> For the exact all-label, normalized, fixed-distance grouped Haar block,
> construct a faithful heat reference kernel \(R_a\) and prove
> \(-\delta_aR_a\preceq E_A\preceq\delta_aR_a\) for every physical input,
> with \(\delta_a\) independent of ambient volume and representation cutoff.

At microscopic distance the correct target remains

\[
  \delta_a
  =
  1-ma+o(a),
\]

or, equivalently,

\[
  \frac{1-\delta_a}{1+\delta_a}
  =
  \frac{ma}{2}+o(a).
\]

After grouping over fixed physical \(L\), the corresponding ratio must be
bounded strictly below one with constants uniform in cutoff and volume.

## 6. Reproduction

- `computations/reference_order_birkhoff.py`;
- `tests/test_reference_order_birkhoff.py`;
- `computations/bf3_3_birkhoff_handoff.py`;
- `notes/bf2-1-general-reflection-positive-carrier.md`;
- `notes/bf3-2-all-label-whole-slab-frontier.md`.

The fail-closed certificate is
`computations.reference_order_birkhoff.bf4_reference_cone_frontier()`.
