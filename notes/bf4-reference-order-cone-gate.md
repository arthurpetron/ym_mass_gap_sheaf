# BF4 gate — reference-order cone and dimension-free minorization

Date: 2026-07-25

Status: **active BF4 gate**.  A fixed-coupling physical minorization is
constructed; its spacing-uniform fixed-distance mass rate remains open.

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

### Fixed-coupling physical minorization

The BF3.2 Jacobi floor supplies a first physical reference-order estimate,
without enumerating representations.  Condition on every link outside one
corrected slab.  For every boundary condition \(b\), the internal-link
weight satisfies

\[
 L_s^{72}
 \le
 w_b(U)
 \le
 H_s^{72},
\]

where \(L_s>0\) is the rational Jacobi floor and \(H_s\) is the rational
all-label character upper bound.  The conditional partition has the same
two bounds.  Relative to normalized internal Haar measure \(\lambda\),

\[
 \left(\frac{L_s}{H_s}\right)^{72}\lambda
 \le
 \mu_b
 \le
 \left(\frac{H_s}{L_s}\right)^{72}\lambda.
\]

Push both sides through the deterministic coarse-holonomy map.  Positivity
of pushforward preserves the inequalities, so every physical boundary
condition has the same reference support and finite projective diameter.
Writing

\[
 \alpha_s=\left(\frac{L_s}{H_s}\right)^{72},
 \qquad
 \beta_s=\left(\frac{H_s}{L_s}\right)^{72},
\]

gives the exact dimension-free fixed-coupling rate

\[
 q_s
 \le
 \frac{\beta_s-\alpha_s}{\beta_s+\alpha_s}<1.
\]

The constants are independent of ambient volume and representation cutoff.
This closes the existence of an all-label physical minorization and repairs
the cutoff-one support disconnection after complete physical grouping.

It is far too crude to close the mass-scale estimate.  Decimal guides for
the exact certified deficits are

| \(s\) | character majorant cutoff | \(\log_{10}(1-q_s)\) |
|---:|---:|---:|
| \(1/2\) | 2 | \(-215.6\) |
| \(3/4\) | 6 | \(-631.5\) |
| \(9/10\) | 16 | \(-1642.1\) |

These numbers do not disprove a physical mass rate; they show that global
pointwise floor/ceiling comparison throws away essentially all of it.  BF4
now needs a grouped comparison that uses fusion/heat locality rather than
the worst holonomy on every plaquette.

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
| exact all-label Haar-network block kernel | BF3.2 closed: the local reflected boundary Gram has a heat-weighted Peter--Weyl trace-norm Cauchy name and complete coherent cutoff modulus |
| invariant positive carrier | BF2 PSD trace-class order carrier proved; invariance of a quantitative reference-order subcone is open |
| signed intertwiner transport | closed at BF3.1 finite cutoff |
| global or grouped mixing | complete for the fixed-coupling physical conditional family by Haar-reference minorization |
| physical projective norm | inhabited at fixed coupling by Hilbert order relative to pushed Haar; a sharp heat-relative cone is open |
| fixed-coupling local diameter | complete, cutoff- and ambient-volume-independent |
| fixed-physical-distance scaling | open; the current pointwise certificate has a catastrophically small deficit |
| coherent representation-tail domination | complete in BF2 trace norm; actual fine/coarse RG remainder open |
| coupling-dependent cutoff | all-coupling rational Jacobi-floor schedule constructed; the differentiated identity's Lean transport is open |
| volume uniformity | local conditional truncation and fixed-coupling minorization are ambient-volume uniform; physical-distance scaling is open |

BF3.2 now supplies an admissible all-label handoff.  BF4 is therefore active
as a precisely formulated gate, not closed as a contraction milestone.

## 5. Intuitionistic contraction normal form

There is now an axiom-clean alternative to formalizing the full logarithmic
Birkhoff--Hopf theorem.  If the grouped physical map admits the literal
decomposition

\[
 \Phi_{a,L}
 =
 \varepsilon_{a,L}\Omega_{R_{a,L}}
 +(1-\varepsilon_{a,L})\Psi_{a,L},
 \qquad
 \Omega_R(A)=\ell(A)R,
\]

with a positive mass-preserving residual, then equal-mass inputs contract
in the base norm by \(1-\varepsilon_{a,L}\).  The finite exact-rational
kernel theorem is proved in
`lean/YMGap/Continuum/ConstructiveRefreshContraction.lean`.

This is already latent in the reference-order formulation.  The lower
inequality

\[
 -\delta R\preceq E_A
\]

gives \(\Phi(A)\succeq(1-\delta)\ell(A)R\), so
\(\varepsilon=1-\delta\) and the refresh rate is exactly \(\delta\).  The
upper Loewner bound remains useful for Hilbert geometry but is not needed
for the base-norm contraction.

The certificate should be sought after grouping over fixed physical
distance.  Microscopic global Haar minorization is intrinsically too weak
near the small-time heat-kernel limit.  The preferred physical witness is

\[
 \varepsilon_{a,L}\ge\varepsilon_L>0,
 \qquad
 q_L=1-\varepsilon_L<1,
\]

uniform in spacing, cutoff, and ambient volume.  Complete positivity of the
residual is the strongest tensor-stable version.  See
`notes/bf4-intuitionistic-proof-routes.md`.

The first all-label corridor candidate is now explicit.  If the grouped
central heat coordinate satisfies \(s^m\le1/2\), then
\[
 K_{s^m}(g)\ge\frac{1055}{2272}
\]
for the complete character series.  The nine canonical coarse-loop disks
are geometrically pinned, but all 27 of their internal links meet two
transverse plaquettes, so the 72-face integrand does not literally factor.
Normalized-Haar leaf elimination reduces the transverse comparison to a
specific 21-face core.  The 1024 admissible fundamental fillings of its
connected component have now been coherently contracted to distinct
canonical trace-word records with rational scalar coefficients on the
protected boundary, and the six decorations complete the full binary
residual.  A nested arbitrary-cutoff recoupling carrier and a fixed-coupling
uniform all-label residual tail are now explicit.  But the cutoff-one
ten-feature Schur symbol becomes indefinite already at \(z=3/2\), so binary
CP domination cannot be promoted monotonically into weak coupling.

The carrier now has exact local magnetic tensors at arbitrary finite cutoff.
At cutoff one, its 33 oriented incidences, 18 shared protected interfaces,
\(1/(k+1)\) dimension weights, signed Racah blocks, and \(J^2=-I\) pivotal
sign are all explicit.  The fixed-coupling scalar tail also lifts to a
trace-norm tail for finite compressions of the positive full-measure Gram,
including coherent cutoff cross corners.  These results still do not
identify the physical source-indexed Choi map.

Moreover no fixed cutoff is weak-coupling uniform, even relatively: an
explicit omitted block exceeds the retained identity head.  The next order
theorem must reconstruct the open-index all-label Choi operator in this
pivotal convention and show that the full interacting map CP-dominates the
corridor packet after a spacing-dependent cutoff or direct all-label
regrouping.

The grouped-half hypothesis itself is not free: for the local bare
heat-kernel multiplier \(\rho=s^3\), it implies
\((1-\rho(a))/a\ge7/(16L)\) at \(m=\lceil L/a\rceil\), \(a\le L\).
This is not yet a physical gap estimate: the identification with the
interacting gauge-invariant transfer separator remains open.  The corridor
construction converts a bare cumulative-heat estimate into a common packet;
the physical promotion belongs to the later shared-object transfer/OS
bridge.  See `notes/bf4-grouped-all-label-haar-kernel.md`.

## 6. The next theorem

The highest-leverage theorem is now:

> For the exact all-label, normalized, fixed-distance grouped Haar block,
> exhibit a common faithful Haar/fusion refresh packet of mass at least
> \(\varepsilon_L>0\), uniformly in spacing, cutoff, and ambient volume,
> and prove that the residual grouped map is positive and mass-preserving.

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

## 7. Reproduction

- `computations/reference_order_birkhoff.py`;
- `tests/test_reference_order_birkhoff.py`;
- `computations/bf3_3_birkhoff_handoff.py`;
- `notes/bf2-1-general-reflection-positive-carrier.md`;
- `notes/bf3-2-all-label-whole-slab-frontier.md`.

The fail-closed certificate is
`computations.reference_order_birkhoff.bf4_reference_cone_frontier()`.
