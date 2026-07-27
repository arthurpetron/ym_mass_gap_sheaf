# BF4 five-holonomy Perron budget

## Status

**Machine-checked status correction (2026-07-26).**  The scalar Perron
arithmetic, the SU(2) Haar--\(L^2\) character layer, the all-label
Hilbert--Schmidt coefficient completion, and the nonlinear same-carrier
five-fusion completion are now proved in Lean.  The remaining assertion in
Section 5 is still an analytic proof programme, not a Lean theorem: the
development does not yet identify the normalized, conditionally integrated
five-holonomy BF4 operator with the Gaussian limit in Hilbert--Schmidt norm,
and therefore does not yet construct the physical certificate
\(q_s\le1/4\).  Likewise, the `AFEnvelope` instantiated below is an exact
bare heat/transmutation envelope; it has not been identified with the
same-action nonperturbative four-dimensional BF4 block-map orbit.  These two
identifications are the fail-closed residuals.  No physical BF4 or Clay
frontier type is inhabited.

The checked components are:

- `SU2HaarL2HilbertSchmidt.lean`: normalized Haar Riemann orthogonality,
  finite packet Parseval, and finite-rank kernel Hilbert--Schmidt limits;
- `SU2HeatChannelHilbertSchmidtCompletion.lean`: the genuine infinite
  diagonal heat-channel squared tail and constructive Hilbert--Schmidt
  completion;
- `SU2GroupedFiveHolonomyHilbertSchmidt.lean`: four exact
  Clebsch--Gordan fusions equal the pointwise fifth power at finite
  cutoff; genuine midpoint-Haar convergence for that nonlinear carrier;
  and a constructive all-label Hilbert--Schmidt completion of the literal
  five-coordinate tensor carrier, stable under
  \(q\mapsto q^{\mathrm{steps}}\).  The same module machine-refutes direct
  domination of the nonlinear carrier by that independent tensor box:
  at \(q=1/2\), cutoff one,
  \[
    \frac{215753357}{524288}
    >
    \frac{9765625}{1048576};
  \]
- `SU2DimensionWeightedHeatTail.lean` and
  `SU2FusionWeightedMass.lean`: the spacing-dependent \(1/8\) label cutoff,
  a uniform dimension-weighted heat mass ceiling, and exact multiplicativity
  of that mass under genuine Clebsch--Gordan fusion;
- `SU2NonlinearFiveFusionTail.lean` and
  `SU2NonlinearFiveFusionCompletion.lean`: directed same-carrier padding,
  the exact omitted weighted packet tail, the quantitative nonlinear
  Haar-square bound, and a constructed `CReal` to which both the direct
  fivefold packet squares and the canonical grouped five-holonomy Haar
  observables converge;
- `FiveHolonomyPerronCutoff.lean`: the explicit spacing-dependent label
  cutoff, all-label ceiling, and the conditional strict inequality
  \(C_s^2q_s^{m-2}<1\);
- `BF4FiveHolonomyGaussian.lean`: the exact rational generalized spectrum
  \(4,4,4,6,6\);
- `BF4GaussianPerronRatio.lean`: a constructive-real
  \(q_0=3-2\sqrt2\) with
  \(1/20\le q_0\le9/50<1/5\), plus the exact nonlinear handoff buffer
  \(9/50+7/100=1/4\);
- `BF4AFInstantiation.lean`: an exact reciprocal bare trajectory, its cubic
  remainder and exponential spacing bound, a concrete `AFEnvelope`, and the
  application of `BareAFImpliesLinearFloor`.

Four additional axiom-gated layers prevent the remaining physical
identifications from being inferred from insufficient premises:

- `BF4InterleavedPotentialShortcutFence.lean` proves with the actual
  all-label Haar floor \(1055/2272\) that a positive interior
  Feynman--Kac weight need not satisfy even the naïve one-factor
  \(QDQ\le4Q^2\) comparison;
- `BF4PhysicalTrajectoryFence.lean` proves that the legacy
  `BondMovingResidual` permits `delta = 0` with an unrelated
  `fullStepWeight`, then supplies the fail-closed
  `CoupledBondMovingResidual` and `LinkedBondMovingTrajectory`
  interfaces that a real block-map construction must inhabit;
- `BF4GroupedFeynmanKacHarnack.lean` proves the exact pathwise sandwich
  with nonconstant interior potentials, the projective spread
  \(k_{\rm spread}v_{\rm spread}^{p}\), and the BF4 kinetic constants
  \(k_{\min}=(1055/2272)^{23}\),
  \(k_{\max}=(3489/2272)^{23}\), and
  \(k_{\rm spread}=(3489/1055)^{23}\).  It also proves that positivity
  plus a unit potential floor yields no finite uniform potential spread;
- `BF4BlockOperatorExtensionalFence.lean` proves that the current genuine
  source-indexed slab operator is insensitive to arbitrary changes of its
  declared `couplingFlow` away from the one endpoint constraint.  Two
  inequivalent flows therefore produce identical raw kernels, so this
  operator cannot determine the physical AF trajectory.

The nonlinear all-label fusion-tail residual is now closed.  In particular,
the proof does not compare against the invalid independent tensor box: it
pads both truncations to one SU(2) carrier, propagates coefficient order
through five genuine fusions, and controls the Haar square by the exact
dimension-weighted omitted tail.  The grouped Harnack residual remains:
prove a spacing-uniform Yang--Mills bound for the conditionally integrated
interior-potential spread, or an exact cancellation/lumpability result that
avoids this spread.  The trajectory residual requires a block constructor
that extracts the next physical action from the pushed current law; only then
may the existing bare `AFEnvelope` and `BareAFImpliesLinearFloor` be
instantiated physically.

At the analytic level, the intended reduced Yang--Mills Perron obstruction is
the following conditional statement under the necessary
heat-time/spacing hypothesis
\[
\tau(a):=-\log s(a)\ge\kappa a
\tag{TS}
\]
for some \(\kappa>0\) along the continuum tail.

The remaining Section 5 argument is intended to prove that the
five-holonomy effective transfer has:

- limiting non-vacuum spectral ratio
  \[
  q_0=3-2\sqrt2<\frac15;
  \]
- eventual nonlinear spectral ratio \(q_s\le1/4\);
- intrinsic two-buffer estimate
  \[
  C_s^2\le \exp\!\left(\frac{1728}{\tau}\right).
  \]

Consequently, if \(m(a,L)=\lceil L/a\rceil\) and
\(L>1728/\kappa\), then
\[
C_{s(a)}^2q_{s(a)}^{m(a,L)-2}\longrightarrow0.
\]

This closes the selected Perron inequality for the executable trajectory
\(s(a)=1-a\), and for every one-loop asymptotically-free trajectory with
\(\tau(a)/a\to\infty\).

Moreover, the repository already contains the axiom-audited constructive
theorem
`YMGap.Continuum.BareAFDiagnostic.BareAFImpliesLinearFloor`. Applied with
the BF4 identification \(s=w=e^{-t/4}\), its `AFEnvelope` implies (TS)
with the explicit coefficient
\[
\kappa=\frac{\alpha\Lambda}{4C}.
\]
Thus (TS) is no longer an independent scalar obstruction: it follows from
the bare asymptotic-freedom envelope. What remains open is to instantiate
that envelope on the nonperturbative physical BF4 trajectory. This does
not construct that trajectory and does not prove the Yang--Mills mass gap.

The executable certificate is
`computations/boundary_five_holonomy_perron.py`.

## 1. Exact spatial Schur complement

Use the full-boundary spanning tree adapted to the 19-edge tree of the
temporal base graph. Order the 23 remaining chords so the five temporal
chords come first. Let
\[
B=(B_y\ B_z):\mathbb R^5\oplus\mathbb R^{18}
\longrightarrow\mathbb R^{24}
\]
be the linearized spatial curvature matrix. Integrating the 18 fiber
directions in the Gaussian limit gives the Schur complement
\[
S
=B_y^\mathsf TB_y
-B_y^\mathsf TB_z
(B_z^\mathsf TB_z)^{-1}
B_z^\mathsf TB_y.
\]

Exact rational elimination gives
\[
S=
\begin{pmatrix}
2&0&0&0&-1\\
0&2&-1&-1&1\\
0&-1&2&1&-1\\
0&-1&1&2&-1\\
-1&1&-1&-1&2
\end{pmatrix},
\qquad
\det S=6.
\tag{S}
\]

The invertibility is the five-coordinate version of the full spatial
single-well coercivity. It is stronger than merely knowing that the full
\(24\times23\) curvature matrix has rank 23.

## 2. Exact temporal quotient metric

Let \(E:\mathbb R^5\to\mathbb R^{24}\) insert the five chord differences
into the temporal faces, and let
\(D:\mathbb R^{19}\to\mathbb R^{24}\) be a pinned full-rank set of temporal
vertex-gauge columns. Gaussian Haar integration minimizes over those
internal directions. The quotient kinetic precision is
\[
K=E^\mathsf T
\left[I-D(D^\mathsf TD)^{-1}D^\mathsf T\right]E.
\]

The exact result is
\[
K=
\begin{pmatrix}
 5/12& 1/24&-1/12&-1/24&-1/6\\
 1/24& 5/12&-5/24&-1/6& 5/24\\
-1/12&-5/24& 5/12& 5/24&-1/6\\
-1/24&-1/6& 5/24& 5/12&-5/24\\
-1/6& 5/24&-1/6&-5/24& 5/12
\end{pmatrix},
\qquad
\det K=\frac1{384}.
\tag{K}
\]

Thus both the spatial and kinetic quadratic forms are strictly positive.

## 3. Generalized spectrum

Put \(A=K^{-1}S\). Exact rational matrix multiplication proves
\[
(A-4I)(A-6I)=0,
\]
together with
\[
\dim\ker(A-4I)=3,\qquad
\dim\ker(A-6I)=2.
\]
Equivalently,
\[
\boxed{
\det(S-\lambda K)
=-\frac{(\lambda-6)^2(\lambda-4)^3}{384}.
}
\tag{GS}
\]

The trace and determinant checks are
\[
\operatorname{tr}A=24,\qquad
\det A=4^3\,6^2.
\]

Every matrix is recomputed directly from the 24 spatial faces, 24 temporal
faces and adapted spanning tree by
`five_holonomy_gaussian_perron()`.

## 4. Gaussian Perron ratio

For one Lie-algebra component, the limiting symmetric kernel is, up to a
positive scalar,
\[
\mathcal A_0(x,y)
=
\exp\left[
-\frac14(x-y)^\mathsf TK(x-y)
-\frac18x^\mathsf TSx
-\frac18y^\mathsf TSy
\right].
\tag{G}
\]

Diagonalize the generalized pair \((S,K)\). For a generalized eigenvalue
\(\sigma\), the corresponding one-dimensional Mehler ratio is
\[
r(\sigma)
=
\frac{2}
 {2+\sigma+\sqrt{\sigma(\sigma+4)}}.
\]
Therefore
\[
r(4)=3-2\sqrt2,\qquad
r(6)=4-\sqrt{15}.
\]
The first is larger. Since \(\sqrt2>7/5\),
\[
\boxed{
q_0=3-2\sqrt2<\frac15.
}
\tag{Q0}
\]

The same five generalized directions occur independently in the three
components of \(\mathfrak{su}(2)\). Tensoring changes multiplicities, not
the largest non-vacuum ratio.

## 5. Passage from the nonlinear kernel

This step uses the exact \(SU(2)\) short-time heat kernel rather than a
formal quadratic replacement.

Choose the adapted based-tree gauge and exponential coordinates
\[
U_j=\exp(\sqrt{\tau}\,X_j),
\qquad \tau=-\log s.
\]
On every fixed bounded set in the rescaled variables,
\[
\tau^{3/2}
K_s\!\left(\exp(\sqrt{\tau}\,X)\right)
\longrightarrow
c_{\!SU(2)}e^{-\lVert X\rVert^2/4}
\]
with the same convergence for the finite collection of products,
Jacobians and first derivatives used here. The Baker--Campbell--Hausdorff
remainders are \(O(\sqrt\tau)\) on bounded rescaled sets.

For the temporal integral, Gaussian integration of the 19 scaled
vertex-gauge variables produces (K). For the spatial fiber integral,
Gaussian integration of the 18 complementary variables produces (S).

It remains to justify discarding the complement of the exponential chart.
The global nonlinear estimate already proved in the spatial audit is
\[
\sum_{\text{23 cycles}}d(U_e,I)^2
\le81\sum_{\text{24 faces}}d(U_p,I)^2.
\tag{GC}
\]
Together with the global Gaussian heat-kernel upper bound, (GC) makes every
configuration outside a fixed flat-orbit neighborhood exponentially small
in \(1/\tau\). Inside the chart, the local heat-kernel upper bound supplies
an integrable Gaussian majorant after rescaling.

Dominated convergence therefore gives Hilbert--Schmidt convergence of the
normalized, unitarily rescaled effective operator to (G). Since the
operators are compact, self-adjoint and positive, their ordered eigenvalues
converge. The Gaussian ground state is simple, so
\[
q_s\longrightarrow q_0.
\]
Using (Q0), there is a weak-coupling threshold \(s_0<1\) such that
\[
\boxed{q_s\le\frac14\qquad(s_0<s<1).}
\tag{Q}
\]

This is an eventual theorem; no numerical value of \(s_0\) is asserted.
A finite prefix of any fixed spacing sequence remains a fixed-coupling
compact problem.

## 6. A global heat-kernel ratio

The spectral ratio alone is insufficient because the two-buffer constant
may grow as \(s\to1\). We now bound that growth.

Let
\[
P_\infty(s)
=\prod_{n\ge1}
(1-s^{2n})(1-s^{2n-1})^2.
\]
Writing \(s=e^{-\tau}\) and expanding \(-\log(1-x)\) gives
\[
\begin{aligned}
-\log P_\infty(e^{-\tau})
&=
\sum_{k\ge1}\frac1k
\left[
\frac1{e^{2k\tau}-1}
+\frac1{\sinh(k\tau)}
\right]\\
&\le
\sum_{k\ge1}\frac1k
\left[
\frac1{2k\tau}
+\frac1{k\tau}
\right]
=\frac{\pi^2}{4\tau}.
\end{aligned}
\]
Thus
\[
P_\infty(e^{-\tau})
\ge e^{-\pi^2/(4\tau)}.
\]

Choose the finite Jacobi prefix so its omitted charge is at most \(1/2\).
The differentiated Jacobi identity used elsewhere in the repository then
gives the uniform single-plaquette floor
\[
L_\tau\ge\frac18e^{-\pi^2/(4\tau)}.
\tag{L}
\]

For the ceiling, \(|\chi_n|\le n+1\) gives
\[
\begin{aligned}
H_\tau
&\le
\sum_{m\ge1}m^2e^{-\tau(m^2-1)}\\
&\le
e^\tau\int_0^\infty(x+1)^2e^{-\tau x^2}\,dx
\le9\tau^{-3/2},
\qquad0<\tau\le1.
\end{aligned}
\tag{H}
\]

Using \(\log72<5\), \(\pi^2<10\) and
\(\log(1/\tau)\le1/\tau\), (L)--(H) imply
\[
\boxed{
\frac{H_\tau}{L_\tau}
\le e^{9/\tau}.
}
\tag{R1}
\]

## 7. The intrinsic buffer constant

The symmetric five-holonomy transfer contains 24 temporal heat kernels and
two square roots of 24 spatial kernels, hence 48 single-plaquette factors.
Conditional Haar integration preserves pointwise bounds, so its kernel
\(\mathcal A_s\) satisfies
\[
\frac{\sup\mathcal A_s}{\inf\mathcal A_s}
\le
\left(\frac{H_\tau}{L_\tau}\right)^{48}
\le e^{432/\tau}.
\tag{R48}
\]

For completeness, let a positive kernel \(T\) on a probability space obey
\(\ell\le T(x,y)\le u\), let \(r=u/\ell\), and normalize its Perron
eigenfunction by \(\lVert\phi\rVert_2=1\). Positivity gives
\[
\frac{\sup\phi}{\inf\phi}\le r.
\]
Since \(\sup\phi\ge1\), it follows that
\(\inf\phi\ge1/r\) and \(\int\phi\ge1/r\). Hence
\[
\lambda\phi(x)
=\int T(x,y)\phi(y)\,dy
\ge\frac{\ell}{r},
\qquad
\lVert T(x,\cdot)\rVert_2\le u.
\]
The intrinsic buffer constant therefore obeys
\[
C
=
\sup_x
\frac{\lVert T(x,\cdot)\rVert_2}
     {\lambda\phi(x)}
\le r^2.
\]
Combining this with (R48) proves
\[
\boxed{
C_s^2\le e^{1728/\tau}.
}
\tag{C}
\]

## 8. Closing the Perron budget

By (Q), \(q_s\le1/4<e^{-1}\) eventually. Therefore
\[
\log\left(C_s^2q_s^{m-2}\right)
\le
\frac{1728}{\tau}-(m-2).
\]
Assume (TS), and use \(m=\lceil L/a\rceil\ge L/a\). Then
\[
\log\left(C_s^2q_s^{m-2}\right)
\le
\frac{1728}{\kappa a}-\frac{L}{a}+2
=
-\frac{L-1728/\kappa}{a}+2.
\tag{B}
\]
For every
\[
\boxed{L>\frac{1728}{\kappa},}
\]
the right side tends to \(-\infty\). This proves
\[
\boxed{
C_{s(a)}^2q_{s(a)}^{m(a,L)-2}<1
}
\]
for all sufficiently fine spacings, and in fact the left side tends to
zero.

### Executable dyadic model

For \(s(a)=1-a\),
\[
\tau(a)=-\log(1-a)\ge a,
\]
so \(\kappa=1\). Every integer \(L\ge1729\) is sufficient for the continuum
tail.

### One-loop asymptotic freedom

If \(a_k=b^{-k}\) and
\[
\tau_k=\frac{c}{A+Bk}
\]
with \(b>1\) and \(A,B,c>0\), then
\[
\frac{\tau_k}{a_k}
=\frac{c\,b^k}{A+Bk}
\longrightarrow\infty.
\]
Thus (TS) eventually holds for every chosen \(\kappa\), and (B) closes for
any fixed \(L>0\) after moving sufficiently far into the UV tail.

### Constructive bare-AF bridge

The same conclusion is already available in a more invariant form. The
constructive `AFEnvelope` in
`lean/YMGap/Continuum/BareAFDiagnostic.lean` carries
\[
t(g)\ge\alpha g^2,
\qquad
a(g)\Lambda\le Cg^2,
\qquad
\alpha,C,\Lambda>0.
\]
The second inequality is the collapsed consequence of the usual
exponential asymptotic-freedom spacing law; the Lean module separately
certifies the scalar exponential-domination kernel.

For the BF4 heat coordinate
\[
s(g)=w(g)=e^{-t(g)/4},
\qquad
\tau(g)=-\log s(g)=\frac{t(g)}4,
\]
one obtains directly
\[
\tau(g)
\ge\frac{\alpha}{4}g^2
\ge\frac{\alpha\Lambda}{4C}a(g).
\tag{AF-TS}
\]
Hence (TS) holds with the explicit constructive witness
\[
\boxed{\kappa=\frac{\alpha\Lambda}{4C}.}
\]
The existing Lean theorem `BareAFImpliesLinearFloor` proves the equivalent
bare-weight floor with a slightly more conservative \(1/8\) constant;
(AF-TS) is the direct heat-time form needed here.

A single collapsed `AFEnvelope` supplies the displayed fixed
\(\kappa=\alpha\Lambda/(4C)\). If the envelope is obtained from the full
standard exponential spacing law, its coefficient \(C\) can be made
arbitrarily small by restricting the coupling window; equivalently
\(\tau(a)/a\to\infty\). Under that sharpened exponential envelope, the
Perron budget closes for every fixed \(L>0\), not merely for
\(L>1728/\kappa\) with one preselected \(\kappa\).

## 9. Why some trajectory hypothesis is necessary

The statement cannot be uniform over arbitrary functions \(s(a)\to1\).
Already in the Gaussian model, the source--target cross coefficient after
\(m\) steps is proportional to \(q_0^m/\tau\). To keep the comparison
inside a shrinking nonlinear flat chart, choose any
\(\alpha_*\in(1/3,1/2)\), endpoints of size \(\tau^{\alpha_*}\), and
\[
\tau(a)=q_0^{\,p\,m(a,L)}
\qquad\text{with}\qquad
p>\frac1{1-2\alpha_*}.
\]
The BCH/action error is
\(m\,O(\tau^{3\alpha_*-1})\to0\), whereas the surviving mixed term has
size
\[
q_0^m\tau^{2\alpha_*-1}\longrightarrow\infty.
\]
Thus the grouped four-boundary cross-ratio diverges. For example,
\(\alpha_*=2/5\) and any \(p>5\) suffice.

Thus the Yang--Mills operator analysis does not manufacture a relation
between heat time and lattice spacing. The next physical obligation is
precisely:

> instantiate the constructive bare-AF envelope, including
> \(s=e^{-t/4}\) and the spacing comparison, on the nonperturbative
> physical BF4 continuum trajectory.

That is now the first fail-closed field in the BF4 frontier.
