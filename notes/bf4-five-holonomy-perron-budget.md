# BF4 five-holonomy Perron budget

## Status

**Machine-checked status correction (2026-07-26).**  The scalar Perron
arithmetic, the SU(2) Haar--\(L^2\) character layer, the all-label
Hilbert--Schmidt coefficient completion, and the nonlinear same-carrier
five-fusion completion are now proved in Lean.  Positive/order/Gram
preservation under finite retained-path conditional integration is also
proved.  The remaining assertion in Section 5 is still an analytic proof
programme, not a Lean theorem: the development does not yet construct the
actual all-label BF4 retained-path kernel with a spacing-uniform pathwise
kinetic estimate, nor identify the resulting normalized five-holonomy
operator with the Gaussian limit in Hilbert--Schmidt norm.  It therefore
does not yet construct the physical certificate \(q_s\le1/4\).  Likewise,
the `AFEnvelope` instantiated below is an exact bare heat/transmutation
envelope; it has not been identified with the same-action nonperturbative
four-dimensional BF4 block-map orbit.  These identifications are the
fail-closed residuals.  No physical BF4 or Clay frontier type is inhabited.

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
- `BF4RetainedPathConditionalOrder.lean`,
  `BF4RetainedKineticWindow.lean`,
  `BF4TerminalSmoothingProjective.lean`, and
  `BF4PositiveKernelSpacingConvergence.lean`: positive conditional
  integration on the enlarged `(terminal, full path)` carrier, finite
  matrix-amplified order preservation, a potential-independent retained
  kinetic Harnack/Gram theorem, the exact implication from a 23-factor
  retained pointwise corridor to BF4 Harnack order, terminal-smoothing
  projective domination, and a constructive positive-kernel convergence
  consumer with an explicit spacing-error modulus;
- `SU2AllLabelPointwiseHeatCorridor.lean`: the previously external
  \(1055/2272\) and \(3489/2272\) constants are now derived in Lean for every
  finite doubled-label SU(2) class-heat partial.  The proof uses
  \(|U_n(x)|\le n+1\), the sharp tail ratio \(1/72\), and the exact tail
  budget \(81/2272\);
- `SU2AllLabelPointwiseHeatCompletion.lean` and
  `SU2AllLabelPointwiseHeatLimitBridge.lean`: the finite class-heat partials
  at \(0\le w\le1/2\) now form an actual `CReal`; their completed value
  retains the exact rational corridor, is the `CReal.ConvergesTo` limit of
  the embedded partials, and is constructively unique up to `CReal.Equiv`;
- `BF4CompletedHeatRetainedConsumer.lean`,
  `BF4CompletedSU2PointwiseRetainedHarnack.lean`,
  `BF4CompletedRetainedConditionalOrder.lean`, and
  `BF4CompletedSU2ConditionalHarnack.lean`: the completed one-factor corridor
  tensorizes over a literal 23-factor retained carrier, the consumer is
  instantiated by the completed SU(2) heat values themselves, and arbitrary
  common nonnegative rational interior weights survive finite conditional
  path integration with the unchanged spread \((3489/1055)^{23}\).
  Entrywise finite amplification and preservation of already-formed
  nonnegative quadratic channels are proved; scalar entrywise order is not
  misidentified with matrix Loewner order;
- `SU2PointwiseHeatSpacingCompletion.lean`: for every rational
  \(0<w<1\), the explicit cutoff
  \(N(w)=\operatorname{powBaseCutoff}(w,1/8)\) gives
  \(\rho(w)=4w^{2N(w)+3}\le1/2\), a two-sided signed geometric tail
  envelope, a constructive pointwise heat `CReal`, and convergence of the
  shifted ordinary character prefixes;
- `SU2PointwiseHeatSpacingTailBound.lean` and
  `SU2PointwiseHeatCompletionCompatibility.lean`: the finite block error and
  semantic completion error are bounded by the exact closed tail
  \(H(w)\rho(w)^M/(1-\rho(w))\); on \(0<w\le1/2\), the spacing-dependent
  completion is constructively equivalent to the fixed-corridor completion
  and inherits its exact rational bounds.  This proves fixed-nome cutoff
  removal while deliberately allowing \(N(w)\) to diverge as \(w\to1\);
- `BF4CompletedProductLimitBridge.lean`: simultaneous common-cutoff rational
  products converge to the recursively completed product for every finite
  retained list, with a specialization to the literal 23-factor SU(2)
  carrier;
- `BF4CompletedConditionalLimitBridge.lean`: multiplication by the common
  rational path potential and finite retained-path integration commute with
  the simultaneous character-cutoff limit;
- `BF4CompletedProductTailBound.lean`: the sign-safe product telescope gives
  the exact literal BF4 error coefficient
  \(23(3489/2272)^{22}\), with completed-product `geRat`/`leRat` bounds around
  every simultaneous finite cutoff;
- `BF4CompletedConditionalTailBound.lean`: the exact conditional error is
  \(23(3489/2272)^{22}T\sum_{\rm path}V(\mathrm{path})\), with two-sided
  semantic bounds and a wrapper for the product of actual nonnegative local
  potential insertions;
- `BF4CompletedConditionalTailModulus.lean`: for a fixed rational nome and
  fixed finite retained carrier, the explicit cutoff
  \(\operatorname{powBaseCutoff}(\rho,\varepsilon/(K+1))\) makes that exact
  conditional tail at most \(\varepsilon\), including the local-potential
  specialization;
- `BF4CompletedConditionalGramLimitBridge.lean`,
  `BF4CompletedRankOneGramLimitBridge.lean`,
  `BF4CompletedFiniteGramLimitBridge.lean`, and
  `BF4CompletedCrossGramMatrixLimit.lean`: finite entrywise matrix
  amplification commutes with cutoff removal; separately supplied
  nonnegative weighted quadratic channels survive the limit; same-path
  rank-one squares are constructed from convergent bounded amplitudes; and
  arbitrary finite signed state combinations are carried through the exact
  Gram-to-SOS identity.  The completed cross-entry matrix is explicitly
  constructed and its quadratic is nonnegative for every finite rational
  test vector.  This finite Loewner conclusion comes from the supplied Gram
  amplitudes, not scalar entrywise order; physical slab-amplitude
  identification remains open;
- `SU2PointwiseHeatPositiveCompletion.lean`: for all rational \(0<w<1\),
  the completed heat series satisfies
  \(wK_w(x)\simeq D_w(x)\) and
  \(K_w(x)\simeq w^{-1}D_w(x)\), where \(D_w\) is the existing
  differentiated-Jacobi completion.  General-nome nonnegativity follows
  from `JTPIdentity.DiffJTP`; that differentiated product/double-limit
  identity remains an explicit uninhabited analytic leaf;
- `JTPFullProductDerivativeNormalization.lean`: the finite derivative of the
  full Jacobi product is exactly `Ppart * Spart` and therefore completes to
  the unhalved `Rproduct`.  This exposes a normalization error in the current
  Wall-2 pointwise product premise: `chebTConv` is the nonconstant half of
  theta, so the correct missing uniform identity is
  \(\vartheta_3\simeq1+2\,\mathrm{chebTConv}\), followed by affine-scaled
  derivative interchange, not direct equality of the full product with
  `chebTConv`;
- `BF4AggregatePathwiseOrderFence.lean`: an exact positive two-path family
  has grouped spread one while its required pre-integration spread exceeds
  every proposed rational constant.  Aggregate projective order therefore
  cannot supply the retained-path premise;
- `BF4RetainedSU2InterfaceGram.lean`: the actual finite-cutoff corrected
  SU(2) reflection slab is exactly a retained singleton-path weighted Gram
  kernel, with nonnegative interface weight and nonnegative quadratic form.
  An exact signed rank-one example proves that Gram/CP positivity does not
  imply entrywise retained kinetic positivity or scalar Harnack order;
- `BF4RetainedGramReferenceOrder.lean`: termwise comparison of physical and
  reference channel weights gives a two-sided Loewner sandwich for every
  finite weighted-Gram quadratic and every finite matrix amplification.  It
  applies to the actual retained SU(2) slab conditional on the now-explicit
  boundary-weight comparison; cutoff- and spacing-uniform construction of
  that comparison remains open;
- `BF4ConditionalCarrierLumpabilityFence.lean`: terminal-message
  lumpability of an actual post-fiber-integration kernel on its complete
  three-bit carrier, together with an exact counterexample when one retained
  source bit is forgotten;
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
- `U1SignedChargeHeatTail.lean`,
  `BF4U1ExponentGramCutoffTailBridge.lean`, and
  `BF4U1SignedChargeTailInstantiation.lean`: fixed-nome signed-charge cutoff
  control, finite-state amplification through the genuine U(1) reflection
  quadratic/block map, and a concrete tolerance modulus for every fixed
  slab with \(0<w<1\);
- `BF4U1ExponentGramOffDiagonalCutoff.lean`,
  `BF4U1FiniteExponentGramTailTube.lean`, and
  `BF4U1ActualExponentGramScoreTube.lean`: arbitrary left/right exponent
  coordinates, finite-coordinate error propagation, and an actual
  finite-atlas tube for the literal U(1) exponent-Gram score at fixed outer
  charge carrier, assuming the fine nome and every atlas candidate are below
  \(1\);
- `BF4U1OuterCutoffNesting.lean` and
  `BF4U1OuterCutoffUniformTensorTail.lean`, together with
  `BF4U1OuterCutoffTensorTailModulus.lean` and
  `BF4U1OuterCutoffFiniteFubiniTail.lean`, followed by
  `BF4U1OuterCutoffNormalizedEventTail.lean`: the exact cutoff-directed
  partition decomposition, a direct recursive heat-tail envelope independent
  of the outer carrier cardinality, its explicit fixed-nome/fixed-face-count
  modulus, its finite-Fubini/Haar domination of the genuine constrained
  new-sector mass, and a sharp normalized Boolean-event Cauchy modulus.
  `BF4U1OuterCutoffCRealLimit.lean` and its probability-algebra companions
  construct the Bishop-real limit with its unit-interval, monotonicity, and
  complement laws. `BF4U1OuterCutoffBlockGramTransport.lean` then identifies
  blocked/coarse entries with fixed events and proves explicit
  fixed-candidate score convergence, with thresholds paid at \(K\) and
  \(4K\). `BF4U1OuterCutoffAtlasUniformScoreTube.lean` takes the finite
  candidate maximum and constructs one complete-atlas Cauchy modulus under
  an explicit all-candidates-below-one hypothesis.
  `BF4U1OuterCutoffScoreCRealLimit.lean` constructs the candidate-wise Bishop
  score limit with exact finite-score approximants, convergence, and
  constructive uniqueness. Uniformity as the nome tends to one remains open;
- `SU2OuterCutoffUniformTensorTail.lean` and
  `SU2PhysicalOuterCutoffTensorTail.lean`, followed by
  `SU2PhysicalOuterCutoffFiniteFubiniTail.lean` and
  `SU2PhysicalOuterCutoffAnchorSchedule.lean`: respectively the free
  nonlinear channel tensor envelope, the physical degree-thirteen Casimir
  envelope forced by the exact four-dimensional link-multiplicity incidence
  ledger, the literal finite-Fubini comparison, and the executable
  \(S=1,\ M(r)=r\) anchor schedule.  The actual interacting anchor cutoff
  increment is bounded by the same outer-cutoff-independent tensor envelope
  without supplied arithmetic premises. SU(2) cutoff nesting,
  normalized-event control, total-tolerance rescaling, weak-coupling
  scheduling, and score transport remain open;
- `BF4ExponentGramLocatedStability.lean`: exact located-margin stability of
  finite SU(2)/U(1) argmins. Together these layers still do not construct the
  required spacing-uniform physical score tubes or located Yang--Mills
  separator;
- `BF4MatchedPhysicalAFBridge.lean`: a conditional constructor whose weight
  is definitionally routed through a matched finite BF4 argmin rather than
  the Padé formula. Its parameterized matching data remain supplied and do
  not themselves certify a genuine continuum trajectory. Supplied physical
  cubic-remainder and spacing certificates produce an `AFEnvelope` and the
  existing linear floor. Those certificates remain uninhabited.

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
dimension-weighted omitted tail.  The generic interior-potential oscillation
loss can now be avoided on an enlarged retained-path carrier: a pathwise
kinetic comparison passes through the complete nonnegative spatial weight
without changing its spread, and rank-one retained channels pass through
conditional integration as weighted Gram forms.  The actual finite BF4 slab
now has that Gram representation, and the finite SU(2) class-heat factor has
the exact pointwise corridor.  These two results do not yet compose: the
retained rank-one amplitudes can have signed off-diagonal products, and no
theorem identifies 23 positive class-heat factors with the interacting
retained slab kinetic channel.  What remains physical is a
positivity-improving regrouping or a Loewner/reference-order comparison on a
common retained carrier.  The finite Loewner implication is now proved; the
remaining datum is a physical reference-weight window with
cutoff-/spacing-uniform constants, together with cutoff-compatible all-label
convergence.  An alternative sufficient route
is the proved spacing-error convergence theorem, but its uniform
closeness-to-one hypothesis has not been established for the Yang--Mills
spatial weight.  The trajectory residual separately requires a block
constructor that extracts the next physical action from the pushed current
law; only then may the existing bare `AFEnvelope` and
`BareAFImpliesLinearFloor` be instantiated physically.

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
