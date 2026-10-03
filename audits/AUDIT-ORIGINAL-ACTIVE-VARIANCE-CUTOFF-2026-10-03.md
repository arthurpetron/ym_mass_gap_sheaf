# Original active variance: linear near-unit cutoff comparison

## Mathematical increment

A constructed comparison transfers the actual ORIGINAL projected conditional
variance to an auxiliary later-cutoff variance with ONE factor 1+eta. The
source, original action, incoming depths, output transfer and output score
remain at ORIGINAL cutoff K. Only the reference conditional kinetic kernel
uses L. Arbitrary certified surviving output weights remain present.

This pays a representation-cutoff comparison leg. It does NOT construct the
reference conditional angular Poincare estimate or the useful complete
signed-window budget on a justified changing family. No continuum, physical
Hamiltonian mass, every-group or Clay conclusion follows here.

## Linear variance comparison, with each kernel's own mean

All declarations in this section are in
`lean/YMGap/Continuum/SU2QuaternionConditionalVarianceOrder.lean`.

Let I integrate the first heads quaternion blocks and retain tail blocks.
The conditional kernels P,R have actual arbitrary-insertion Haar pins
I(P)=I(R)=1, not free-polynomial coefficient identities. Let

```text
v=I(P*Q), m=I(R*Q), z=Q-lift(m),
Var_P=determinant(heads,P,Q), Var_R=determinant(heads,R,Q).
```

`centeredSquare` (:54) and `centered_square_minimization_pin` (:105) prove

```text
I[P*z^2] = Var_P + (v-m)^2
```

under EVERY surviving Haar insertion. `conditional_variance_order_certificate`
(:144) constructs a positivity certificate for c*Var_R-Var_P from a certificate
for c*R-P, using

```text
c*Var_R-Var_P = I[(c*R-P)*z^2] + (v-m)^2.
```

The mean mismatch is retained, not deleted. The comparison is linear in c,
not quadratic. The support hypotheses on P,R,Q and both unit pins are explicit.
No conditional mass, source or variance is inverted. The generic identity
needs no c>=0 assumption; its supplied order certificate is the actual input.
`conditional_variance_order_weighted` (:200) retains ANY certified upper W:
H[W*Var_P] <= c*H[W*Var_R], including zero W.

## Computed near-unit product-kernel factor

All declarations in this section are in
`lean/YMGap/Continuum/SU2QuaternionProductHeatRelativeCutoff.lean`.

For 0<w<1, 0<eta<=1 and count m, `factorTolerance` (:60) and
`productRelativeCutoff` (:63) compute

```text
delta=eta/(2*m+2),
C=max(headCutoff(w), tailCutoff(w,delta*headFloor(w))).
```

`heatAt_differenceInterval` (:158) bounds the actual finite-prefix difference
by the explicit tail interval, for ANY K,L>=C. It handles either cutoff
ordering; a prefix is not silently treated as an infinite heat kernel.
The existing positive head floor and the tail bound give a per-factor order
certificate. `factor_power_le` (:238) proves (1+delta)^m <= 1+eta using a
positive inverse-Bernoulli guard, not an exponential-volume comparison.

`productHeat_relative_upperCertificate` (:329) constructs

```text
(1+eta)*productHeat(n,w,L,ids) - productHeat(n,w,K,ids) >= 0.
```

Every occurrence in ids is counted; the theorem allows repeated factors and
the empty product. Swapping K,L gives the reverse comparison. Product-kernel
comparison itself does not need a distinctness premise. The later actual
unit-marginal use DOES use the original active list's proved distinctness.

The factor 1+eta is independent of source, degree, cutoff ordering and list
size. Its constructed onset C depends explicitly on w, eta and m. This is
NOT a coupling-, spacing- or spatially-uniform cutoff or rate.

## Join to the ORIGINAL projected active Jensen debt

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean`.
For the ORIGINAL source pair a,c write

```text
Q_K=lastStepProjectedDerivative(w,K,width,s,i,j,a,c),
P_K=kineticWeight(w,K,width),
S_K=conditionalScore(D,transferStep_K(a),transferStep_K(c)),
V_K=lastStepProjectedDerivativeBudget_K-S_K^2.
```

The COMPLETE Q_K still contains the original action derivative; the lower
fringe has already been integrated before squaring by the previous checked
milestone. `kinetic_conditional_unit` (:56) proves I(P_K)=1 under EVERY
surviving insertion for every w,K. It uses the original active-block list,
`activeBlocks_nodup`, actual `productMap_one` and `carrier_of_supported`.
It does not claim coefficient equality or require a source normalization.

`projectedVarianceCutoff` (:71) computes C using the actual active-factor
count. `projectedActiveVariance` (:75) defines V_K with the original transfer
score. `projectedReferenceVariance` (:83) is

```text
Vref_(K,L)=determinant(N(width), P_L, Q_K).
```

The source remains Q_K, NOT Q_L. `variance_pin` (:88) uses the existing
arbitrary-insertion original score pin to identify V_K with the P_K
determinant, retaining its literal kinetic mass.
`projected_variance_cutoff_certificate` (:103) constructs

```text
(1+eta)*Vref_(K,L)-V_K >= 0,       K,L>=projectedVarianceCutoff.
```

`projected_variance_cutoff_weighted_le` (:133) gives

```text
H[W*V_K] <= (1+eta)*H[W*Vref_(K,L)]
```

for arbitrary certified W, supported original a,c, and the actual block/plane
indices. In particular the literal original Vbar^2*G_k^2 can be inserted
without a false independence assumption. No source, terminal mass, surviving
norm or variance inverse occurs. The reference kernel is auxiliary weighting,
not a substituted Yang--Mills theory, transfer operator or excitation.

## Forward/backward connection and remaining producer

The existing backward endpoint is `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
It requires the COMPLETE original normalized window cost relative to the
original window-start variance, with each lag's own partitions and common
stage OWN center. The cutoff comparison does not supply this input, nor does
it telescope the raw source, Taylor or action terms separately.

Next concrete analytic producer: a conditional angular variance bound for
the auxiliary kernel applied to Q_K, retaining shared surviving variables
and W. A source-specific L can be taken beyond the finite degrees without
changing the ORIGINAL K-source; the source-independent relative comparison
is now available. This choice alone is not the Poincare proof.

Source/math review found a possible finite-polynomial Bochner/heat-flow
route, NOT a checked result of this milestone. Existing
`polynomial_heat_pairing_above_cutoff`,
`lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:210`,
has explicit exponent ell*(ell+2) and a computed fixed-input cutoff. It is
not a conditional Poincare theorem or a changing-source uniform bound.
`retainedImage`,
`lean/YMGap/Continuum/SU2QuaternionHarmonicHeatInsertion.lean:42`, replaces
the head by the existing retained block. Composing Q(x,y,z) there would
identify x with y. The existing spectator-preserving `headMap`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:247`, uses
`SpareHeadCopy.copy` to supply a distinct output; its actual expansion is
`headMap_grouped`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatSmoothing.lean:64`. Reuse this
placement rather than silently identifying shared parameters. The angular Lie-bracket,
Bochner square, saturated endpoint, composition and derivative-order steps
are NOT provided by this comparison. Do not assume them.

## Verification boundary

Three focused, serialized checks exited zero with 14 printed gates:

| Target | Accepted log | Gates |
| --- | --- | --- |
| SU2QuaternionConditionalVarianceOrder | `/tmp/ym-conditional-variance-order-20261003-2.log` | 4 |
| SU2QuaternionProductHeatRelativeCutoff | `/tmp/ym-product-relative-cutoff-20261003-2.log` | 4 |
| BF4ExactSlabFixedSpatialProjectedVarianceCutoff | `/tmp/ym-projected-variance-cutoff-20261003-3.log` | 6 |

Each command used `scripts/safe_lean_build.py --jobs 1 --reserve-gib 12
--check-worker-limit-gib 20 --status-seconds 300`, the named source and an
explicit olean output. Fresh preflights found 76--77% memory free, zero swap
and no competing Lean worker. No full/root build or full axiom audit is claimed.
Two gates are axiom-free; all others are subsets of {propext, Quot.sound}.
No accepted log contains errors, warnings, sorryAx or Classical.choice.
Earlier failed elaboration attempts are rejected, not proof evidence.

Independent read-only reviews passed the actual own-mean algebra, arbitrary
weights, original K/L split, real unit pins, either cutoff ordering and
repeated/empty products. No new sorry, axiom, weakened field or CI change.
Root imports register the checked leaves only; the exact chart is unchanged.

SHA-256, accepted source snapshots:

```text
d7af2262a9f0729dcddc86292a551440a776f7c6465c4ce90ecbe0a910a1eb67  SU2QuaternionConditionalVarianceOrder.lean
0df5bf95024dabceb8b681852e76cef0690f4adc9eb60ecfc211173052c9d33c  SU2QuaternionProductHeatRelativeCutoff.lean
3e68c40fcc20aee9679c21dd84113e7a037ceba76c888ad346d17e156bbea3ea  BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean
```

SHA-256, accepted logs in table order:

```text
22ce5a3a8913d49156eaee9803ef021bf8bec831cc053ce575f60f9ecc66ff21
4255f50f06884c7f8c9487159b6314706dbdd736273e8f8ebc887787638427b2
67b0a500ba71eaaa8591696a0a1409b71f793c76ec4e31b8f4127732fd5a46bc
```

OPEN: useful reference conditional variance versus angular energy and SAME
surviving norm; complete signed Taylor/action cancellation; justified changing
family and aggregate window budget; physical calibration/survival; full
same-theory continuum QFT; every compact simple group; Clay closure.
