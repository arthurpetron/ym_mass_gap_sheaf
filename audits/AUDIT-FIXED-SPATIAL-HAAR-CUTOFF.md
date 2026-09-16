# Actual completed-operator cutoff control and partial-Haar positivity

Date: 2026-09-16. Classification: PROGRESS after `350e095`.

Whole-project goal: constructive nontrivial continuum Yang--Mills on R^4,
the required QFT axioms, and a positive physical Hamiltonian gap for every
compact simple gauge group, on the SAME theory. Neither finite-width result
below closes that target or identifies the ordinary-Haar space with physical OS.

## Same-operator cutoff-Cauchy estimate

For rational 0<w<1, fixed spatial width and epsilon>0, the computed threshold

    max(headCutoff(w), productCutoff(w, stepFaceCount(width), epsilon))

gives, for every two later cutoffs J,K and EVERY completed vector x,

    ||(T_J-T_K)x||^2 <= epsilon^2 ||x||^2.

These are the previously constructed completed maps of the actual
`T_K f(y) = integral K_K(x,y) V_K(x) f(x) dH(x)`. The input vector does not
enter the threshold. Nome and spatial width do; no coupling/volume/spacing
uniformity or rate below one is asserted.

The finite product telescope retains every original relative and plaquette
word, including the complete low-spin head and precisely one head V.
`stepFaceCount` is the sum of temporal and spatial face counts. Existing
`sensitivity` is defined by S_0=0, S_(n+1)=prefixCap(w)*S_n+prefixCap(w)^n;
`productTolerance` and `productCutoff` turn its finite bound into an explicit
heat cutoff. Their definitions are in
`lean/YMGap/Continuum/BF4ExactSlabAllNomeProductTail.lean:49`, `:76`, `:93`.
The underlying `tailCutoff` is defined in
`lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:102`.

The difference of two weights is SIGNED. Its interval is squared, and ordinary
Haar Cauchy--Schwarz is applied to `(W_J-W_K)*f` and the retained test. The
result is not obtained by pretending that difference is a positive weight.
Choosing the output as test and rationally separating its positive/zero norm
gives the operator estimate. Quotient induction and the existing CReal limits
then pass it to arbitrary completion points.

Paths in the following tables have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `kernelMap_weight_difference` | `SU2QuaternionHaarSignedKernelBound.lean:55` | Actual signed weight difference equals the difference of the two maps. |
| `kernelMap_bilinear_bound`, `kernelMap_square_bound` | `SU2QuaternionHaarSignedKernelBound.lean:65`, `:114` | Interval alone suffices; no Certificate of the signed kernel. |
| `kernelMap_difference_bound` | `SU2QuaternionHaarSignedKernelBound.lean:139` | Dense norm-relative difference bound. |
| `stepFaceCount`, `stepTailCutoff` | `BF4ExactSlabFixedSpatialTransferTail.lean:58`, `:169` | Explicit actual face count and cutoff. |
| `stepWeightTailInterval` | `BF4ExactSlabFixedSpatialTransferTail.lean:173` | Actual finite later-prefix tail, any length. |
| `stepWeightDifferenceInterval`, `stepTailData` | `BF4ExactSlabFixedSpatialTransferTail.lean:192`, `:211` | Both cutoff orders handled; modulus returned as data. |
| `transferCutoff` | `BF4ExactSlabFixedSpatialCompletedCutoffControl.lean:39` | Includes the positivity threshold needed by the existing completed maps. |
| `transferStep_difference_bound` | `BF4ExactSlabFixedSpatialCompletedCutoffControl.lean:43` | Exact original polynomial steps satisfy the norm-relative estimate. |
| `completedTransfer_difference_bound` | `BF4ExactSlabFixedSpatialCompletedCutoffControl.lean:96` | Same bound for every point of the ordinary-Haar completion. |

This is an operator-norm Cauchy estimate, NOT a newly constructed limiting
operator. The next consumer must construct its representative/modulus,
prove quotient descent and convergence, and retain the original dense and
moment pins. No completed limit is selected from a proposition here.

## Actual partial-Haar certificate preservation

The square producer retains all tail coordinates. Split p by TOTAL head-degree
parity; cross terms have odd degree and vanish coefficientwise. Insert powers
of the head sphere radius to homogenize each sector without changing any tail
coefficient. The homogeneous square has the explicit positive sphere radial
denominator. The already checked Gaussian channel certificate, scaled by its
constructive rational reciprocal, gives the actual Haar certificate.

| Declaration | Module:line | Content |
|---|---|---|
| `partialHaarHead_mul_radius` | `SU2QuaternionHeadHaarSquareCertificate.lean:110` | Radius insertion preserves every retained coefficient. |
| `homogenizeHead_pair`, `homogenizeHead_supported`, `homogenizeHead_degree` | `SU2QuaternionHeadHaarSquareCertificate.lean:164`, `:176`, `:186` | Computed head-only homogenization, support and degree. |
| `homogeneous_square_certificate` | `SU2QuaternionHeadHaarSquareCertificate.lean:217` | Gaussian-to-Haar certificate using the positive radial factor. |
| `partialHaarHead_sector_square_split` | `SU2QuaternionHeadHaarSquareCertificate.lean:274` | Two same-parity squares; both cross terms vanish. |
| `sectorDegree`, `sector_square_certificate` | `SU2QuaternionHeadHaarSquareCertificate.lean:303`, `:321` | Explicit finite degree and sector certificates. |
| `partialHaarHead_square_certificate` | `SU2QuaternionHeadHaarSquareCertificate.lean:336` | Concrete supported-square producer; no analytic positivity input. |
| `partialHaarHeads_carrier`, `partialHaarHead_carrier` | `SU2QuaternionHaarCertificateIntegration.lean:62`, `:70` | Fubini retains arbitrary tail insertions, not just the bare integral. |
| `partialHaarHead_certificate`, `partialHaarHeads_certificate` | `SU2QuaternionHaarCertificateIntegration.lean:77`, `:91` | Actual certificate recursion under one or any number of ordered Haar integrations. |

The next actual-transfer consumer needs to enlarge a SUPPORTED input message
certificate from N to N+N blocks before multiplying by W and integrating.
That support-guarded construction is not included in this checkpoint.
Unconditional certificate enlargement is false: arbitrary-insertion transport
on N blocks can hide off-carrier polynomial terms which become visible when
the carrier grows. No such rule was postulated.

Neither certificate positivity of an integration weight nor preservation of
the polynomial positive cone asserts positive-semidefiniteness/self-adjointness
of the completed transfer. Quantitative boundary forgetting, stationary vacuum,
physical OS identification, controlled width/spacing passage, continuum QFT
and the all-group physical gap remain open.

## Verification boundary

Five focused serialized one-worker/20 GiB checks passed all 29 public axiom
gates within {propext, Quot.sound}. Fixes were local namespace, macro layout,
tactic sequencing and beta-reduction before a rewrite. No analytic premise,
literal hole, axiom, old statement or canonical frontier field changed.
An independent read-only review found no mathematical mismatch in the signed
estimate, original weights, completed-vector quantifier or uniformity scope.
Five selective-root imports added; root/full-tree verification and the full
axiom audit were not run. CI remains manual-only.

| Focused log in `/tmp/` | SHA-256 |
|---|---|
| `SU2QuaternionHeadHaarSquareCertificate.log` | `fcfbd42b8bad27cbb3963f02502f42784a66a91a898cc11a2bc01cebdfbfc1c2` |
| `SU2QuaternionHaarCertificateIntegration.log` | `6ba102672081a6fc9cdf9460d345de1ac60df682c12be6bb68eadcde9761687c` |
| `SU2QuaternionHaarSignedKernelBound.log` | `5ebb3955549b058c9546197722aa90dec4b3dd4fdf4834bf53e42d00f55553b8` |
| `BF4ExactSlabFixedSpatialTransferTail.log` | `bcca1dc347b84c5277f77e6e3a01bb82bd6cba9f9262e3cf1bc64e424b679b67` |
| `BF4ExactSlabFixedSpatialCompletedCutoffControl.log` | `8988f33cc2c4a7c24e321a91b367fae7e211b12f92c182653a4cc729a625560d` |
