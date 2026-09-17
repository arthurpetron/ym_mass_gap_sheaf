# Current Wilson complexification and the next kinetic-positivity join

Date: 2026-09-17, source baseline `e2468d4`. This report separates new
kernel-checked algebra from source-level mathematical planning.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, isolated
vacuum and positive finite physical Hamiltonian mass gap. **OPEN.**

## 1. A backward requirement met by existing forward inputs

The current real Wilson carrier has its own pairing, witnessed scalar
action, time maps and Wilson multipliers. Its direct complexification is
now constructed without changing those objects. All paths in this table
are under `lean/YMGap/Continuum/`.

| Output | Declaration and source | Scope |
| --- | --- | --- |
| Actual pair carrier | `ComplexCarrier`, `BF4WilsonSpatialUnionComplexification.lean:199` | Two copies of CURRENT `UnionCompletion`, not the old plaquette carrier. |
| Hermitian form | `inner`, `BF4WilsonSpatialUnionComplexification.lean:210`; `inner_conj_symm`, :262 | B(x,u)+B(y,v) + i[B(x,v)-B(y,u)], conjugate-linear first slot. |
| Exact real inclusion | `inner_embedReal`, `BF4WilsonSpatialUnionComplexification.lean:258`; `embedReal_injective`, :231 | Preserves the original pairing and does not collapse vectors. |
| Positive definiteness | `inner_posdef`, `BF4WilsonSpatialUnionComplexification.lean:285` | Vanishing norm means BOTH original real components vanish. |
| Witnessed scalar action | `complexSmul`, `BF4WilsonSpatialUnionComplexification.lean:214`; `inner_smul_right`, :321; `inner_smul_left`, :331; `complexSmul_congr`, :337 | Two CReal components and their explicit QCauchy data; no arbitrary quotient representative selected. |
| Same operators | `complexTime_smul`, `BF4WilsonSpatialUnionComplexification.lean:360`; `inner_time_balance`, :366; `complexMultiply_smul`, :382; `complexMultiply_comm`, :393 | Original maps act componentwise; their embedding pins and algebraic laws are proved. |
| Actual complex vacuum | `complexUnit`, `BF4WilsonSpatialUnionComplexBounds.lean:54`; `complexUnit_fixed`, :58; `complex_orthogonal_iff`, :68 | Orthogonality is exactly the conjunction of BOTH real vacuum-complement conditions. |
| Even positivity | `inner_even_diagonal`, `BF4WilsonSpatialUnionComplexBounds.lean:82`; `inner_even_nonnegative`, :85 | Full complex equality to the half-time norm, including zero imaginary part. Not odd-time positivity. |
| Same quantitative decay | `complexTime_norm_decay`, `BF4WilsonSpatialUnionComplexBounds.lean:97`; `complex_even_form_decay`, :105 | ALL complex vacuum-complement vectors, unchanged q^n, by adding the two existing real estimates. |
| Same observable cap | `complexMultiply_norm_bound`, `BF4WilsonSpatialUnionComplexBounds.lean:116` | Original characterBound, with no factor-of-two degradation. |

The rate is the existing `twoStepRate`, defined in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`;
`twoStepRate_lt_one` there at :72 supplies its strictness under the existing
guards. The new files retain the original small-nome hypotheses. This is
not a new estimate beyond that regime, nor a spacing-uniform physical mass.

The remaining complex scalar-field/module packaging is NOT supplied.
Neither is arbitrary quotient-sequence completeness: `CauchyRows`,
`lean/YMGap/Continuum/CRealSeminormCauchyRows.lean:50`, takes actual
representative rows as data. The existing `PositiveTimeOSRoot`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, still uses `GNSData`, whose
`B` is Q'-valued (`lean/YMGap/Continuum/GNSQuotient.lean:102`). This new
RC-pair form does not inhabit that root or rationalize the current pairing.
No canonical field, analytic guard or full QFT requirement changes.

## 2. The primary generated-orbit obstruction remains analytic

The parallel source review did not find a beyond-small-nome generated-orbit
bound. The following are statements about inspected source, not a new
counterexample or a proof of impossibility.

- `family_energy_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`,
  bounds coefficients of a fundamental-plaquette span. It does not give
  invariance of that span under the original transfer.
- `original_transfer_haar_active`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:87`,
  removes fringe variables under a stated independence hypothesis;
  `energy_active`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`,
  retains the full active spatial action and terminal messages.
- `conditionalMessage`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:58`,
  integrates the full V*g_n. Independence of its erased coordinate
  (`conditionalMessage_independent`, :71) is not a fixed local-support
  theorem for the generated orbit.
- `actualResidual_corrected_energy`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`,
  retains the joint correction D+2*h*R in its upper factor. R includes the
  message determinant `messageDeterminant`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:141`, via
  `determinantCross` at :171. `joint_remainder_nonnegative`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedCostPositive.lean:108`,
  proves a LOWER bound, not the upper budget needed for decay.
- `sourceCost`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReciprocalSourceBudget.lean:65`,
  and `family_norm_le_sourceCost` at :73 retain source information, but
  `family_norm_budget`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedNormBudget.lean:149`,
  still has density-contrast dependence on cutoff, width and depth.

**NOT FOUND:** the required regulator-controlled upper budget for the
actual generated Wilson source and its signed joint remainder. Search
scope: the modules above, `BF4ExactSlabFixedSpatialDirichletForm.lean`,
`SU2QuaternionProductHeatMarginals.lean`, and the separated-orbit sources
listed in `AUDIT-FUSION-TEMPORAL-CONSUMER-2026-09-17.md`.
No new structure merely assuming this conclusion was introduced.

## 3. A separate finite backward join: actual kinetic PSD

Current one-step form positivity is **NOT FOUND** in the inspected Wilson
intrinsic/time-form and completion modules. `completedInner_even_nonnegative`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeForm.lean:119`, is explicitly
even-time only. `reflectedWindowRatio_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive.lean:85`,
uses the site-reflection selected-action construction.
`completedTime_one_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicOneStepPositivity.lean:51`,
uses the different `BF4ExactSlabThermodynamicSeminormCompletion.Completion`.
No current-carrier identification was found in those modules.

The reviewed finite target, NOT yet implemented, is

    0 <= H_n[(productMap n w K ids f) * f]

for w>=0, every cutoff K, supported f and selected indices i<n.
It concerns the actual kinetic kernel, not merely its pointwise-positive
density or a Markov spectral gap. Existing source inputs are:

| Input | Declaration and source |
| --- | --- |
| Actual map and pairing | `productMap`, `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:52`; `productMap_pairing`, :247 |
| Character Gram under arbitrary insertions | `character_haar_gram_of_unit_radii`, `lean/YMGap/Continuum/SU2QuaternionSymmetricPowerKernelGram.lean:189`; actual `polynomialColumn`, :129; `polynomialGramKernel`, :159 |
| Coordinate unit radius | `haarNorm_coordinate`, `lean/YMGap/Continuum/BF4ExactSlabSymmetricPowerHaarTrace.lean:92` |
| Scalar coordinate-product pin | `pathProduct_scalar`, `lean/YMGap/Continuum/BF4ExactSlabPlaquettePathGram.lean:105` |
| Positive Gram weights | `basisInverseWeight_pos`, `lean/YMGap/Continuum/SU2QuaternionSymmetricPowerPolynomialBasis.lean:170` |
| Nonnegative heat coefficients | `coeffAt_heatKernelPacket`, `lean/YMGap/Continuum/Z4FiniteBoxHeatKernelPacketState.lean:64`; `coeffW_nonneg`, `lean/YMGap/Continuum/BondMovingStep.lean:261` |
| Exact separated-half factorization | `haar_split_pairing`, `lean/YMGap/Continuum/SU2QuaternionHaarMarkovContraction.lean:51` |

Paper argument: expand one heat factor as a finite positive sum of real
Gram channels c*a(x)*a(y). Then the quadratic Q_(i::ids)(f) is the sum of
c*Q_ids(f*a). Induct directly on ids; the empty product gives H_n(f)^2.
No distinctness assumption on ids is mathematically needed by this argument.
This paragraph is a proof plan, not a Lean theorem or axiom-status claim.

**NOT FOUND / next algebraic work:** generic coordinate-column support,
the upper-column `liftBoundary` identity, local heat insertion expansion,
and the final induction. Searched the Gram and product-heat modules above,
`SU2QuaternionAuxiliaryLiftAlgebra.lean`,
`BF4ExactSlabSpatialChannelReflection.lean` and
`BF4ExactSlabReflectedSquareHaarForm.lean`. The latter files have
slab-specific column reflection/support proofs, not these literal joins.

The actual original transfer consumer retains V in BOTH factors:
H[V*f*T f] = H[(V*f)*P(V*f)]. The source identity is private
`transfer_product`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:64`, with
weighted pairing algebra in private `weighted_step_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:85`.
An additional same-object pin and limit passage to the CURRENT Wilson
one-step form remain open even after kinetic PSD is proved. Neither this
positivity nor complexification supplies the primary strict analytic
estimate or physical mass calibration.

## 4. Verification and review boundary

Both final focused checks exited successfully, serialized with one worker
and an explicit 20 GiB cap through `scripts/safe_lean_build.py`. All 40
complexification and 11 bounds printed gates have only allowed axioms
{propext, Quot.sound}. No sorry introduced or discharged. The first base
check failed on layout of pattern alternatives and a quotient-induction
goal; these were corrected before the clean final check. The consumer
passed its first run after an independent source reviewer caught a missing
namespace open. No mathematical statement changed during these fixes.

Parent inspected both full sources. Independent reviewers checked the
Hermitian signs, explicit moduli, both vacuum conditions, same-rate sum
and same operators. Separate reviewers investigated the generated-source
and kinetic-PSD paths without compiling or editing their sources.

| Artifact | SHA256 |
| --- | --- |
| `/tmp/ym-wilson-complexification-retry1-20260917.log` | `b2cbac634c7896e0362b7f15aa362744bebf708e6dd1ae8aa97a377a6b20f3cd` |
| `/tmp/ym-wilson-complex-bounds-20260917.log` | `1a36b2207528d9e46a8c3578a872bb72463c842c5256d55fa97bc42a06f4e328` |
| `BF4WilsonSpatialUnionComplexification.lean` | `1d87f14235215fdb77cead7eca06c0bc492d8c3f471f8204c805792f03e7f3fa` |
| `BF4WilsonSpatialUnionComplexBounds.lean` | `32d7d01d3516bfc0e564814036b8c4a58754a7d9541352afcdd71023b7860baa` |

Two semantic-root imports were added. A full root/full-tree build, audit,
guard or progress run was NOT performed. CI and resource policy are
unchanged. This report closes no canonical continuum/Clay frontier atom.
