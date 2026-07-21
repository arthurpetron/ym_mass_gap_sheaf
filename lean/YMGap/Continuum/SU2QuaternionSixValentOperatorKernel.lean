/-
# Canonical balanced six-valent operator Haar kernel

The balanced `F F F R R R` sixth moment is the Haar projector on the
three-leg fundamental operator space.  This leaf fixes the operator-index
wiring explicitly:

* the first three factors are `F(targetOutput, sourceOutput)`;
* the last three factors are `R(sourceInput, targetInput)`.

The latter order is essential because `reverseFundamentalCoefficient`
already contains conjugate transpose.  With this wiring, the existing signed
inverse-Gram kernel becomes a manifest sum of five positive normalized
Temperley--Lieb rank-one channels.  We prove the exact positive resolution,
pure reality, self-adjointness, and trace mass five without enumerating the
twelve external Boolean indices or any six-bit assignment family.

The existing channel Gram supplies the finite-dimensional algebraic core of
idempotence.  We record that core here, but deliberately do not claim a raw
Boolean-middle-index square theorem: the current public API does not yet
identify the six-bit channel-coordinate inner product with the pulled-back
TL Gram without opening a deep Boolean sum.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge

namespace YMGap.Continuum.SU2QuaternionSixValentOperatorKernel

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionSixValentPairingGram
open YMGap.Continuum.SU2QuaternionSixValentTemperleyLiebChannelBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Three-leg operator coordinates -/

/-- One Boolean matrix coordinate on each of three ordered fundamental legs. -/
structure ThreeLegOperatorIndex where
  firstOutput : Bool
  firstInput : Bool
  secondOutput : Bool
  secondInput : Bool
  thirdOutput : Bool
  thirdInput : Bool
deriving DecidableEq, Repr

/-- The signed scalar Haar-projector entry with canonical operator wiring.
Forward factors store `(targetOutput,sourceOutput)`; reverse factors store
`(sourceInput,targetInput)`. -/
def balancedSixValentOperatorKernelScalar
    (target source : ThreeLegOperatorIndex) : Q' :=
  orientedSixFundamentalHaarProjectorScalar
    target.firstOutput source.firstOutput
    target.secondOutput source.secondOutput
    target.thirdOutput source.thirdOutput
    source.firstInput target.firstInput
    source.secondInput target.secondInput
    source.thirdInput target.thirdInput

/-- Rational-complex form of the canonical operator kernel. -/
def balancedSixValentOperatorKernel
    (target source : ThreeLegOperatorIndex) : RationalComplex :=
  (balancedSixValentOperatorKernelScalar target source, 0)

/-- Matrix transpose on the two three-leg operator coordinates. -/
def balancedSixValentOperatorKernelTranspose
    (target source : ThreeLegOperatorIndex) : RationalComplex :=
  balancedSixValentOperatorKernel source target

/-! ## 2. Manifest positive TL-channel resolution -/

/-- The six-index tensor coordinate of one orthogonal TL channel. -/
def sixValentOperatorChannelCoordinate
    (channel : SixValentTLChannel) (index : ThreeLegOperatorIndex) : Q' :=
  sixValentTLChannelOrientedPairing channel
    index.firstOutput index.secondOutput index.thirdOutput
    index.firstInput index.secondInput index.thirdInput

/-- The coefficient-resolved form of the canonical operator kernel. -/
def balancedSixValentOperatorTLResolvedScalar
    (target source : ThreeLegOperatorIndex) : Q' :=
  orientedSixFundamentalHaarProjectorTLResolvedScalar
    target.firstOutput source.firstOutput
    target.secondOutput source.secondOutput
    target.thirdOutput source.thirdOutput
    source.firstInput target.firstInput
    source.secondInput target.secondInput
    source.thirdInput target.thirdInput

/-- Five positive rank-one TL channels.  Every displayed weight is the
inverse of the corresponding positive channel norm. -/
def balancedSixValentOperatorTLPositiveScalar
    (target source : ThreeLegOperatorIndex) : Q' :=
  sixValentTLChannelSum (fun channel =>
    sixValentTLChannelInverseWeight channel *
      (sixValentOperatorChannelCoordinate channel target *
        sixValentOperatorChannelCoordinate channel source))

/-- Rational-complex form of the manifest positive channel resolution. -/
def balancedSixValentOperatorTLPositive
    (target source : ThreeLegOperatorIndex) : RationalComplex :=
  (balancedSixValentOperatorTLPositiveScalar target source, 0)

/-- Exact replacement of the signed inverse Gram matrix by its positive
TL-channel resolution, with no Boolean case split. -/
theorem balancedSixValentOperatorKernelScalar_eqv_TL_resolution
    (target source : ThreeLegOperatorIndex) :
    balancedSixValentOperatorKernelScalar target source ≈
      balancedSixValentOperatorTLResolvedScalar target source := by
  exact orientedSixFundamentalHaarProjectorScalar_eqv_TL_resolution
    target.firstOutput source.firstOutput
    target.secondOutput source.secondOutput
    target.thirdOutput source.thirdOutput
    source.firstInput target.firstInput
    source.secondInput target.secondInput
    source.thirdInput target.thirdInput

/-- The resolved coefficient kernel is the manifest five-channel rank-one
factorization. -/
theorem balancedSixValentOperatorTLResolvedScalar_eqv_positive
    (target source : ThreeLegOperatorIndex) :
    balancedSixValentOperatorTLResolvedScalar target source ≈
      balancedSixValentOperatorTLPositiveScalar target source := by
  exact orientedSixFundamentalHaarProjectorTLResolvedScalar_eqv_factorized
    target.firstOutput source.firstOutput
    target.secondOutput source.secondOutput
    target.thirdOutput source.thirdOutput
    source.firstInput target.firstInput
    source.secondInput target.secondInput
    source.thirdInput target.thirdInput

/-- **Canonical positive resolution of the balanced six-valent operator
kernel.**  The signed entries are exactly the sum of five rank-one channel
tensors with positive weights `1/4,1/2,1/2,2/3,2/3`. -/
theorem balancedSixValentOperatorKernelScalar_eqv_positive
    (target source : ThreeLegOperatorIndex) :
    balancedSixValentOperatorKernelScalar target source ≈
      balancedSixValentOperatorTLPositiveScalar target source := by
  exact Q'.eqv_trans _ _ _
    (balancedSixValentOperatorKernelScalar_eqv_TL_resolution target source)
    (balancedSixValentOperatorTLResolvedScalar_eqv_positive target source)

/-- Rational-complex form of the exact positive resolution. -/
theorem balancedSixValentOperatorKernel_eqv_positive
    (target source : ThreeLegOperatorIndex) :
    RationalComplexEqv
      (balancedSixValentOperatorKernel target source)
      (balancedSixValentOperatorTLPositive target source) :=
  ⟨balancedSixValentOperatorKernelScalar_eqv_positive target source,
    Q'.eqv_refl 0⟩

/-- Every channel inverse norm is strictly positive. -/
theorem sixValentOperatorChannelInverseWeight_positive
    (channel : SixValentTLChannel) :
    (0 : Q') < sixValentTLChannelInverseWeight channel := by
  cases channel <;>
    unfold sixValentTLChannelInverseWeight oneQuarter channelOneHalf
      channelTwoThirds <;>
    decide

/-- Every channel norm is strictly positive. -/
theorem sixValentOperatorChannelNorm_positive
    (channel : SixValentTLChannel) :
    (0 : Q') < sixValentTLChannelNorm channel := by
  cases channel <;>
    unfold sixValentTLChannelNorm channelThreeHalves <;>
    decide

/-! ## 3. Pure reality and self-adjointness -/

/-- The canonical balanced operator kernel is pure real. -/
theorem balancedSixValentOperatorKernel_pureReal
    (target source : ThreeLegOperatorIndex) :
    (balancedSixValentOperatorKernel target source).2 ≈ 0 :=
  Q'.eqv_refl 0

/-- The manifest positive channel scalar is symmetric in target and source. -/
theorem balancedSixValentOperatorTLPositiveScalar_symmetric
    (target source : ThreeLegOperatorIndex) :
    balancedSixValentOperatorTLPositiveScalar target source ≈
      balancedSixValentOperatorTLPositiveScalar source target := by
  unfold balancedSixValentOperatorTLPositiveScalar
  exact sixValentTLChannelSum_eqv_congr _ _ (fun channel =>
    Q'.mul_eqv_congr_left
      (sixValentTLChannelInverseWeight channel)
      (sixValentOperatorChannelCoordinate channel target *
        sixValentOperatorChannelCoordinate channel source)
      (sixValentOperatorChannelCoordinate channel source *
        sixValentOperatorChannelCoordinate channel target)
      (Q'.mul_comm_eqv _ _))

/-- The signed operator kernel is symmetric because its exact positive
rank-one resolution is symmetric. -/
theorem balancedSixValentOperatorKernelScalar_symmetric
    (target source : ThreeLegOperatorIndex) :
    balancedSixValentOperatorKernelScalar target source ≈
      balancedSixValentOperatorKernelScalar source target := by
  refine Q'.eqv_trans _ _ _
    (balancedSixValentOperatorKernelScalar_eqv_positive target source) ?_
  refine Q'.eqv_trans _ _ _
    (balancedSixValentOperatorTLPositiveScalar_symmetric target source) ?_
  exact Q'.eqv_symm
    (balancedSixValentOperatorKernelScalar_eqv_positive source target)

/-- The canonical balanced six-valent operator kernel is self-adjoint. -/
theorem balancedSixValentOperatorKernel_selfAdjoint
    (target source : ThreeLegOperatorIndex) :
    RationalComplexEqv
      (balancedSixValentOperatorKernel target source)
      (balancedSixValentOperatorKernelTranspose target source) :=
  ⟨balancedSixValentOperatorKernelScalar_symmetric target source,
    Q'.eqv_refl 0⟩

/-! ## 4. Actual trace and resolved trace mass -/

/-- Inner three-Bool diagonal contraction over the operator input indices,
leaving the three output indices opaque. -/
def balancedSixValentOperatorInputDiagonalSum
    (firstOutput secondOutput thirdOutput : Bool) : Q' :=
  rationalThreeBoolSum (fun firstInput secondInput thirdInput =>
    balancedSixValentOperatorKernelScalar
      ⟨firstOutput, firstInput, secondOutput, secondInput,
        thirdOutput, thirdInput⟩
      ⟨firstOutput, firstInput, secondOutput, secondInput,
        thirdOutput, thirdInput⟩)

/-- The inner operator trace is definitionally the existing reverse-index
partial trace. -/
theorem balancedSixValentOperatorInputDiagonalSum_eq_reverseDiagonalSum
    (firstOutput secondOutput thirdOutput : Bool) :
    balancedSixValentOperatorInputDiagonalSum
        firstOutput secondOutput thirdOutput =
      orientedSixFundamentalProjectorReverseDiagonalSum
        firstOutput secondOutput thirdOutput := by
  rfl

/-- Full operator trace, factored into two three-Bool contractions. -/
def balancedSixValentOperatorKernelDiagonalTrace : Q' :=
  rationalThreeBoolSum (fun firstOutput secondOutput thirdOutput =>
    balancedSixValentOperatorInputDiagonalSum
      firstOutput secondOutput thirdOutput)

/-- The actual operator trace is the existing signed-projector trace. -/
theorem balancedSixValentOperatorKernelDiagonalTrace_eq_existing :
    balancedSixValentOperatorKernelDiagonalTrace =
      orientedSixFundamentalHaarProjectorDiagonalTrace := by
  rfl

/-- The actual balanced operator projector has trace five. -/
theorem balancedSixValentOperatorKernel_trace_exact :
    balancedSixValentOperatorKernelDiagonalTrace ≈ 5 := by
  change orientedSixFundamentalHaarProjectorDiagonalTrace ≈ 5
  exact orientedSixFundamentalHaarProjector_diagonal_trace_exact

/-- Structural trace mass of the positive orthogonal TL resolution. -/
def balancedSixValentOperatorTLResolvedTraceMass : Q' :=
  sixValentTLChannelSum (fun channel =>
    sixValentTLChannelInverseWeight channel *
      sixValentTLChannelNorm channel)

/-- Every normalized rank-one TL channel contributes trace one. -/
theorem balancedSixValentOperatorTLChannel_trace_one
    (channel : SixValentTLChannel) :
    sixValentTLChannelInverseWeight channel *
        sixValentTLChannelNorm channel ≈ 1 :=
  sixValentTLChannel_weighted_trace_one channel

/-- **Resolved trace mass.**  The five positive normalized channels have
total mass five. -/
theorem balancedSixValentOperatorTLResolvedTraceMass_exact :
    balancedSixValentOperatorTLResolvedTraceMass ≈ 5 :=
  sixValentTLChannel_total_weighted_trace_five

/-- The actual signed trace and the manifest positive-resolution trace mass
agree exactly. -/
theorem balancedSixValentOperatorKernel_trace_eqv_TLResolvedTraceMass :
    balancedSixValentOperatorKernelDiagonalTrace ≈
      balancedSixValentOperatorTLResolvedTraceMass := by
  exact Q'.eqv_trans _ 5 _
    balancedSixValentOperatorKernel_trace_exact
    (Q'.eqv_symm balancedSixValentOperatorTLResolvedTraceMass_exact)

/-! ## 5. Channel-space idempotence core -/

/-- The algebraic middle-channel inner product supplied by the pulled-back
pairing Gram.  A later shallow-sum bridge must identify this with the actual
six-Boolean inner product of `sixValentOperatorChannelCoordinate`. -/
def balancedSixValentOperatorChannelPulledBackInner
    (left right : SixValentTLChannel) : Q' :=
  sixValentTLChannelPulledBackGram left right

/-- The pulled-back channel inner product is exactly diagonal. -/
theorem balancedSixValentOperatorChannelPulledBackInner_exact
    (left right : SixValentTLChannel) :
    balancedSixValentOperatorChannelPulledBackInner left right ≈
      sixValentTLChannelGram left right :=
  sixValentTLChannel_pulledBackGram_exact left right

/-- Algebraic composition of two normalized rank-one channel summands.  It
is diagonal, and its diagonal coefficient is the original inverse norm.
This is the finite five-channel core of projector idempotence. -/
theorem balancedSixValentOperatorChannelComposition_exact
    (left right : SixValentTLChannel) :
    sixValentTLChannelInverseWeight left *
        (sixValentTLChannelGram left right *
          sixValentTLChannelInverseWeight right) ≈
      if left = right then sixValentTLChannelInverseWeight left else 0 := by
  cases left <;> cases right <;>
    unfold sixValentTLChannelInverseWeight sixValentTLChannelGram
      sixValentTLChannelNorm oneQuarter channelOneHalf channelTwoThirds
      channelThreeHalves <;>
    decide

/-! ## 6. Transpose and interference regressions -/

/-- The all-false operator coordinate. -/
def allFalseThreeLegOperatorIndex : ThreeLegOperatorIndex :=
  ⟨false, false, false, false, false, false⟩

/-- A diagonal coordinate with only the third leg equal to `true`. -/
def thirdTrueDiagonalThreeLegOperatorIndex : ThreeLegOperatorIndex :=
  ⟨false, false, false, false, true, true⟩

/-- Correct reverse transpose makes this cross-coordinate entry `1/12`.
The deliberately untransposed six-valent convention in the upstream leaf
gives zero on the corresponding raw twelve-index entry. -/
theorem balancedSixValentOperatorKernel_transpose_sensitive_pin :
    balancedSixValentOperatorKernelScalar
        allFalseThreeLegOperatorIndex
        thirdTrueDiagonalThreeLegOperatorIndex ≈ oneTwelfth := by
  exact orientedSixFundamentalHaarProjectorScalar_transpose_sensitive_entry

/-- The manifest positive TL resolution retains the same transpose-sensitive
`1/12` entry. -/
theorem balancedSixValentOperatorTLPositive_transpose_sensitive_pin :
    balancedSixValentOperatorTLPositiveScalar
        allFalseThreeLegOperatorIndex
        thirdTrueDiagonalThreeLegOperatorIndex ≈ oneTwelfth := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (balancedSixValentOperatorKernelScalar_eqv_positive
        allFalseThreeLegOperatorIndex
        thirdTrueDiagonalThreeLegOperatorIndex))
    balancedSixValentOperatorKernel_transpose_sensitive_pin

/-- Target coordinate for a concrete negative interference entry. -/
def negativeInterferenceTargetIndex : ThreeLegOperatorIndex :=
  ⟨false, false, false, true, true, false⟩

/-- Source coordinate for the same negative interference entry. -/
def negativeInterferenceSourceIndex : ThreeLegOperatorIndex :=
  ⟨false, false, false, false, true, true⟩

/-- Positive channel weights do not mean entrywise positivity: channel
interference exactly retains the signed value `-1/12`. -/
theorem balancedSixValentOperatorTLPositive_negative_interference_pin :
    balancedSixValentOperatorTLPositiveScalar
        negativeInterferenceTargetIndex negativeInterferenceSourceIndex ≈
      -oneTwelfth := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (balancedSixValentOperatorKernelScalar_eqv_positive
        negativeInterferenceTargetIndex negativeInterferenceSourceIndex)) ?_
  exact orientedSixFundamentalHaarProjectorScalar_negative_entry

#print axioms balancedSixValentOperatorKernelScalar_eqv_TL_resolution
#print axioms balancedSixValentOperatorTLResolvedScalar_eqv_positive
#print axioms balancedSixValentOperatorKernelScalar_eqv_positive
#print axioms balancedSixValentOperatorKernel_eqv_positive
#print axioms sixValentOperatorChannelInverseWeight_positive
#print axioms sixValentOperatorChannelNorm_positive
#print axioms balancedSixValentOperatorKernel_pureReal
#print axioms balancedSixValentOperatorTLPositiveScalar_symmetric
#print axioms balancedSixValentOperatorKernel_selfAdjoint
#print axioms balancedSixValentOperatorKernel_trace_exact
#print axioms balancedSixValentOperatorTLChannel_trace_one
#print axioms balancedSixValentOperatorTLResolvedTraceMass_exact
#print axioms balancedSixValentOperatorKernel_trace_eqv_TLResolvedTraceMass
#print axioms balancedSixValentOperatorChannelPulledBackInner_exact
#print axioms balancedSixValentOperatorChannelComposition_exact
#print axioms balancedSixValentOperatorKernel_transpose_sensitive_pin
#print axioms balancedSixValentOperatorTLPositive_transpose_sensitive_pin
#print axioms balancedSixValentOperatorTLPositive_negative_interference_pin

end YMGap.Continuum.SU2QuaternionSixValentOperatorKernel
