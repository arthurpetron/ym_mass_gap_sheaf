/-
# Canonical balanced four-valent SU(2) operator Haar kernel

This leaf packages the balanced `F F R R` Haar moment as an operator kernel.
Forward legs store `(output,input)`, while reverse legs store
`(input,output)` because conjugate transpose is already built into the
reverse fundamental coefficient.  The resulting kernel is resolved into
the positive singlet/triplet channels with squared norms `1,3` and inverse
weights `1,1/3`.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization

namespace YMGap.Continuum.SU2QuaternionFourValentOperatorKernel

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionFourValentChannelDiagonalization

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem fourKernelRationalBoolSum_eqv_congr
    (left right : Bool → Q')
    (h : ∀ value, left value ≈ right value) :
    rationalBoolSum left ≈ rationalBoolSum right := by
  unfold rationalBoolSum
  exact q_add_congr (h false) (h true)

/-- Pointwise rational equivalence transports through the four operator
coordinate binders without enumerating their assignments. -/
theorem fourKernelRationalFourBoolSum_eqv_congr
    (left right : Bool → Bool → Bool → Bool → Q')
    (h : ∀ first second third fourth,
      left first second third fourth ≈
        right first second third fourth) :
    rationalFourBoolSum left ≈ rationalFourBoolSum right := by
  unfold rationalFourBoolSum
  exact fourKernelRationalBoolSum_eqv_congr _ _ (fun first =>
    fourKernelRationalBoolSum_eqv_congr _ _ (fun second =>
      fourKernelRationalBoolSum_eqv_congr _ _ (fun third =>
        fourKernelRationalBoolSum_eqv_congr _ _ (fun fourth =>
          h first second third fourth))))

private theorem fourKernelRationalBoolSum_linear_four
    (firstFactor secondFactor thirdFactor fourthFactor : Q')
    (firstFamily secondFamily thirdFamily fourthFamily :
      Bool → Q') :
    rationalBoolSum (fun value =>
      firstFactor * firstFamily value +
        (secondFactor * secondFamily value +
          (thirdFactor * thirdFamily value +
            fourthFactor * fourthFamily value))) ≈
    firstFactor * rationalBoolSum firstFamily +
      (secondFactor * rationalBoolSum secondFamily +
        (thirdFactor * rationalBoolSum thirdFamily +
          fourthFactor * rationalBoolSum fourthFamily)) := by
  unfold rationalBoolSum
  ring_qeqv

private def fourKernelRationalTwoBoolSum
    (family : Bool → Bool → Q') : Q' :=
  rationalBoolSum (fun first =>
    rationalBoolSum (fun second => family first second))

private theorem fourKernelRationalTwoBoolSum_linear_four
    (firstFactor secondFactor thirdFactor fourthFactor : Q')
    (firstFamily secondFamily thirdFamily fourthFamily :
      Bool → Bool → Q') :
    fourKernelRationalTwoBoolSum (fun a b =>
      firstFactor * firstFamily a b +
        (secondFactor * secondFamily a b +
          (thirdFactor * thirdFamily a b +
            fourthFactor * fourthFamily a b))) ≈
    firstFactor * fourKernelRationalTwoBoolSum firstFamily +
      (secondFactor * fourKernelRationalTwoBoolSum secondFamily +
        (thirdFactor * fourKernelRationalTwoBoolSum thirdFamily +
          fourthFactor * fourKernelRationalTwoBoolSum fourthFamily)) := by
  unfold fourKernelRationalTwoBoolSum
  let middle : Q' := rationalBoolSum (fun first =>
      firstFactor * rationalBoolSum (firstFamily first) +
        (secondFactor * rationalBoolSum (secondFamily first) +
          (thirdFactor * rationalBoolSum (thirdFamily first) +
            fourthFactor * rationalBoolSum (fourthFamily first))))
  refine Q'.eqv_trans _ middle _ ?_ ?_
  · exact fourKernelRationalBoolSum_eqv_congr _ _ (fun first =>
      fourKernelRationalBoolSum_linear_four _ _ _ _ _ _ _ _)
  · exact fourKernelRationalBoolSum_linear_four _ _ _ _ _ _ _ _

private def fourKernelRationalThreeBoolSum
    (family : Bool → Bool → Bool → Q') : Q' :=
  rationalBoolSum (fun first =>
    fourKernelRationalTwoBoolSum (family first))

private theorem fourKernelRationalThreeBoolSum_linear_four
    (firstFactor secondFactor thirdFactor fourthFactor : Q')
    (firstFamily secondFamily thirdFamily fourthFamily :
      Bool → Bool → Bool → Q') :
    fourKernelRationalThreeBoolSum (fun a b c =>
      firstFactor * firstFamily a b c +
        (secondFactor * secondFamily a b c +
          (thirdFactor * thirdFamily a b c +
            fourthFactor * fourthFamily a b c))) ≈
    firstFactor * fourKernelRationalThreeBoolSum firstFamily +
      (secondFactor * fourKernelRationalThreeBoolSum secondFamily +
        (thirdFactor * fourKernelRationalThreeBoolSum thirdFamily +
          fourthFactor * fourKernelRationalThreeBoolSum fourthFamily)) := by
  unfold fourKernelRationalThreeBoolSum
  let middle : Q' := rationalBoolSum (fun first =>
      firstFactor * fourKernelRationalTwoBoolSum (firstFamily first) +
        (secondFactor * fourKernelRationalTwoBoolSum (secondFamily first) +
          (thirdFactor * fourKernelRationalTwoBoolSum (thirdFamily first) +
            fourthFactor * fourKernelRationalTwoBoolSum
              (fourthFamily first))))
  refine Q'.eqv_trans _ middle _ ?_ ?_
  · exact fourKernelRationalBoolSum_eqv_congr _ _ (fun first =>
      fourKernelRationalTwoBoolSum_linear_four _ _ _ _ _ _ _ _)
  · exact fourKernelRationalBoolSum_linear_four _ _ _ _ _ _ _ _

private def fourKernelRationalFourBoolSum
    (family : Bool → Bool → Bool → Bool → Q') : Q' :=
  rationalBoolSum (fun first =>
    fourKernelRationalThreeBoolSum (family first))

/-- Four-term scalar linearity of the four bounded coordinate binders.
The proof advances one binder at a time, so it never exposes the sixteen
middle assignments or a distributed sixty-four-term expression. -/
theorem fourKernelRationalFourBoolSum_linear_four
    (firstFactor secondFactor thirdFactor fourthFactor : Q')
    (firstFamily secondFamily thirdFamily fourthFamily :
      Bool → Bool → Bool → Bool → Q') :
    rationalFourBoolSum (fun a b c d =>
      firstFactor * firstFamily a b c d +
        (secondFactor * secondFamily a b c d +
          (thirdFactor * thirdFamily a b c d +
            fourthFactor * fourthFamily a b c d))) ≈
    firstFactor * rationalFourBoolSum firstFamily +
      (secondFactor * rationalFourBoolSum secondFamily +
        (thirdFactor * rationalFourBoolSum thirdFamily +
          fourthFactor * rationalFourBoolSum fourthFamily)) := by
  change fourKernelRationalFourBoolSum (fun a b c d =>
      firstFactor * firstFamily a b c d +
        (secondFactor * secondFamily a b c d +
          (thirdFactor * thirdFamily a b c d +
            fourthFactor * fourthFamily a b c d))) ≈
    firstFactor * fourKernelRationalFourBoolSum firstFamily +
      (secondFactor * fourKernelRationalFourBoolSum secondFamily +
        (thirdFactor * fourKernelRationalFourBoolSum thirdFamily +
          fourthFactor * fourKernelRationalFourBoolSum fourthFamily))
  unfold fourKernelRationalFourBoolSum
  let middle : Q' := rationalBoolSum (fun first =>
      firstFactor * fourKernelRationalThreeBoolSum (firstFamily first) +
        (secondFactor * fourKernelRationalThreeBoolSum (secondFamily first) +
          (thirdFactor * fourKernelRationalThreeBoolSum (thirdFamily first) +
            fourthFactor * fourKernelRationalThreeBoolSum
              (fourthFamily first))))
  refine Q'.eqv_trans _ middle _ ?_ ?_
  · exact fourKernelRationalBoolSum_eqv_congr _ _ (fun first =>
      fourKernelRationalThreeBoolSum_linear_four _ _ _ _ _ _ _ _)
  · exact fourKernelRationalBoolSum_linear_four _ _ _ _ _ _ _ _

/-! ## 1. Canonical two-leg operator indices -/

/-- One operator coordinate for a balanced pair of fundamental legs.

The two forward coefficients store `(output,input)`.  The two reverse
coefficients store `(input,output)`, so their input coordinates appear in
the row slots and their output coordinates appear in the column slots of
the underlying oriented Haar projector. -/
structure TwoLegOperatorIndex where
  firstOutput : Bool
  firstInput : Bool
  secondOutput : Bool
  secondInput : Bool
  deriving DecidableEq

/-- The exact balanced Haar kernel on the sixteen operator coordinates.
The reverse arguments are deliberately transposed. -/
def fourValentOperatorKernel
    (target source : TwoLegOperatorIndex) : RationalComplex :=
  orientedFourFundamentalHaarProjector
    target.firstOutput source.firstOutput
    target.secondOutput source.secondOutput
    source.firstInput target.firstInput
    source.secondInput target.secondInput

/-- Scalar component of the exact operator kernel. -/
def fourValentOperatorKernelScalar
    (target source : TwoLegOperatorIndex) : Q' :=
  orientedFourFundamentalHaarProjectorScalar
    target.firstOutput source.firstOutput
    target.secondOutput source.secondOutput
    source.firstInput target.firstInput
    source.secondInput target.secondInput

/-! ## 2. Positive singlet/triplet resolution -/

/-- The invariant-channel coordinates of one operator index. -/
def twoLegOperatorChannelCoordinates
    (index : TwoLegOperatorIndex) :
    YMGap.Continuum.SU2TrivalentThetaRecoupling.RecoupleVec :=
  orientedPairingChannelCoordinates
    index.firstOutput index.secondOutput
    index.firstInput index.secondInput

/-- Singlet coordinate of one operator index. -/
def twoLegOperatorSingletCoordinate
    (index : TwoLegOperatorIndex) : Q' :=
  singletOrientedPairing
    index.firstOutput index.secondOutput
    index.firstInput index.secondInput

/-- Triplet coordinate of one operator index. -/
def twoLegOperatorTripletCoordinate
    (index : TwoLegOperatorIndex) : Q' :=
  tripletOrientedPairing
    index.firstOutput index.secondOutput
    index.firstInput index.secondInput

/-- The manifest positive two-channel scalar kernel

`|S><S| + (1/3)|T><T|`.
-/
def fourValentOperatorPositiveChannelScalar
    (target source : TwoLegOperatorIndex) : Q' :=
  twoLegOperatorSingletCoordinate target *
    twoLegOperatorSingletCoordinate source +
  oneThird *
    (twoLegOperatorTripletCoordinate target *
      twoLegOperatorTripletCoordinate source)

/-- Rational-complex lift of the positive channel resolution. -/
def fourValentOperatorPositiveChannelKernel
    (target source : TwoLegOperatorIndex) : RationalComplex :=
  (fourValentOperatorPositiveChannelScalar target source, 0)

/-- The signed inverse-Gram Haar kernel is exactly the positive
singlet/triplet resolution.  No external Boolean assignment is split. -/
theorem fourValentOperatorKernelScalar_eqv_positiveChannel
    (target source : TwoLegOperatorIndex) :
    fourValentOperatorKernelScalar target source ≈
      fourValentOperatorPositiveChannelScalar target source := by
  refine Q'.eqv_trans _
    (orientedFourFundamentalHaarProjectorChannelScalar
      target.firstOutput source.firstOutput
      target.secondOutput source.secondOutput
      source.firstInput target.firstInput
      source.secondInput target.secondInput) _ ?_ ?_
  · exact orientedFourFundamentalHaarProjectorScalar_eqv_channel
      target.firstOutput source.firstOutput
      target.secondOutput source.secondOutput
      source.firstInput target.firstInput
      source.secondInput target.secondInput
  · exact Q'.eqv_refl _

/-- Rational-complex form of the exact positive resolution. -/
theorem fourValentOperatorKernel_eqv_positiveChannel
    (target source : TwoLegOperatorIndex) :
    RationalComplexEqv
      (fourValentOperatorKernel target source)
      (fourValentOperatorPositiveChannelKernel target source) := by
  constructor
  · exact fourValentOperatorKernelScalar_eqv_positiveChannel target source
  · exact Q'.eqv_refl 0

/-! ## 3. Channel norms and weighted trace mass -/

/-- The singlet and triplet tensors are orthogonal, with exact squared norms
`1` and `3`. -/
theorem fourValentOperatorChannelGram_exact :
    orientedPairingInner singletOrientedPairing
        singletOrientedPairing ≈ 1 ∧
    orientedPairingInner singletOrientedPairing
        tripletOrientedPairing ≈ 0 ∧
    orientedPairingInner tripletOrientedPairing
        singletOrientedPairing ≈ 0 ∧
    orientedPairingInner tripletOrientedPairing
        tripletOrientedPairing ≈ 3 :=
  singlet_triplet_oriented_pairing_gram_exact

/-- The trace mass of the two positive rank-one channels, before reducing
the exact norms.  The inverse channel weights are `1` and `1/3`. -/
def fourValentOperatorWeightedTraceMass : Q' :=
  orientedPairingInner singletOrientedPairing singletOrientedPairing +
    oneThird *
      orientedPairingInner tripletOrientedPairing tripletOrientedPairing

/-- Each positive rank-one channel contributes one unit of trace, so the
weighted channel mass is exactly two. -/
theorem fourValentOperatorWeightedTraceMass_exact :
    fourValentOperatorWeightedTraceMass ≈ 2 := by
  refine Q'.eqv_trans _ (1 + oneThird * 3) _ ?_ ?_
  · exact q_add_congr
      fourValentOperatorChannelGram_exact.1
      (q_mul_congr (Q'.eqv_refl oneThird)
        fourValentOperatorChannelGram_exact.2.2.2)
  · unfold oneThird
    decide

/-! ## 4. Exact operator trace -/

/-- Diagonal trace over all sixteen two-leg operator coordinates. -/
def fourValentOperatorKernelTrace : RationalComplex :=
  rationalComplexFourBoolSum
    (fun firstOutput secondOutput firstInput secondInput =>
      let index : TwoLegOperatorIndex :=
        ⟨firstOutput, firstInput, secondOutput, secondInput⟩
      fourValentOperatorKernel index index)

/-- The canonical balanced operator Haar projector has exact trace two. -/
theorem fourValentOperatorKernel_trace_exact :
    RationalComplexEqv fourValentOperatorKernelTrace ((2 : Q'), 0) := by
  exact orientedFourFundamentalHaarProjector_diagonal_trace_exact

/-! ## 5. Reality and self-adjointness -/

/-- Matrix transpose on the two operator coordinates. -/
def fourValentOperatorKernelTranspose
    (target source : TwoLegOperatorIndex) : RationalComplex :=
  fourValentOperatorKernel source target

/-- Every entry of the balanced operator kernel is pure real. -/
theorem fourValentOperatorKernel_pureReal
    (target source : TwoLegOperatorIndex) :
    (fourValentOperatorKernel target source).2 ≈ 0 :=
  Q'.eqv_refl 0

/-- The manifest positive channel resolution is symmetric. -/
theorem fourValentOperatorPositiveChannelScalar_symm
    (target source : TwoLegOperatorIndex) :
    fourValentOperatorPositiveChannelScalar target source ≈
      fourValentOperatorPositiveChannelScalar source target := by
  unfold fourValentOperatorPositiveChannelScalar
  exact q_add_congr
    (Q'.mul_comm_eqv _ _)
    (Q'.mul_eqv_congr_left oneThird _ _ (Q'.mul_comm_eqv _ _))

/-- The exact operator kernel is self-adjoint; because it is pure real this
is ordinary matrix symmetry.  The proof passes through the positive channel
resolution and never splits external coordinates. -/
theorem fourValentOperatorKernel_selfAdjoint
    (target source : TwoLegOperatorIndex) :
    RationalComplexEqv
      (fourValentOperatorKernel target source)
      (fourValentOperatorKernelTranspose target source) := by
  constructor
  · exact Q'.eqv_trans _
      (fourValentOperatorPositiveChannelScalar target source) _
      (fourValentOperatorKernelScalar_eqv_positiveChannel target source)
      (Q'.eqv_trans _
        (fourValentOperatorPositiveChannelScalar source target) _
        (fourValentOperatorPositiveChannelScalar_symm target source)
        (Q'.eqv_symm
          (fourValentOperatorKernelScalar_eqv_positiveChannel source target)))
  · exact Q'.eqv_refl 0

/-! ## 6. Structural idempotence from the channel Gram -/

/-- Real-coordinate matrix square over the four middle operator indices. -/
def fourValentOperatorKernelSquareScalar
    (target source : TwoLegOperatorIndex) : Q' :=
  rationalFourBoolSum
    (fun firstOutput secondOutput firstInput secondInput =>
      let middle : TwoLegOperatorIndex :=
        ⟨firstOutput, firstInput, secondOutput, secondInput⟩
      fourValentOperatorKernelScalar target middle *
        fourValentOperatorKernelScalar middle source)

/-- Matrix square of the positive channel resolution. -/
def fourValentOperatorPositiveChannelSquareScalar
    (target source : TwoLegOperatorIndex) : Q' :=
  rationalFourBoolSum
    (fun firstOutput secondOutput firstInput secondInput =>
      let middle : TwoLegOperatorIndex :=
        ⟨firstOutput, firstInput, secondOutput, secondInput⟩
      fourValentOperatorPositiveChannelScalar target middle *
        fourValentOperatorPositiveChannelScalar middle source)

private def fourValentOperatorExpandedChannelProduct
    (target source middle : TwoLegOperatorIndex) : Q' :=
  (twoLegOperatorSingletCoordinate target *
      twoLegOperatorSingletCoordinate source) *
    (twoLegOperatorSingletCoordinate middle *
      twoLegOperatorSingletCoordinate middle) +
  ((oneThird *
      (twoLegOperatorSingletCoordinate target *
        twoLegOperatorTripletCoordinate source)) *
      (twoLegOperatorSingletCoordinate middle *
        twoLegOperatorTripletCoordinate middle) +
    ((oneThird *
        (twoLegOperatorTripletCoordinate target *
          twoLegOperatorSingletCoordinate source)) *
        (twoLegOperatorTripletCoordinate middle *
          twoLegOperatorSingletCoordinate middle) +
      (((oneThird * oneThird) *
          (twoLegOperatorTripletCoordinate target *
            twoLegOperatorTripletCoordinate source)) *
        (twoLegOperatorTripletCoordinate middle *
          twoLegOperatorTripletCoordinate middle))))

private theorem positiveChannelProduct_expanded
    (target middle source : TwoLegOperatorIndex) :
    fourValentOperatorPositiveChannelScalar target middle *
        fourValentOperatorPositiveChannelScalar middle source ≈
      fourValentOperatorExpandedChannelProduct target source middle := by
  unfold fourValentOperatorPositiveChannelScalar
    fourValentOperatorExpandedChannelProduct
  ring_qeqv

private def fourValentOperatorExpandedChannelSquare
    (target source : TwoLegOperatorIndex) : Q' :=
  rationalFourBoolSum
    (fun firstOutput secondOutput firstInput secondInput =>
      fourValentOperatorExpandedChannelProduct target source
        ⟨firstOutput, firstInput, secondOutput, secondInput⟩)

private def fourValentOperatorFactoredChannelSquare
    (target source : TwoLegOperatorIndex) : Q' :=
  (twoLegOperatorSingletCoordinate target *
      twoLegOperatorSingletCoordinate source) *
      orientedPairingInner singletOrientedPairing singletOrientedPairing +
  ((oneThird *
      (twoLegOperatorSingletCoordinate target *
        twoLegOperatorTripletCoordinate source)) *
      orientedPairingInner singletOrientedPairing tripletOrientedPairing +
    ((oneThird *
        (twoLegOperatorTripletCoordinate target *
          twoLegOperatorSingletCoordinate source)) *
        orientedPairingInner tripletOrientedPairing singletOrientedPairing +
      (((oneThird * oneThird) *
          (twoLegOperatorTripletCoordinate target *
            twoLegOperatorTripletCoordinate source)) *
        orientedPairingInner tripletOrientedPairing
          tripletOrientedPairing)))

private theorem expandedChannelSquare_eqv_factored
    (target source : TwoLegOperatorIndex) :
    fourValentOperatorExpandedChannelSquare target source ≈
      fourValentOperatorFactoredChannelSquare target source := by
  unfold fourValentOperatorExpandedChannelSquare
    fourValentOperatorExpandedChannelProduct
    fourValentOperatorFactoredChannelSquare
    twoLegOperatorSingletCoordinate twoLegOperatorTripletCoordinate
    orientedPairingInner
  exact fourKernelRationalFourBoolSum_linear_four _ _ _ _ _ _ _ _

private theorem oneThird_mul_three_exact : oneThird * 3 ≈ 1 := by
  unfold oneThird
  decide

private theorem tripletWeight_idempotent (value : Q') :
    ((oneThird * oneThird) * value) * 3 ≈ oneThird * value := by
  refine Q'.eqv_trans _
    ((oneThird * value) * (oneThird * 3)) _ ?_ ?_
  · ring_qeqv
  · exact Q'.eqv_trans _ ((oneThird * value) * 1) _
      (q_mul_congr (Q'.eqv_refl _) oneThird_mul_three_exact)
      (Q'.mul_one_eqv _)

private theorem factoredChannelSquare_eqv_positive
    (target source : TwoLegOperatorIndex) :
    fourValentOperatorFactoredChannelSquare target source ≈
      fourValentOperatorPositiveChannelScalar target source := by
  let collapsed : Q' :=
    (twoLegOperatorSingletCoordinate target *
        twoLegOperatorSingletCoordinate source) * 1 +
    ((oneThird *
        (twoLegOperatorSingletCoordinate target *
          twoLegOperatorTripletCoordinate source)) * 0 +
      ((oneThird *
          (twoLegOperatorTripletCoordinate target *
            twoLegOperatorSingletCoordinate source)) * 0 +
        (((oneThird * oneThird) *
            (twoLegOperatorTripletCoordinate target *
              twoLegOperatorTripletCoordinate source)) * 3)))
  refine Q'.eqv_trans _ collapsed _ ?_ ?_
  · exact q_add_congr
      (q_mul_congr (Q'.eqv_refl _)
        fourValentOperatorChannelGram_exact.1)
      (q_add_congr
        (q_mul_congr (Q'.eqv_refl _)
          fourValentOperatorChannelGram_exact.2.1)
        (q_add_congr
          (q_mul_congr (Q'.eqv_refl _)
            fourValentOperatorChannelGram_exact.2.2.1)
          (q_mul_congr (Q'.eqv_refl _)
            fourValentOperatorChannelGram_exact.2.2.2)))
  · let tripletTerm : Q' :=
      oneThird *
        (twoLegOperatorTripletCoordinate target *
          twoLegOperatorTripletCoordinate source)
    refine Q'.eqv_trans _
      ((twoLegOperatorSingletCoordinate target *
          twoLegOperatorSingletCoordinate source) +
        (0 + (0 + tripletTerm))) _ ?_ ?_
    · exact q_add_congr
        (Q'.mul_one_eqv _)
        (q_add_congr
          (QPoly.q_mul_zero _)
          (q_add_congr
            (QPoly.q_mul_zero _)
            (tripletWeight_idempotent _)))
    · have htail : (0 : Q') + (0 + tripletTerm) ≈ tripletTerm :=
        Q'.eqv_trans _ (0 + tripletTerm) _
          (q_add_congr (Q'.eqv_refl 0)
            (QPoly.q_zero_add_eqv tripletTerm))
          (QPoly.q_zero_add_eqv tripletTerm)
      exact q_add_congr (Q'.eqv_refl _) htail

/-- The positive singlet/triplet resolution squares to itself.  The four
middle contractions are replaced by the exact channel Gram
`diag(1,3)`; no middle assignment is case-split. -/
theorem fourValentOperatorPositiveChannelScalar_idempotent
    (target source : TwoLegOperatorIndex) :
    fourValentOperatorPositiveChannelSquareScalar target source ≈
      fourValentOperatorPositiveChannelScalar target source := by
  refine Q'.eqv_trans _
    (fourValentOperatorExpandedChannelSquare target source) _ ?_ ?_
  · exact fourKernelRationalFourBoolSum_eqv_congr _ _
      (fun firstOutput secondOutput firstInput secondInput =>
        positiveChannelProduct_expanded target
          ⟨firstOutput, firstInput, secondOutput, secondInput⟩ source)
  · exact Q'.eqv_trans _
      (fourValentOperatorFactoredChannelSquare target source) _
      (expandedChannelSquare_eqv_factored target source)
      (factoredChannelSquare_eqv_positive target source)

/-- The scalar square of the actual signed Haar kernel equals the kernel.
Both factors are transported to the positive resolution before the Gram
calculation. -/
theorem fourValentOperatorKernelSquareScalar_idempotent
    (target source : TwoLegOperatorIndex) :
    fourValentOperatorKernelSquareScalar target source ≈
      fourValentOperatorKernelScalar target source := by
  refine Q'.eqv_trans _
    (fourValentOperatorPositiveChannelSquareScalar target source) _ ?_ ?_
  · exact fourKernelRationalFourBoolSum_eqv_congr _ _
      (fun firstOutput secondOutput firstInput secondInput =>
        let middle : TwoLegOperatorIndex :=
          ⟨firstOutput, firstInput, secondOutput, secondInput⟩
        q_mul_congr
          (fourValentOperatorKernelScalar_eqv_positiveChannel target middle)
          (fourValentOperatorKernelScalar_eqv_positiveChannel middle source))
  · exact Q'.eqv_trans _
      (fourValentOperatorPositiveChannelScalar target source) _
      (fourValentOperatorPositiveChannelScalar_idempotent target source)
      (Q'.eqv_symm
        (fourValentOperatorKernelScalar_eqv_positiveChannel target source))

/-- Rational-complex real-coordinate square. -/
def fourValentOperatorKernelSquare
    (target source : TwoLegOperatorIndex) : RationalComplex :=
  (fourValentOperatorKernelSquareScalar target source, 0)

/-- The balanced four-valent Haar kernel is an exact idempotent operator. -/
theorem fourValentOperatorKernel_idempotent
    (target source : TwoLegOperatorIndex) :
    RationalComplexEqv
      (fourValentOperatorKernelSquare target source)
      (fourValentOperatorKernel target source) :=
  ⟨fourValentOperatorKernelSquareScalar_idempotent target source,
    Q'.eqv_refl 0⟩

/-! ## 7. Transpose-sensitive regression pins -/

def fourValentZeroOperatorIndex : TwoLegOperatorIndex :=
  ⟨false, false, false, false⟩

def fourValentOneOperatorIndex : TwoLegOperatorIndex :=
  ⟨true, true, true, true⟩

/-- Correct reverse storage retains a nonzero triplet-channel matrix entry
between the all-zero and all-one operator coordinates. -/
theorem fourValentOperatorKernel_transpose_sensitive_pin :
    RationalComplexEqv
      (fourValentOperatorKernel
        fourValentZeroOperatorIndex fourValentOneOperatorIndex)
      (oneThird, 0) := by
  constructor <;> decide

/-- If the reverse coefficients were incorrectly stored as `(output,input)`,
the same displayed entry would vanish.  This pin prevents an unnoticed
reverse-index transpose regression. -/
theorem fourValentOperatorKernel_untransposed_reverse_zero_pin :
    RationalComplexEqv
      (orientedFourFundamentalHaarProjector
        false true false true false true false true)
      (0, 0) := by
  constructor <;> decide

#print axioms fourValentOperatorKernelScalar_eqv_positiveChannel
#print axioms fourValentOperatorKernel_eqv_positiveChannel
#print axioms fourValentOperatorChannelGram_exact
#print axioms fourValentOperatorWeightedTraceMass_exact
#print axioms fourValentOperatorKernel_trace_exact
#print axioms fourValentOperatorKernel_pureReal
#print axioms fourValentOperatorKernel_selfAdjoint
#print axioms fourValentOperatorPositiveChannelScalar_idempotent
#print axioms fourValentOperatorKernelSquareScalar_idempotent
#print axioms fourValentOperatorKernel_idempotent
#print axioms fourValentOperatorKernel_transpose_sensitive_pin
#print axioms fourValentOperatorKernel_untransposed_reverse_zero_pin

end YMGap.Continuum.SU2QuaternionFourValentOperatorKernel
