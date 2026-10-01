/-
# The negative rational tangent on supplied original physical graph points

The inverse signed action and the already constructed positive rational
tangent give the negative-time tangent with the SAME `-2i` generator phase.
The output is used only as a represented physical vector: its original Rows
compute the zero-time continuity radius.  It is never presumed to be in the
unbounded derivative domain.  This is fixed nome and width, not physical
clock calibration or a continuum assertion.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows rowsOfState ofRows_rowsOfState value value_injective
    value_ofState distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point Domain ofPoint input output value_output_ofPoint)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
  (tangentRadius tangentRadius_positive physicalPoint_tangent_bound normSq_realScale
    signedAction_positive_rational)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
  (radius radius_positive limitMap_near_identity_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_neg_left signedAction_neg_right signedAction_distance
    signedAction_pairing_preserved signedAction_add_state signedAction_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale imagScale_smul cneg realScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (normSq_neg normSq_imagScale add_assoc add_comm add_zero zero_add neg_add add_neg
    add_right_cancel)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_symm)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_smul bondValue_add bondValue_negate bondValue_sub bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_zero completedZero_add completedAdd_zero completedNeg_add
    completedSmul_add completedSmul_mul completedSmul_congr)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "G" => signedAction hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "Neg" => cneg hw0 hw1
local notation "I" => imagScale hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Z" =>
  (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width),
   BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width))

/-- The output range witness is data already present in the supplied original
sector-domain point, not a representative selected from a quotient. -/
def outputRows (p : P) : Rows hw0 hw1 (width := width) :=
  rowsOfState hw0 hw1 (BF4WilsonAllNomeComplexSectorDerivative.output hw0 hw1 p)

theorem outputRows_pin (p : P) :
    ofRows hw0 hw1 (outputRows hw0 hw1 p) = Out (ofPoint hw0 hw1 p) := by
  apply value_injective hw0 hw1
  rw [outputRows,ofRows_rowsOfState,value_ofState,value_output_ofPoint]
  rfl

private def posTime (t : Q') (ht : (0 : Q') < t) : SignedRealTimeData.SignedTimeValue :=
  SignedRealTimeData.positiveTime
    (BF4ExactSlabThermodynamicPositiveTimePins.timeValue
      (PositiveRealDyadicTimeData.rational t ht))

private def negTime (t : Q') (ht : (0 : Q') < t) : SignedRealTimeData.SignedTimeValue :=
  SignedRealTimeData.negTime (posTime t ht)

private def qquarter : Q' := Q'.mkPos 1 4 (by decide)
private def qsixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- A single positive rational radius from the supplied graph Point and its
output Rows.  The output is not required to lie in the derivative domain. -/
def negativeRadius (p : P) (e : Q') (he : (0 : Q') < e) : Q' :=
  Q'.min'
    (tangentRadius hw0 hw1 p (qquarter*e) (Q'.mul_pos (by decide) he))
    (radius hw0 hw1 (outputRows hw0 hw1 p) (qsixteenth*e)
      (Q'.mul_pos (by decide) he))

theorem negativeRadius_positive (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < negativeRadius hw0 hw1 p e he := by
  unfold negativeRadius
  exact CReal.min_pos
    (tangentRadius_positive hw0 hw1 p (qquarter*e) (Q'.mul_pos (by decide) he))
    (radius_positive hw0 hw1 (outputRows hw0 hw1 p) (qsixteenth*e)
      (Q'.mul_pos (by decide) he))

/-- At a negative time `-t`, the numerator error for division by signed
time is `G(-t)x-x-2it*y`.  Multiplication by `-1/t` therefore retains the
same `-2i*y` derivative as the positive-time quotient. -/
def negativeError (t : Q') (ht : (0 : Q') < t) (d : D) : H :=
  A (diff hw0 hw1 (G (negTime t ht) (In d)) (In d))
    (Neg (I t (A (Out d) (Out d))))

private theorem cneg_smul (x : H) :
    Neg x = S (ofQ' (-1)) (ofQ' 0)
      (rationalCauchy (-1)) (rationalCauchy 0) x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg,
      BF4WilsonAllNomeComplexBondOSTime.smul,bondValue_negate,bondValue_sub,
      bondValue_realSmul,completedRealSmul_ofQ',completedSmul_zero]
    change BF4WilsonAllNomeLinear.completedNeg hw0 hw1 (bondValue hw0 hw1 x.1) =
      BF4WilsonAllNomeLinear.completedAdd hw0 hw1
        (BF4WilsonAllNomeLinear.completedNeg hw0 hw1 (bondValue hw0 hw1 x.1))
        (BF4WilsonAllNomeLinear.completedNeg hw0 hw1
          (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width))
    have hz : BF4WilsonAllNomeLinear.completedNeg hw0 hw1
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) =
        BF4WilsonAllNomeLinear.completedZero hw0 hw1 width := by
      have h := completedNeg_add hw0 hw1
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width)
      rw [completedAdd_zero] at h
      exact h
    rw [hz,completedAdd_zero]
  · apply bondValue_injective hw0 hw1
    simp only [BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg,
      BF4WilsonAllNomeComplexBondOSTime.smul,bondValue_negate,bondValue_add,
      bondValue_realSmul,completedRealSmul_ofQ',completedSmul_zero]
    exact (completedZero_add hw0 hw1 _).symm

private theorem action_neg (s : SignedRealTimeData.SignedTimeValue) (x : H) :
    G s (Neg x) = Neg (G s x) := by
  rw [cneg_smul,cneg_smul]
  exact signedAction_smul hw0 hw1 s (ofQ' (-1)) (ofQ' 0)
    (rationalCauchy (-1)) (rationalCauchy 0) x

private theorem action_diff (s : SignedRealTimeData.SignedTimeValue) (x y : H) :
    G s (diff hw0 hw1 x y) = diff hw0 hw1 (G s x) (G s y) := by
  unfold diff
  rw [signedAction_add_state,action_neg]

private theorem action_imag (s : SignedRealTimeData.SignedTimeValue)
    (t : Q') (x : H) : G s (I t x) = I t (G s x) := by
  rw [imagScale_smul,imagScale_smul]
  exact signedAction_smul hw0 hw1 s (ofQ' 0) (ofQ' t)
    (rationalCauchy 0) (rationalCauchy t) x

private theorem add_exchange (a b c d : H) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  calc
    A (A a b) (A c d) = A a (A b (A c d)) := add_assoc hw0 hw1 _ _ _
    _ = A a (A c (A b d)) := by
      rw [← add_assoc hw0 hw1 b c d,add_comm hw0 hw1 b c,
        add_assoc hw0 hw1 c b d]
    _ = A (A a c) (A b d) := (add_assoc hw0 hw1 _ _ _).symm

private theorem add_move_last (a b c d : H) :
    A (A a b) (A c d) = A (A a d) (A b c) := by
  calc
    A (A a b) (A c d) = A (A a b) (A d c) := by rw [add_comm hw0 hw1 c d]
    _ = A (A a d) (A b c) := add_exchange hw0 hw1 a b d c

private theorem neg_additive (x y : H) : Neg (A x y) = A (Neg x) (Neg y) := by
  apply add_right_cancel hw0 hw1 _ _ (A x y)
  calc
    A (Neg (A x y)) (A x y) = Z := neg_add hw0 hw1 _
    _ = A Z Z := (zero_add hw0 hw1 Z).symm
    _ = A (A (Neg x) x) (A (Neg y) y) := by
      rw [neg_add,neg_add]
      rfl
    _ = A (A (Neg x) (Neg y)) (A x y) :=
      (add_exchange hw0 hw1 _ _ _ _).symm

private theorem neg_neg (x : H) : Neg (Neg x) = x := by
  apply add_right_cancel hw0 hw1 _ _ (Neg x)
  calc
    A (Neg (Neg x)) (Neg x) = Z := neg_add hw0 hw1 _
    _ = A x (Neg x) := (add_neg hw0 hw1 x).symm

private theorem diff_reverse (x y : H) :
    Neg (diff hw0 hw1 x y) = diff hw0 hw1 y x := by
  unfold diff
  rw [neg_additive,neg_neg,add_comm]

private theorem diff_add (a b c d : H) :
    diff hw0 hw1 (A a b) (A c d) =
      A (diff hw0 hw1 a c) (diff hw0 hw1 b d) := by
  unfold diff
  rw [neg_additive]
  exact add_exchange hw0 hw1 a b (Neg c) (Neg d)

private theorem real_scale_add (t : Q')
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t x)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 t _ _

private theorem real_neg_additive
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
    BF4WilsonAllNomeBondOSLinear.add hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x)
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add,bondValue_negate]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem imag_add (t : Q') (x y : H) : I t (A x y) = A (I t x) (I t y) := by
  apply Prod.ext
  · exact (congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_add hw0 hw1 t x.2 y.2)).trans
      (real_neg_additive hw0 hw1 _ _)
  · exact real_scale_add hw0 hw1 t x.1 y.1

private theorem imag_neg (t : Q') (x : H) : I t (Neg x) = Neg (I t x) := by
  have real_scale_neg (z : BF4WilsonAllNomeBondOSCompletion.BondCompletion
      hw0 hw1 (width := width)) :
      BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 z) =
      BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t z) := by
    apply bondValue_injective hw0 hw1
    simp only [bondValue_smul,bondValue_negate]
    change BF4WilsonAllNomeLinear.completedSmul hw0 hw1 t
        (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 z)) =
      BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (-1)
        (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 t (bondValue hw0 hw1 z))
    rw [completedSmul_mul,completedSmul_mul]
    exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv t (-1)) _
  apply Prod.ext
  · exact congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_neg x.2)
  · exact real_scale_neg x.1

private theorem imag_diff (t : Q') (x y : H) :
    diff hw0 hw1 (I t x) (I t y) = I t (diff hw0 hw1 x y) := by
  unfold diff
  rw [imag_add,imag_neg]

private theorem phase_correction (t : Q') (ht : (0 : Q') < t)
    (y : H) :
    diff hw0 hw1 (G (negTime t ht) (I t (A y y))) (I t (A y y)) =
      I t (A (diff hw0 hw1 (G (negTime t ht) y) y)
        (diff hw0 hw1 (G (negTime t ht) y) y)) := by
  rw [action_imag,signedAction_add_state,imag_diff,diff_add]

private theorem algebra_cancel (a x p q : H) :
    A (Neg (A (diff hw0 hw1 x a) p)) (diff hw0 hw1 p q) =
      A (diff hw0 hw1 a x) (Neg q) := by
  rw [neg_additive,diff_reverse]
  unfold diff
  calc
    A (A (diff hw0 hw1 a x) (Neg p)) (A p (Neg q)) =
        A (A (diff hw0 hw1 a x) (Neg q)) (A (Neg p) p) :=
      add_move_last hw0 hw1 _ _ _ _
    _ = A (diff hw0 hw1 a x) (Neg q) := by rw [neg_add,add_zero]

/-- Exact inverse-group residual identity.  Only the ORIGINAL graph input is
acted upon; the second term uses continuity of the ordinary output vector. -/
theorem negative_error_identity (t : Q') (ht : (0 : Q') < t) (d : D) :
    negativeError hw0 hw1 t ht d =
      A (Neg (G (negTime t ht)
          (BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
            hw0 hw1 t ht d)))
        (I t (A (diff hw0 hw1 (G (negTime t ht) (Out d)) (Out d))
          (diff hw0 hw1 (G (negTime t ht) (Out d)) (Out d)))) := by
  let x := In d
  let y := Out d
  let p := I t (A y y)
  let a := G (negTime t ht) x
  have hplus :
      BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
        hw0 hw1 t ht d =
      A (diff hw0 hw1 (G (posTime t ht) x) x) p := by
    unfold BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
    rw [← signedAction_positive_rational hw0 hw1 t ht x]
    rfl
  have hback : G (negTime t ht) (G (posTime t ht) x) = x :=
    signedAction_neg_left hw0 hw1 (posTime t ht) x
  have hact : G (negTime t ht)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
          hw0 hw1 t ht d) =
      A (diff hw0 hw1 x a) (G (negTime t ht) p) := by
    rw [hplus,signedAction_add_state,action_diff,hback]
  have hcancel := algebra_cancel hw0 hw1 a x (G (negTime t ht) p) p
  have hphase := phase_correction hw0 hw1 t ht y
  unfold negativeError
  change A (diff hw0 hw1 a x) (Neg p) = _
  rw [hact,← hphase]
  exact hcancel.symm

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) :=
  Quotient.sound (CRealAlg.ofQ'_mul _ _).symm

private theorem add_rat (a b : Q') : RCadd (rat a) (rat b) = rat (a+b) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl (a+b)))

private theorem phase_norm_le (t : Q') (ht : (0 : Q') < t) (z : H) :
    RCle (N (I t (A z z))) (RCscale (4*(t*t)) (N z)) := by
  have hdouble := normSq_add_le hw0 hw1 z z
  change RCle (N (A z z))
    (BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound.fourCopies (N z)) at hdouble
  rw [BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound.fourCopies_eq_scale_four] at hdouble
  have ht2 : (0 : Q') ≤ t*t := Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht)
  have hscaled := RCscale_mono ht2 hdouble
  rw [RCscale_RCscale] at hscaled
  rw [normSq_imagScale]
  have hc : Q'.eqv ((t*t)*4) (4*(t*t)) := Q'.mul_comm_eqv _ _
  rwa [scale_congr hc] at hscaled

private theorem negative_displacement (t : Q') (ht : (0 : Q') < t) (y : H) :
    distance hw0 hw1 (G (negTime t ht) y) y =
      distance hw0 hw1
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht y) y := by
  calc
    distance hw0 hw1 (G (negTime t ht) y) y =
        distance hw0 hw1 (G (posTime t ht) (G (negTime t ht) y))
          (G (posTime t ht) y) :=
      (signedAction_distance hw0 hw1 (posTime t ht) _ _).symm
    _ = distance hw0 hw1 y (G (posTime t ht) y) := by
      unfold negTime
      rw [signedAction_neg_right]
    _ = distance hw0 hw1 (G (posTime t ht) y) y :=
      distance_symm hw0 hw1 _ _
    _ = distance hw0 hw1
        (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht y) y := by
      unfold posTime
      rw [signedAction_positive_rational]

private theorem negative_error_budget (p : P) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t) (htr : t ≤ negativeRadius hw0 hw1 p e he) :
    RCle (N (negativeError hw0 hw1 t ht (ofPoint hw0 hw1 p))) (rat ((t*t)*e)) := by
  let d := ofPoint hw0 hw1 p
  let y := Out d
  let z := diff hw0 hw1 (G (negTime t ht) y) y
  let e4 := qquarter*e
  let e16 := qsixteenth*e
  have he4 : (0 : Q') < e4 := Q'.mul_pos (by decide) he
  have he16 : (0 : Q') < e16 := Q'.mul_pos (by decide) he
  have hr4 : t ≤ tangentRadius hw0 hw1 p e4 he4 :=
    Q'.le_trans' _ _ _ htr (Q'.min_le_left' _ _)
  have hr16 : t ≤ radius hw0 hw1 (outputRows hw0 hw1 p) e16 he16 :=
    Q'.le_trans' _ _ _ htr (Q'.min_le_right' _ _)
  have hpos := physicalPoint_tangent_bound hw0 hw1 p e4 he4 t ht hr4
  have hneg : N (G (negTime t ht)
      (BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
        hw0 hw1 t ht d)) =
      N (BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
        hw0 hw1 t ht d) := by
    exact congrArg Prod.fst (signedAction_pairing_preserved hw0 hw1 (negTime t ht) _ _)
  have hnear : RCle (distance hw0 hw1 (G (negTime t ht) y) y) (rat e16) := by
    rw [negative_displacement]
    change RCle (distance hw0 hw1
      (BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht
        (Out (ofPoint hw0 hw1 p))) (Out (ofPoint hw0 hw1 p))) (rat e16)
    rw [← outputRows_pin hw0 hw1 p]
    exact limitMap_near_identity_ofRows hw0 hw1 (outputRows hw0 hw1 p)
      e16 he16 t ht hr16
  have hphase := phase_norm_le hw0 hw1 t ht z
  have hphase' : RCle (N (I t (A z z)))
      (RCscale (4*(t*t)) (rat e16)) :=
    RCle_trans hphase (RCscale_mono
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht)))
      (by rw [← distance_eq_norm_difference]; exact hnear))
  have hleft : RCle
      (N (Neg (G (negTime t ht)
        (BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
          hw0 hw1 t ht d)))) (rat ((t*t)*e4)) := by
    rw [normSq_neg,hneg]
    exact hpos
  have hsum := normSq_add_le hw0 hw1
    (Neg (G (negTime t ht)
      (BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.tangentError
        hw0 hw1 t ht d))) (I t (A z z))
  rw [← negative_error_identity hw0 hw1 t ht d] at hsum
  have h := RCle_trans hsum
    (RCadd_le_add (RCadd_le_add hleft hleft)
      (RCadd_le_add hphase' hphase'))
  simp only [scale_rat,add_rat] at h
  have hcoeff : Q'.eqv
      ((qquarter+qquarter)+(4*qsixteenth+4*qsixteenth)) 1 := by decide
  have hpoly : Q'.eqv
      (((t*t)*e4+(t*t)*e4)+
        ((4*(t*t))*e16+(4*(t*t))*e16))
      ((t*t)*(((qquarter+qquarter)+(4*qsixteenth+4*qsixteenth))*e)) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.mul (.var 0) (.var 0))
          (.mul (.var 2) (.var 1)))
          (.mul (.mul (.var 0) (.var 0))
            (.mul (.var 2) (.var 1))))
        (.add (.mul (.mul (.const 4) (.mul (.var 0) (.var 0)))
          (.mul (.var 3) (.var 1)))
          (.mul (.mul (.const 4) (.mul (.var 0) (.var 0)))
            (.mul (.var 3) (.var 1)))))
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.add (.add (.var 2) (.var 2))
          (.add (.mul (.const 4) (.var 3)) (.mul (.const 4) (.var 3)))) (.var 1)))
      (by decide) (fun | 0 => t | 1 => e | 2 => qquarter | _ => qsixteenth)
  have hc : Q'.eqv
      (((t*t)*e4+(t*t)*e4)+
        ((4*(t*t))*e16+(4*(t*t))*e16)) ((t*t)*e) :=
    Q'.eqv_trans _ _ _ hpoly
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (t*t) _ _
          (Q'.mul_eqv_congr_right _ _ e hcoeff))
        (Q'.mul_eqv_congr_left (t*t) _ _ (Q'.one_mul_eqv e)))
  have hrat : rat (((t*t)*e4+(t*t)*e4)+
      ((4*(t*t))*e16+(4*(t*t))*e16)) = rat ((t*t)*e) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => hc))
  rwa [hrat] at h

/-- Signed-time division by `-t`: the `cneg` changes the positive-denominator
residual into the usual right derivative convention `-2i*output`. -/
def normalizedNegativeResidual (t : Q') (ht : (0 : Q') < t) (d : D) : H :=
  Neg (realScale hw0 hw1 (Q'.recipPos t ht) (negativeError hw0 hw1 t ht d))

theorem physicalPoint_negative_normalized_bound (p : P) (e : Q')
    (he : (0 : Q') < e) (t : Q') (ht : (0 : Q') < t)
    (htr : t ≤ negativeRadius hw0 hw1 p e he) :
    RCle (N (normalizedNegativeResidual hw0 hw1 t ht (ofPoint hw0 hw1 p)))
      (rat e) := by
  have hr : (0 : Q') ≤ Q'.recipPos t ht := Q'.le_of_lt (Q'.recipPos_pos t ht)
  have h := RCscale_mono (Q'.mul_nonneg _ _ hr hr)
    (negative_error_budget hw0 hw1 p e he t ht htr)
  rw [scale_rat] at h
  have hcancel : Q'.eqv
      ((Q'.recipPos t ht*Q'.recipPos t ht)*((t*t)*e)) e := by
    let r := Q'.recipPos t ht
    have htr : Q'.eqv (t*r) 1 := Q'.mul_recipPos_eqv t ht
    have hpoly : Q'.eqv ((r*r)*((t*t)*e)) (((t*r)*(t*r))*e) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0))
          (.mul (.mul (.var 1) (.var 1)) (.var 2)))
        (.mul (.mul (.mul (.var 1) (.var 0))
          (.mul (.var 1) (.var 0))) (.var 2))
        (by decide) (fun | 0 => r | 1 => t | _ => e)
    have hsq : Q'.eqv ((t*r)*(t*r)) 1 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ htr)
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) htr)
    exact Q'.eqv_trans _ _ _ hpoly
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e hsq)
        (Q'.one_mul_eqv e))
  have hrat : rat ((Q'.recipPos t ht*Q'.recipPos t ht)*((t*t)*e)) = rat e :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => hcancel))
  rw [hrat] at h
  change RCle
    (N (Neg (realScale hw0 hw1 (Q'.recipPos t ht)
      (negativeError hw0 hw1 t ht (ofPoint hw0 hw1 p))))) (rat e)
  rw [normSq_neg,normSq_realScale]
  exact h

/-- The complete modulus remains Type-level data from one supplied Point. -/
def negativeTangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : Q', ∀ ht : (0 : Q') < t, t ≤ r →
        RCle (N (normalizedNegativeResidual hw0 hw1 t ht (ofPoint hw0 hw1 p)))
          (rat e)) :=
  ⟨negativeRadius hw0 hw1 p e he,negativeRadius_positive hw0 hw1 p e he,
    physicalPoint_negative_normalized_bound hw0 hw1 p e he⟩

#print axioms outputRows
#print axioms outputRows_pin
#print axioms negativeRadius
#print axioms negativeRadius_positive
#print axioms negativeError
#print axioms negative_error_identity
#print axioms normalizedNegativeResidual
#print axioms physicalPoint_negative_normalized_bound
#print axioms negativeTangentCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeTangent
