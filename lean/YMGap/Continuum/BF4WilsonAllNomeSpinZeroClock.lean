/-
# Spin-zero insertions retain the original separated-word clock

The spin-zero time-zero multiplier is the identity on the CURRENT all-nome
ambient Wilson completion. Its physical bond insertion is nevertheless the
ORIGINAL one-step transfer: the two half-step buffers do not disappear.
Every all-zero word therefore records its full length, on every bond class;
its signed-source matrix elements are the original reflected joint limits.

Only 0 < w < 1 and the literal source width are used. No small-nome carrier,
new analytic input, equal-time sector multiplier, physical spacing, changing
family or continuum QFT claim is supplied.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
import YMGap.Continuum.BF4WilsonAllNomeWindowPins

namespace YMGap.Continuum.BF4WilsonAllNomeSpinZeroClock

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance advance_zero advance_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (originalJointLimit)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply chart_multiply)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_chart intrinsicForm_symm commonForm)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completion_eq_of_pointwise)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
  (completedMultiply completedMultiply_mk multiplyCauchy_seq)
open YMGap.Continuum.BF4WilsonAllNomeWindowPins (originalJoint_padded_congr)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root root_zero_depth)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (root_square)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_original)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd crossOdd_within)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion ofSource bondCompletedInner constant_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner bondAction bondAction_value
    bondAction_ofSource_one)
open YMGap.Continuum.BF4WilsonAllNomeBondOSInsertion (act act_root_pin)
open YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
  (Word wordAct wordAct_append)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyOne)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_one)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "F" => intrinsicForm hw0 hw1

private theorem spin_zero_source_identity (blocks J : Nat) (L : SourceLoop width)
    (x : IntrinsicExpression width) (hx : x.radius ≤ J) :
    PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (chart J (multiply L 0 x)))
      (sourcePolynomial (chart J x)) := by
  rw [chart_multiply J L 0 x hx]
  have hloop : PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (.loop J L 0)) polyOne := by
    simpa only [sourcePolynomial, sourceCharacter, characterPolynomial] using
      (lift_one blocks (J * List.length (baseLinks width)))
  exact (hloop.mul (PaddedPolynomialCoeffEqv.refl _ _)).trans
    (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.one_mul _))

private theorem intrinsicForm_spin_zero_right (L : SourceLoop width)
    (z x : IntrinsicExpression width) : Equiv (F z (multiply L 0 x)) (F z x) := by
  let J := max z.radius x.radius
  have hz : z.radius ≤ J := Nat.le_max_left _ _
  have hx : x.radius ≤ J := Nat.le_max_right _ _
  have hsource := (PaddedPolynomialCoeffEqv.refl
    ((2*J+1)*List.length (baseLinks width)) (sourcePolynomial (mirror J (chart J z)))).mul
      (spin_zero_source_identity ((2*J+1)*List.length (baseLinks width)) J L x hx)
  have hlimit := originalJoint_padded_congr hw0 hw1 (2*J)
    (.mul (mirror J (chart J z)) (chart J (multiply L 0 x)))
    (.mul (mirror J (chart J z)) (chart J x))
    ⟨mirror_within J (chart J z),
      within_mono (by omega : J ≤ 2*J) _ (chart_within J (multiply L 0 x) hx)⟩
    ⟨mirror_within J (chart J z),
      within_mono (by omega : J ≤ 2*J) _ (chart_within J x hx)⟩ hsource
  have hcommon : Equiv
      (commonForm hw0 hw1 J (chart J z) (chart J (multiply L 0 x))
        (chart_within J z hz) (chart_within J (multiply L 0 x) hx))
      (commonForm hw0 hw1 J (chart J z) (chart J x)
        (chart_within J z hz) (chart_within J x hx)) := hlimit
  exact (intrinsicForm_chart hw0 hw1 z (multiply L 0 x) J hz hx).trans
    (hcommon.trans (intrinsicForm_chart hw0 hw1 z x J hz hx).symm)

/-- The ambient multiplier identity uses original padded joint congruence,
not a free-coefficient identity that would discard lifted zero exponents. -/
theorem completedMultiply_spin_zero (L : SourceLoop width) (x : V) :
    completedMultiply hw0 hw1 L 0 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [completedMultiply_mk]
  apply completion_eq_of_pointwise hw0 hw1
  intro n z
  change Equiv (F (multiply L 0 (X.seq n)) z) (F (X.seq n) z)
  exact (intrinsicForm_symm hw0 hw1 (multiply L 0 (X.seq n)) z).trans
    ((intrinsicForm_spin_zero_right hw0 hw1 L z (X.seq n)).trans
      (intrinsicForm_symm hw0 hw1 (X.seq n) z).symm)

/-- One ORIGINAL dimensionless lattice step; no physical spacing is chosen. -/
def timeOne : PositiveTime := dyadicTime ⟨0,1⟩ (Nat.succ_pos 0)

/-- On every physical bond class the two buffers remain: R I R = T(1). -/
theorem act_spin_zero_value (L : SourceLoop width) (x : H) :
    bondValue hw0 hw1 (act hw0 hw1 L 0 x) =
      completedTime hw0 hw1 1 (bondValue hw0 hw1 x) := by
  rw [act_root_pin, completedMultiply_spin_zero, root_square hw0 hw1 0,
    root_zero_depth]

theorem act_spin_zero_time (L : SourceLoop width) (x : H) :
    act hw0 hw1 L 0 x = bondAction hw0 hw1 timeOne x := by
  apply bondValue_injective hw0 hw1
  rw [act_spin_zero_value, bondAction_value, timeOne, positiveAction_original]

/-- All zero-labelled words keep their full elapsed time on EVERY class. -/
theorem wordAct_spin_zero_value (loops : List (SourceLoop width)) (x : H) :
    bondValue hw0 hw1 (wordAct hw0 hw1 (loops.map (fun L => (L,0))) x) =
      completedTime hw0 hw1 loops.length (bondValue hw0 hw1 x) := by
  induction loops with
  | nil => exact (completedTime_zero hw0 hw1 _).symm
  | cons L rest ih =>
      change bondValue hw0 hw1
        (act hw0 hw1 L 0 (wordAct hw0 hw1 (rest.map (fun K => (K,0))) x)) = _
      rw [act_spin_zero_value, ih, ← completedTime_add]
      rw [List.length_cons, Nat.add_comm 1 rest.length]

/-- The original geometric source advances by exactly the number of entries. -/
theorem wordAct_spin_zero_ofSource (loops : List (SourceLoop width))
    (y : IntrinsicExpression width) :
    wordAct hw0 hw1 (loops.map (fun L => (L,0))) (ofSource hw0 hw1 y) =
      ofSource hw0 hw1 (advance loops.length y) := by
  induction loops with
  | nil => rw [List.map_nil, wordAct, List.length_nil, advance_zero]
  | cons L rest ih =>
      change act hw0 hw1 L 0
        (wordAct hw0 hw1 (rest.map (fun K => (K,0))) (ofSource hw0 hw1 y)) = _
      rw [ih, act_spin_zero_time, timeOne, bondAction_ofSource_one, advance_add,
        List.length_cons, Nat.add_comm 1 rest.length]

/-- The completed mixed correlation uses the recorded original integer time;
the empty word has time zero and hence the identity action. -/
theorem wordAct_spin_zero_pairing (loops : List (SourceLoop width)) (x y : H) :
    bondCompletedInner hw0 hw1 x
      (wordAct hw0 hw1 (loops.map (fun L => (L,0))) y) =
      completedInner hw0 hw1 (bondValue hw0 hw1 x)
        (completedTime hw0 hw1 loops.length (bondValue hw0 hw1 y)) := by
  rw [bondValue_inner, wordAct_spin_zero_value]

/-- Every signed-source matrix element retains the same original action,
normalization and both source expressions in the reflected joint limit. -/
theorem wordAct_spin_zero_source_pairing (loops : List (SourceLoop width))
    (x y : IntrinsicExpression width) :
    bondCompletedInner hw0 hw1 (ofSource hw0 hw1 x)
      (wordAct hw0 hw1 (loops.map (fun L => (L,0))) (ofSource hw0 hw1 y)) =
      Quotient.mk crealSetoid
        (originalJointLimit hw0 hw1 (2*(max x.radius (advance loops.length y).radius)+1)
          (crossOdd x (advance loops.length y))
          (crossOdd_within x (advance loops.length y))) := by
  rw [wordAct_spin_zero_ofSource, constant_pairing]
  rfl

/-- An interior zero label retains an explicit time step between arbitrary
words. No inequality against the deleted word or commutativity is asserted. -/
theorem wordAct_insert_spin_zero (left right : Word width) (L : SourceLoop width)
    (x : H) :
    wordAct hw0 hw1 (left ++ ((L,0) :: right)) x =
      wordAct hw0 hw1 left (bondAction hw0 hw1 timeOne (wordAct hw0 hw1 right x)) := by
  rw [wordAct_append]
  change wordAct hw0 hw1 left (act hw0 hw1 L 0 (wordAct hw0 hw1 right x)) = _
  rw [act_spin_zero_time]

#print axioms completedMultiply_spin_zero
#print axioms timeOne
#print axioms act_spin_zero_value
#print axioms act_spin_zero_time
#print axioms wordAct_spin_zero_value
#print axioms wordAct_spin_zero_ofSource
#print axioms wordAct_spin_zero_pairing
#print axioms wordAct_spin_zero_source_pairing
#print axioms wordAct_insert_spin_zero

end YMGap.Continuum.BF4WilsonAllNomeSpinZeroClock
