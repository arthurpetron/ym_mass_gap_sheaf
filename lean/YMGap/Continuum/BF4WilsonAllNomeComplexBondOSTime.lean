/-
# Algebra and positive time on the complex physical bond completion

Complex operations and numerical positive time are built componentwise on the
two existing physical bond completions. Pins are through the original
completed vectors and finite-source bond pairings. No quotient representative
is selected, and no physical-time calibration or continuum/QFT claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
import YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
import YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue dyadicTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (addTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows Source value inner distance ofSource ofRows inner_value)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (bondCompletedDistance rowSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (add negate sub realSmul bondValue_add bondValue_negate bondValue_sub bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
  (action action_value action_addTime action_distance_bound action_symmetric
    action_ofSource_one continuityRadius continuityRadius_positive action_smallTime)
open YMGap.Continuum.BF4WilsonAllNomeComplexification
  (ComplexValue ComplexCarrier complexAdd complexSmul valueAdd valueMul
    valueConj scalarValue)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def add (x y : H) : H :=
  (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x.1 y.1,
   BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x.2 y.2)

def smul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : H) : H :=
  (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs x.1)
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 t ct x.2),
   BF4WilsonAllNomeBondOSLinear.add hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 t ct x.1)
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs x.2))

theorem value_add (x y : H) :
    value hw0 hw1 (add hw0 hw1 x y) =
      complexAdd hw0 hw1 width (value hw0 hw1 x) (value hw0 hw1 y) := by
  apply Prod.ext
  · exact bondValue_add hw0 hw1 x.1 y.1
  · exact bondValue_add hw0 hw1 x.2 y.2

theorem value_smul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : H) :
    value hw0 hw1 (smul hw0 hw1 s t cs ct x) =
      complexSmul hw0 hw1 width s t cs ct (value hw0 hw1 x) := by
  apply Prod.ext
  · dsimp only [value,smul,complexSmul]
    rw [BF4WilsonAllNomeBondOSLinear.bondValue_sub,
      BF4WilsonAllNomeBondOSLinear.bondValue_realSmul,
      BF4WilsonAllNomeBondOSLinear.bondValue_realSmul]
  · dsimp only [value,smul,complexSmul]
    rw [BF4WilsonAllNomeBondOSLinear.bondValue_add,
      BF4WilsonAllNomeBondOSLinear.bondValue_realSmul,
      BF4WilsonAllNomeBondOSLinear.bondValue_realSmul]

theorem inner_add_right (x y z : H) :
    inner hw0 hw1 x (add hw0 hw1 y z) =
      valueAdd (inner hw0 hw1 x y) (inner hw0 hw1 x z) := by
  calc
    inner hw0 hw1 x (add hw0 hw1 y z) =
        BF4WilsonAllNomeComplexification.inner hw0 hw1 width
          (value hw0 hw1 x)
          (complexAdd hw0 hw1 width (value hw0 hw1 y) (value hw0 hw1 z)) := by
            rw [inner_value, value_add]
    _ = valueAdd
          (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
            (value hw0 hw1 x) (value hw0 hw1 y))
          (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
            (value hw0 hw1 x) (value hw0 hw1 z)) :=
        BF4WilsonAllNomeComplexification.inner_add_right hw0 hw1 width _ _ _
    _ = valueAdd (inner hw0 hw1 x y) (inner hw0 hw1 x z) := by
          rw [← inner_value, ← inner_value]

theorem inner_add_left (x y z : H) :
    inner hw0 hw1 (add hw0 hw1 x y) z =
      valueAdd (inner hw0 hw1 x z) (inner hw0 hw1 y z) := by
  calc
    inner hw0 hw1 (add hw0 hw1 x y) z =
        BF4WilsonAllNomeComplexification.inner hw0 hw1 width
          (complexAdd hw0 hw1 width (value hw0 hw1 x) (value hw0 hw1 y))
          (value hw0 hw1 z) := by
            rw [inner_value, value_add]
    _ = valueAdd
          (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
            (value hw0 hw1 x) (value hw0 hw1 z))
          (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
            (value hw0 hw1 y) (value hw0 hw1 z)) :=
        BF4WilsonAllNomeComplexification.inner_add_left hw0 hw1 width _ _ _
    _ = valueAdd (inner hw0 hw1 x z) (inner hw0 hw1 y z) := by
          rw [← inner_value, ← inner_value]

theorem inner_smul_right (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x y : H) :
    inner hw0 hw1 x (smul hw0 hw1 s t cs ct y) =
      valueMul (scalarValue s t) (inner hw0 hw1 x y) := by
  calc
    inner hw0 hw1 x (smul hw0 hw1 s t cs ct y) =
        BF4WilsonAllNomeComplexification.inner hw0 hw1 width
          (value hw0 hw1 x)
          (complexSmul hw0 hw1 width s t cs ct (value hw0 hw1 y)) := by
            rw [inner_value, value_smul]
    _ = valueMul (BF4WilsonAllNomeComplexification.scalarValue s t)
          (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
            (value hw0 hw1 x) (value hw0 hw1 y)) :=
        BF4WilsonAllNomeComplexification.inner_smul_right hw0 hw1 width s t cs ct _ _
    _ = valueMul (scalarValue s t) (inner hw0 hw1 x y) := by
          rw [inner_value]

theorem inner_smul_left (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x y : H) :
    inner hw0 hw1 (smul hw0 hw1 s t cs ct x) y =
      valueMul (valueConj (scalarValue s t)) (inner hw0 hw1 x y) := by
  calc
    inner hw0 hw1 (smul hw0 hw1 s t cs ct x) y =
        BF4WilsonAllNomeComplexification.inner hw0 hw1 width
          (complexSmul hw0 hw1 width s t cs ct (value hw0 hw1 x))
          (value hw0 hw1 y) := by
            rw [inner_value, value_smul]
    _ = valueMul
          (valueConj (scalarValue s t))
          (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
            (value hw0 hw1 x) (value hw0 hw1 y)) :=
        BF4WilsonAllNomeComplexification.inner_smul_left hw0 hw1 width s t cs ct _ _
    _ = valueMul (valueConj (scalarValue s t)) (inner hw0 hw1 x y) := by
          rw [inner_value]

theorem inner_conj_symm (x y : H) :
    inner hw0 hw1 x y = valueConj (inner hw0 hw1 y x) := by
  rw [inner_value, inner_value]
  exact BF4WilsonAllNomeComplexification.inner_conj_symm hw0 hw1 width _ _

def action (t : PositiveTimeValue) (x : H) : H :=
  (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t x.1,
   BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t x.2)

theorem action_value (t : PositiveTimeValue) (x : H) :
    value hw0 hw1 (action hw0 hw1 t x) =
      (realTimeAction hw0 hw1 t (value hw0 hw1 x).1,
       realTimeAction hw0 hw1 t (value hw0 hw1 x).2) := by
  apply Prod.ext
  · exact BF4WilsonAllNomeBondOSRealTime.action_value hw0 hw1 t x.1
  · exact BF4WilsonAllNomeBondOSRealTime.action_value hw0 hw1 t x.2

theorem action_addTime (s t : PositiveTimeValue) (x : H) :
    action hw0 hw1 (addTime s t) x = action hw0 hw1 s (action hw0 hw1 t x) := by
  apply Prod.ext
  · exact BF4WilsonAllNomeBondOSRealTime.action_addTime hw0 hw1 s t x.1
  · exact BF4WilsonAllNomeBondOSRealTime.action_addTime hw0 hw1 s t x.2

theorem action_symmetric (t : PositiveTimeValue) (x y : H) :
    inner hw0 hw1 (action hw0 hw1 t x) y =
      inner hw0 hw1 x (action hw0 hw1 t y) := by
  apply Prod.ext
  · simp only [inner, action]
    simp only [BF4WilsonAllNomeBondOSRealTime.action_symmetric]
  · simp only [inner, action]
    simp only [BF4WilsonAllNomeBondOSRealTime.action_symmetric]

theorem action_distance_bound (t : PositiveTimeValue) (x y : H) :
    RCle (distance hw0 hw1 (action hw0 hw1 t x) (action hw0 hw1 t y))
      (distance hw0 hw1 x y) := by
  change RCle
    (RCadd
      (bondCompletedDistance hw0 hw1
        (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t x.1)
        (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t y.1))
      (bondCompletedDistance hw0 hw1
        (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t x.2)
        (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t y.2)))
    (RCadd (bondCompletedDistance hw0 hw1 x.1 y.1)
      (bondCompletedDistance hw0 hw1 x.2 y.2))
  exact RCadd_le_add
    (BF4WilsonAllNomeBondOSRealTime.action_distance_bound hw0 hw1 t x.1 y.1)
    (BF4WilsonAllNomeBondOSRealTime.action_distance_bound hw0 hw1 t x.2 y.2)

theorem action_ofSource_one (x : Source width) :
    action hw0 hw1
      (timeValue (dyadicTime ⟨0,1⟩ (Nat.succ_pos 0)))
      (ofSource hw0 hw1 x) =
      ofSource hw0 hw1 (advance 1 x.1, advance 1 x.2) := by
  apply Prod.ext
  · exact BF4WilsonAllNomeBondOSRealTime.action_ofSource_one hw0 hw1 x.1
  · exact BF4WilsonAllNomeBondOSRealTime.action_ofSource_one hw0 hw1 x.2

private theorem half_budget (e : Q') :
    RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e)) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves e))

def continuityRadius (X : Rows hw0 hw1 (width := width)) (e : Q') : Q' :=
  Q'.min'
    (BF4WilsonAllNomeBondOSRealTime.continuityRadius hw0 hw1 X.1 (HalfPow.half*e))
    (BF4WilsonAllNomeBondOSRealTime.continuityRadius hw0 hw1 X.2 (HalfPow.half*e))

theorem continuityRadius_positive (X : Rows hw0 hw1 (width := width)) (e : Q') :
    (0 : Q') < continuityRadius hw0 hw1 X e := by
  unfold continuityRadius Q'.min'
  split
  · exact BF4WilsonAllNomeBondOSRealTime.continuityRadius_positive hw0 hw1 X.1 _
  · exact BF4WilsonAllNomeBondOSRealTime.continuityRadius_positive hw0 hw1 X.2 _

theorem action_smallTime (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (t : PositiveTimeValue)
    (ht : RCle (realValue t) (rat (continuityRadius hw0 hw1 X e))) :
    RCle (distance hw0 hw1
      (action hw0 hw1 t (ofRows hw0 hw1 X)) (ofRows hw0 hw1 X)) (rat e) := by
  have hl : RCle (rat (continuityRadius hw0 hw1 X e))
      (rat (BF4WilsonAllNomeBondOSRealTime.continuityRadius hw0 hw1 X.1 (HalfPow.half*e))) := by
    change leEv (ofQ' (continuityRadius hw0 hw1 X e)) _
    exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.min_le_left' _ _)
  have hr : RCle (rat (continuityRadius hw0 hw1 X e))
      (rat (BF4WilsonAllNomeBondOSRealTime.continuityRadius hw0 hw1 X.2 (HalfPow.half*e))) := by
    change leEv (ofQ' (continuityRadius hw0 hw1 X e)) _
    exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.min_le_right' _ _)
  have hleft := RCle_trans ht hl
  have hright := RCle_trans ht hr
  have hehalf : (0 : Q') < HalfPow.half*e := ExpNeg.half_mul_pos _ he
  have h1 := BF4WilsonAllNomeBondOSRealTime.action_smallTime
    hw0 hw1 X.1 (HalfPow.half*e) hehalf t hleft
  have h2 := BF4WilsonAllNomeBondOSRealTime.action_smallTime
    hw0 hw1 X.2 (HalfPow.half*e) hehalf t hright
  change RCle (RCadd
      (bondCompletedDistance hw0 hw1
        (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t
          (Quotient.mk (rowSetoid hw0 hw1) X.1))
        (Quotient.mk (rowSetoid hw0 hw1) X.1))
    (bondCompletedDistance hw0 hw1
      (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1 t
        (Quotient.mk (rowSetoid hw0 hw1) X.2))
      (Quotient.mk (rowSetoid hw0 hw1) X.2))) (rat e)
  rw [← half_budget e]
  exact RCadd_le_add h1 h2

def continuityCertificate (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat r) →
        RCle (distance hw0 hw1
          (action hw0 hw1 t (ofRows hw0 hw1 X)) (ofRows hw0 hw1 X)) (rat e)) :=
  ⟨continuityRadius hw0 hw1 X e, continuityRadius_positive hw0 hw1 X e,
    action_smallTime hw0 hw1 X e he⟩

#print axioms add
#print axioms smul
#print axioms value_add
#print axioms value_smul
#print axioms inner_add_right
#print axioms inner_add_left
#print axioms inner_smul_right
#print axioms inner_smul_left
#print axioms inner_conj_symm
#print axioms action
#print axioms action_value
#print axioms action_addTime
#print axioms action_symmetric
#print axioms action_distance_bound
#print axioms action_ofSource_one
#print axioms continuityRadius
#print axioms continuityRadius_positive
#print axioms action_smallTime
#print axioms continuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
