/-
# Sharp complex Cauchy--Schwarz on the reflected window limit

The finite realified inequality passes through the original time-window
limits.  This file performs only that first limit hop; intrinsic chart
removal, joint cutoff removal and completion descent remain downstream.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width h stage : Nat)

local notation "R" t => finiteRealifiedPreInnerForm hw0 hw1 width h stage t

/-- Direct-sum reflected pairing of two real components. -/
def realifiedForm
    (x y : guardedSpan width h × guardedSpan width h) : CReal :=
  add
    (form hw0 hw1 width h x.1.val y.1.val x.1.property.1 y.1.property.1 stage)
    (form hw0 hw1 width h x.2.val y.2.val x.2.property.1 y.2.property.1 stage)

/-- The literal quarter-turn pairing inherited from the finite realification. -/
def quarterTurnForm
    (x y : guardedSpan width h × guardedSpan width h) : CReal :=
  realifiedForm hw0 hw1 width h stage x (quarterTurn y)

private theorem realifiedForm_converges
    (x y : guardedSpan width h × guardedSpan width h) :
    ConvergesTo (fun t => ofQ' ((R t).B x y))
      (realifiedForm hw0 hw1 width h stage x y) := by
  have h1 := form_converges hw0 hw1 width h x.1.val y.1.val
    x.1.property.1 y.1.property.1 stage
  have h2 := form_converges hw0 hw1 width h x.2.val y.2.val
    x.2.property.1 y.2.property.1 stage
  simpa only [realifiedForm, finiteRealifiedPreInnerForm, directSumPreInnerForm,
    finitePreInnerForm, finitePairing, ofQ'_add] using
    (TrigAddCReal.convergesTo_add h1 h2)

/-- Sharp complex Cauchy--Schwarz after the time-window limit.  The two
squares are the real pairing and its literal quarter-turn companion. -/
theorem formComplex_cauchySchwarz
    (x y : guardedSpan width h × guardedSpan width h) :
    leEv
      (add
        (mul (realifiedForm hw0 hw1 width h stage x y)
          (realifiedForm hw0 hw1 width h stage x y))
        (mul (quarterTurnForm hw0 hw1 width h stage x y)
          (quarterTurnForm hw0 hw1 width h stage x y)))
      (mul (realifiedForm hw0 hw1 width h stage x x)
        (realifiedForm hw0 hw1 width h stage y y)) := by
  have hxy := realifiedForm_converges hw0 hw1 width h stage x y
  have hj := realifiedForm_converges hw0 hw1 width h stage x (quarterTurn y)
  have hxx := realifiedForm_converges hw0 hw1 width h stage x x
  have hyy := realifiedForm_converges hw0 hw1 width h stage y y
  refine leEv_of_convergesTo_le
    (TrigAddCReal.convergesTo_add
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hxy hxy)
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hj hj))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      hxx hyy) ?_
  intro t epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  have hfinite := finiteComplex_cauchySchwarz hw0 hw1 width h stage t x y
  change (R t).B x y * (R t).B x y +
      (R t).B x (quarterTurn y) * (R t).B x (quarterTurn y) ≤
    (R t).B x x * (R t).B y y + epsilon
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

end YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz.realifiedForm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz.formComplex_cauchySchwarz
