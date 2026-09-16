/-
# Normalized constant observable for the intrinsic reflected form

The literal constant-one spatial-probe presentation has reflected squared
norm one under the SAME constructed window limit. It is consequently not
null. This supplies the normalized candidate vacuum observable; invariance
under a physical transfer and isolation of its vacuum sector are separate.
It does not prove a nonconstant excitation or continuum QFT nontriviality.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState (windowLimit_one)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyOne)

/-- One constant coefficient times the empty ordered probe schedule. -/
def unitSpan : DistanceSpan := [(1, [])]

theorem unit_physical (width : Nat) : Physical width unitSpan := by
  intro x hx e he
  have hx' : x = ((1 : Q'), []) := List.mem_singleton.mp hx
  subst x
  exact False.elim (List.not_mem_nil he)

theorem radius_unit : radius unitSpan = 0 := rfl

theorem encodeChart_unit (h : Nat) : encodeChart h unitSpan = unitSpan := rfl

theorem sourceSpan_unit (width : Nat) : sourceSpan width unitSpan = polyOne := rfl

/-- Same-partition normalization, not an imposed inner-product convention. -/
theorem pairing_unit_unit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) : Equiv (pairing hw0 hw1 width unitSpan unitSpan stage) (ofQ' 1) :=
  windowLimit_one hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) 0

/-- The constant observable cannot disappear in the reflected radical. -/
theorem unit_not_null {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) :
    ¬ Equiv (pairing hw0 hw1 width unitSpan unitSpan stage) (ofQ' 0) := by
  intro hnull
  have h := Equiv.trans (Equiv.symm (pairing_unit_unit hw0 hw1 width stage)) hnull
  obtain ⟨N, hN⟩ := h HalfPow.half (by decide)
  have hbad : (1 : Q') ≤ 0+HalfPow.half := (hN N (Nat.le_refl N)).1
  exact (by decide : ¬ ((1 : Q') ≤ 0+HalfPow.half)) hbad

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.unitSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.unit_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.radius_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.encodeChart_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.sourceSpan_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.pairing_unit_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit.unit_not_null
