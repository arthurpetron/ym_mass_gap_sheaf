/-
# A finite original-action floor certifies the ACTUAL completed full unit

STATUS UPDATE (2026-09-12): BF4ExactSlabOriginalActionStrictFloor now
constructs the required finite certificate for every rational 0<w<1 and
odd slab, and applies this unchanged implication to prove the actual full
unit non-null. Normalization and physical stationarity/gap remain open.

The imported certificate consists only of finite exact inequalities and an
explicit original product-tail threshold. Its positive rational floor excludes
zero for the original action-integral limit. The proved norm/action identity
then excludes the zero vector for the SAME completed heat unit.

This consumes a successful finite certificate; it does not produce one for
every w and slab. In particular it is not an unconditional non-nullness or
normalization theorem, and says nothing about stationarity or a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction
open YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate

private theorem half_lt {b : Q'} (hb : (0 : Q') < b) : HalfPow.half * b < b :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_lt_mul_of_pos_left hb (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.mul_one_eqv b)))

theorem actionLimit_not_equiv_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (C : FiniteActionFloor w half) :
    ¬ CReal.Equiv (fullActionLimit w hw0 hw1 half) (CReal.ofQ' 0) := by
  intro heq
  obtain ⟨N, hN⟩ := heq (HalfPow.half * C.floor) (ExpNeg.half_mul_pos _ C.floor_pos)
  have hupper := (hN (max N C.index) (Nat.le_max_left _ _)).1
  change _ ≤ (0 : Q') + HalfPow.half * C.floor at hupper
  rw [Q'.zero_add'] at hupper
  have hle := Q'.le_trans' _ _ _ (C.approx_ge hw0 hw1 (max N C.index) (Nat.le_max_right _ _)) hupper
  have hlt : C.floor < C.floor := Q'.lt_of_le_of_lt hle (half_lt C.floor_pos)
  exact (Int.lt_irrefl _) hlt

theorem actionLimit_class_ne_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (C : FiniteActionFloor w half) :
    Quotient.mk CReal.crealSetoid (fullActionLimit w hw0 hw1 half) ≠
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) :=
  fun heq => actionLimit_not_equiv_zero hw0 hw1 C (Quotient.exact heq)

theorem completedHeatUnit_norm_ne_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (C : FiniteActionFloor w half) :
    (cutoffLimitCompletion w (Q'.le_of_lt hw0) half).hilbert.cinner
      (completedHeatUnit w hw0 hw1 half) (completedHeatUnit w hw0 hw1 half) ≠
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) := by
  rw [completedHeatUnit_norm_action]
  exact actionLimit_class_ne_zero hw0 hw1 C

private theorem completed_zero_norm (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (BoundaryObservable.zero half))
      (cutoffLimitEmbed w hw (BoundaryObservable.zero half)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) := by
  have hz := (cutoffLimitGNSData w hw half).B_zero_left (BoundaryObservable.zero half)
  rw [cutoffLimitGNSData_form] at hz
  exact (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv hz))

/-- The zero and unit are in the original carrier, not a replacement Hilbert model. -/
theorem completedHeatUnit_ne_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (C : FiniteActionFloor w half) :
    completedHeatUnit w hw0 hw1 half ≠
      cutoffLimitEmbed w (Q'.le_of_lt hw0) (BoundaryObservable.zero half) := by
  intro heq
  have hnorm := completedHeatUnit_norm_ne_zero hw0 hw1 C
  rw [heq] at hnorm
  exact hnorm (completed_zero_norm w (Q'.le_of_lt hw0) half)

end YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.actionLimit_not_equiv_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.actionLimit_class_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.completedHeatUnit_norm_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.completedHeatUnit_ne_zero
