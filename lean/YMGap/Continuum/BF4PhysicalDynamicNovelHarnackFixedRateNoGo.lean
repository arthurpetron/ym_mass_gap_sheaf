/-
# Fixed-nome novel-Harnack data cannot be the continuum rate band

The localized novel-flow certificate is a fixed-nome finite construction.  If
one reuses its completed rate at every physical scale while assigning a
spacing sequence tending to zero, the resulting lattice margin is constant.
The existing dynamic physical-rate-band theorem forces that margin to vanish,
so the two inputs are incompatible.

This is a route-pruning theorem, not a Yang--Mills no-go theorem.  It leaves
open the scale-dependent Harnack/capacity producer required for a physical
continuum path.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityHarnackBridge
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicNovelHarnackFixedRateNoGo

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Reuse the fixed-nome finite certificate at every scale -/

def fixedHarnackDynamicFamily
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck)
    (spacing : PhysicalSpacing)
    (spacingToZero : SpacingToZero spacing) :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := fun _ => cutoffTwoHalfCoupling
  nome_pos := fun _ => by decide
  nome_lt_one := fun _ => by decide
  transferSpacing := spacing
  transferSpacingToZero := spacingToZero
  completedGap := fun _ =>
    checked.toCompletedStrictContractionData

/-! ## 2. The physical-rate-band contradiction -/

theorem noPhysicalRateBand_of_fixedHarnack
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck)
    (spacing : PhysicalSpacing)
    (spacingToZero : SpacingToZero spacing)
    (band :
      DynamicVacuumSectorPhysicalRateBand
        (fixedHarnackDynamicFamily checked spacing spacingToZero)) :
    False := by
  let family := fixedHarnackDynamicFamily checked spacing spacingToZero
  have hmarginPos : (0 : Q') < family.latticeMargin 0 :=
    family.latticeMargin_pos 0
  let epsilon : Q' := HalfPow.half * family.latticeMargin 0
  have hepsilon : (0 : Q') < epsilon := by
    unfold epsilon
    exact ExpNeg.half_mul_pos _ hmarginPos
  let hscale := band.marginModulus epsilon
  have hsmall := band.latticeMargin_le_epsilon
    epsilon hepsilon hscale (Nat.le_refl _)
  have hfixed : family.latticeMargin hscale ≈
      family.latticeMargin 0 := by
    unfold family fixedHarnackDynamicFamily
      DynamicVacuumSectorCompletedFamily.latticeMargin
    exact Q'.eqv_refl _
  have hle : family.latticeMargin 0 ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hfixed)) hsmall
  have hmul := Q'.mul_lt_mul_of_pos_left
    hmarginPos (by decide : HalfPow.half < (1 : Q'))
  have hstrict : epsilon < family.latticeMargin 0 * (1 : Q') := by
    unfold epsilon
    exact Q'.lt_of_le_of_lt
      (Q'.le_of_eqv (Q'.mul_comm_eqv
        HalfPow.half (family.latticeMargin 0))) hmul
  have hreverse : family.latticeMargin 0 * (1 : Q') ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv (family.latticeMargin 0))) hle
  exact (Int.not_lt_of_ge hreverse) hstrict

end YMGap.Continuum.BF4PhysicalDynamicNovelHarnackFixedRateNoGo

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicNovelHarnackFixedRateNoGo.fixedHarnackDynamicFamily
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicNovelHarnackFixedRateNoGo.noPhysicalRateBand_of_fixedHarnack
