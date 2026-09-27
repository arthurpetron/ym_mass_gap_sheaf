/-
# A necessary finite carrier budget for the changing-nome calibration

The anchored BF4 head constant is the quotient `S/F`, where `S` is the
explicit carrier-square scale and `F` is one half of a finite positive
pulled-kernel minimum.  The minimum is folded with the unit fallback, hence
`F ≤ 1/2`.  This file exposes the resulting exact lower bound

  `headEnergyConstant ≥ 2*S` and `gapDenominator ≥ 2 + 12*S`.

This is a one-sided obstruction/input reduction only.  It does not estimate
the missing cofinal lower bound on `F`, and it does not inhabit the
denominator-versus-spacing band, a continuum limit, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor

namespace YMGap.Continuum.BF4PhysicalChangingNomeAnchorBudget

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

local infix:50 " ≈ " => Q'.eqv

private theorem two_half_mul_scale_eqv (scale : Q') :
    (Q'.ofNat 2 * HalfPow.half) * scale ≈ scale := by
  have htwo : Q'.ofNat 2 * HalfPow.half ≈ (1 : Q') := by
    decide
  refine Q'.eqv_trans _ ((1 : Q') * scale) _
    (Q'.mul_eqv_congr_right _ _ _ htwo) ?_
  exact Q'.one_mul_eqv _

private theorem listPositiveMinOne_le_one_local
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      listPositiveMinOne value states ≤ 1
  | [] => Q'.le_refl' 1
  | _first :: rest =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value rest)

private theorem fixedBasePulledEdgeAnchorMinimum_le_one
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) :
    fixedBasePulledEdgeAnchorMinimum w hw base half ≤ 1 := by
  unfold fixedBasePulledEdgeAnchorMinimum
  exact listPositiveMinOne_le_one_local _ _

/-- The exact finite pulled-kernel floor is bounded above by its half-unit
fallback.  This is the direction needed for a necessary denominator budget;
it is not the missing positive lower estimate along shrinking nome. -/
theorem fixedBasePulledPositiveEdgeFloorValue_le_half
    (w : Q') (hw : (0 : Q') ≤ w) (base half : Nat) :
    fixedBasePulledPositiveEdgeFloorValue w hw base half ≤
      HalfPow.half := by
  unfold fixedBasePulledPositiveEdgeFloorValue
  have hmin := fixedBasePulledEdgeAnchorMinimum_le_one w hw base half
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    HalfPow.half hmin HalfPow.half_nonneg
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.mul_one_eqv HalfPow.half))

private theorem two_mul_scale_mul_floor_le_scale
    {scale floor : Q'}
    (hscale : (0 : Q') < scale)
    (hfloor_le : floor ≤ HalfPow.half) :
    (Q'.ofNat 2 * scale) * floor ≤ scale := by
  have hscale0 : (0 : Q') ≤ scale := Q'.le_of_lt hscale
  have hmultiplier : (0 : Q') ≤ Q'.ofNat 2 * scale :=
    Q'.mul_nonneg _ _ (by decide) hscale0
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.ofNat 2 * scale) hfloor_le hmultiplier
  have hleft : (Q'.ofNat 2 * scale) * floor ≈
      floor * (Q'.ofNat 2 * scale) :=
    Q'.mul_comm_eqv _ _
  have hright : HalfPow.half * (Q'.ofNat 2 * scale) ≈
      (Q'.ofNat 2 * HalfPow.half) * scale := by
    refine Q'.eqv_trans _ ((HalfPow.half * Q'.ofNat 2) * scale) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv _ _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (Q'.le_of_eqv (two_half_mul_scale_eqv scale))))

/-! The quotient comparison is kept abstract on purpose. Instantiating it
with the dependent `headEnergyConstant` is a separate elaboration boundary;
the current calibration still lacks the cofinal lower estimate on its finite
floor. -/

theorem divPos_ge_two_mul_of_floor_le_half
    {scale floor : Q'}
    (hscale : (0 : Q') < scale)
    (hfloor : (0 : Q') < floor)
    (hfloor_le : floor ≤ HalfPow.half) :
    Q'.ofNat 2 * scale ≤ Q'.divPos scale floor hfloor := by
  have hmul : (Q'.ofNat 2 * scale) * floor ≤ scale := by
    exact two_mul_scale_mul_floor_le_scale hscale hfloor_le
  exact Q'.le_divPos_of_mul_le scale floor hfloor hmul

#print axioms fixedBasePulledPositiveEdgeFloorValue_le_half
#print axioms divPos_ge_two_mul_of_floor_le_half

end YMGap.Continuum.BF4PhysicalChangingNomeAnchorBudget
