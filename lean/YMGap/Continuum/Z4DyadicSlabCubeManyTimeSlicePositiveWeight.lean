/-
# Exact positive weight of the many-time-slice cube family

The common-horizon family is not merely an abstract factorization carrier.
Every one of its projected fine-cube factors has the same derived raw mass
`(coeffW w 1)^6`.  Hence the complete `h+1`-slice product is exactly
`(coeffW w 1)^(6*(h+1))`, and the actual production summand of the physical
union has that same value.

At every strictly positive heat-kernel coupling this gives a strictly positive
finite-horizon path weight.  This is an unnormalized production summand, not a
claim about a normalized cylinder probability or an infinite-volume transfer
eigenvalue.
-/

import YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily

namespace YMGap.Continuum.Z4DyadicSlabCubeManyTimeSlicePositiveWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
open YMGap.Continuum.Z4DyadicSlabCubeKernelProductComposition
open YMGap.Continuum.Z4DyadicSlabCubeTranslatedProjectedComposition
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Exact scalar collapse of an arbitrary bridge list -/

theorem projectedFineCubeRawProduct_eqv_coefficientPower
    (w : Q') {n : Nat} :
    ∀ bridges : List (ProjectedFineCubeSummandBridge w n),
      projectedFineCubeRawProduct w bridges ≈
        (coeffW w 1) ^ (6 * bridges.length)
  | [] => by
      change (1 : Q') ≈ (coeffW w 1) ^ (6 * 0)
      simp only [Nat.mul_zero, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | head :: tail => by
      change
        closedCubeFineSlotRawWeight w head.assignment *
            projectedFineCubeRawProduct w tail ≈
          (coeffW w 1) ^ (6 * (tail.length + 1))
      have hexponent :
          6 * (tail.length + 1) = 6 + 6 * tail.length := by
        omega
      rw [hexponent]
      exact Q'.eqv_trans _
        ((coeffW w 1) ^ 6 *
          (coeffW w 1) ^ (6 * tail.length)) _
        (qmul_congr_local
          (closedCubeFineSlotRawWeight_eqv_pow_six w head.assignment)
          (projectedFineCubeRawProduct_eqv_coefficientPower w tail))
        (Q'.eqv_symm
          (Q'.pow_add_eqv (coeffW w 1) 6 (6 * tail.length)))

theorem manyTimeSliceProjectedRawProduct_eqv_coefficientPower
    (w : Q') (horizon : Nat) :
    projectedFineCubeRawProduct w
        (manyTimeSliceProjectedBridges w horizon) ≈
      (coeffW w 1) ^ (6 * (horizon + 1)) := by
  have hproduct := projectedFineCubeRawProduct_eqv_coefficientPower w
    (manyTimeSliceProjectedBridges w horizon)
  rw [manyTimeSliceProjectedBridges_length w horizon] at hproduct
  exact hproduct

/-! ## 2. The actual common-box union has the derived positive weight -/

theorem manyTimeSliceUnionProduction_eqv_coefficientPower
    (w : Q') (horizon : Nat) :
    parametricLocalizedSpinFoamWeight w (4 + horizon)
        (binaryUnionLabels
          ((manyTimeSliceProjectedBridges w horizon).map
            fun bridge => bridge.physical)) ≈
      (coeffW w 1) ^ (6 * (horizon + 1)) := by
  exact Q'.eqv_trans _
    (projectedFineCubeRawProduct w
      (manyTimeSliceProjectedBridges w horizon)) _
    (Q'.eqv_symm
      (manyTimeSliceProjectedFamily_unionProduction w horizon))
    (manyTimeSliceProjectedRawProduct_eqv_coefficientPower w horizon)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 =>
      Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

theorem manyTimeSliceUnionProduction_pos
    {w : Q'} (hw : (0 : Q') < w) (horizon : Nat) :
    (0 : Q') <
      parametricLocalizedSpinFoamWeight w (4 + horizon)
        (binaryUnionLabels
          ((manyTimeSliceProjectedBridges w horizon).map
            fun bridge => bridge.physical)) := by
  have hcoefficient : (0 : Q') < coeffW w 1 :=
    YMGap.Continuum.FusionResidualBound.coeffW_pos hw 1
  have hpower :
      (0 : Q') < (coeffW w 1) ^ (6 * (horizon + 1)) :=
    qpow_pos_local hcoefficient _
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv
      (manyTimeSliceUnionProduction_eqv_coefficientPower w horizon))

/-! ## Dependency gates -/

#print axioms projectedFineCubeRawProduct_eqv_coefficientPower
#print axioms manyTimeSliceProjectedRawProduct_eqv_coefficientPower
#print axioms manyTimeSliceUnionProduction_eqv_coefficientPower
#print axioms manyTimeSliceUnionProduction_pos
#print axioms oddFineCube_self_not_faceDisjoint

end YMGap.Continuum.Z4DyadicSlabCubeManyTimeSlicePositiveWeight
