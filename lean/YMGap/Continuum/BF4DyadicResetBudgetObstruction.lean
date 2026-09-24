/-
# The proposed dyadic reset floor cannot pay the existing cubic loss budget

This file bounds only the numerical floor proposed by the reset expansion.
It does not bound the actual Wilson variance or response.  Even if the reset
expansion were proved, its floor is at most perimeter times the nome defect,
and therefore cannot pay the already displayed cubic absolute-loss budget.
-/

import YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.R1CornerAtoms

namespace YMGap.Continuum.BF4DyadicResetBudgetObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal (ofNat_le_ofNat)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.R1CornerAtoms (oneSub_qpow_le)
open YMGap.Continuum.R1RegimeGE (sub_nonpos')
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
  (starRatio starRatio_positive starRatio_le_one)
open YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction
  (starRatio_le_nome_defect)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (OrientedBF4Link)

local infix:50 " ≈ " => Q'.eqv

/-- Mass of the branch in which all `k` proposed residual factors occur. -/
def residualMass (w : Q') (k : Nat) : Q' :=
  qpow ((1 : Q') + -starRatio w) k

/-- The numerical lower-floor expression proposed by the reset argument.
This definition is not an assertion that the corresponding expansion exists. -/
def resetFloor (w : Q') (k : Nat) : Q' :=
  (1 : Q') + -residualMass w k +
    -((4 : Q') * residualMass w k * residualMass w k)

private theorem resetFloor_le_one_sub (w : Q') (k : Nat) :
    resetFloor w k ≤ (1 : Q') + -residualMass w k := by
  let p := residualMass w k
  have hs : (0 : Q') ≤ (4 : Q') * p * p := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg (4 : Q') (p*p) (by decide) (SumOfSquares.q_mul_self_nonneg p))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (4 : Q') p p)))
  have hn : -((4 : Q') * p * p) ≤ (0 : Q') := Q'.neg_le_neg hs
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left (1 + -p) _ _ hn)
    (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))

/-- Bernoulli bounds the proposed reset floor by the number of selected
links times the star ratio. -/
theorem resetFloor_le_count_mul_starRatio {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (k : Nat) :
    resetFloor w k ≤ Q'.ofNat k * starRatio w := by
  let r := starRatio w
  let a : Q' := 1 + -r
  have ha0 : (0 : Q') ≤ a := Q'.sub_nonneg_of_le (starRatio_le_one hw0 hw1)
  have ha1 : a ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt (starRatio_positive hw0 hw1))))
      (Q'.le_of_eqv (by decide : Q'.eqv ((1 : Q') + -0) 1))
  have hb := oneSub_qpow_le ha0 ha1 k
  have hd : (1 : Q') + -a ≈ r :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => r)
  exact Q'.le_trans' _ _ _ (resetFloor_le_one_sub w k)
    (Q'.le_trans' _ _ _ hb
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat k) _ _ hd)))

/-- The nome ceiling for the star ratio turns the count bound into a linear
nome-defect bound. -/
theorem resetFloor_le_count_mul_nomeDefect {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (k : Nat) :
    resetFloor w k ≤ Q'.ofNat k * ((1 : Q') + -w) :=
  Q'.le_trans' _ _ _ (resetFloor_le_count_mul_starRatio hw0 hw1 k)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (starRatio_le_nome_defect hw0 hw1)
      (ofNat_le_ofNat (Nat.zero_le k)))

/-- Any proposed selection with at most the square perimeter has reset floor
no larger than half of the existing displayed `384*L^3*(1-w)` budget.
This is only a comparison of certificate numbers. -/
theorem resetFloor_cubic_budget_nonpositive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale k : Nat) (hk : k ≤ 4 * side scale) :
    resetFloor w k + -((192 : Q') *
      (Q'.ofNat (side scale) *
        (Q'.ofNat (side scale) * Q'.ofNat (side scale))) * (1 + -w)) ≤ (0 : Q') := by
  let L := side scale
  let d : Q' := 1 + -w
  have hd : (0 : Q') ≤ d := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hkq : Q'.ofNat k ≤ Q'.ofNat (4*L) := ofNat_le_ofNat hk
  have hL : 0 < L := side_positive scale
  have hL1 : 1 ≤ L := hL
  have hsq : L ≤ L*L := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left L hL1
  have hcube : L ≤ L*(L*L) := Nat.le_trans hsq (Nat.mul_le_mul_left L hsq)
  have hnat : 4*L ≤ 192*(L*(L*L)) :=
    Nat.le_trans (Nat.mul_le_mul_left 4 hcube)
      (Nat.mul_le_mul_right (L*(L*L)) (by decide : 4 ≤ 192))
  have hcoef0 : Q'.ofNat (4*L) ≤ Q'.ofNat (192*(L*(L*L))) := ofNat_le_ofNat hnat
  have hright : Q'.ofNat (192*(L*(L*L))) ≈
      (192 : Q') * (Q'.ofNat L * (Q'.ofNat L * Q'.ofNat L)) := by
    exact Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv 192 (L*(L*L)))
      (Q'.mul_eqv_congr_left (192 : Q') _ _
        (Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv L (L*L))
          (Q'.mul_eqv_congr_left (Q'.ofNat L) _ _
            (HeatKernelRGStep.ofNat_mul_eqv L L))))
  have hcoef : Q'.ofNat (4*L) ≤
      (192 : Q') * (Q'.ofNat L * (Q'.ofNat L * Q'.ofNat L)) :=
    Q'.le_trans' _ _ _ hcoef0 (Q'.le_of_eqv hright)
  have hfloor : resetFloor w k ≤
      (192 : Q') * (Q'.ofNat L * (Q'.ofNat L * Q'.ofNat L)) * d :=
    Q'.le_trans' _ _ _ (resetFloor_le_count_mul_nomeDefect hw0 hw1 k)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ d hkq hd)
        (Q'.mul_le_mul_of_nonneg_right _ _ d hcoef hd))
  exact sub_nonpos' hfloor

/-- A literal selected sublist automatically satisfies the perimeter count
premise; no distinctness or injectivity assumption is inserted. -/
theorem selectedSublist_resetFloor_cubic_budget_nonpositive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width)
    (selected : List OrientedBF4Link)
    (hselected : selected.Sublist (paddedSquare scale width hwidth).edges) :
    resetFloor w selected.length + -((192 : Q') *
      (Q'.ofNat (side scale) *
        (Q'.ofNat (side scale) * Q'.ofNat (side scale))) * (1 + -w)) ≤ (0 : Q') := by
  apply resetFloor_cubic_budget_nonpositive hw0 hw1 scale selected.length
  have hlen := hselected.length_le
  rw [paddedSquare_edges, square_length] at hlen
  exact hlen

#print axioms residualMass
#print axioms resetFloor
#print axioms resetFloor_le_count_mul_starRatio
#print axioms resetFloor_le_count_mul_nomeDefect
#print axioms resetFloor_cubic_budget_nonpositive
#print axioms selectedSublist_resetFloor_cubic_budget_nonpositive

end YMGap.Continuum.BF4DyadicResetBudgetObstruction
