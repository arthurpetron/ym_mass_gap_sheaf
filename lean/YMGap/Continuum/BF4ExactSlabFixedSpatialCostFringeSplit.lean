/-
# Exact fringe contribution to the original finite-family cost

Zeroing the fringe tests leaves every active--active determinant term
unchanged. The diagonal cost loses exactly (1-h) times the original
fringe marginal norm sum. This is finite signed algebra on the SAME
original marginal, at the supplied finite reciprocal degrees.

No approximation property is asserted for the active-only family, and
no sign of the remaining joint cost is assumed or proved here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarFamilyErasure (singleCuts pairCuts)
open YMGap.Continuum.QuaternionHaarFamilySquare
  (singleCuts_map_fst qListSum_congr qListSum_scale)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks activeBlocks

/-- Preserve the actual active tests and set every other test to zero. -/
def activeTests (width : Nat) (qs : Nat → RatPoly) (i : Nat) : RatPoly :=
  if i ∈ activeBlocks width then qs i else polyZero

/-- The restriction stays on the original full polynomial carrier. -/
theorem activeTests_supported (width : Nat) (qs : Nat → RatPoly)
    (hqs : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (qs i)) :
    ∀ i, i < N width → SupportedQuaternionBlocks (N width) (activeTests width qs i) := by
  intro i hi
  unfold activeTests
  split
  · exact hqs i hi
  · intro term ht
    cases ht

private theorem sum_append (xs ys : List Q') :
    qListSum (xs ++ ys) ≈ qListSum xs + qListSum ys := by
  induction xs with
  | nil => exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | cons x xs ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl x) ih)
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sum_zero {A : Type} (ids : List A) (f : A → Q')
    (hf : ∀ i, i ∈ ids → f i ≈ 0) : qListSum (ids.map f) ≈ 0 := by
  revert hf
  induction ids with
  | nil => intro _; exact Q'.eqv_refl _
  | cons i ids ih =>
      intro hf
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (hf i List.mem_cons_self)
          (ih (fun j hj => hf j (List.mem_cons_of_mem i hj))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

set_option maxHeartbeats 800000 in
private theorem marginalPair_zero (w : Q') (K width n : Nat) :
    marginalPair w K width n polyZero polyZero ≈ 0 := by
  change quaternionHaar (N width)
    (polyMul (marginalWeight w K width n) polyZero) ≈ 0
  exact haar_of_coeff (RatPolyCoeffEqv.mul_zero_right (marginalWeight w K width n))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- Exact equality: no determinant term contains a fringe test. -/
theorem determinantRemainder_activeTests (qs : Nat → RatPoly) (degrees : Nat → Nat) :
    determinantRemainder hw0 hw1 K width hK n (activeTests width qs) degrees =
      determinantRemainder hw0 hw1 K width hK n qs degrees := by
  unfold determinantRemainder
  apply congrArg qListSum
  apply List.map_congr_left
  intro c _
  by_cases hi : c.1 ∈ activeBlocks width
  · by_cases hj : c.2.1 ∈ activeBlocks width
    · simp only [componentDeterminant, activeTests, if_pos hi, if_pos hj]
    · simp only [componentDeterminant, if_pos hi, if_neg hj]
  · simp only [componentDeterminant, if_neg hi]

private theorem diagonal_indexed (qs : Nat → RatPoly) (degrees : Nat → Nat) :
    diagonalRemainder hw0 hw1 K width hK n qs degrees =
      qListSum ((labels width).map (componentCost hw0 hw1 K width hK n qs degrees)) := by
  unfold diagonalRemainder
  apply congrArg qListSum
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (componentCost hw0 hw1 K width hK n qs degrees))
      (singleCuts_map_fst (labels width))

private theorem component_active (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (i : Nat) (hi : i ∈ activeBlocks width) :
    componentCost hw0 hw1 K width hK n (activeTests width qs) degrees i =
      componentCost hw0 hw1 K width hK n qs degrees i := by
  simp only [componentCost, activeTests, if_pos hi]

private theorem component_inactive_zero (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (i : Nat) (hi : i ∉ activeBlocks width) :
    componentCost hw0 hw1 K width hK n (activeTests width qs) degrees i ≈ 0 := by
  simp only [componentCost, activeTests, if_neg hi]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (marginalPair_zero w K width n))
    (Q'.mul_zero_eqv _)

/-- The lost diagonal is exactly the original fringe norm sum. The tests
and reciprocal degrees are arbitrary; there is no centering premise. -/
theorem diagonalRemainder_split (qs : Nat → RatPoly) (degrees : Nat → Nat) :
    diagonalRemainder hw0 hw1 K width hK n qs degrees ≈
      diagonalRemainder hw0 hw1 K width hK n (activeTests width qs) degrees +
        ((1 : Q') + -(headFloor w)) * qListSum ((fringeBlocks width).map
          (fun i => marginalPair w K width n (qs i) (qs i))) := by
  let activeSum := qListSum ((activeBlocks width).map
    (componentCost hw0 hw1 K width hK n qs degrees))
  have ha : diagonalRemainder hw0 hw1 K width hK n (activeTests width qs) degrees ≈
      activeSum := by
    rw [diagonal_indexed, labels, List.map_append]
    exact Q'.eqv_trans _ _ _ (sum_append _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (qListSum_congr (activeBlocks width)
            (componentCost hw0 hw1 K width hK n (activeTests width qs) degrees)
            (componentCost hw0 hw1 K width hK n qs degrees) (fun i hi =>
            Q'.eqv_of_eq (component_active hw0 hw1 K width hK n qs degrees i hi)))
          (sum_zero (fringeBlocks width)
            (componentCost hw0 hw1 K width hK n (activeTests width qs) degrees) (fun i hi =>
            component_inactive_zero hw0 hw1 K width hK n qs degrees i
              ((fringeBlocks_mem_iff width i).mp hi).2)))
        (Q'.eqv_of_eq (Q'.add_zero' activeSum)))
  have hfull : diagonalRemainder hw0 hw1 K width hK n qs degrees ≈
      activeSum + ((1 : Q') + -(headFloor w)) * qListSum ((fringeBlocks width).map
        (fun i => marginalPair w K width n (qs i) (qs i))) := by
    rw [diagonal_indexed, labels, List.map_append]
    exact Q'.eqv_trans _ _ _ (sum_append _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl activeSum)
        (Q'.eqv_trans _ _ _
          (qListSum_congr (fringeBlocks width)
            (componentCost hw0 hw1 K width hK n qs degrees)
            (fun i => ((1 : Q') + -(headFloor w)) * marginalPair w K width n (qs i) (qs i))
            (fun i hi => by
            have hn := ((fringeBlocks_mem_iff width i).mp hi).2
            exact Q'.eqv_of_eq (by simp only [componentCost, if_neg hn])))
          (qListSum_scale (fringeBlocks width)
            (fun i => marginalPair w K width n (qs i) (qs i))
            ((1 : Q') + -(headFloor w)))))
  exact Q'.eqv_trans _ _ _ hfull
    (Q'.add_eqv_congr' (Q'.eqv_symm ha) (Q'.eqv_refl _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit.activeTests
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit.activeTests_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit.determinantRemainder_activeTests
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit.diagonalRemainder_split
