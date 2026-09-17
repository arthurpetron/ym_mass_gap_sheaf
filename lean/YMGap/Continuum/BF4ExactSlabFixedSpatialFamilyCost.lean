/-
# The full signed cost on the same actual marginal

At finite polynomial reciprocal degrees, the family cost is h times the
norm of the SUM of corrected tests, plus a positive diagonal remainder,
plus the signed active--active message-determinant sum. Fringe cross
pairings belong to the ordinary norm; only their determinant is zero.

The exact flow belongs to this same corrected sum. Thus the resulting
energy estimate has no changing ambient measure or inverse-limit premise.
Constructing a controlled approximation to the centered observable and
bounding its signed remainder uniformly remain separate OPEN obligations.
-/

import YMGap.Continuum.QuaternionHaarFamilySquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage (conditionalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse (reciprocal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet (erasedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering (weightedResidual)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFamilyErasure (singleCuts pairCuts)
open YMGap.Continuum.QuaternionHaarFamilySquare

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks activeBlocks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- Same finite tests as residualTests, now with the q_i explicitly supplied. -/
def finiteTests (qs : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) : RatPoly :=
  if i ∈ activeBlocks width then dualTest hw0 hw1 K width hK n i (qs i) (degrees i) else qs i

/-- Corrected ordinary marginal tests; fringe tests stay unchanged. -/
def corrected (qs : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) : RatPoly :=
  if i ∈ activeBlocks width then correctedTest hw0 hw1 K width hK n i (qs i) (degrees i) else qs i

def correctedSum (qs : Nat → RatPoly) (degrees : Nat → Nat) : RatPoly :=
  polySum ((labels width).map (corrected hw0 hw1 K width hK n qs degrees))

/-- Positive diagonal cost, with the exact coefficient 1-h on fringe links. -/
def componentCost (qs : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) : Q' :=
  if i ∈ activeBlocks width then diagonalCost hw0 hw1 K width hK n i (qs i) (degrees i)
  else ((1 : Q') + -(headFloor w))*marginalPair w K width n (qs i) (qs i)

def diagonalRemainder (qs : Nat → RatPoly) (degrees : Nat → Nat) : Q' :=
  qListSum ((singleCuts (labels width)).map (fun c => componentCost hw0 hw1 K width hK n qs degrees c.1))

/-- The determinant remainder is present only when BOTH indices are active. -/
def componentDeterminant (qs : Nat → RatPoly) (degrees : Nat → Nat) (i j : Nat) : Q' :=
  if i ∈ activeBlocks width then
    if j ∈ activeBlocks width then determinantCross hw0 hw1 K width hK n i j (qs i) (qs j) (degrees i) (degrees j)
    else 0
  else 0

def determinantRemainder (qs : Nat → RatPoly) (degrees : Nat → Nat) : Q' :=
  qListSum ((pairCuts (labels width)).map
    (fun c => componentDeterminant hw0 hw1 K width hK n qs degrees c.1 c.2.1))

private theorem one_pin (qs : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) (f : RatPoly) :
    erasedPair w K width n i f (finiteTests hw0 hw1 K width hK n qs degrees i) ≈
      marginalPair w K width n f (corrected hw0 hw1 K width hK n qs degrees i) := by
  unfold finiteTests corrected
  by_cases hi : i ∈ activeBlocks width
  · rw [if_pos hi, if_pos hi]
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 4) (.mul (.mul (.var 2) (.var 3)) (.var 5))))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 4) (.mul (.mul (.var 1) (.var 5)) (.var 3))))
      (by decide) (fun
        | 0 => polyMul (spatialWeight w K width) (terminalMessage w K width n)
        | 1 => conditionalMessage w K width n i | 2 => terminalMessage w K width (n+1)
        | 3 => qs i | 4 => f | _ => reciprocal hw0 hw1 K width hK n i (degrees i)))
  · rw [if_neg hi, if_neg hi]
    unfold erasedPair
    rw [conditionalMessage_inactive w K width n i hi]
    exact Q'.eqv_refl _

private theorem component_diagonal_pin (qs : Nat → RatPoly) (degrees : Nat → Nat) (i : Nat) :
    erasedPair w K width n i (finiteTests hw0 hw1 K width hK n qs degrees i)
      (finiteTests hw0 hw1 K width hK n qs degrees i) ≈
      headFloor w*marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees i)
        (corrected hw0 hw1 K width hK n qs degrees i) + componentCost hw0 hw1 K width hK n qs degrees i := by
  unfold finiteTests corrected componentCost
  by_cases hi : i ∈ activeBlocks width
  · rw [if_pos hi, if_pos hi, if_pos hi]
    exact diagonal_pin hw0 hw1 K width hK n i (qs i) (degrees i)
  · rw [if_neg hi, if_neg hi, if_neg hi]
    have hp : erasedPair w K width n i (qs i) (qs i) ≈ marginalPair w K width n (qs i) (qs i) := by
      unfold erasedPair
      rw [conditionalMessage_inactive w K width n i hi]
      exact Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ hp (poly_identity_of_normal_eq (.var 1)
      (.add (.mul (.var 0) (.var 1)) (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)))
      (by decide) (fun | 0 => headFloor w | _ => marginalPair w K width n (qs i) (qs i)))

set_option maxHeartbeats 800000 in
private theorem component_cross_pin (qs : Nat → RatPoly) (degrees : Nat → Nat) (i j : Nat) :
    crossPair w K width n i j (finiteTests hw0 hw1 K width hK n qs degrees i)
      (finiteTests hw0 hw1 K width hK n qs degrees j) ≈
      marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees i)
        (corrected hw0 hw1 K width hK n qs degrees j) + componentDeterminant hw0 hw1 K width hK n qs degrees i j := by
  unfold finiteTests corrected componentDeterminant
  by_cases hi : i ∈ activeBlocks width <;> by_cases hj : j ∈ activeBlocks width
  · simp only [if_pos hi, if_pos hj]
    refine Q'.eqv_trans _ _ _ (dualTest_cross_pin hw0 hw1 K width hK n i j (qs i) (qs j) (degrees i) (degrees j)) ?_
    apply Q'.add_eqv_congr'
    · exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
        (.mul (.var 0) (.mul (.mul (.var 3) (.var 1)) (.mul (.var 4) (.var 2))))
        (by decide) (fun
          | 0 => marginalWeight w K width n | 1 => qs i | 2 => qs j
          | 3 => polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i (degrees i))
          | _ => polyMul (conditionalMessage w K width n j) (reciprocal hw0 hw1 K width hK n j (degrees j))))
    · exact Q'.eqv_refl _
  · simp only [if_pos hi, if_neg hj]
    exact Q'.eqv_trans _ _ _ (dualTest_fringe_cross_pin hw0 hw1 K width hK n i j hj (qs i) (qs j) (degrees i))
      (by rw [Q'.add_zero']; exact Q'.eqv_refl _)
  · simp only [if_neg hi, if_pos hj]
    exact Q'.eqv_trans _ _ _ (fringe_dualTest_cross_pin hw0 hw1 K width hK n i j hi (qs i) (qs j) (degrees j))
      (by rw [Q'.add_zero']; exact Q'.eqv_refl _)
  · simp only [if_neg hi, if_neg hj]
    exact Q'.eqv_trans _ _ _ (fringe_fringe_cross_pin w K width n i j hi hj (qs i) (qs j))
      (by rw [Q'.add_zero']; exact Q'.eqv_refl _)

private theorem norm_sum (qs : Nat → RatPoly) (degrees : Nat → Nat) :
    marginalPair w K width n (correctedSum hw0 hw1 K width hK n qs degrees)
      (correctedSum hw0 hw1 K width hK n qs degrees) ≈
      qListSum ((singleCuts (labels width)).map (fun c => marginalPair w K width n
        (corrected hw0 hw1 K width hK n qs degrees c.1) (corrected hw0 hw1 K width hK n qs degrees c.1))) +
      (qListSum ((pairCuts (labels width)).map (fun c => marginalPair w K width n
        (corrected hw0 hw1 K width hK n qs degrees c.1) (corrected hw0 hw1 K width hK n qs degrees c.2.1))) +
       qListSum ((pairCuts (labels width)).map (fun c => marginalPair w K width n
        (corrected hw0 hw1 K width hK n qs degrees c.1) (corrected hw0 hw1 K width hK n qs degrees c.2.1)))) := by
  let v := corrected hw0 hw1 K width hK n qs degrees
  let mu := marginalWeight w K width n
  have hd := haar_weighted_sum_indexed (N width) mu
    (fun c : Nat × List Nat => polyMul (v c.1) (v c.1)) (singleCuts (labels width))
  have hx := haar_weighted_sum_indexed (N width) mu
    (fun c : Nat × Nat × List Nat => polyMul (v c.1) (v c.2.1)) (pairCuts (labels width))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((sumSquare_expansion v (labels width)).mul_left mu))
    (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) mu _ _)
      (Q'.add_eqv_congr' hd (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) mu _ _)
        (Q'.add_eqv_congr' hx hx))))

/-- The finite family flow is the pairing with the SAME corrected sum in nu. -/
theorem flow_actual_pin (qs : Nat → RatPoly) (degrees : Nat → Nat) (f : RatPoly) :
    marginalFlow w K width n (finiteTests hw0 hw1 K width hK n qs degrees) f ≈
      marginalPair w K width n f (correctedSum hw0 hw1 K width hK n qs degrees) := by
  let v := corrected hw0 hw1 K width hK n qs degrees
  let mu := marginalWeight w K width n
  have hidx : ((singleCuts (labels width)).map (fun c => marginalPair w K width n f (v c.1))) =
      (labels width).map (fun i => marginalPair w K width n f (v i)) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun i => marginalPair w K width n f (v i))) (singleCuts_map_fst (labels width))
  have hsum := haar_weighted_sum_indexed (N width) (polyMul mu f) v (labels width)
  have hterms := qListSum_congr (labels width)
    (fun i => quaternionHaar (N width) (polyMul (polyMul mu f) (v i)))
    (fun i => marginalPair w K width n f (v i))
    (fun _ _ => haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
  have hright : marginalPair w K width n f (correctedSum hw0 hw1 K width hK n qs degrees) ≈
      qListSum ((labels width).map (fun i => marginalPair w K width n f (v i))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc mu f _).symm)
      (Q'.eqv_trans _ _ _ hsum hterms)
  have hleft := qListSum_congr (singleCuts (labels width))
    (fun c => erasedPair w K width n c.1 f (finiteTests hw0 hw1 K width hK n qs degrees c.1))
    (fun c => marginalPair w K width n f (v c.1))
    (fun c _ => one_pin hw0 hw1 K width hK n qs degrees c.1 f)
  rw [hidx] at hleft
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright)

set_option maxHeartbeats 800000 in
/-- Complete finite-degree cost split. No cross term or remainder has an
assumed sign. In particular, the positive diagonal COST is still on the RHS. -/
theorem cost_actual_split (qs : Nat → RatPoly) (degrees : Nat → Nat) :
    marginalCost w K width n (finiteTests hw0 hw1 K width hK n qs degrees) ≈
      headFloor w*marginalPair w K width n (correctedSum hw0 hw1 K width hK n qs degrees)
        (correctedSum hw0 hw1 K width hK n qs degrees) +
      diagonalRemainder hw0 hw1 K width hK n qs degrees +
      ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees := by
  let v := corrected hw0 hw1 K width hK n qs degrees
  let xs := singleCuts (labels width)
  let ps := pairCuts (labels width)
  let X := qListSum (xs.map (fun c => marginalPair w K width n (v c.1) (v c.1)))
  let Y := qListSum (ps.map (fun c => marginalPair w K width n (v c.1) (v c.2.1)))
  let D := diagonalRemainder hw0 hw1 K width hK n qs degrees
  let R := determinantRemainder hw0 hw1 K width hK n qs degrees
  have hd : marginalDiagonal w K width n (finiteTests hw0 hw1 K width hK n qs degrees) ≈ headFloor w*X+D :=
    Q'.eqv_trans _ _ _ (qListSum_congr xs _ _ (fun c _ => component_diagonal_pin hw0 hw1 K width hK n qs degrees c.1))
      (Q'.eqv_trans _ _ _ (qListSum_add xs _ _)
        (Q'.add_eqv_congr' (qListSum_scale xs _ (headFloor w)) (Q'.eqv_refl _)))
  have hx : marginalCross w K width n (finiteTests hw0 hw1 K width hK n qs degrees) ≈ Y+R :=
    Q'.eqv_trans _ _ _ (qListSum_congr ps _ _ (fun c _ => component_cross_pin hw0 hw1 K width hK n qs degrees c.1 c.2.1))
      (qListSum_add ps _ _)
  have hn := norm_sum hw0 hw1 K width hK n qs degrees
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hd (Q'.mul_eqv_congr_left _ _ _ hx))
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.mul (.const 2) (.var 0)) (.add (.var 2) (.var 4))))
      (.add (.add (.mul (.var 0) (.add (.var 1) (.add (.var 2) (.var 2)))) (.var 3))
        (.mul (.mul (.const 2) (.var 0)) (.var 4))) (by decide)
      (fun | 0 => headFloor w | 1 => X | 2 => Y | 3 => D | _ => R))
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hn)) (Q'.eqv_refl _))
        (Q'.eqv_refl _)))

private theorem qsum_nonnegative {A : Type} (ids : List A) (f : A → Q')
    (h : ∀ i, i ∈ ids → (0 : Q') ≤ f i) : (0 : Q') ≤ qListSum (ids.map f) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.le_of_eqv (Q'.eqv_refl _)
  | cons i ids ih =>
      intro h
      exact Q'.zero_le_add _ _ (h i List.mem_cons_self) (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem qsum_le {A : Type} (ids : List A) (f g : A → Q')
    (h : ∀ i, i ∈ ids → f i ≤ g i) : qListSum (ids.map f) ≤ qListSum (ids.map g) := by
  revert h
  induction ids with
  | nil => intro _; exact Q'.le_of_eqv (Q'.eqv_refl _)
  | cons i ids ih =>
      intro h
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (h i List.mem_cons_self))
        (Q'.add_le_add_left _ _ _ (ih (fun j hj => h j (List.mem_cons_of_mem i hj))))

/-- Explicit sum of component norms; NOT a uniform bound by the sum's norm. -/
def diagonalBudget (qs : Nat → RatPoly) (degrees : Nat → Nat) : Q' :=
  qListSum ((singleCuts (labels width)).map (fun c =>
    (if c.1 ∈ activeBlocks width then prefixCap w + -(headFloor w) else (1 : Q') + -(headFloor w)) *
      marginalPair w K width n (corrected hw0 hw1 K width hK n qs degrees c.1)
        (corrected hw0 hw1 K width hK n qs degrees c.1)))

/-- The diagonal cost is positive and bounded by its precise component-norm
budget. This supplies neither a stable decomposition nor determinant control. -/
theorem diagonalRemainder_bounds (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (hq : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (qs i)) :
    (0 : Q') ≤ diagonalRemainder hw0 hw1 K width hK n qs degrees ∧
      diagonalRemainder hw0 hw1 K width hK n qs degrees ≤ diagonalBudget hw0 hw1 K width hK n qs degrees := by
  constructor
  · apply qsum_nonnegative
    intro c hc
    have hs := hq c.1 (single_selected_lt hc)
    unfold componentCost
    by_cases hi : c.1 ∈ activeBlocks width
    · rw [if_pos hi]
      exact diagonalCost_nonnegative hw0 hw1 K width hK n c.1 hi hs (degrees c.1)
    · rw [if_neg hi]
      apply Q'.mul_nonneg
      · exact Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide))
      · exact ((marginalCertificate hw0 hw1 K width hK n).mul (Certificate.square (qs c.1) hs)).haar_nonnegative
  · apply qsum_le
    intro c hc
    unfold componentCost corrected
    by_cases hi : c.1 ∈ activeBlocks width
    · simp only [if_pos hi]
      exact diagonalCost_upper hw0 hw1 K width hK n c.1 hi (hq c.1 (single_selected_lt hc)) (degrees c.1)
    · simp only [if_neg hi]
      exact Q'.le_of_eqv (Q'.eqv_refl _)

set_option maxHeartbeats 800000 in
/-- Concrete actual residuals satisfy the shared-energy bound entirely on
the SAME marginal nu and corrected sum, at every supplied finite degree.
The remaining task is a controlled choice of seeds/degrees, not a missing
identification of this flow or its signed cost. -/
theorem actualResidual_corrected_energy (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (hs : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (seeds i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let qs := fun i => weightedResidual i (marginalWeight w K width n) (seeds i)
    let s := correctedSum hw0 hw1 K width hK n qs degrees
    headFloor w*(marginalPair w K width n f s * marginalPair w K width n f s) ≤
      energy w K width (terminalMessage w K width n) f *
        (headFloor w*marginalPair w K width n s s + diagonalRemainder hw0 hw1 K width hK n qs degrees +
          ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees) := by
  let qs := fun i => weightedResidual i (marginalWeight w K width n) (seeds i)
  have h := actualResidual_family_energy hw0 hw1 K width hK n seeds degrees hs hf
  have hl := flow_actual_pin hw0 hw1 K width hK n qs degrees f
  have hr := cost_actual_split hw0 hw1 K width hK n qs degrees
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl) (Q'.mul_eqv_congr_left _ _ _ hl))))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hr)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.finiteTests
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.corrected
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.correctedSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.componentCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.diagonalRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.componentDeterminant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.determinantRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.flow_actual_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.cost_actual_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.diagonalBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.diagonalRemainder_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost.actualResidual_corrected_energy
