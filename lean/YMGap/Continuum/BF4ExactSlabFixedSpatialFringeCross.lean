/-
# Exact cross pairings with genuinely inactive retained coordinates

Deleting an inactive coordinate deletes no original heat factor. Its erased
message is the full next terminal message; deleting it together with an
active coordinate leaves the latter's one-erased message. Consequently the
two-message determinant is coefficient-zero whenever either label is inactive.

An active corrected dual test paired with an unchanged fringe test therefore
has only its ordinary corrected pairing in the original marginal. The cross
pairing itself is signed and need not vanish. These finite identities assume
no centering, smallness or new inverse. The displayed reciprocal is the already
constructed finite polynomial, not a rational-function observable.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure
import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage (conditionalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair dualTest)
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse (reciprocal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual (terminal_product)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual
  (twiceErasedMessage crossPair messageDeterminant)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks activeBlocks spatialWeight

private theorem erase_absent (i : Nat) : ∀ ids : List Nat, i ∉ ids → eraseIndex i ids = ids
  | [], _ => rfl
  | j::ids, h => by
      have hji : j ≠ i := fun he => h (List.mem_cons.mpr (Or.inl he.symm))
      have ht : i ∉ ids := fun hi => h (List.mem_cons_of_mem j hi)
      rw [eraseIndex, if_neg hji, erase_absent i ids ht]

/-- Exact polynomial identity: no marginal normalization or positivity is used. -/
theorem conditionalMessage_inactive (w : Q') (K width n i : Nat)
    (hi : i ∉ activeBlocks width) :
    conditionalMessage w K width n i = terminalMessage w K width (n+1) := by
  unfold conditionalMessage
  rw [erase_absent i (activeBlocks width) hi]
  exact (terminal_product w K width n).symm

theorem twiceErasedMessage_inactive_right (w : Q') (K width n i j : Nat)
    (hj : j ∉ activeBlocks width) :
    twiceErasedMessage w K width n i j = conditionalMessage w K width n i := by
  unfold twiceErasedMessage
  rw [erase_absent j (eraseIndex i (activeBlocks width)) (fun h => hj (mem_of_mem_erase i h))]
  rfl

theorem twiceErasedMessage_inactive_left (w : Q') (K width n i j : Nat)
    (hi : i ∉ activeBlocks width) :
    twiceErasedMessage w K width n i j = conditionalMessage w K width n j := by
  unfold twiceErasedMessage
  rw [erase_absent i (activeBlocks width) hi]
  rfl

theorem determinant_zero_of_inactive_left (w : Q') (K width n i j : Nat)
    (hi : i ∉ activeBlocks width) :
    RatPolyCoeffEqv (messageDeterminant w K width n i j) polyZero := by
  unfold messageDeterminant
  rw [twiceErasedMessage_inactive_left w K width n i j hi,
    conditionalMessage_inactive w K width n i hi]
  exact (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
    (fun _ => polyMul (terminalMessage w K width (n+1)) (conditionalMessage w K width n j))).trans
    (RatPolyCoeffEqv.zero_smul polyOne)

theorem determinant_zero_of_inactive_right (w : Q') (K width n i j : Nat)
    (hj : j ∉ activeBlocks width) :
    RatPolyCoeffEqv (messageDeterminant w K width n i j) polyZero := by
  unfold messageDeterminant
  rw [twiceErasedMessage_inactive_right w K width n i j hj,
    conditionalMessage_inactive w K width n j hj]
  exact (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 0))))
    (.const 0) (by decide)
    (fun | 0 => terminalMessage w K width (n+1) | _ => conditionalMessage w K width n i)).trans
    (RatPolyCoeffEqv.zero_smul polyOne)

/-- This kills only the determinant correction, not the signed cross pairing. -/
theorem determinant_zero_if_either_inactive (w : Q') (K width n i j : Nat)
    (h : i ∉ activeBlocks width ∨ j ∉ activeBlocks width) :
    RatPolyCoeffEqv (messageDeterminant w K width n i j) polyZero := by
  rcases h with hi | hj
  · exact determinant_zero_of_inactive_left w K width n i j hi
  · exact determinant_zero_of_inactive_right w K width n i j hj

/-- One corrected active test and one unchanged fringe test. The identity
also holds if the first label is inactive; no first-label membership is needed. -/
theorem dualTest_fringe_cross_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i j : Nat) (hj : j ∉ activeBlocks width) (q s : RatPoly) (k : Nat) :
    crossPair w K width n i j (dualTest hw0 hw1 K width hK n i q k) s ≈
      marginalPair w K width n
        (polyMul (polyMul (conditionalMessage w K width n i)
          (reciprocal hw0 hw1 K width hK n i k)) q) s := by
  unfold crossPair
  rw [twiceErasedMessage_inactive_right w K width n i j hj]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 2))
      (.mul (.mul (.mul (.var 1) (.var 4)) (.var 3)) (.var 5)))
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.mul (.mul (.var 2) (.var 3)) (.var 4)) (.var 5)))
    (by decide) (fun
      | 0 => polyMul (spatialWeight w K width) (terminalMessage w K width n)
      | 1 => terminalMessage w K width (n+1)
      | 2 => conditionalMessage w K width n i
      | 3 => reciprocal hw0 hw1 K width hK n i k
      | 4 => q | _ => s))

/-- The other orientation retains the unchanged fringe test on the left. -/
theorem fringe_dualTest_cross_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i j : Nat) (hi : i ∉ activeBlocks width) (r q : RatPoly) (k : Nat) :
    crossPair w K width n i j r (dualTest hw0 hw1 K width hK n j q k) ≈
      marginalPair w K width n r
        (polyMul (polyMul (conditionalMessage w K width n j)
          (reciprocal hw0 hw1 K width hK n j k)) q) := by
  unfold crossPair
  rw [twiceErasedMessage_inactive_left w K width n i j hi]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 2))
      (.mul (.var 5) (.mul (.mul (.var 1) (.var 4)) (.var 3))))
    (.mul (.mul (.var 0) (.var 1))
      (.mul (.var 5) (.mul (.mul (.var 2) (.var 3)) (.var 4))))
    (by decide) (fun
      | 0 => polyMul (spatialWeight w K width) (terminalMessage w K width n)
      | 1 => terminalMessage w K width (n+1)
      | 2 => conditionalMessage w K width n j
      | 3 => reciprocal hw0 hw1 K width hK n j k
      | 4 => q | _ => r))

/-- Two inactive labels retain exactly the ordinary original-marginal pairing. -/
theorem fringe_fringe_cross_pin (w : Q') (K width n i j : Nat)
    (hi : i ∉ activeBlocks width) (hj : j ∉ activeBlocks width) (r s : RatPoly) :
    crossPair w K width n i j r s ≈ marginalPair w K width n r s := by
  unfold crossPair
  rw [twiceErasedMessage_inactive_left w K width n i j hi,
    conditionalMessage_inactive w K width n j hj]
  exact Q'.eqv_refl _

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.conditionalMessage_inactive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.twiceErasedMessage_inactive_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.twiceErasedMessage_inactive_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.determinant_zero_of_inactive_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.determinant_zero_of_inactive_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.determinant_zero_if_either_inactive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.dualTest_fringe_cross_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.fringe_dualTest_cross_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeCross.fringe_fringe_cross_pin
