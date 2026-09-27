/-
# Positive reference term in the original two-link comparison

The reference residuals live on the original completed carrier, but the
square identity and contraction here are in the SAME detached-background
form. They do not assert positivity of the actual conditional cross term.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection
import YMGap.Continuum.GNSProjectionResidualPair

namespace YMGap.Continuum.BF4ExactSlabTwoLinkReferenceEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection
open YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- A physical coordinate in the chosen two-link list; no analytic input. -/
abbrev PairLink (extent : Nat) (left right : Z4Link) :=
  {i : Z4Link // i ∈ boundaryCompleteSlabLinks extent ∧ i ∈ [left,right]}

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (K extent : Nat) (hK : headCutoff w ≤ K) (left right : Z4Link)

local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "F" => fullData hw0 hw1 K extent hK
local notation "W" => background w K extent [left,right]
local notation "H" => small_background_certificate (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
  hsmall (Q'.le_of_lt hd) K extent [left,right]
local notation "B0" => twoLinkBackgroundData (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
  hsmall (Q'.le_of_lt hd) K extent left right
local notation "J" => toBackground hw0 hw1 hsmall hd K extent hK left right

/-- The constructed background-orthogonal family, using only coordinates
whose independence from the retained action was already proved. -/
def backgroundFamily : Family B0 (PairLink extent left right) where
  op i := projection blocks W H (List.idxOf i.val (boundaryCompleteSlabLinks extent))
    (List.idxOf_lt_length_of_mem i.property.1)
    (background_independent_on_support w K extent [left,right] i.property.1 i.property.2)
  adjoint i := projection_selfAdjoint blocks W H _ _ _
  idem i := projection_idempotent blocks W H _ _ _

local notation "B" => backgroundFamily hw0 hw1 hsmall hd K extent left right

/-- The actual reference remainder on the original completion. -/
def remainder (i : PairLink extent left right) (x : GNSCompletionSpace F) :
    GNSCompletionSpace F := (F).cSub x
      (reference hw0 hw1 hsmall hd K extent hK left right i.val i.property.1 i.property.2 x)

theorem remainder_image (i : PairLink extent left right) (x : GNSCompletionSpace F) :
    J (remainder hw0 hw1 hsmall hd K extent hK left right i x) = (B).residual i (J x) := by
  unfold remainder
  rw [toBackground_sub, background_reference]
  rfl

theorem background_commute (i j : PairLink extent left right) (x : GNSCompletionSpace B0) :
    (B).op i ((B).op j x) = (B).op j ((B).op i x) :=
  projection_comm blocks W H _ _ _ _ _ _ x

theorem remainder_background_norm (i : PairLink extent left right) (x : GNSCompletionSpace F) :
    CReal.RCle
      ((B0).cinnerCompl (J (remainder hw0 hw1 hsmall hd K extent hK left right i x))
        (J (remainder hw0 hw1 hsmall hd K extent hK left right i x)))
      ((B0).cinnerCompl (J x) (J x)) := by
  rw [remainder_image]
  exact (B).residual_norm i (J x)

/-- The common reference cross term is a genuine completed square. -/
theorem remainder_pair_square (i j : PairLink extent left right) (x : GNSCompletionSpace F) :
    (B0).cinnerCompl
      (J (remainder hw0 hw1 hsmall hd K extent hK left right i x))
      (J (remainder hw0 hw1 hsmall hd K extent hK left right j x)) =
    (B0).cinnerCompl
      (J (remainder hw0 hw1 hsmall hd K extent hK left right i
        (remainder hw0 hw1 hsmall hd K extent hK left right j x)))
      (J (remainder hw0 hw1 hsmall hd K extent hK left right i
        (remainder hw0 hw1 hsmall hd K extent hK left right j x))) := by
  simp only [remainder_image]
  exact (B).commuting_residual_pairing_eq_normSq i j
    (background_commute hw0 hw1 hsmall hd K extent left right i j) (J x)

theorem remainder_pair_nonnegative (i j : PairLink extent left right) (x : GNSCompletionSpace F) :
    CReal.RCle CReal.RCzero ((B0).cinnerCompl
      (J (remainder hw0 hw1 hsmall hd K extent hK left right i x))
      (J (remainder hw0 hw1 hsmall hd K extent hK left right j x))) := by
  rw [remainder_pair_square]
  exact (B0).cinner_self_nonneg _

#print axioms backgroundFamily
#print axioms remainder
#print axioms remainder_image
#print axioms background_commute
#print axioms remainder_background_norm
#print axioms remainder_pair_square
#print axioms remainder_pair_nonnegative

end YMGap.Continuum.BF4ExactSlabTwoLinkReferenceEnergy
