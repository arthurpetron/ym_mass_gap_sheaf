/-
# Coordinate reference projections on the SAME original completion

The reference is constructed by the proved two-link comparison maps and
the actual weighted Haar-coordinate projection. It is orthogonal in the
detached background form, NOT asserted orthogonal in the original form.
Both completed range identities with the original conditional projection
are proved using explicit Cauchy representatives, not assumed as inputs.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
import YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
import YMGap.Continuum.BF4ExactSlabHaarCoordinateLocality
import YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
import YMGap.Continuum.GNSDenseFixedPoint

namespace YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabSmallNomeCollarComparison
open YMGap.Continuum.BF4ExactSlabTwoLinkCompletionComparison
open YMGap.Continuum.BF4ExactSlabHaarCoordinateLocality
open YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

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
local notation "I" => toFull hw0 hw1 hsmall hd K extent hK left right

variable (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
  (hp : link ∈ [left,right])

local notation "idx" => List.idxOf link (boundaryCompleteSlabLinks extent)
local notation "hind" => background_independent_on_support w K extent [left,right] hl hp
local notation "Q0" => projection blocks W H idx (List.idxOf_lt_length_of_mem hl) hind
local notation "P" => conditionalProjection hw0 hw1 K extent hK link hl

/-- Its literal terms are the raw coordinate projection of the input terms. -/
def referenceCauchy (X : CauchyGNS F) : CauchyGNS F :=
  toFullCauchy hw0 hw1 hsmall hd K extent hK left right
    ((projectionMap blocks W H idx (List.idxOf_lt_length_of_mem hl) hind).mapCauchy
      (toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right X))

/-- An actual map on the original carrier, constructed through the common
detached background with no assumed norm comparison or range certificate. -/
def reference (x : GNSCompletionSpace F) : GNSCompletionSpace F := I (Q0 (J x))

local notation "Q" => reference hw0 hw1 hsmall hd K extent hK left right link hl hp

theorem reference_mk (X : CauchyGNS F) :
    Q (Quotient.mk (cauchySetoid F) X) = Quotient.mk (cauchySetoid F)
      (referenceCauchy hw0 hw1 hsmall hd K extent hK left right link hl hp X) := rfl

theorem reference_embed (p : (F).V) :
    Q (embedV F p) = embedV F ⟨project idx p.val, project_supported idx p.property⟩ := by
  unfold reference
  rw [toBackground_embed]
  exact (congrArg I (projection_embed blocks W H idx
    (List.idxOf_lt_length_of_mem hl) hind p)).trans
    (toFull_embed hw0 hw1 hsmall hd K extent hK left right _)

/-- The background image of the original reference is exactly its coordinate
projection, not a new operator with a merely matching bound. -/
theorem background_reference (x : GNSCompletionSpace F) : J (Q x) = Q0 (J x) :=
  toBackground_toFull hw0 hw1 hsmall hd K extent hK left right _

theorem reference_idempotent (x : GNSCompletionSpace F) : Q (Q x) = Q x := by
  change I (Q0 (J (Q x))) = I (Q0 (J x))
  rw [background_reference, projection_idempotent]

theorem reference_sub (x y : GNSCompletionSpace F) :
    Q ((F).cSub x y) = (F).cSub (Q x) (Q y) := by
  unfold reference
  rw [toBackground_sub]
  exact (congrArg I (projection_sub blocks W H idx
    (List.idxOf_lt_length_of_mem hl) hind (J x) (J y))).trans
    (toFull_sub hw0 hw1 hsmall hd K extent hK left right _ _)

/-- Orthogonality is in the retained original BACKGROUND, not in F. -/
theorem reference_background_adjoint (x y : GNSCompletionSpace F) :
    (B0).cinnerCompl (J (Q x)) (J y) = (B0).cinnerCompl (J x) (J (Q y)) := by
  rw [background_reference, background_reference]
  exact projection_selfAdjoint blocks W H idx (List.idxOf_lt_length_of_mem hl) hind _ _

theorem reference_background_norm (x : GNSCompletionSpace F) :
    CReal.RCle ((B0).cinnerCompl (J (Q x)) (J (Q x))) ((B0).cinnerCompl (J x) (J x)) := by
  rw [background_reference]
  exact projection_norm blocks W H idx (List.idxOf_lt_length_of_mem hl) hind _

/-- The original conditional projection fixes the entire reference range. -/
theorem conditional_reference (x : GNSCompletionSpace F) : P (Q x) = Q x := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [reference_mk]
  apply GNSDenseFixedPoint.fixed_of_cauchy_terms P
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK link hl)
  intro n
  change P (embedV F ⟨project idx (X.seq n).val, project_supported idx (X.seq n).property⟩) = _
  exact conditional_fixes_raw_project hw0 hw1 K extent hK link hl (X.seq n)

/-- Conversely, each actual conditional output has a literal exterior-probe
representative fixed by the background coordinate projection. -/
theorem reference_conditional (x : GNSCompletionSpace F) : Q (P x) = P x := by
  refine Quotient.inductionOn x ?_
  intro X
  let T := conditionalDenseMap hw0 hw1 K extent hK link hl
  let Y := T.mapRep X
  let Z := toBackgroundCauchy hw0 hw1 hsmall hd K extent hK left right Y
  have hy (n : Nat) : QuaternionBlockIndependent idx (Y.seq n).val := by
    let m := (T.mapOuter X).phi n
    let j := (T.mapOuter X).reindex.Jidx n
    change QuaternionBlockIndependent idx ((T.toRep (X.seq m)).seq j).val
    exact probeMap_independent_selected hw0 hw1 K extent hK link hl _
  have hfix : Q0 (Quotient.mk (cauchySetoid B0) Z) = Quotient.mk (cauchySetoid B0) Z :=
    projection_fixed_cauchy blocks W H idx (List.idxOf_lt_length_of_mem hl) hind Z hy
  change I (Q0 (Quotient.mk (cauchySetoid B0) Z)) = Quotient.mk (cauchySetoid F) Y
  rw [hfix]
  exact toFull_toBackground hw0 hw1 hsmall hd K extent hK left right
    (Quotient.mk (cauchySetoid F) Y)

/-- Both chosen coordinate references commute on the original carrier. -/
theorem reference_commute (other : Z4Link)
    (ho : other ∈ boundaryCompleteSlabLinks extent) (hop : other ∈ [left,right])
    (x : GNSCompletionSpace F) :
    Q (reference hw0 hw1 hsmall hd K extent hK left right other ho hop x) =
      reference hw0 hw1 hsmall hd K extent hK left right other ho hop (Q x) := by
  unfold reference
  rw [toBackground_toFull, toBackground_toFull]
  apply congrArg I
  exact projection_comm blocks W H idx ((boundaryCompleteSlabLinks extent).idxOf other)
    (List.idxOf_lt_length_of_mem hl) (List.idxOf_lt_length_of_mem ho) hind
    (background_independent_on_support w K extent [left,right] ho hop) _

#print axioms referenceCauchy
#print axioms reference
#print axioms reference_mk
#print axioms reference_embed
#print axioms background_reference
#print axioms reference_idempotent
#print axioms reference_sub
#print axioms reference_background_adjoint
#print axioms reference_background_norm
#print axioms conditional_reference
#print axioms reference_conditional
#print axioms reference_commute

end YMGap.Continuum.BF4ExactSlabTwoLinkReferenceProjection
