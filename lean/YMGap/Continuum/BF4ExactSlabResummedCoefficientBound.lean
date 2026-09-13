/-
# Partition-relative bounds AFTER exact original spectator resummation

An anchored family is first summed to C_anchor * Z_spectator^2. Only then
is its magnitude bounded. The computed detached region and original
relative partition comparison give
  removalFloor(collar)^2 * |family| <= anchorCap * Z_ambient^2.
The removed-face count, not the spectator volume, supplies the loss.

This is a denominator-cleared anchored-family estimate. A global ordered
family decomposition/count, collar-size control and distance summability
remain open. The boundary specialization uses the original INTERIOR
partition square, not the full boundary comparison's mixed denominator.
-/

import YMGap.Continuum.BF4ExactSlabRelativePartitionBound
import YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
import YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
import YMGap.Continuum.BF4ExactSlabBoundaryConnectingSelections

namespace YMGap.Continuum.BF4ExactSlabResummedCoefficientBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarBiadditive
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabRemainderExpansion
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def anchorCap (w c d : Q') (count : Nat) : Q' := (c*d+c*d)*(pairedHeatRate w)^count

theorem anchorCap_nonnegative {w c d : Q'} (hw : (0 : Q') ≤ w) (hc : (0 : Q') ≤ c)
    (hd : (0 : Q') ≤ d) (count : Nat) : (0 : Q') ≤ anchorCap w c d count :=
  Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hc hd) (Q'.mul_nonneg _ _ hc hd))
    (Q'.pow_nonneg _ (pairedHeatRate_nonnegative hw) count)

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
include hw0 hw1 hsmall

theorem resummed_bound (K extent : Nat) (p q : RatPoly) (c d : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Q : Interval (boundaryCompleteSlabLinks extent).length q d)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q) (core spectators : List Nat)
    (hc : ∀ id, id ∈ core → id ∈ slabPhysicalFaceEdges extent)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    Q'.abs (spectatorSum w K extent p q core spectators) ≤ anchorCap w c d core.length * partitionSquare w K extent spectators := by
  have hsq : Q'.abs (partitionSquare w K extent spectators) ≤ partitionSquare w K extent spectators := by
    unfold partitionSquare
    rw [ExpNeg.abs_of_nonneg (SumOfSquares.q_mul_self_nonneg _)]
    exact Q'.le_refl' _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (spectatorSum_pin w K extent p q links P.support Q.support hlp hlq core spectators hd)))
    (abs_product_bound (connectedCoefficient_bound hw0 hw1 hsmall K extent p q c d P Q core hc) hsq)

theorem detached_cleared_bound (hdelta : heatRemainderBound w ≤ 1) (K extent : Nat)
    (p q : RatPoly) (c d : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Q : Interval (boundaryCompleteSlabLinks extent).length q d)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q) (core ambient : List Nat)
    (hc : ∀ id, id ∈ core → id ∈ slabPhysicalFaceEdges extent)
    (ha : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    let F := removalFloor w (collarIds extent links core ambient).length
    (F*F)*Q'.abs (spectatorSum w K extent p q core (detachedIds extent links core ambient)) ≤
      anchorCap w c d core.length * partitionSquare w K extent ambient := by
  let F := removalFloor w (collarIds extent links core ambient).length
  let M := anchorCap w c d core.length
  let Z := partitionSquare w K extent (detachedIds extent links core ambient)
  have hres := resummed_bound hw0 hw1 hsmall K extent p q c d links P Q hlp hlq core _ hc (detached_disjoint extent links core ambient)
  have hpart := relative_square_floor_perm hw0 hw1 hsmall hdelta K extent
    (collarIds extent links core ambient) (detachedIds extent links core ambient) ambient
    (fun id hi => ha id (collar_mem hi)) (fun id hi => ha id (detached_mem hi)) (region_partition extent links core ambient)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (F*F) hres (SumOfSquares.q_mul_self_nonneg F))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 2))) (by decide)
      (fun i => if i = 0 then F else if i = 1 then M else Z)))
      (Q'.mul_le_mul_of_nonneg_left _ _ M hpart (anchorCap_nonnegative hw0 P.nonnegative Q.nonnegative _)))

end SmallNome

/-- Anchored family on the SAME probe and selected exterior remainder used by
the existing boundary expansion. Global family reorganization is not asserted. -/
def boundarySpectatorFamily (w : Q') (K half padding : Nat) (p : RatPoly) (links : List Z4Link)
    (exterior core : List Nat) : Q' :=
  let extent := centralExtent (half+padding)
  spectatorSum w K extent p (remainderProduct w K extent exterior) core
    (detachedIds extent (links++faceLinks extent exterior) core (interiorIds half padding))

theorem boundarySpectatorFamily_cleared_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half)
    (hdelta : heatRemainderBound w ≤ 1) (K half padding : Nat) (p : RatPoly) (c : Q') (links : List Z4Link)
    (P : Interval (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p c)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (exterior core : List Nat)
    (he : exterior ∈ selections (exteriorIds half padding)) (hc : core ∈ selections (interiorIds half padding)) :
    let extent := centralExtent (half+padding)
    let F := removalFloor w (collarIds extent (links++faceLinks extent exterior) core (interiorIds half padding)).length
    (F*F)*Q'.abs (boundarySpectatorFamily w K half padding p links exterior core) ≤
      anchorCap w c ((heatRemainderBound w)^exterior.length) core.length * partitionSquare w K extent (interiorIds half padding) :=
  detached_cleared_bound hw0 hw1 hsmall hdelta K (centralExtent (half+padding)) p
    (remainderProduct w K (centralExtent (half+padding)) exterior) c ((heatRemainderBound w)^exterior.length)
    (links++faceLinks (centralExtent (half+padding)) exterior) P
    (productInterval hw0 hw1 hsmall K _ exterior (fun id hi => (List.mem_filter.mp (selected_mem he id hi)).1))
    (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
    ((remainderProduct_local w K _ exterior).mono (fun _ h => List.mem_append.mpr (Or.inr h))) core (interiorIds half padding)
    (fun id hi => (List.mem_filter.mp (selected_mem hc id hi)).1) (fun _ hi => (List.mem_filter.mp hi).1)

end YMGap.Continuum.BF4ExactSlabResummedCoefficientBound

#print axioms YMGap.Continuum.BF4ExactSlabResummedCoefficientBound.anchorCap
#print axioms YMGap.Continuum.BF4ExactSlabResummedCoefficientBound.anchorCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabResummedCoefficientBound.resummed_bound
#print axioms YMGap.Continuum.BF4ExactSlabResummedCoefficientBound.detached_cleared_bound
#print axioms YMGap.Continuum.BF4ExactSlabResummedCoefficientBound.boundarySpectatorFamily
#print axioms YMGap.Continuum.BF4ExactSlabResummedCoefficientBound.boundarySpectatorFamily_cleared_bound
