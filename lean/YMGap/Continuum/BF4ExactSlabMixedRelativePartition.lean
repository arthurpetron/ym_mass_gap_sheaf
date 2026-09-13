/-
# Matched ORIGINAL mixed-partition comparison after probe-rooted resummation

Removing faces costs (1-delta)^|removed| in the full action and
(1-delta)^|inside removed| in the interior action. Their product bounds the
ACTUAL mixed spectator factor relative to Z_full * Z_inside, not Z_inside^2.
The resulting denominator-cleared family estimate retains the absolute
value of the NEW mixed coefficient. No bound on that coefficient, collar
size, normalized summability, decay or continuum passage is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
import YMGap.Continuum.BF4ExactSlabRelativePartitionBound

namespace YMGap.Continuum.BF4ExactSlabMixedRelativePartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRootedResummation
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabRelativePartitionBound
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def mixedRemovalFloor (w : Q') (keep : Nat → Bool) (removed : List Nat) : Q' :=
  removalFloor w removed.length * removalFloor w (inside keep removed).length

theorem mixedRemovalFloor_nonnegative {w : Q'} (hd : heatRemainderBound w ≤ 1)
    (keep : Nat → Bool) (removed : List Nat) : (0 : Q') ≤ mixedRemovalFloor w keep removed :=
  Q'.mul_nonneg _ _ (removalFloor_nonnegative hd _) (removalFloor_nonnegative hd _)

theorem existingNome_mixedRemovalFloor_pos (keep : Nat → Bool) (removed : List Nat) :
    (0 : Q') < mixedRemovalFloor BF4ExactSlabPlaquetteSmallNomeCertificate.nome keep removed :=
  Q'.mul_pos (existingNome_removalFloor_pos _) (existingNome_removalFloor_pos _)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem mixedPartition_perm (w : Q') (K extent : Nat) (keep : Nat → Bool)
    {xs ys : List Nat} (h : xs.Perm ys) : mixedPartition w K extent keep xs ≈ mixedPartition w K extent keep ys :=
  qmul (partition_perm w K extent h) (partition_perm w K extent (h.filter keep))

/-- Same two partition factors as the original boundary determinant. -/
theorem boundary_mixedPartition (w : Q') (K half padding : Nat) :
    mixedPartition w K (centralExtent (half+padding)) (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding))) ≈
        fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K :=
  qmul (Q'.eqv_symm (unit_numerator w K (centralExtent (half+padding)) _))
    (Q'.eqv_symm (unit_numerator w K (centralExtent (half+padding)) _))

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)

include hw0 hw1 hsmall hdelta

theorem mixedPartition_nonnegative (K extent : Nat) (keep : Nat → Bool) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) : (0 : Q') ≤ mixedPartition w K extent keep ids :=
  Q'.mul_nonneg _ _ (faceProductCertificate hw0 hw1 hsmall hdelta K extent ids hi).haar_nonnegative
    (faceProductCertificate hw0 hw1 hsmall hdelta K extent (inside keep ids)
      (fun id hid => hi id (List.mem_filter.mp hid).1)).haar_nonnegative

theorem relative_mixed_floor (K extent : Nat) (keep : Nat → Bool) (removed background : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) :
    mixedRemovalFloor w keep removed * mixedPartition w K extent keep background ≤
      mixedPartition w K extent keep (removed++background) := by
  let f := removalFloor w removed.length
  let g := removalFloor w (inside keep removed).length
  let z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent background K
  let zi := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (inside keep background) K
  let Z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (removed++background) K
  let Zi := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (inside keep removed++inside keep background) K
  have hz : (0 : Q') ≤ z := (faceProductCertificate hw0 hw1 hsmall hdelta K extent background hb).haar_nonnegative
  have hzi : (0 : Q') ≤ zi := (faceProductCertificate hw0 hw1 hsmall hdelta K extent (inside keep background)
    (fun id hi => hb id (List.mem_filter.mp hi).1)).haar_nonnegative
  have hx : f*z ≤ Z := relative_floor hw0 hw1 hsmall hdelta K extent background hb removed hr
  have hy : g*zi ≤ Zi := relative_floor hw0 hw1 hsmall hdelta K extent (inside keep background)
    (fun id hi => hb id (List.mem_filter.mp hi).1) (inside keep removed) (fun id hi => hr id (List.mem_filter.mp hi).1)
  have hZ : (0 : Q') ≤ Z := Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (removalFloor_nonnegative hdelta _) hz) hx
  have hprod := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hx (Q'.mul_nonneg _ _ (removalFloor_nonnegative hdelta _) hzi))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hy hZ)
  have he : (f*g)*(z*zi) ≈ (f*z)*(g*zi) := poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
    (fun i => if i = 0 then f else if i = 1 then g else if i = 2 then z else zi)
  simpa only [mixedRemovalFloor, mixedPartition, inside, List.filter_append] using
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hprod

theorem relative_mixed_floor_perm (K extent : Nat) (keep : Nat → Bool) (removed background full : List Nat)
    (hr : ∀ id, id ∈ removed → id ∈ slabPhysicalFaceEdges extent)
    (hb : ∀ id, id ∈ background → id ∈ slabPhysicalFaceEdges extent) (hperm : (removed++background).Perm full) :
    mixedRemovalFloor w keep removed * mixedPartition w K extent keep background ≤ mixedPartition w K extent keep full :=
  Q'.le_trans' _ _ _ (relative_mixed_floor hw0 hw1 hsmall hdelta K extent keep removed background hr hb)
    (Q'.le_of_eqv (mixedPartition_perm w K extent keep hperm))

theorem detached_mixed_floor (K extent : Nat) (keep : Nat → Bool) (links : List Z4Link) (anchor ambient : List Nat)
    (ha : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    mixedRemovalFloor w keep (collarIds extent links anchor ambient) *
      mixedPartition w K extent keep (detachedIds extent links anchor ambient) ≤ mixedPartition w K extent keep ambient :=
  relative_mixed_floor_perm hw0 hw1 hsmall hdelta K extent keep _ _ ambient
    (fun id hi => ha id (collar_mem hi)) (fun id hi => ha id (detached_mem hi)) (region_partition extent links anchor ambient)

/-- The partition denominator is now matched; the NEW core coefficient is
retained explicitly and still needs its own small-factor estimate. -/
theorem mixedFamily_cleared_bound (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) (hl : LinkLocal extent links p)
    (ambient anchor : List Nat) (hn : ambient.Nodup) (ha : anchor ∈ selections ambient)
    (hf : core extent links anchor = anchor) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    mixedRemovalFloor w keep (collarIds extent links anchor ambient) * Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤
      Q'.abs (mixedCoefficient w K extent keep p anchor) * mixedPartition w K extent keep ambient := by
  let F := mixedRemovalFloor w keep (collarIds extent links anchor ambient)
  let C := Q'.abs (mixedCoefficient w K extent keep p anchor)
  let z := mixedPartition w K extent keep (detachedIds extent links anchor ambient)
  have hz : (0 : Q') ≤ z := mixedPartition_nonnegative hw0 hw1 hsmall hdelta K extent keep _
    (fun id hi => hphys id (detached_mem hi))
  have hcap : Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤ C*z :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (mixedFamily_resummed w K extent keep p links hp hl ambient anchor hn ha hf)))
      (by simpa only [ExpNeg.abs_of_nonneg hz] using ExpNeg.abs_mul_le (mixedCoefficient w K extent keep p anchor) z)
  have he : F*(C*z) ≈ C*(F*z) := poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun i => if i = 0 then F else if i = 1 then C else z)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ F hcap (mixedRemovalFloor_nonnegative hdelta _ _))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ C (detached_mixed_floor hw0 hw1 hsmall hdelta K extent keep links anchor ambient hphys)
        (Q'.abs_nonneg _)))

/-- Concrete retained boundary family: the RHS has the two ORIGINAL unit
moments appearing in the existing boundary determinant, at the same cutoff. -/
theorem boundary_mixedFamily_cleared_bound (K half padding : Nat) (p : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hl : LinkLocal (centralExtent (half+padding)) links p) (anchor : List Nat)
    (ha : anchor ∈ activeAnchors (centralExtent (half+padding)) links (boundaryKeep half padding)
      (slabPhysicalFaceEdges (centralExtent (half+padding)))) :
    let extent := centralExtent (half+padding)
    let keep := boundaryKeep half padding
    let ambient := slabPhysicalFaceEdges extent
    mixedRemovalFloor w keep (collarIds extent links anchor ambient) * Q'.abs (mixedFamily w K extent keep p links ambient anchor) ≤
      Q'.abs (mixedCoefficient w K extent keep p anchor) *
        (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K) :=
  Q'.le_trans' _ _ _ (mixedFamily_cleared_bound hw0 hw1 hsmall hdelta K (centralExtent (half+padding))
    (boundaryKeep half padding) p links hp hl _ anchor (YMGap.Continuum.CayleyParentInj.range_nodup _)
    (List.mem_filter.mp (List.mem_filter.mp ha).1).1
    (of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp ha).1).2) (fun _ h => h))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (boundary_mixedPartition w K half padding)))

end SmallNome

end YMGap.Continuum.BF4ExactSlabMixedRelativePartition

#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.mixedRemovalFloor
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.mixedRemovalFloor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.existingNome_mixedRemovalFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.mixedPartition_perm
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.boundary_mixedPartition
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.mixedPartition_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.relative_mixed_floor
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.relative_mixed_floor_perm
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.detached_mixed_floor
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.mixedFamily_cleared_bound
#print axioms YMGap.Continuum.BF4ExactSlabMixedRelativePartition.boundary_mixedFamily_cleared_bound
