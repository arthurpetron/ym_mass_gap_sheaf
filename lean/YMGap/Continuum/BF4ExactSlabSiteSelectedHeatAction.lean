/-
# Site-reflection dressing for a literal selected original heat action

Partition a supplied finite physical face-id list into lower, fixed and
upper parts using the actual adjacent-even plaquette classifier. Every
factor retains its original heat polynomial. An explicit permutation from
the reflected lower list to the upper list identifies the reflected lower
heat with the upper heat. No full-slab action is substituted for this list.

The selected reflected numerator is exactly the boundary-weighted square
of the heat-dressed one-sided insertion. The original fixed-face weight
has a constructed certificate whenever 0 < w < 1 and K >= headCutoff w;
no positivity of the insertion or lower heat is assumed. List order and
multiplicities are retained by the partition and permutation identities.

This is selected-list machinery with its reflection permutation supplied
explicitly, not a proved reflection instance for an arbitrary selected
chain. Instantiating that permutation and passing the same reflected form
to a limit remain separate consumers. No continuum or physical gap claim
is made.
-/

import YMGap.Continuum.BF4ExactSlabSiteHeatAction
import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

namespace YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteWeightedSquare
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headProduct_certificate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

local infix:50 " ≈ " => Q'.eqv

/-- Stable three-way partition of precisely the supplied face-id list. -/
def faceIdParts (radius : Nat) (ids : List Nat) : List Nat × List Nat × List Nat :=
  partitionBySide
    (fun id => adjacentEvenPlaquetteSide radius (slabPlaquetteAt (adjacentEvenExtent radius) id)) ids

def lowerFaceIds (radius : Nat) (ids : List Nat) : List Nat := (faceIdParts radius ids).1

def fixedFaceIds (radius : Nat) (ids : List Nat) : List Nat := (faceIdParts radius ids).2.1

def upperFaceIds (radius : Nat) (ids : List Nat) : List Nat := (faceIdParts radius ids).2.2

theorem mem_lowerFaceIds {radius id : Nat} {ids : List Nat} :
    id ∈ lowerFaceIds radius ids ↔ id ∈ ids ∧
      adjacentEvenPlaquetteSide radius (slabPlaquetteAt (adjacentEvenExtent radius) id) = .lower :=
  mem_partitionBySide_lower _ _ _

theorem mem_fixedFaceIds {radius id : Nat} {ids : List Nat} :
    id ∈ fixedFaceIds radius ids ↔ id ∈ ids ∧
      adjacentEvenPlaquetteSide radius (slabPlaquetteAt (adjacentEvenExtent radius) id) = .fixed :=
  mem_partitionBySide_fixed _ _ _

theorem mem_upperFaceIds {radius id : Nat} {ids : List Nat} :
    id ∈ upperFaceIds radius ids ↔ id ∈ ids ∧
      adjacentEvenPlaquetteSide radius (slabPlaquetteAt (adjacentEvenExtent radius) id) = .upper :=
  mem_partitionBySide_upper _ _ _

/-- Every occurrence in the supplied list is retained, including repetitions. -/
theorem faceIdParts_perm (radius : Nat) (ids : List Nat) :
    (lowerFaceIds radius ids ++ fixedFaceIds radius ids ++ upperFaceIds radius ids).Perm ids :=
  partitionBySide_perm _ _

def lowerHeat (w : Q') (K radius : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) (lowerFaceIds radius ids)

def fixedHeat (w : Q') (K radius : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) (fixedFaceIds radius ids)

def upperHeat (w : Q') (K radius : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) (upperFaceIds radius ids)

/-- The original heat product on the literal selected list, not the full slab. -/
def selectedHeat (w : Q') (K radius : Nat) (ids : List Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) ids

theorem lowerHeat_supported (w : Q') (K radius : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (blockCount radius) (lowerHeat w K radius ids) :=
  heatProduct_supported w K _ _

theorem fixedHeat_supported (w : Q') (K radius : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (blockCount radius) (fixedHeat w K radius ids) :=
  heatProduct_supported w K _ _

theorem upperHeat_supported (w : Q') (K radius : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (blockCount radius) (upperHeat w K radius ids) :=
  heatProduct_supported w K _ _

theorem selectedHeat_supported (w : Q') (K radius : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (blockCount radius) (selectedHeat w K radius ids) :=
  heatProduct_supported w K _ _

/-- Lower temporal faces retain their shared-slice links. Strict lower
locality is neither needed nor asserted. -/
theorem lowerHeat_oneSided (w : Q') (K radius : Nat) (ids : List Nat) :
    OneSided radius (lowerHeat w K radius ids) := by
  intro t ht b hb hn
  apply heatProduct_local w K (adjacentEvenExtent radius) (lowerFaceIds radius ids) t ht b hb
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  apply hn
  intro hu
  have h := adjacentEven_upper_link_incident_face_upper hu he
  rw [(mem_lowerFaceIds.mp hi).2] at h
  cases h

/-- A selected fixed face is an actual fixed face of the original slab;
all its participating links remain on the shared reflection slice. -/
theorem fixedHeat_local (w : Q') (K radius : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius)) :
    Local radius .fixed (fixedHeat w K radius ids) := by
  intro t ht b hb hn
  apply heatProduct_local w K (adjacentEvenExtent radius) (fixedFaceIds radius ids) t ht b hb
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  have hs := mem_fixedFaceIds.mp hi
  have hfixed : id ∈ adjacentEvenFixedFaceIds radius :=
    mem_adjacentEvenFixedFaceIds.mpr ⟨hids id hs.1, hs.2⟩
  exact hn (mem_adjacentEvenFixedSlabLinks.mp
    (adjacentEvenFixedFaceLink_mem_fixedSlabLinks hfixed he)).2

private theorem reflected_product (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    ReflectionImage extent (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polynomialProduct (fun id => faceHeatPolynomial w K extent (slabFaceReflectId extent id)) ids)
  | [], _ => ReflectionImage.one extent
  | id::ids, hi => (faceHeat_reflection w K (hi id List.mem_cons_self)).mul
      (reflected_product w K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

/-- Reflection uses the explicitly supplied permutation of THESE selected
lists. It is not inferred from symmetry of the ambient full slab. -/
theorem lowerHeat_reflection (w : Q') (K radius : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hreflection : ((lowerFaceIds radius ids).map (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (upperFaceIds radius ids)) :
    ReflectionImage (adjacentEvenExtent radius) (lowerHeat w K radius ids) (upperHeat w K radius ids) := by
  have h := reflected_product w K (adjacentEvenExtent radius) (lowerFaceIds radius ids)
    (fun id hi => hids id (mem_lowerFaceIds.mp hi).1)
  have hp := polynomialProduct_perm (faceHeatPolynomial w K (adjacentEvenExtent radius)) hreflection
  simp only [polynomialProduct, List.foldr_map] at hp
  exact h.trans (PaddedPolynomialCoeffEqv.of_coeff hp)

/-- Exact split of the supplied action, before reflection or positivity. -/
theorem selectedHeat_split (w : Q') (K radius : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (selectedHeat w K radius ids)
      (polyMul (lowerHeat w K radius ids) (polyMul (fixedHeat w K radius ids) (upperHeat w K radius ids))) :=
  (polynomialProduct_perm _ (by
    have h := faceIdParts_perm radius ids
    rw [List.append_assoc] at h
    exact h.symm)).trans
      ((polynomialProduct_append _ (lowerFaceIds radius ids)
        (fixedFaceIds radius ids ++ upperFaceIds radius ids)).trans
        ((polynomialProduct_append _ (fixedFaceIds radius ids) (upperFaceIds radius ids)).mul_left _))

/-- Dressing equality for the SAME selected action, including its fixed
weight. No sign assumption on p or on the lower factor is used. -/
theorem selectedAction_dressing (w : Q') (K radius : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hreflection : ((lowerFaceIds radius ids).map (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (upperFaceIds radius ids)) (p : RatPoly) :
    PaddedPolynomialCoeffEqv (blockCount radius)
      (polyMul (polyMul
        (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (polyMul p (lowerHeat w K radius ids)))
        (polyMul p (lowerHeat w K radius ids))) (fixedHeat w K radius ids))
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (selectedHeat w K radius ids)) := by
  have hR := (show ReflectionImage (adjacentEvenExtent radius) p
    (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) from .refl _ _).mul
      (lowerHeat_reflection w K radius ids hids hreflection)
  refine (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.mul hR (.refl _ _)) (.refl _ _)).trans ?_
  apply PaddedPolynomialCoeffEqv.of_coeff
  exact (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (by decide)
    (fun
      | 0 => reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p
      | 1 => p
      | 2 => lowerHeat w K radius ids
      | 3 => fixedHeat w K radius ids
      | _ => upperHeat w K radius ids)).trans
    ((selectedHeat_split w K radius ids).symm.mul_left _)

/-- The exact original reflected numerator is a square under the retained
fixed-slice weight. This identity is valid for arbitrary rational nome. -/
theorem selectedAction_square (w : Q') (K radius : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hreflection : ((lowerFaceIds radius ids).map (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (upperFaceIds radius ids)) (p : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (selectedHeat w K radius ids)) ≈
    quaternionHaar (blockCount radius)
      (polyMul (polyMul
        (conditionalPolynomial radius (polyMul p (lowerHeat w K radius ids))
          (hp.mul (lowerHeat_oneSided w K radius ids)))
        (conditionalPolynomial radius (polyMul p (lowerHeat w K radius ids))
          (hp.mul (lowerHeat_oneSided w K radius ids)))) (fixedHeat w K radius ids)) := by
  have hP := supported_polyMul hs (lowerHeat_supported w K radius ids)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm ((selectedAction_dressing w K radius ids hids hreflection p).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hP)
        (fixedHeat_supported w K radius ids))
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs)
        (selectedHeat_supported w K radius ids))))
    (conditional_weighted_square radius _ _ (hp.mul (lowerHeat_oneSided w K radius ids)) hP
      (fixedHeat_supported w K radius ids) (fixedHeat_local w K radius ids hids))

/-- Constructed certificate for precisely the original selected fixed
factors at the existing nome-dependent retained cutoff. -/
def fixedHeatCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius)) :
    Certificate (blockCount radius) (fixedHeat w K radius ids) :=
  headProduct_certificate hw0 hw1 K (adjacentEvenExtent radius) hK (fixedFaceIds radius ids)
    (fun id hi => hids id (mem_fixedFaceIds.mp hi).1)

/-- Actual selected-action site-reflection positivity. Physical membership
and the displayed selected-list reflection permutation remain explicit. -/
theorem selectedAction_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hreflection : ((lowerFaceIds radius ids).map (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (upperFaceIds radius ids)) (p : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (selectedHeat w K radius ids)) := by
  have hP := supported_polyMul hs (lowerHeat_supported w K radius ids)
  have hnonneg := certified_weighted_nonnegative radius (polyMul p (lowerHeat w K radius ids))
    (fixedHeat w K radius ids) (hp.mul (lowerHeat_oneSided w K radius ids)) hP
    (fixedHeat_supported w K radius ids) (fixedHeat_local w K radius ids hids)
    (fixedHeatCertificate hw0 hw1 K radius hK ids hids)
  exact Q'.le_trans' _ _ _ hnonneg
    (Q'.le_of_eqv ((selectedAction_dressing w K radius ids hids hreflection p).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hP)
        (fixedHeat_supported w K radius ids))
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs)
        (selectedHeat_supported w K radius ids))))

end YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction

#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.faceIdParts
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.lowerFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.fixedFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.upperFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.mem_lowerFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.mem_fixedFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.mem_upperFaceIds
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.faceIdParts_perm
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.lowerHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.fixedHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.upperHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.selectedHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.lowerHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.fixedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.upperHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.selectedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.lowerHeat_oneSided
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.fixedHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.lowerHeat_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.selectedHeat_split
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.selectedAction_dressing
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.selectedAction_square
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.fixedHeatCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction.selectedAction_nonnegative
