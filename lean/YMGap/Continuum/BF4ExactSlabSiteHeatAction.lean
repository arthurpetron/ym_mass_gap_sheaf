/-
# Site reflection positivity for the FULL original finite heat action

The actual even-slab face list is partitioned into lower, fixed and upper
faces. Their original heat polynomials give L, W and U, with U = theta(L).
L is one-sided, not strictly lower-local: its temporal plaquettes retain the
shared spatial links. W is boundary-local. Thus for every original supported
one-sided p the full action form is exactly

    H((theta(p) * p) * fullHeat) = H(C(p*L)^2 * W).

Existing small-nome certificates for every ORIGINAL fixed face prove this
nonnegative at every finite cutoff and even extent. The nome guards are
explicit; no positivity of an auxiliary multiplicity model is used.

This is a finite full-action result, not yet its identification with the
existing thermodynamic geometric one-step pairing. That same-object limit
pin, T1/root equality, range density, time zero, physical mass normalization
and the continuum/all-group Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabSiteWeightedSquare
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

namespace YMGap.Continuum.BF4ExactSlabSiteHeatAction

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
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteWeightedSquare
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

local infix:50 " ≈ " => Q'.eqv

def lowerHeat (w : Q') (K radius : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) (adjacentEvenLowerFaceIds radius)

def fixedHeat (w : Q') (K radius : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) (adjacentEvenFixedFaceIds radius)

def upperHeat (w : Q') (K radius : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius)) (adjacentEvenUpperFaceIds radius)

/-- Every physical face occurs once, with its original heat polynomial. -/
def fullHeat (w : Q') (K radius : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (adjacentEvenExtent radius))
    (slabPhysicalFaceEdges (adjacentEvenExtent radius))

theorem lowerHeat_supported (w : Q') (K radius : Nat) :
    SupportedQuaternionBlocks (blockCount radius) (lowerHeat w K radius) := heatProduct_supported w K _ _

theorem fixedHeat_supported (w : Q') (K radius : Nat) :
    SupportedQuaternionBlocks (blockCount radius) (fixedHeat w K radius) := heatProduct_supported w K _ _

theorem upperHeat_supported (w : Q') (K radius : Nat) :
    SupportedQuaternionBlocks (blockCount radius) (upperHeat w K radius) := heatProduct_supported w K _ _

theorem fullHeat_supported (w : Q') (K radius : Nat) :
    SupportedQuaternionBlocks (blockCount radius) (fullHeat w K radius) := heatProduct_supported w K _ _

/-- The shared links in lower temporal faces are retained, not integrated away. -/
theorem lowerHeat_oneSided (w : Q') (K radius : Nat) : OneSided radius (lowerHeat w K radius) := by
  intro t ht b hb hn
  apply heatProduct_local w K (adjacentEvenExtent radius) (adjacentEvenLowerFaceIds radius) t ht b hb
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  apply hn
  intro hu
  have h := adjacentEven_upper_link_incident_face_upper hu he
  rw [(mem_adjacentEvenLowerFaceIds.mp hi).2] at h
  cases h

theorem fixedHeat_local (w : Q') (K radius : Nat) : Local radius .fixed (fixedHeat w K radius) := by
  intro t ht b hb hn
  apply heatProduct_local w K (adjacentEvenExtent radius) (adjacentEvenFixedFaceIds radius) t ht b hb
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  exact hn (mem_adjacentEvenFixedSlabLinks.mp (adjacentEvenFixedFaceLink_mem_fixedSlabLinks hi he)).2

theorem reflected_lower_ids (radius : Nat) :
    ((adjacentEvenLowerFaceIds radius).map (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (adjacentEvenUpperFaceIds radius) := by
  have h := (adjacentEvenUpperFaceIds_reflection_perm radius).map (slabFaceReflectId (adjacentEvenExtent radius))
  have hi : ((adjacentEvenUpperFaceIds radius).map (slabFaceReflectId (adjacentEvenExtent radius))).map
      (slabFaceReflectId (adjacentEvenExtent radius)) = adjacentEvenUpperFaceIds radius := by
    rw [List.map_map]
    have hm : (adjacentEvenUpperFaceIds radius).map
        (fun id => slabFaceReflectId (adjacentEvenExtent radius) (slabFaceReflectId (adjacentEvenExtent radius) id)) =
        (adjacentEvenUpperFaceIds radius).map (fun id => id) := by
      apply List.map_congr_left
      intro id hid
      exact slabFaceReflectId_involutive (mem_adjacentEvenUpperFaceIds.mp hid).1
    exact hm.trans (List.map_id _)
  change (((adjacentEvenUpperFaceIds radius).map (slabFaceReflectId (adjacentEvenExtent radius))).map
    (slabFaceReflectId (adjacentEvenExtent radius))).Perm _ at h
  rw [hi] at h
  exact h.symm

private theorem reflected_product (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    ReflectionImage extent (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polynomialProduct (fun id => faceHeatPolynomial w K extent (slabFaceReflectId extent id)) ids)
  | [], _ => ReflectionImage.one extent
  | id :: ids, hi => (faceHeat_reflection w K (hi id List.mem_cons_self)).mul
      (reflected_product w K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

theorem lowerHeat_reflection (w : Q') (K radius : Nat) :
    ReflectionImage (adjacentEvenExtent radius) (lowerHeat w K radius) (upperHeat w K radius) := by
  have h := reflected_product w K (adjacentEvenExtent radius) (adjacentEvenLowerFaceIds radius)
    (fun _ hi => (mem_adjacentEvenLowerFaceIds.mp hi).1)
  have hp := polynomialProduct_perm (faceHeatPolynomial w K (adjacentEvenExtent radius)) (reflected_lower_ids radius)
  simp only [polynomialProduct, List.foldr_map] at hp
  exact h.trans (PaddedPolynomialCoeffEqv.of_coeff hp)

theorem fullHeat_split (w : Q') (K radius : Nat) :
    RatPolyCoeffEqv (fullHeat w K radius)
      (polyMul (lowerHeat w K radius) (polyMul (fixedHeat w K radius) (upperHeat w K radius))) :=
  (polynomialProduct_perm _ (by
    have h := adjacentEvenSlabFaceIdParts_perm radius
    rw [List.append_assoc] at h
    exact h.symm)).trans
      ((polynomialProduct_append _ (adjacentEvenLowerFaceIds radius)
        (adjacentEvenFixedFaceIds radius ++ adjacentEvenUpperFaceIds radius)).trans
        ((polynomialProduct_append _ (adjacentEvenFixedFaceIds radius) (adjacentEvenUpperFaceIds radius)).mul_left _))

/-- Exact carrier equality, before taking Haar or asserting positivity. -/
theorem fullAction_dressing (w : Q') (K radius : Nat) (p : RatPoly) :
    PaddedPolynomialCoeffEqv (blockCount radius)
      (polyMul (polyMul
        (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (polyMul p (lowerHeat w K radius)))
        (polyMul p (lowerHeat w K radius))) (fixedHeat w K radius))
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) (fullHeat w K radius)) := by
  have hR := (show ReflectionImage (adjacentEvenExtent radius) p
    (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) from .refl _ _).mul (lowerHeat_reflection w K radius)
  refine (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.mul hR (.refl _ _)) (.refl _ _)).trans ?_
  apply PaddedPolynomialCoeffEqv.of_coeff
  exact (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (by decide)
    (fun | 0 => reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p
         | 1 => p | 2 => lowerHeat w K radius | 3 => fixedHeat w K radius | _ => upperHeat w K radius)).trans
    ((fullHeat_split w K radius).symm.mul_left _)

/-- Full original action, arbitrary signed one-sided insertion, every finite cutoff. -/
theorem fullAction_square (w : Q') (K radius : Nat) (p : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) (fullHeat w K radius)) ≈
    quaternionHaar (blockCount radius)
      (polyMul (polyMul
        (conditionalPolynomial radius (polyMul p (lowerHeat w K radius)) (hp.mul (lowerHeat_oneSided w K radius)))
        (conditionalPolynomial radius (polyMul p (lowerHeat w K radius)) (hp.mul (lowerHeat_oneSided w K radius))))
        (fixedHeat w K radius)) := by
  have hP := supported_polyMul hs (lowerHeat_supported w K radius)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm ((fullAction_dressing w K radius p).haar
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hP) (fixedHeat_supported w K radius))
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs) (fullHeat_supported w K radius))))
    (conditional_weighted_square radius _ _ (hp.mul (lowerHeat_oneSided w K radius)) hP
      (fixedHeat_supported w K radius) (fixedHeat_local w K radius))

/-- A constructed certificate for all actual fixed faces; the coupling guards are explicit. -/
def fixedHeatCertificate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1) (K radius : Nat) :
    Certificate (blockCount radius) (fixedHeat w K radius) :=
  faceProductCertificate hw0 hw1 hsmall hdelta K _ _ (fun _ hi => (mem_adjacentEvenFixedFaceIds.mp hi).1)

/-- Finite site reflection positivity of the full original heat action. -/
theorem fullAction_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)
    (K radius : Nat) (p : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) (fullHeat w K radius)) :=
  Q'.le_trans' _ _ _
    ((fixedHeatCertificate hw0 hw1 hsmall hdelta K radius).square_insertion_nonnegative _
      (conditional_supported radius _ (hp.mul (lowerHeat_oneSided w K radius))))
    (Q'.ge_of_eqv (fullAction_square w K radius p hp hs))

theorem existingNome_fullAction_nonnegative (K radius : Nat) (p : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (fullHeat BF4ExactSlabPlaquetteSmallNomeCertificate.nome K radius)) :=
  fullAction_nonnegative (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos)
    (Q'.le_of_lt BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one)
    existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K radius p hp hs

end YMGap.Continuum.BF4ExactSlabSiteHeatAction

#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.lowerHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fixedHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.upperHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fullHeat
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.lowerHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fixedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.upperHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fullHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.lowerHeat_oneSided
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fixedHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.reflected_lower_ids
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.lowerHeat_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fullHeat_split
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fullAction_dressing
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fullAction_square
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fixedHeatCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.fullAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSiteHeatAction.existingNome_fullAction_nonnegative
