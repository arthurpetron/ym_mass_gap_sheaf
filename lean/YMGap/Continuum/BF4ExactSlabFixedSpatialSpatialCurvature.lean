/-
# Frozen curvature of the complete ORIGINAL spatial weight

At a selected retained physical link only its at most six incident original
spatial faces contribute curvature. The complementary literal faces remain in
the polynomial product, but their selected-block jets vanish. This certificate
is at fixed strict nome and computed cutoff; its cost is not nome-uniform and
it asserts no terminal-marginal, variance, or continuum estimate.
-/

import YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Link Z4Plaq edgesOf)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
  (polynomialProduct polynomialProduct_append polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (heatFace_supported heatProduct_supported heatProduct_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalRelativeBound
  (spatialIncidentFaces spatialComplementFaces spatialFace_partition
    spatialIncidentFaces_length_le_six)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets (facePrefix)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature
  (plaquetteCurvatureCutoff plaquetteCurvatureCost
    plaquettePrefix_frozen_curvature_nearFlat_certificate)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyOne)
open YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem complement_omits (width : Nat) (selected : Z4Link) :
    ∀ face, face ∈ spatialComplementFaces width selected →
      selected ∉ edgesOf face := by
  intro face hf
  exact of_decide_eq_false (by
    simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hf).2)

private def incidentCurvature {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : plaquetteCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i)) :
    (faces : List Z4Plaq) →
    (∀ face, face ∈ faces → face ∈ spatialIncidentFaces width selected) →
    Certificate (N width)
      (frozenCurvatureAt ((baseLinks width).idxOf selected)
        (Q'.ofNat faces.length * plaquetteCurvatureCost w)
        (polynomialProduct (fun face => facePrefix w K width face) faces) u)
  | [], _ => by
      have hzero := frozen_independent_curvature_zero_certificate (blocks := N width)
        ((baseLinks width).idxOf selected) polyOne u
        (quaternionBlockIndependent_polyOne _)
      exact frozenCurvatureAt_raise_cost_certificate
        ((baseLinks width).idxOf selected) polyOne u hu (supported_one _)
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))) hzero
  | face :: faces, hfaces => by
      have hf : face ∈ spatialIncidentFaces width selected :=
        hfaces face List.mem_cons_self
      have hsp : face ∈ YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width :=
        (List.mem_filter.mp hf).1
      have hedge : selected ∈ edgesOf face :=
        of_decide_eq_true (List.mem_filter.mp hf).2
      have F : Certificate (N width)
          (frozenCurvatureAt ((baseLinks width).idxOf selected)
            (plaquetteCurvatureCost w) (facePrefix w K width face) u) := by
        exact plaquettePrefix_frozen_curvature_nearFlat_certificate
          hsp selected hedge hw0 hw1 K hK u hu
      have T := incidentCurvature hw0 hw1 K width hK selected hl u hu faces
        (fun other hm => hfaces other (List.mem_cons_of_mem face hm))
      have P := frozen_product_curvature_certificate
        ((baseLinks width).idxOf selected) (plaquetteCurvatureCost w)
        (Q'.ofNat faces.length * plaquetteCurvatureCost w)
        (facePrefix w K width face)
        (polynomialProduct (fun other => facePrefix w K width other) faces) u
        (heatFace_supported w K width face)
        (heatProduct_supported w K width faces) F T
      have hpoly := poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.add (.var 1) (.const 1)) (.var 0)) (by decide)
        (fun | 0 => plaquetteCurvatureCost w | _ => Q'.ofNat faces.length)
      have hnat : Q'.eqv (Q'.ofNat faces.length + 1)
          (Q'.ofNat (face :: faces).length) := by
        simpa only [List.length_cons, Nat.succ_eq_add_one] using
          Q'.eqv_symm (Q'.ofNat_add_eqv faces.length 1)
      have hcost : plaquetteCurvatureCost w +
          Q'.ofNat faces.length * plaquetteCurvatureCost w ≤
          Q'.ofNat (face :: faces).length * plaquetteCurvatureCost w :=
        Q'.le_of_eqv (Q'.eqv_trans _ _ _ hpoly
          (Q'.mul_eqv_congr_right _ _ _ hnat))
      exact frozenCurvatureAt_raise_cost_certificate
        ((baseLinks width).idxOf selected)
        (polynomialProduct (fun other => facePrefix w K width other) (face :: faces))
        u hu (heatProduct_supported w K width (face :: faces)) hcost P

/-- Frozen three-frame curvature of the complete, literal original spatial
product, at any selected retained physical link. The cost counts at most six
incident faces, independently of width and finite cutoff at fixed nome. -/
def spatialWeight_frozen_curvature_nearFlat_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : plaquetteCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i)) :
    Certificate (N width)
      (frozenCurvatureAt ((baseLinks width).idxOf selected)
        (6 * plaquetteCurvatureCost w) (spatialWeight w K width) u) := by
  let I := spatialIncidentFaces width selected
  let C := spatialComplementFaces width selected
  let s := (baseLinks width).idxOf selected
  let F := fun face => facePrefix w K width face
  have PI : Certificate (N width)
      (frozenCurvatureAt s (Q'.ofNat I.length * plaquetteCurvatureCost w)
        (polynomialProduct F I) u) :=
    incidentCurvature hw0 hw1 K width hK selected hl u hu I (fun _ hf => hf)
  have PC : Certificate (N width)
      (frozenCurvatureAt s 0 (polynomialProduct F C) u) :=
    frozen_independent_curvature_zero_certificate s (polynomialProduct F C) u
      (heatProduct_independent w K hl C (complement_omits width selected))
  have P := frozen_product_curvature_certificate s
    (Q'.ofNat I.length * plaquetteCurvatureCost w) 0
    (polynomialProduct F I) (polynomialProduct F C) u
    (heatProduct_supported w K width I)
    (heatProduct_supported w K width C) PI PC
  have hpoly : RatPolyCoeffEqv (spatialWeight w K width)
      (polyMul (polynomialProduct F I) (polynomialProduct F C)) := by
    unfold spatialWeight
    exact ((polynomialProduct_perm F (spatialFace_partition width selected).symm).trans
      (polynomialProduct_append F I C))
  have Pspatial : Certificate (N width)
      (frozenCurvatureAt s (Q'.ofNat I.length * plaquetteCurvatureCost w + 0)
        (spatialWeight w K width) u) :=
    Certificate.ofCoeff
      (frozenCurvatureAt_congr s
        (Q'.ofNat I.length * plaquetteCurvatureCost w + 0) u hpoly) P
  have hcost0 : (0 : Q') ≤ plaquetteCurvatureCost w := by
    unfold plaquetteCurvatureCost
    exact Q'.zero_le_add _ _
      (YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatCurvatureCap_nonnegative hw0)
      (by decide)
  have hcost : Q'.ofNat I.length * plaquetteCurvatureCost w + 0 ≤
      6 * plaquetteCurvatureCost w :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (CReal.ofNat_le_ofNat (spatialIncidentFaces_length_le_six width selected)) hcost0)
  exact frozenCurvatureAt_raise_cost_certificate s (spatialWeight w K width) u
    hu (spatialWeight_supported w K width) hcost Pspatial

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCurvature.spatialWeight_frozen_curvature_nearFlat_certificate
