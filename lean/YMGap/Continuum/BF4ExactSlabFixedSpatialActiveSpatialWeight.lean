/-
# Exact removal of spatial faces touching the inactive fringe

Each removed face has an original fringe link belonging to no other
spatial face. Its full finite heat prefix integrates to one against the
UNCHANGED other factors and any fringe-independent insertion. The retained
action is the same product restricted to fully-active faces, not a new
approximate action. The conditional spatial mass agrees with this product
under every supported original-Haar test.

No positivity, coupling restriction, inverse, or coercivity estimate is
used. This identifies the interaction remaining after the proved stable
fringe extraction; it does not bound that interaction's spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces spatialFaces_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (heatFace_haar_remove)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_independent)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
  (familyProject familyProject_supported familyProject_independent)
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
  (quaternionHaar_polyMul_eq_after_integratingBlocks)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight

/-- The original face order, with exactly the fringe-touching faces removed. -/
def activeSpatialFaces (width : Nat) : List Z4Plaq :=
  (spatialFaces width).filter (fun face => decide (FullyActive width face))

/-- The original finite heat factors, unchanged on every retained face. -/
def activeSpatialWeight (w : Q') (K width : Nat) : RatPoly :=
  polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) (activeSpatialFaces width)

theorem activeSpatialWeight_supported (w : Q') (K width : Nat) :
    SupportedQuaternionBlocks (N width) (activeSpatialWeight w K width) :=
  heatProduct_supported w K width (activeSpatialFaces width)

theorem fullyActive_heat_independent (w : Q') (K width : Nat) (face : Z4Plaq)
    (hf : FullyActive width face) (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i (heatPrefix w K (plaquette width face).scalar) :=
  heatFace_independent_index w K width face i (fringeBlocks_lt width i hi)
    (fun link hl _ he => ((fringeBlocks_mem_iff width i).mp hi).2 (he ▸ hf link hl))

theorem activeSpatialWeight_independent (w : Q') (K width i : Nat)
    (hi : i ∈ fringeBlocks width) : QuaternionBlockIndependent i (activeSpatialWeight w K width) :=
  heatProduct_independent_index w K width (activeSpatialFaces width) i (fringeBlocks_lt width i hi)
    (fun face hf link hl _ he => ((fringeBlocks_mem_iff width i).mp hi).2
      (he ▸ (of_decide_eq_true (List.mem_filter.mp hf).2 : FullyActive width face) link hl))

private theorem rearrange (a b q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a b) q) (polyMul b (polyMul a q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => q)

private theorem peel (w : Q') (K width : Nat) :
    ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces → face ∈ spatialFaces width) → faces.Nodup →
    ∀ q : RatPoly, SupportedQuaternionBlocks (N width) q →
    (∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i q) →
    quaternionHaar (N width)
      (polyMul (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces) q) ≈
    quaternionHaar (N width)
      (polyMul (polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar)
        (faces.filter (fun face => decide (FullyActive width face)))) q)
  | [], _, _, _, _, _ => Q'.eqv_refl _
  | face::faces, hfaces, hn, q, hq, hi => by
      let a := heatPrefix w K (plaquette width face).scalar
      let b := polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) faces
      have htail := fun p hp => hfaces p (List.mem_cons_of_mem face hp)
      have hnd := (List.nodup_cons.mp hn).2
      by_cases ha : FullyActive width face
      · simp only [List.filter_cons, decide_eq_true ha, ↓reduceIte]
        exact Q'.eqv_trans _ _ _ (haar_of_coeff (rearrange a b q))
          (Q'.eqv_trans _ _ _
            (peel w K width faces htail hnd (polyMul a q)
              (supported_polyMul (heatFace_supported w K width face) hq)
              (fun i h => quaternionBlockIndependent_polyMul (fullyActive_heat_independent w K width face ha i h) (hi i h)))
            (haar_of_coeff (rearrange a _ q).symm))
      · simp only [List.filter_cons, decide_eq_false ha]
        let leaf := fringeFaceLeaf width face (hfaces face List.mem_cons_self) ha
        have hfr : (baseLinks width).idxOf leaf.link ∈ fringeBlocks width :=
          (fringeBlocks_mem_iff width _).mpr
            ⟨List.idxOf_lt_length_of_mem leaf.in_carrier, leaf.inactive⟩
        have hnot : ∀ p, p ∈ faces → leaf.link ∉ edgesOf p := by
          intro p hp hl
          have he := leaf.unique p (htail p hp) hl
          exact (List.nodup_cons.mp hn).1 (he ▸ hp)
        exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc a b q))
          (Q'.eqv_trans _ _ _
            (heatFace_haar_remove w K (hfaces face List.mem_cons_self) leaf.link leaf.on_face
              (polyMul b q) (supported_polyMul (heatProduct_supported w K width faces) hq)
              (quaternionBlockIndependent_polyMul
                (heatProduct_independent w K leaf.in_carrier faces hnot) (hi _ hfr)))
            (peel w K width faces htail hnd q hq hi))

/-- Remove every fringe-touching face with its full spectator still present. -/
theorem spatialWeight_haar_active (w : Q') (K width : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q)
    (hi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i q) :
    quaternionHaar (N width) (polyMul (spatialWeight w K width) q) ≈
      quaternionHaar (N width) (polyMul (activeSpatialWeight w K width) q) := by
  unfold spatialWeight activeSpatialWeight activeSpatialFaces
  exact peel w K width (spatialFaces width) (fun _ h => h) (spatialFaces_nodup width) q hq hi

/-- The previously constructed conditional spatial mass is exactly the
active-face product under every supported Haar test, not coefficientwise. -/
theorem spatialFringeMass_haar_active (w : Q') (K width : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    quaternionHaar (N width) (polyMul (spatialFringeMass w K width) q) ≈
      quaternionHaar (N width) (polyMul (activeSpatialWeight w K width) q) := by
  let F := fringeBlocks width
  let Pq := familyProject F q
  have hproj (W : RatPoly) (hi : ∀ i, i ∈ F → QuaternionBlockIndependent i W) :
      quaternionHaar (N width) (polyMul W q) ≈ quaternionHaar (N width) (polyMul W Pq) :=
    quaternionHaar_polyMul_eq_after_integratingBlocks (N width) F W q (fringeBlocks_lt width) hi
  have hm := quaternionHaar_polyMul_eq_after_integratingBlocks (N width) F Pq (spatialWeight w K width)
    (fringeBlocks_lt width) (familyProject_independent F q)
  exact Q'.eqv_trans _ _ _
    (hproj (spatialFringeMass w K width) (spatialFringeMass_independent w K width))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hm)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
          (Q'.eqv_trans _ _ _
            (spatialWeight_haar_active w K width Pq (familyProject_supported F hq)
              (familyProject_independent F q))
            (Q'.eqv_symm (hproj (activeSpatialWeight w K width) (activeSpatialWeight_independent w K width)))))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.activeSpatialFaces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.activeSpatialWeight
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.activeSpatialWeight_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.fullyActive_heat_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.activeSpatialWeight_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.spatialWeight_haar_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight.spatialFringeMass_haar_active
