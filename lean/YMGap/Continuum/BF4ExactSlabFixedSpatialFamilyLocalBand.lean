/-
# A common local band for the original signed-family terminal source

The source is exactly `a = V*u_(n+1)`, before any fringe projection. A
single spectator retains the complete previous message and all exterior
spatial and kinetic factors, and is independent of every link in the signed
family. The comparison count depends on the family link list, not width or
depth. The original active kinetic map is unchanged.

This is finite source data; no energy/variance ratio or continuum scaling
claim is made here. The terminal depth is explicitly positive.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
  (spectator spectator_supported spectator_certificate spectator_independent
    endpoint_lowerCertificate endpoint_upperCertificate lowerFactor upperFactor
    comparison_count_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic
  (plaquette_spectator_kinetic)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorDual
  (active_erased_spectator)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments
  (plaquette_first_moment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap productMap_supported productMap_add productMap_congr)
open YMGap.Continuum.SU2QuaternionProductHeatConstant (productMap_smul)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

/-- One shared footprint, with repetitions retained rather than separate
facewise estimates. -/
def familyLinks : List Z4Plaq → List Z4Link
  | [] => []
  | face :: qs => edgesOf face ++ familyLinks qs

theorem familyLinks_length : ∀ qs : List Z4Plaq,
    (familyLinks qs).length = 4 * qs.length
  | [] => rfl
  | face::rest => by
      simp only [familyLinks, List.length_append, edgesOf, List.length_cons,
        List.length_nil, familyLinks_length rest]
      omega

theorem familyLinks_mem (qs : List Z4Plaq) (face : Z4Plaq)
    (hf : face ∈ qs) (l : Z4Link) (hl : l ∈ edgesOf face) :
    l ∈ familyLinks qs := by
  induction qs with
  | nil => exact False.elim (List.not_mem_nil hf)
  | cons first rest ih =>
      rcases List.mem_cons.mp hf with hfirst | hrest
      · subst face
        exact List.mem_append.mpr (Or.inl hl)
      · exact List.mem_append.mpr (Or.inr (ih hrest))

theorem familyLinks_base {base width : Nat} (hwidth : base < width)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (l : Z4Link) (hl : l ∈ familyLinks qs) : l ∈ baseLinks width := by
  induction qs with
  | nil => exact False.elim (List.not_mem_nil hl)
  | cons face rest ih =>
      rcases List.mem_append.mp hl with hface | hrest
      · exact face_link_mem_base
          (spatialFaces_mono (Nat.le_of_lt hwidth) (hqs face List.mem_cons_self)) hface
      · exact ih (fun p hp => hqs p (List.mem_cons_of_mem face hp)) hrest

theorem familyLinks_active {base width : Nat} (hwidth : base < width)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (l : Z4Link) (hl : l ∈ familyLinks qs) :
    (baseLinks width).idxOf l ∈ activeBlocks width := by
  induction qs with
  | nil => exact False.elim (List.not_mem_nil hl)
  | cons face rest ih =>
      rcases List.mem_append.mp hl with hface | hrest
      · exact plaquette_active_after_padding hwidth face
          (hqs face List.mem_cons_self) l hface
      · exact ih (fun p hp => hqs p (List.mem_cons_of_mem face hp)) hrest

/-- The original unprojected source and its complete link-independent
spectator. The predecessor `n` is explicit: this band controls depth `n+1`. -/
def familyEndpoint (w : Q') (K width n : Nat) : RatPoly :=
  endpointSource w K width (terminalMessage w K width (n+1))

def familySpectator (w : Q') (K width n : Nat) (qs : List Z4Plaq) : RatPoly :=
  spectator w K width n (familyLinks qs)

def familySpectator_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (qs : List Z4Plaq) :
    Certificate (N width) (familySpectator w K width n qs) :=
  spectator_certificate hw0 hw1 K width hK n (familyLinks qs)

theorem familySpectator_supported (w : Q') (K width n : Nat)
    (qs : List Z4Plaq) :
    SupportedQuaternionBlocks (N width) (familySpectator w K width n qs) :=
  spectator_supported w K width n (familyLinks qs)

theorem familySpectator_independent {base width : Nat}
    (hwidth : base < width) (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (w : Q') (K n : Nat) (l : Z4Link) (hl : l ∈ familyLinks qs) :
    QuaternionBlockIndependent ((baseLinks width).idxOf l)
      (familySpectator w K width n qs) :=
  spectator_independent w K width n (familyLinks qs) l hl
    (familyLinks_base hwidth qs hqs l hl)

/-- Both actual-source bands are existing certificates specialized to the
entire signed family's common link list. -/
def familyEndpoint_lowerCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (qs : List Z4Plaq) :
    Certificate (N width)
      (polyAdd (familyEndpoint w K width n)
        (polyNeg (polySmul (lowerFactor w width (familyLinks qs))
          (familySpectator w K width n qs)))) :=
  endpoint_lowerCertificate hw0 hw1 K width hK n (familyLinks qs)

def familyEndpoint_upperCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (qs : List Z4Plaq) :
    Certificate (N width)
      (polyAdd (polySmul (upperFactor w width (familyLinks qs))
          (familySpectator w K width n qs))
        (polyNeg (familyEndpoint w K width n))) :=
  endpoint_upperCertificate hw0 hw1 K width hK n (familyLinks qs)

/-- The footprint count is independent of width and terminal depth at fixed
family size; the factors themselves remain nome-dependent. -/
theorem family_band_factor_count (width : Nat) (qs : List Z4Plaq) :
    (YMGap.Continuum.BF4ExactSlabFixedSpatialLocalCollarGeometry.spatialCollarFaces
      width (familyLinks qs)).length +
      (YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator.localBlocks
        width (familyLinks qs)).length ≤ 7 * (familyLinks qs).length :=
  comparison_count_le width (familyLinks qs)

private theorem family_kinetic_fixedR (width : Nat) (c : Z4Plaq → Q')
    (w : Q') (K : Nat) (hK : 1 ≤ K) (R : RatPoly)
    (hR : SupportedQuaternionBlocks (N width) R) :
    ∀ qs : List Z4Plaq,
      (∀ p, p ∈ qs → p ∈ spatialFaces width) →
      (∀ p, p ∈ qs → ∀ l, l ∈ edgesOf p →
        (baseLinks width).idxOf l ∈ activeBlocks width) →
      (∀ p, p ∈ qs → ∀ l, l ∈ edgesOf p →
        QuaternionBlockIndependent ((baseLinks width).idxOf l) R) →
      SupportedHaarEqv (N width)
        (productMap (N width) w K (activeBlocks width)
          (polyMul (spatialSpan width c qs) R))
        (polySmul (qpow w 12)
          (polyMul (spatialSpan width c qs)
            (productMap (N width) w K (activeBlocks width) R)))
  | [], _, _, _ => by
      let P := productMap (N width) w K (activeBlocks width)
      have hz : RatPolyCoeffEqv (P polyZero) polyZero :=
        (productMap_congr (N width) w K (activeBlocks width)
          (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
          ((productMap_smul (N width) w K (activeBlocks width) 0 polyOne).trans
            (RatPolyCoeffEqv.zero_smul _))
      have hr : RatPolyCoeffEqv polyZero
          (polySmul (qpow w 12) (polyMul polyZero (P R))) :=
        (((RatPolyCoeffEqv.mul_zero_left (P R)).smul (qpow w 12)).trans
          (RatPolyCoeffEqv.smul_zero (qpow w 12))).symm
      exact SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
        ((productMap_congr (N width) w K (activeBlocks width)
          (RatPolyCoeffEqv.mul_zero_left R)).trans
          (hz.trans hr)))
  | face::rest, hfaces, hactive, hind => by
      let P := productMap (N width) w K (activeBlocks width)
      let g := characterPolynomial (plaquette width face).scalar 1
      let t := spatialSpan width c rest
      let a := c face
      let lambda := qpow w 12
      have hg := plaquette_spectator_kinetic width face
        (hfaces face List.mem_cons_self)
        (hactive face List.mem_cons_self) w K hK R hR
        (hind face List.mem_cons_self)
      have ht := family_kinetic_fixedR width c w K hK R hR rest
        (fun p hp => hfaces p (List.mem_cons_of_mem face hp))
        (fun p hp => hactive p (List.mem_cons_of_mem face hp))
        (fun p hp => hind p (List.mem_cons_of_mem face hp))
      have hleft : RatPolyCoeffEqv
          (P (polyMul (spatialSpan width c (face::rest)) R))
          (polyAdd (polySmul a (P (polyMul g R))) (P (polyMul t R))) := by
        change RatPolyCoeffEqv (P (polyMul (polyAdd (polySmul a g) t) R)) _
        rw [polyMul_add_left_exact]
        exact (productMap_add (N width) w K (activeBlocks width) _ _).trans
          (((productMap_congr (N width) w K (activeBlocks width)
              (RatPolyCoeffEqv.polyMul_smul_left a g R)).trans
              (productMap_smul (N width) w K (activeBlocks width)
                a (polyMul g R))).add (RatPolyCoeffEqv.refl _))
      have hcomm : RatPolyCoeffEqv
          (polySmul a (polySmul lambda (polyMul g (P R))))
          (polySmul lambda (polySmul a (polyMul g (P R)))) :=
        (RatPolyCoeffEqv.smul_assoc a lambda _).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv a lambda) _).trans
            (RatPolyCoeffEqv.smul_assoc lambda a _).symm)
      have hmul : RatPolyCoeffEqv
          (polyMul (spatialSpan width c (face::rest)) (P R))
          (polyAdd (polySmul a (polyMul g (P R))) (polyMul t (P R))) := by
        change RatPolyCoeffEqv (polyMul (polyAdd (polySmul a g) t) (P R)) _
        rw [polyMul_add_left_exact]
        exact (RatPolyCoeffEqv.polyMul_smul_left a g (P R)).add (RatPolyCoeffEqv.refl _)
      have hright : RatPolyCoeffEqv
          (polyAdd (polySmul a (polySmul lambda (polyMul g (P R))))
            (polySmul lambda (polyMul t (P R))))
          (polySmul lambda (polyMul (spatialSpan width c (face::rest)) (P R))) :=
        (hcomm.add (RatPolyCoeffEqv.refl _)).trans
          ((RatPolyCoeffEqv.smul_add lambda _ _).symm.trans
            (RatPolyCoeffEqv.smul lambda hmul.symm))
      exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hleft)).trans
        (((hg.smul a).add ht).trans
          (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hright)))

/-- The complete signed span transmits through the ORIGINAL active heat with
the same factor `w^12` and the transformed common spectator retained. -/
theorem family_spectator_kinetic {base width : Nat} (hwidth : base < width)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (c : Z4Plaq → Q') (w : Q') (K : Nat) (hK : 1 ≤ K) (n : Nat) :
    let R := familySpectator w K width n qs
    let f := spatialSpan width c qs
    SupportedHaarEqv (N width)
      (productMap (N width) w K (activeBlocks width) (polyMul R f))
      (polySmul (qpow w 12)
        (polyMul (productMap (N width) w K (activeBlocks width) R) f)) := by
  dsimp only
  let R := familySpectator w K width n qs
  let f := spatialSpan width c qs
  let P := productMap (N width) w K (activeBlocks width)
  have h := family_kinetic_fixedR width c w K hK R
    (familySpectator_supported w K width n qs) qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))
    (fun p hp => plaquette_active_after_padding hwidth p (hqs p hp))
    (fun p hp l hl => familySpectator_independent hwidth qs hqs w K n l
      (familyLinks_mem qs p hp l hl))
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
    (productMap_congr (N width) w K (activeBlocks width)
      (RatPolyCoeffEqv.mul_comm R f)))).trans
    (h.trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.mul_comm f (P R)).smul (qpow w 12)))))

private theorem span_zero_of_faces (width : Nat) (c : Z4Plaq → Q')
    (W : RatPoly) : ∀ qs : List Z4Plaq,
      (∀ p, p ∈ qs → H width
        (polyMul W (characterPolynomial (plaquette width p).scalar 1)) ≈ 0) →
      H width (polyMul W (spatialSpan width c qs)) ≈ 0
  | [], _ => by
      exact Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right W)) (Q'.eqv_refl _)
  | face::rest, hz => by
      let g := characterPolynomial (plaquette width face).scalar 1
      let t := spatialSpan width c rest
      have hsplit : H width (polyMul W (spatialSpan width c (face::rest))) ≈
          c face * H width (polyMul W g) + H width (polyMul W t) := by
        change H width (polyMul W (polyAdd (polySmul (c face) g) t)) ≈ _
        exact Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_add_right (N width) W _ _)
          (Q'.add_eqv_congr_right _ _ _
            (quaternionHaar_polyMul_smul_right (N width) (c face) W g))
      exact Q'.eqv_trans _ _ _ hsplit
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left (c face) _ _ (hz face List.mem_cons_self))
            (span_zero_of_faces width c W rest
              (fun p hp => hz p (List.mem_cons_of_mem face hp))))
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _
            (Q'.mul_zero_eqv (c face))) (QPoly.q_zero_add_eqv 0)))

/-- The original kinetic-weighted first moment of the entire signed span
vanishes against the SAME common spectator. One active edge of each face is
erased only for the supported-Haar proof; no heat factor is dropped from the
statement. -/
theorem family_spectator_zero {base width : Nat} (hwidth : base < width)
    (qs : List Z4Plaq) (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base)
    (c : Z4Plaq → Q') (w : Q') (K n : Nat) :
    let R := familySpectator w K width n qs
    let f := spatialSpan width c qs
    H width (polyMul
      (polyMul R (productMap (N width) w K (activeBlocks width) R)) f) ≈ 0 := by
  dsimp only
  let R := familySpectator w K width n qs
  let P := productMap (N width) w K (activeBlocks width)
  let W := polyMul R (P R)
  have hR : SupportedQuaternionBlocks (N width) R :=
    familySpectator_supported w K width n qs
  have hPR : SupportedQuaternionBlocks (N width) (P R) :=
    productMap_supported (N width) w K (activeBlocks width)
      (activeBlocks_lt width) hR
  apply span_zero_of_faces width c W qs
  intro face hface
  let l : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : l ∈ edgesOf face := by simp [l, edgesOf]
  have hf : face ∈ spatialFaces width :=
    spatialFaces_mono (Nat.le_of_lt hwidth) (hqs face hface)
  have hi : (baseLinks width).idxOf l ∈ activeBlocks width :=
    familyLinks_active hwidth qs hqs l (familyLinks_mem qs face hface l hl)
  have hRI : QuaternionBlockIndependent ((baseLinks width).idxOf l) R :=
    familySpectator_independent hwidth qs hqs w K n l
      (familyLinks_mem qs face hface l hl)
  let E := productMap (N width) w K
    (eraseIndex ((baseLinks width).idxOf l) (activeBlocks width)) R
  have hE : SupportedQuaternionBlocks (N width) E :=
    productMap_supported (N width) w K _
      (fun j hj => activeBlocks_lt width j
        (mem_of_mem_erase ((baseLinks width).idxOf l) hj)) hR
  have hpair := active_erased_spectator width w K
    ((baseLinks width).idxOf l) hi R hR hRI
  let g := characterPolynomial (plaquette width face).scalar 1
  have hinsert : SupportedQuaternionBlocks (N width) (polyMul R g) :=
    supported_polyMul hR
      (BF4ExactSlabFixedSpatialPlaquetteHaar.plaquette_supported width face)
  have hfirst := plaquette_first_moment hf l hl (polyMul R E)
    (supported_polyMul hR hE)
    (quaternionBlockIndependent_polyMul hRI hpair.2)
  have hleft : RatPolyCoeffEqv (polyMul (polyMul R (P R)) g)
      (polyMul (polyMul R g) (P R)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => R | 1 => P R | _ => g)
  have hright : RatPolyCoeffEqv (polyMul (polyMul R g) E)
      (polyMul g (polyMul R E)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => R | 1 => E | _ => g)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hleft)
    (Q'.eqv_trans _ _ _ (hpair.1 (polyMul R g) hinsert)
      (Q'.eqv_trans _ _ _ (haar_of_coeff hright) hfirst))

#print axioms familyLinks
#print axioms familyLinks_length
#print axioms familyLinks_mem
#print axioms familyLinks_base
#print axioms familyLinks_active
#print axioms familyEndpoint
#print axioms familySpectator
#print axioms familySpectator_certificate
#print axioms familySpectator_supported
#print axioms familySpectator_independent
#print axioms familyEndpoint_lowerCertificate
#print axioms familyEndpoint_upperCertificate
#print axioms family_band_factor_count
#print axioms family_spectator_kinetic
#print axioms family_spectator_zero

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand
