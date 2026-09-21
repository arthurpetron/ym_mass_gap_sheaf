/-
# Affine signed-family detection by the original boundary dual

Subtracting an arbitrary rational constant from the signed plaquette span does
not change the coefficient detected by the local dual: the fundamental
character is exactly orthogonal to constants against the erased-star
background.  The finite inverse residual retains that same shifted polynomial,
and its norm is controlled in the unchanged full selected action.

These are exact finite polynomial identities and a weighted Cauchy--Schwarz
bound.  No variance floor, limiting statement, or continuum conclusion is
asserted here.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem rest_character_one_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face) polyOne)) ≈ 0 := by
  let link : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : link ∈ edgesOf face := List.mem_cons_self
  exact rest_character_spectator_zero w K extent ids hf link hl 1 (by decide)
    polyOne (supported_one (B extent)) []
    (BlockLocal.one _ (fun b => correctedSlabLinkAt extent b ∈ ([] : List Z4Link)))
    (by intro h; cases h)

/-- Exact coefficient detection survives subtracting any rational constant. -/
theorem rest_shifted_pairing (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (terms : List (Q' × Z4Plaq)) (m : Q') :
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face) (shifted (faceSpan extent terms) m))) ≈
      coefficientAt face terms * quaternionHaar (B extent) (restHeat w K extent ids face) := by
  let R := restHeat w K extent ids face
  let C := faceCharacter extent face
  let F := faceSpan extent terms
  have hF : quaternionHaar (B extent) (polyMul (polyMul R C) F) ≈
      coefficientAt face terms * quaternionHaar (B extent) R :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R C F))
      (rest_signed_pairing w K extent ids hf terms)
  have h1 : quaternionHaar (B extent) (polyMul (polyMul R C) (polySmul 1 F)) ≈
      coefficientAt face terms * quaternionHaar (B extent) R :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (B extent) 1 (polyMul R C) F)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 1 _ _ hF) (Q'.one_mul_eqv _))
  have h0 : quaternionHaar (B extent) (polyMul (polyMul R C) (polySmul (-m) polyOne)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_smul_right (B extent) (-m) (polyMul R C) polyOne)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-m) _ _
          (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R C polyOne))
            (rest_character_one_zero w K extent ids hf)))
        (Q'.mul_zero_eqv (-m)))
  unfold shifted
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R C _).symm)
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right (B extent) (polyMul R C)
        (polySmul 1 F) (polySmul (-m) polyOne))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h1 h0)
        (Q'.eqv_of_eq (Q'.add_zero' _))))

private theorem cancellation_insert (S R C D E F : RatPoly)
    (h : RatPolyCoeffEqv (polyAdd (polyMul S D) (polyMul C E)) C) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul S R) (polyMul D F))
        (polyMul R (polyMul C (polyMul E F))))
      (polyMul R (polyMul C F)) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 5)))
      (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.var 5)))))
    (.mul (.var 1)
      (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 4))) (.var 5)))
    (by decide) (fun | 0 => S | 1 => R | 2 => C | 3 => D | 4 => E | _ => F)).trans
    ((h.mul_right F).mul_left R)

/-- The full selected action detects the unchanged coefficient, while the
finite residual contains the same affine-shifted source. -/
theorem fullAction_shifted_pairing {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (k : Nat) (terms : List (Q' × Z4Plaq)) (m : Q') :
    quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids face k) (shifted (faceSpan extent terms) m))) +
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face)
          (polyMul (residualPolynomial hw0 K extent ids face k)
            (shifted (faceSpan extent terms) m)))) ≈
      coefficientAt face terms * quaternionHaar (B extent) (restHeat w K extent ids face) := by
  let F := shifted (faceSpan extent terms) m
  have he := (((selected_heat_partition w K extent ids face).mul_right
      (polyMul (dualTest hw0 K extent ids face k) F)).add
      (RatPolyCoeffEqv.refl
        (polyMul (restHeat w K extent ids face)
          (polyMul (faceCharacter extent face)
            (polyMul (residualPolynomial hw0 K extent ids face k) F))))).trans
    (cancellation_insert (starHeat w K extent ids face) (restHeat w K extent ids face)
      (faceCharacter extent face) (dualTest hw0 K extent ids face k)
      (residualPolynomial hw0 K extent ids face k) F
      (cancellation_pin hw0 K extent ids face k))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (rest_shifted_pairing w K extent ids hf terms m))

/-- Generic residual control for any supported affine or non-affine source.
The right-hand square uses the unchanged full selected action. -/
theorem fullAction_pairing_error {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (k : Nat) (F : RatPoly) (hF : SupportedQuaternionBlocks (B extent) F) :
    let error := quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face)
          (polyMul (residualPolynomial hw0 K extent ids face k) F)))
    lower w * (error * error) ≤
      ((rate hw0)^k * (rate hw0)^k * quaternionHaar (B extent) (restHeat w K extent ids face)) *
        quaternionHaar (B extent)
          (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids) (polyMul F F)) := by
  let S := starHeat w K extent ids face
  let R := restHeat w K extent ids face
  let C := faceCharacter extent face
  let E := residualPolynomial hw0 K extent ids face k
  have Rpos : Certificate (B extent) R :=
    headProduct_certificate hw0 hw1 K extent hK _
      (fun id hi => hids id (boundaryRest_mem hi).1)
  have hb := QuaternionHaarLocalDualNorm.local_dual_pairing_error
    (starHeat_supported w K extent ids face) (lower_positive hw0 hw1)
    (upper_positive hw0) (lower_le_upper hw0 hw1)
    (starLowerCertificate hw0 hw1 K extent hK ids hids hnodup face)
    (starUpperCertificate hw0 hw1 K extent ids hids hnodup face) k Rpos
    (faceCharacter_supported extent face) hF
  have he : quaternionHaar (B extent) (polyMul R (polyMul C (polyMul E F))) ≈
      quaternionHaar (B extent) (polyMul R (polyMul C (polyMul F E))) :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_comm E F).mul_left C).mul_left R)
  have hn : quaternionHaar (B extent) (polyMul (polyMul R S) (polyMul F F)) ≈
      quaternionHaar (B extent)
        (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids) (polyMul F F)) :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_comm R S).trans
      (selected_heat_partition w K extent ids face).symm).mul_right (polyMul F F))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (qmul (Q'.eqv_refl _) (qmul he he)))
    (Q'.le_trans' _ _ _ hb
      (Q'.le_of_eqv (qmul (qmul (Q'.eqv_refl _) (rest_square_moment w K extent ids hf)) hn)))

end YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing.rest_shifted_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing.fullAction_shifted_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffinePairing.fullAction_pairing_error
