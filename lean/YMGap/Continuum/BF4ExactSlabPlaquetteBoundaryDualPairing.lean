/-
# Signed plaquette-family detection by the original boundary dual

Every face occurrence retains its rational coefficient. Repeated labels are
summed, not silently discarded. Exact character orthogonality against the
four-link-erased background detects this combined coefficient, even when the
family has shared links or is a closed surface.

The finite reciprocal dual obeys the same identity under the FULL selected
action with an explicit residual integral. No common private link, positivity
of the coefficients, limiting inverse, summed frame estimate or gap is assumed.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDual
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

attribute [local irreducible] correctedSlabPlaquettePolynomial

/-- A literal finite signed sum; the list may contain repeated face labels. -/
def faceSpan (extent : Nat) (terms : List (Q' × Z4Plaq)) : RatPoly :=
  finitePolySum (fun term => polySmul term.1 (faceCharacter extent term.2)) terms

/-- All occurrences of the selected face contribute, with their signs. -/
def coefficientAt (face : Z4Plaq) (terms : List (Q' × Z4Plaq)) : Q' :=
  listQSum (fun term => if term.2 = face then term.1 else 0) terms

private theorem supported_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem faceSpan_supported (extent : Nat) : ∀ terms : List (Q' × Z4Plaq),
    SupportedQuaternionBlocks (B extent) (faceSpan extent terms)
  | [] => by intro t ht; cases ht
  | term :: terms => supported_add
      (supported_smul (faceCharacter_supported extent term.2) term.1)
      (faceSpan_supported extent terms)

private theorem rest_term_pairing (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (a : Q') (other : Z4Plaq) :
    quaternionHaar (B extent)
      (polyMul (polyMul (restHeat w K extent ids face) (faceCharacter extent face))
        (polySmul a (faceCharacter extent other))) ≈
      (if other = face then a else 0) * quaternionHaar (B extent) (restHeat w K extent ids face) := by
  let R := restHeat w K extent ids face
  let C := faceCharacter extent face
  have hs := quaternionHaar_polyMul_smul_right (B extent) a (polyMul R C)
    (faceCharacter extent other)
  have ha := haar_of_coeff (blocks := B extent)
    (RatPolyCoeffEqv.mul_assoc R C (faceCharacter extent other))
  by_cases he : other = face
  · subst other
    simp only
    exact Q'.eqv_trans _ _ _ hs (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ ha (rest_square_moment w K extent ids hf)))
  · simp only [if_neg he]
    have hz := Q'.eqv_trans _ _ _ ha
      (rest_distinct_character_zero w K extent ids hf other (fun h => he h.symm))
    exact Q'.eqv_trans _ _ _ hs
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz)
        (Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv a) (Q'.eqv_symm (Q'.zero_mul_eqv _))))

private theorem rest_sum_pairing (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    ∀ terms : List (Q' × Z4Plaq),
    quaternionHaar (B extent)
      (polyMul (polyMul (restHeat w K extent ids face) (faceCharacter extent face))
        (faceSpan extent terms)) ≈
      coefficientAt face terms * quaternionHaar (B extent) (restHeat w K extent ids face)
  | [] => Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right _))
      (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | term :: terms => by
      let R := restHeat w K extent ids face
      let C := faceCharacter extent face
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_add_right (B extent) (polyMul R C)
          (polySmul term.1 (faceCharacter extent term.2)) (faceSpan extent terms))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (rest_term_pairing w K extent ids hf term.1 term.2)
            (rest_sum_pairing w K extent ids hf terms))
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)))

/-- Exact coefficient detection with all repeated-label cancellations retained. -/
theorem rest_signed_pairing (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (terms : List (Q' × Z4Plaq)) :
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face) (faceSpan extent terms))) ≈
      coefficientAt face terms * quaternionHaar (B extent) (restHeat w K extent ids face) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc
    (restHeat w K extent ids face) (faceCharacter extent face) (faceSpan extent terms)).symm)
    (rest_sum_pairing w K extent ids hf terms)

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

/-- The finite dual detects the same signed coefficient under the FULL original
selected action. The unreduced finite residual is displayed as a second term. -/
theorem fullAction_signed_pairing {w : Q'} (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (k : Nat) (terms : List (Q' × Z4Plaq)) :
    quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (dualTest hw0 K extent ids face k) (faceSpan extent terms))) +
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face)
          (polyMul (residualPolynomial hw0 K extent ids face k) (faceSpan extent terms)))) ≈
      coefficientAt face terms * quaternionHaar (B extent) (restHeat w K extent ids face) := by
  have he := (((selected_heat_partition w K extent ids face).mul_right
      (polyMul (dualTest hw0 K extent ids face k) (faceSpan extent terms))).add
      (RatPolyCoeffEqv.refl
        (polyMul (restHeat w K extent ids face)
          (polyMul (faceCharacter extent face)
            (polyMul (residualPolynomial hw0 K extent ids face k) (faceSpan extent terms)))))).trans
    (cancellation_insert (starHeat w K extent ids face) (restHeat w K extent ids face)
      (faceCharacter extent face) (dualTest hw0 K extent ids face k)
      (residualPolynomial hw0 K extent ids face k) (faceSpan extent terms)
      (cancellation_pin hw0 K extent ids face k))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append _ _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff he) (rest_signed_pairing w K extent ids hf terms))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The displayed coefficient-detection residual is geometrically small in
the ORIGINAL signed family's weighted square norm, not its coefficient l1 cap.
The local constants depend on nome; no sum over dual labels is bounded here. -/
theorem fullAction_signed_pairing_error {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (k : Nat) (terms : List (Q' × Z4Plaq)) :
    let error := quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face)
          (polyMul (residualPolynomial hw0 K extent ids face k) (faceSpan extent terms))))
    lower w * (error * error) ≤
      ((rate hw0)^k * (rate hw0)^k * quaternionHaar (B extent) (restHeat w K extent ids face)) *
        quaternionHaar (B extent)
          (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
            (polyMul (faceSpan extent terms) (faceSpan extent terms))) := by
  let S := starHeat w K extent ids face
  let R := restHeat w K extent ids face
  let C := faceCharacter extent face
  let F := faceSpan extent terms
  let E := residualPolynomial hw0 K extent ids face k
  have Rpos : Certificate (B extent) R :=
    headProduct_certificate hw0 hw1 K extent hK _
      (fun id hi => hids id (boundaryRest_mem hi).1)
  have hb := QuaternionHaarLocalDualNorm.local_dual_pairing_error
    (starHeat_supported w K extent ids face) (lower_positive hw0 hw1)
    (upper_positive hw0) (lower_le_upper hw0 hw1)
    (starLowerCertificate hw0 hw1 K extent hK ids hids hnodup face)
    (starUpperCertificate hw0 hw1 K extent ids hids hnodup face) k Rpos
    (faceCharacter_supported extent face) (faceSpan_supported extent terms)
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

#print axioms faceSpan
#print axioms coefficientAt
#print axioms faceSpan_supported
#print axioms rest_signed_pairing
#print axioms fullAction_signed_pairing
#print axioms fullAction_signed_pairing_error

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
