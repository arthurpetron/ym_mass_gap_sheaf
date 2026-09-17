/-
# A nonzero two-plaquette direction in the original selected action

Two distinct physical fundamental plaquettes retain any two rational
coefficients whose square sum is positive. The checked signed-family
coercivity theorem and the SAME original partition give a strictly positive
raw weighted square norm. No variance upper bound, response sign, uniform
spectral gap or continuum conclusion is asserted.

The bare-Haar statements concern the same literal polynomial, not a
replacement action. They make its nonconstant character explicit.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily

namespace YMGap.Continuum.BF4ExactSlabTwoPlaquettePositiveNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
  (faceCharacter faceCharacter_supported selectedMass_positive)
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one supported_add)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] correctedSlabPlaquettePolynomial

def twoFaceSpan (extent : Nat) (p q : Z4Plaq) (a b : Q') : RatPoly :=
  polyAdd (polySmul a (faceCharacter extent p)) (polySmul b (faceCharacter extent q))

private theorem supported_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem twoFaceSpan_supported (extent : Nat) (p q : Z4Plaq) (a b : Q') :
    SupportedQuaternionBlocks (B extent) (twoFaceSpan extent p q a b) :=
  supported_add (supported_smul (faceCharacter_supported extent p) a)
    (supported_smul (faceCharacter_supported extent q) b)

private def coefficients (p : Z4Plaq) (a b : Q') (x : Z4Plaq) : Q' :=
  if x = p then a else b

private theorem source_pin (extent : Nat) (p q : Z4Plaq) (hpq : p ≠ q) (a b : Q') :
    RatPolyCoeffEqv (sourceSpan extent (coefficients p a b) [p,q])
      (twoFaceSpan extent p q a b) := by
  simp only [sourceSpan, faceSpan, List.map_cons, List.map_nil, finitePolySum,
    coefficients, if_neg (Ne.symm hpq), twoFaceSpan]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)

private theorem coefficient_squares (p q : Z4Plaq) (hpq : p ≠ q) (a b : Q') :
    listQSum (fun x => coefficients p a b x * coefficients p a b x) [p,q] ≈ a*a+b*b := by
  simp only [listQSum, coefficients, if_neg (Ne.symm hpq)]
  exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_of_eq (Q'.add_zero' _))

private theorem positive_of_positive_multiple {c x : Q'} (hc : (0 : Q') < c)
    (hx : (0 : Q') < c*x) : (0 : Q') < x := by
  have hp := Q'.mul_pos hx (Q'.recipPos_pos c hc)
  have he : (c*x)*Q'.recipPos c hc ≈ x :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c x))
        (Q'.mul_assoc_eqv x c (Q'.recipPos c hc)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv c hc))
        (Q'.mul_one_eqv x))
  exact Q'.pos_of_lt_of_le hp (Q'.le_of_eqv he)

/-- Nonzero coefficient data gives a strictly positive square norm in the
full original physical selected action, at every cofinal cutoff. -/
theorem twoFaceSpan_norm_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    {p q : Z4Plaq} (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (hpq : p ≠ q)
    (a b : Q') (hab : (0 : Q') < a*a+b*b) :
    (0 : Q') < quaternionHaar (B extent)
      (polyMul (polynomialProduct (faceHeatPolynomial w K extent) ids)
        (polyMul (twoFaceSpan extent p q a b) (twoFaceSpan extent p q a b))) := by
  have hn : ([p,q] : List Z4Plaq).Nodup := by simp [hpq]
  have hphysical : ∀ x, x ∈ ([p,q] : List Z4Plaq) →
      x ∈ boundaryCompleteSlabPlaquettes extent := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hq
      · exact False.elim (List.not_mem_nil hx)
  have h := family_partition_coercivity hw0 hw1 K extent hK ids hids hnodup
    [p,q] hn hphysical (coefficients p a b)
  have hz := selectedMass_positive hw0 hw1 K extent hK ids hids
  have hcoeff : (0 : Q') <
      listQSum (fun x => coefficients p a b x * coefficients p a b x) [p,q] :=
    Q'.pos_of_lt_of_le hab (Q'.ge_of_eqv (coefficient_squares p q hpq a b))
  have hpos := Q'.pos_of_lt_of_le
    (Q'.mul_pos (Q'.mul_pos (lower_positive hw0 hw1) hz) hcoeff) h
  have hraw := positive_of_positive_multiple
    (Q'.mul_pos (by decide : (0 : Q') < 600) (upper_positive hw0)) hpos
  have he := haar_of_coeff (blocks := B extent)
    ((RatPolyCoeffEqv.refl (polynomialProduct (faceHeatPolynomial w K extent) ids)).mul
      ((source_pin extent p q hpq a b).mul (source_pin extent p q hpq a b)))
  exact Q'.pos_of_lt_of_le hraw (Q'.le_of_eqv he)

private theorem face_mean_zero {extent : Nat} {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (B extent) (faceCharacter extent p) ≈ 0 := by
  have hz := original_character_local_zero hp (p.1, (dirsOf p.2).1)
    (show (p.1, (dirsOf p.2).1) ∈ edgesOf p from List.mem_cons_self)
    1 (by decide) polyOne [] (supported_one _) (BlockLocal.one _ _)
    List.not_mem_nil
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_one (faceCharacter extent p)).symm) hz

/-- Bare Haar centering of the same literal two-face polynomial. -/
theorem twoFaceSpan_haar_mean_zero (extent : Nat) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (a b : Q') :
    quaternionHaar (B extent) (twoFaceSpan extent p q a b) ≈ 0 := by
  have ha := Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (B extent) a (faceCharacter extent p))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (face_mean_zero hp)) (Q'.mul_zero_eqv a))
  have hb := Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (B extent) b (faceCharacter extent q))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (face_mean_zero hq)) (Q'.mul_zero_eqv b))
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append (B extent) _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha hb) (Q'.eqv_of_eq (Q'.add_zero' 0)))

/-- No action hypothesis is hidden here: this is the empty-action
specialization of the original norm theorem, on the same polynomial. -/
theorem twoFaceSpan_haar_square_positive (extent : Nat) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (hpq : p ≠ q)
    (a b : Q') (hab : (0 : Q') < a*a+b*b) :
    (0 : Q') < quaternionHaar (B extent)
      (polyMul (twoFaceSpan extent p q a b) (twoFaceSpan extent p q a b)) := by
  let w : Q' := Q'.mkPos 1 2 (by decide)
  have h := twoFaceSpan_norm_positive (w := w) (by decide) (by decide)
    (headCutoff w) extent (Nat.le_refl _) []
    (by intro id hi; exact False.elim (List.not_mem_nil hi)) (by simp)
    hp hq hpq a b hab
  exact Q'.pos_of_lt_of_le h (Q'.le_of_eqv
    (haar_of_coeff (RatPolyCoeffEqv.one_mul _)))

/-- This nonzero direction is not a constant polynomial modulo coefficient
equality. This does not assert nonconstancy of any continuum observable. -/
theorem twoFaceSpan_not_constant (extent : Nat) {p q : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes extent)
    (hq : q ∈ boundaryCompleteSlabPlaquettes extent) (hpq : p ≠ q)
    (a b : Q') (hab : (0 : Q') < a*a+b*b) (c : Q') :
    ¬ RatPolyCoeffEqv (twoFaceSpan extent p q a b) (polySmul c polyOne) := by
  intro he
  have hm : quaternionHaar (B extent) (polySmul c polyOne) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff he.symm)
      (twoFaceSpan_haar_mean_zero extent hp hq a b)
  have hz : quaternionHaar (B extent)
      (polyMul (twoFaceSpan extent p q a b) (twoFaceSpan extent p q a b)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (he.mul he))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (B extent) c (polySmul c polyOne) polyOne)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _)) hm))
          (Q'.mul_zero_eqv c)))
  exact (by decide : ¬ ((0 : Q') < 0))
    (Q'.pos_of_lt_of_le (twoFaceSpan_haar_square_positive extent hp hq hpq a b hab)
      (Q'.le_of_eqv hz))

#print axioms twoFaceSpan
#print axioms twoFaceSpan_supported
#print axioms twoFaceSpan_norm_positive
#print axioms twoFaceSpan_haar_mean_zero
#print axioms twoFaceSpan_haar_square_positive
#print axioms twoFaceSpan_not_constant

end YMGap.Continuum.BF4ExactSlabTwoPlaquettePositiveNorm
