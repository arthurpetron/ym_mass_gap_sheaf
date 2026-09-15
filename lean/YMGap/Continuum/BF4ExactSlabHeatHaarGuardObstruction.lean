/-
# An original-Haar square test excludes small all-cutoff heat intervals

On any actual slab plaquette, r=1+chi_1 satisfies H(r^2)=2 and
H(r^2 chi_1)=2. The cutoff-one positive-label heat remainder therefore
has H(r^2 R)=4*w^3. At w>=7/8 no original Haar Interval for R can
have cap <=1. This tests the actual polynomial and the actual certificate
semantics, not the previous coarse cap 128*w^3 or pointwise positivity.

The obstruction is to the existing ALL-CUTOFF interval interface (already
at cutoff one). It does not exclude a later-cutoff estimate, a different
reference action, an AF law, or Yang--Mills existence. It supplies no
physical-scale family, continuum limit or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.BF4SmallNomeAFGuardObstruction

namespace YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.FusedAmplitudeDerivation (qpow_mono_base)
open YMGap.Continuum.HeatKernelRGStep (lt_of_lt_of_le)
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4SmallNomeAFGuardObstruction (guardThreshold nome_lower_of_margin_le)

local infix:50 " ≈ " => Q'.eqv

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem haar_cap (blocks : Nat) (c : Q') : quaternionHaar blocks (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks)) (Q'.mul_one_eqv _))

/-- Exact bare-Haar cancellation on the original plaquette, all positive spins. -/
theorem face_character_haar_zero {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (spin : Nat) (hs : 0 < spin) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (faceScalar extent id) spin) ≈ 0 := by
  have h := original_character_link_zero (slabPlaquetteAt_mem hi)
    (faceLinkA (slabPlaquetteAt extent id)) (by simp [faceLinkA, edgesOf]) spin hs polyOne
    (supported_one _) (by
      intro t ht
      have he := List.mem_singleton.mp ht
      subst t
      rfl)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _))) h

def testPolynomial (extent id : Nat) : RatPoly :=
  polyAdd polyOne (characterPolynomial (faceScalar extent id) 1)

theorem test_supported (extent id : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (testPolynomial extent id) :=
  supported_add (supported_one _) (original_character_support _ _ _)

private def c2 : PolyExpr := .add (.mul (.var 0) (.var 0)) (.const (-1))
private def c3 : PolyExpr := .add (.mul (.var 0) c2) (.mul (.const (-1)) (.var 0))
private def texpr : PolyExpr := .add (.const 1) (.var 0)

private theorem char3_pin (p : RatPoly) :
    RatPolyCoeffEqv (coeffEvalExpr (fun _ => characterPolynomial p 1) c3) (characterPolynomial p 3) :=
  (RatPolyCoeffEqv.refl _).add (cap_mul_left (-1) (characterPolynomial p 1))

private theorem test_square_pin (p : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyAdd polyOne (characterPolynomial p 1)) (polyAdd polyOne (characterPolynomial p 1)))
      (polyAdd (cap 2) (polyAdd (polySmul 2 (characterPolynomial p 1)) (characterPolynomial p 2))) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.mul texpr texpr)
    (.add (.const 2) (.add (.mul (.const 2) (.var 0)) c2)) (by decide)
    (fun _ => characterPolynomial p 1)).trans
    ((RatPolyCoeffEqv.refl _).add ((cap_mul_left 2 _).add (RatPolyCoeffEqv.refl _)))

private theorem test_square_character_pin (p : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (polyAdd polyOne (characterPolynomial p 1))
        (polyAdd polyOne (characterPolynomial p 1))) (characterPolynomial p 1))
      (polyAdd (cap 2) (polyAdd (polySmul 3 (characterPolynomial p 1))
        (polyAdd (polySmul 2 (characterPolynomial p 2)) (characterPolynomial p 3)))) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.mul (.mul texpr texpr) (.var 0))
    (.add (.const 2) (.add (.mul (.const 3) (.var 0)) (.add (.mul (.const 2) c2) c3)))
    (by decide) (fun _ => characterPolynomial p 1)).trans
    ((RatPolyCoeffEqv.refl _).add ((cap_mul_left 3 _).add ((cap_mul_left 2 _).add (char3_pin p))))

theorem test_square_haar {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (testPolynomial extent id) (testPolynomial extent id)) ≈ 2 := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (test_square_pin (faceScalar extent id))) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_cap _ 2)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (face_character_haar_zero hi 1 (by decide))))
        (face_character_haar_zero hi 2 (by decide))))) ?_
  decide

theorem test_square_character_haar {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (characterPolynomial (faceScalar extent id) 1)) ≈ 2 := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (test_square_character_pin (faceScalar extent id))) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_cap _ 2)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (face_character_haar_zero hi 1 (by decide))))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr'
            (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
              (Q'.mul_eqv_congr_left _ _ _ (face_character_haar_zero hi 2 (by decide))))
            (face_character_haar_zero hi 3 (by decide))))))) ?_
  decide

theorem tail_one (w : Q') (extent id : Nat) :
    faceHeatTail w extent id 1 1 = polySmul (coeffW w 1) (characterPolynomial (faceScalar extent id) 1) := by
  simp [faceHeatTail, finitePolySum, faceHeatTerm, polyAdd, polyZero]

/-- Actual original remainder, actual square insertion, exact heat coefficient. -/
theorem test_remainder_haar (w : Q') {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (faceHeatTail w extent id 1 1)) ≈ 4 * qpow w 3 := by
  rw [tail_one]
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (test_square_character_haar hi)) ?_
  exact poly_identity_of_normal_eq (.mul (.mul (.const 2) (.var 0)) (.const 2))
    (.mul (.const 4) (.var 0)) (by decide) (fun _ => qpow w 3)

/-- Every actual Interval cap must pay the explicit square test. -/
theorem interval_cap_constraint (w c : Q') {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (R : Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 1) c) :
    4 * qpow w 3 ≤ c * 2 := by
  have h := R.weighted_haar_bound (Certificate.square (testPolynomial extent id) (test_supported _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (test_remainder_haar w hi))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (test_square_haar hi)))))

def nomeThreshold : Q' := Q'.mkPos 7 8 (by decide)

/-- No sharpening of the old cap can satisfy its <=1 guard at cutoff one. -/
theorem no_small_interval {w c : Q'} (hw : nomeThreshold ≤ w) (hc : c ≤ 1)
    {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (R : Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 1) c) : False := by
  have hlow : (2 : Q') < 4 * qpow w 3 :=
    lt_of_lt_of_le (by decide : (2 : Q') < 4 * qpow nomeThreshold 3)
      (Q'.mul_le_mul_of_nonneg_left _ _ 4
        (qpow_mono_base (by decide : (0 : Q') ≤ nomeThreshold) hw 3) (by decide))
  have hu : 4 * qpow w 3 ≤ 2 :=
    Q'.le_trans' _ _ _ (interval_cap_constraint w c hi R)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ 2 hc (by decide))
        (Q'.le_of_eqv (Q'.one_mul_eqv 2)))
  exact Int.not_lt_of_ge hu hlow

theorem no_allCutoff_intervals {w c : Q'} (hw : nomeThreshold ≤ w) (hc : c ≤ 1)
    {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)
    (R : ∀ K : Nat, Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 K) c) :
    False := no_small_interval hw hc hi (R 1)

theorem fine_nome_ge_threshold (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) (hsmall : g ≤ guardThreshold) :
    nomeThreshold ≤ fineWeight family g := by
  have hs : g*g ≤ guardThreshold*guardThreshold :=
    Q'.mul_le_mul_of_nonneg hsmall hsmall (by decide) (Q'.le_of_lt hg)
  have hm := Q'.le_trans' _ _ _ (Q'.le_of_eqv (law.current_margin g hg hgle)) hs
  exact Q'.le_trans' _ _ _ (by decide : nomeThreshold ≤ 1 + -(guardThreshold*guardThreshold))
    (nome_lower_of_margin_le _ _ hm)

theorem blocked_nome_ge_threshold (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) (hsmall : g ≤ guardThreshold) :
    nomeThreshold ≤ blockedWeight family g := by
  have hs : g*g ≤ guardThreshold*guardThreshold :=
    Q'.mul_le_mul_of_nonneg hsmall hsmall (by decide) (Q'.le_of_lt hg)
  have hm := Q'.le_trans' _ _ _ (blockedMargin_le_two_square family law g hg hgle)
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hs (by decide))
  exact Q'.le_trans' _ _ _ (by decide : nomeThreshold ≤ 1 + -(2*(guardThreshold*guardThreshold)))
    (nome_lower_of_margin_le _ _ hm)

/-- A computed AF-chart point where neither fine nor matched blocked weight
admits the old all-cutoff Interval interface with any cap <=1. The supplied
law remains an input; the returned nomes feed `no_small_interval` directly. -/
def afObstructionWitness (family : MatchedBlockFamily) (law : CubicMarginLaw family) :
    Σ' g : Q', ((0 : Q') < g) ×' (g ≤ law.g₁) ×'
      (nomeThreshold ≤ fineWeight family g) ×' (nomeThreshold ≤ blockedWeight family g) := by
  let g := Q'.min' law.g₁ guardThreshold
  have hg : (0 : Q') < g := by
    unfold g Q'.min'
    split
    · exact law.g₁_pos
    · exact (by decide : (0 : Q') < guardThreshold)
  exact ⟨g, hg, Q'.min_le_left' _ _,
    fine_nome_ge_threshold family law g hg (Q'.min_le_left' _ _) (Q'.min_le_right' _ _),
    blocked_nome_ge_threshold family law g hg (Q'.min_le_left' _ _) (Q'.min_le_right' _ _)⟩

end YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction

#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.face_character_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.testPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.test_supported
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.test_square_haar
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.test_square_character_haar
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.tail_one
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.test_remainder_haar
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.interval_cap_constraint
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.nomeThreshold
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.no_small_interval
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.no_allCutoff_intervals
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.fine_nome_ge_threshold
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.blocked_nome_ge_threshold
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.afObstructionWitness
