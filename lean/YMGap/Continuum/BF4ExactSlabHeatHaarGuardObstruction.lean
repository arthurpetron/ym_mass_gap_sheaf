/-
# An original-Haar square test excludes even EVENTUAL small heat intervals

On any actual slab plaquette, r=1+chi_1 satisfies H(r^2)=2 and
H(r^2 chi_1)=2. The cutoff-one positive-label heat remainder therefore
has H(r^2 R)=4*w^3. At every K>=2 its moment is exactly
4*w^3+3*w^8: the character recurrence kills all spins above two.
At w>=7/8 no original Haar Interval for the FULL positive-label remainder
can have cap <=1, even after an arbitrary cutoff threshold and with a
cutoff-dependent cap. This tests the actual polynomial and certificate
semantics, not the coarse cap 128*w^3 or pointwise positivity.

The obstruction is to comparison of the FULL interaction with one, not to
smallness of an OMITTED late tail relative to a retained head. It does not
exclude a different reference action, an AF law or Yang--Mills existence.
It supplies no
physical-scale family, continuum limit or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.BF4SmallNomeAFGuardObstruction
import YMGap.Continuum.PolynomialWeightedSumBounds

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

private theorem first_character_mul_succ (p : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p (n+1)))
      (polyAdd (characterPolynomial p (n+2)) (characterPolynomial p n)) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p (n+1))
  let b := characterPolynomial p n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (RatPolyCoeffEqv.refl b))

theorem first_character_pair {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (n : Nat) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (characterPolynomial (faceScalar extent id) 1)
        (characterPolynomial (faceScalar extent id) (n+1))) ≈ (if n = 0 then 1 else 0) := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (first_character_mul_succ (faceScalar extent id) n)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  cases n with
  | zero =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (face_character_haar_zero hi 2 (by decide)) (haar_one _)) (by decide)
  | succ n =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (face_character_haar_zero hi (n+1+2) (by omega))
        (face_character_haar_zero hi (n+1) (by omega))) (by simp only [Nat.succ_ne_zero, ↓reduceIte]; decide)

/-- Exact original square-test moments at EVERY spin >=2. Only spin two survives. -/
theorem test_square_character_haar_high {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (n : Nat) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (characterPolynomial (faceScalar extent id) (n+2))) ≈ (if n = 0 then 1 else 0) := by
  let a := characterPolynomial (faceScalar extent id) 1
  let b := characterPolynomial (faceScalar extent id) (n+2)
  have hexpand : RatPolyCoeffEqv
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id)) b)
      (polyAdd b (polyAdd (polySmul 2 (polyMul a b)) (polyMul a (polyMul a b)))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul texpr texpr) (.var 1))
      (.add (.var 1) (.add (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.mul (.var 0) (.var 1))))) (by decide)
      (fun i => if i = 0 then a else b)).trans
      ((RatPolyCoeffEqv.refl b).add ((cap_mul_left 2 _).add (RatPolyCoeffEqv.refl _)))
  have hlast := ((first_character_mul_succ (faceScalar extent id) (n+1)).mul_left a).trans
    (RatPolyCoeffEqv.mul_add_right _ _ _)
  refine Q'.eqv_trans _ _ _ (haar_of_coeff
    (hexpand.trans ((RatPolyCoeffEqv.refl b).add ((RatPolyCoeffEqv.refl _).add hlast)))) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (face_character_haar_zero hi (n+2) (by omega))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (first_character_pair hi (n+1))))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (first_character_pair hi (n+2)) (first_character_pair hi n)))))) ?_
  cases n <;> simp only [Nat.succ_ne_zero, ↓reduceIte] <;> decide

private theorem test_heatTerm_high (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (n : Nat) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (faceHeatTerm w extent id (n+3))) ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (test_square_character_haar_high hi (n+1)))
        (Q'.mul_zero_eqv _)))

theorem inserted_sum_zero (blocks : Nat) (p : RatPoly) (f : Nat → RatPoly) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → quaternionHaar blocks (polyMul p (f i)) ≈ 0) →
      quaternionHaar blocks (polyMul p (finitePolySum f ids)) ≈ 0
  | [], _ => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right p)
  | i :: ids, h =>
      Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h i List.mem_cons_self)
            (inserted_sum_zero blocks p f ids (fun j hj => h j (List.mem_cons_of_mem i hj)))) (by decide)))

private theorem test_heatTail_high (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (N : Nat) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (faceHeatTail w extent id 3 N)) ≈ 0 := by
  apply inserted_sum_zero
  intro i _
  rw [Nat.add_comm 3 i]
  exact test_heatTerm_high w hi i

/-- Increasing the cutoff does not remove the low-spin obstruction: the
complete positive-label remainder has this SAME square moment at every K>=2. -/
theorem test_remainder_haar_late (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) (hK : 2 ≤ K) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (faceHeatTail w extent id 1 K)) ≈ 4 * qpow w 3 + 3 * qpow w 8 := by
  have hsplit := PolynomialWeightedSumBounds.sum_range_add (fun i => faceHeatTerm w extent id (1+i)) 2 (K-2)
  rw [Nat.add_sub_of_le hK] at hsplit
  unfold faceHeatTail
  rw [hsplit]
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  have htail : quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul (testPolynomial extent id) (testPolynomial extent id))
        (finitePolySum (fun i => faceHeatTerm w extent id (1+(2+i))) (List.range (K-2)))) ≈ 0 := by
    simp only [← Nat.add_assoc]
    exact test_heatTail_high w hi (K-2)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ?_ htail) (Q'.eqv_of_eq (Q'.add_zero' _))
  simp only [show List.range 2 = [0,1] from rfl, finitePolySum, Nat.reduceAdd,
    polyAdd, polyZero, List.append_nil]
  change quaternionHaar _ (polyMul _ (polyAdd (faceHeatTerm w extent id 1) (faceHeatTerm w extent id 2))) ≈ _
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · simpa only [tail_one] using test_remainder_haar w hi
  · refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (test_square_character_haar_high hi 0))
      (Q'.mul_one_eqv _)

theorem interval_cap_constraint_late (w c : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) (hK : 2 ≤ K)
    (R : Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 K) c) :
    4 * qpow w 3 + 3 * qpow w 8 ≤ c * 2 := by
  have h := R.weighted_haar_bound (Certificate.square (testPolynomial extent id) (test_supported _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (test_remainder_haar_late w hi K hK))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (test_square_haar hi)))))

/-- Even EVENTUAL full-interaction intervals with cap<=1 fail at these nomes. -/
theorem no_small_interval_late {w c : Q'} (hw : nomeThreshold ≤ w) (hc : c ≤ 1)
    {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) (hK : 2 ≤ K)
    (R : Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 K) c) : False := by
  have hw0 : (0 : Q') ≤ w := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ nomeThreshold) hw
  have hlow : (2 : Q') < 4 * qpow w 3 :=
    lt_of_lt_of_le (by decide : (2 : Q') < 4 * qpow nomeThreshold 3)
      (Q'.mul_le_mul_of_nonneg_left _ _ 4
        (qpow_mono_base (by decide : (0 : Q') ≤ nomeThreshold) hw 3) (by decide))
  have hu : 4 * qpow w 3 ≤ 2 :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 3) (RGTransport.qpow_nonneg w hw0 8)))
      (Q'.le_trans' _ _ _ (interval_cap_constraint_late w c hi K hK R)
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ 2 hc (by decide))
          (Q'.le_of_eqv (Q'.one_mul_eqv 2))))
  exact Int.not_lt_of_ge hu hlow

theorem no_eventual_small_intervals {w : Q'} (hw : nomeThreshold ≤ w)
    {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) (K0 : Nat) (c : Nat → Q')
    (hc : ∀ K, K0 ≤ K → c K ≤ 1)
    (R : ∀ K, K0 ≤ K → Interval (boundaryCompleteSlabLinks extent).length (faceHeatTail w extent id 1 K) (c K)) :
    False := no_small_interval_late hw (hc (max K0 2) (Nat.le_max_left _ _)) hi
      (max K0 2) (Nat.le_max_right _ _) (R (max K0 2) (Nat.le_max_left _ _))

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
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.first_character_pair
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.inserted_sum_zero
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
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.test_square_character_haar_high
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.test_remainder_haar_late
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.interval_cap_constraint_late
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.no_small_interval_late
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.no_eventual_small_intervals
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.fine_nome_ge_threshold
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.blocked_nome_ge_threshold
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction.afObstructionWitness
