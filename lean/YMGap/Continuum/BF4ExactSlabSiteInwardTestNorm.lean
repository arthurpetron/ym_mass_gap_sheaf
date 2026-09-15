/-
# Original-action normalization of the inward site test

The inward test's site quadratic is bounded by its unchanged syntactic
square cap in the FULL original normalized heat action. The original
partition cancels exactly, at each cutoff; there is no volume-dependent
reciprocal loss in the resulting estimate. Its mixed site form is pinned
to the original zero-lag reflected form after cutoff removal and along the
existing thermodynamic sequence.

These are the concrete test norm and same-object pins needed for site
Cauchy--Schwarz. The transfer-relative inequality itself, its extension to
the completed first argument, range/time-zero, physical normalization and
the continuum/all-group Clay target remain separate.
-/

import YMGap.Continuum.BF4ExactSlabSiteInwardTest

namespace YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSiteInwardTest
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm (formLimit)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_upper {blocks : Nat} {p W : RatPoly} {c : Q'}
    (P : Certificate blocks (polyAdd (cap c) (polyNeg p))) (H : Certificate blocks W) :
    quaternionHaar blocks (polyMul p W) ≤ c*quaternionHaar blocks W := by
  have he : quaternionHaar blocks (polyMul (polyAdd (cap c) (polyNeg p)) W) ≈
      c*quaternionHaar blocks W + -(quaternionHaar blocks (polyMul p W)) := by
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c W)) (quaternionHaar_polySmul _ _ _))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
          (by decide) (fun | 0 => p | _ => W))) (haar_neg _ _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (P.mul H).haar_nonnegative (Q'.le_of_eqv he))

section Normalization

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (extent : Nat) (ids : List Nat) (hids : ∀ id,id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
  (p : RatPoly) (c : Q')
  (P : Certificate (boundaryCompleteSlabLinks extent).length (polyAdd (cap c) (polyNeg p)))

include P in
/-- All original face weights and the SAME finite partition are retained. -/
theorem finite_upper (K : Nat) : finiteValue w hw0 hw1 hsmall hd extent ids hids p K ≤ c := by
  have hZ := faceProductCertificate (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall (Q'.le_of_lt hd) K extent ids hids
  have h := weighted_upper P hZ
  unfold finiteValue PositiveRationalCauchyReciprocal.term
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (Q'.recipPos_pos _ _))) ?_
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ _)) (Q'.mul_one_eqv _)))

include P in
theorem expectation_upper : leEv (expectation w hw0 hw1 hsmall hd extent ids hids p) (ofQ' c) :=
  leEv_of_convergesTo_le (finite_converges w hw0 hw1 hsmall hd extent ids hids p) (convergesTo_const _)
    (fun K => leEv_ofQ'_of_approx_ge (fun _ => finite_upper w hw0 hw1 hsmall hd extent ids hids p c P K))

theorem expectation_padded_congr {a b : RatPoly}
    (h : PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length a b)
    (ha : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length a)
    (hb : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length b) :
    Equiv (expectation w hw0 hw1 hsmall hd extent ids hids a)
      (expectation w hw0 hw1 hsmall hd extent ids hids b) := by
  have hn := Equiv_of_ofQ'_limit_close
    (numerator_converges w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids a)
    (numerator_converges w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids b)
    (fun epsilon he => ⟨0, fun K _ => eqv_close
      ((PaddedPolynomialCoeffEqv.mul h (.refl _ (polynomialProduct (faceHeatPolynomial w K extent) ids))).haar
        (supported_polyMul ha (heatProduct_supported w K _ _))
        (supported_polyMul hb (heatProduct_supported w K _ _))) epsilon he⟩)
  exact Pivot2.mul_congr_left hn

end Normalization

private theorem congr_two {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a=a') (hb : b=b') : f a b = f a' b' := by cases ha; cases hb; rfl

private theorem upper_bound {base : Nat} : ∀ e : PlaquetteExpression base,
    bound (fromUpper (bulkAtTime 1 ⟨0, by decide⟩ e)) = BF4ExactSlabPlaquetteUniformSquareBound.bound e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e f => congr_two sumBound (upper_bound e) (upper_bound f)
  | .mul e f => congr_two (fun a b : Q' => a*b) (upper_bound e) (upper_bound f)
  | .smul c e => congrArg (fun a : Q' => (c*c)*a) (upper_bound e)

def upperSquareBound {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    SquareBound (blockCount (base+1+margin))
      (evenEvaluate margin (fromUpper (bulkAtTime 1 ⟨0, by decide⟩ e)))
      (BF4ExactSlabPlaquetteUniformSquareBound.bound e) := by
  rw [← upper_bound e]
  exact evenSquareBound margin _

/-- This is the pinned polynomial image of the actual site quadratic. -/
def diagonal {base : Nat} (margin : Nat) (e : PlaquetteExpression base) : RatPoly :=
  polyMul (evenEvaluate margin (fromUpper (bulkAtTime 1 ⟨0, by decide⟩ e))) (evenEvaluate margin (inward e))

theorem diagonal_pin {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    PaddedPolynomialCoeffEqv (blockCount (base+1+margin))
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent (base+1+margin)) (evenEvaluate margin (inward e)))
        (evenEvaluate margin (inward e))) (diagonal margin e) :=
  PaddedPolynomialCoeffEqv.mul (inward_reflection margin e) (.refl _ _)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  {base : Nat} (margin : Nat) (e f : PlaquetteExpression base)

local notation "radius" => base+1+margin
local notation "extent" => adjacentEvenExtent radius
local notation "faces" => slabPhysicalFaceEdges extent

/-- The cap names its source dependence; it does not depend on margin, cutoff or w. -/
theorem diagonal_bound :
    leEv (expectation w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) (diagonal margin f))
      (ofQ' (BF4ExactSlabPlaquetteUniformSquareBound.bound f)) :=
  expectation_upper w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) _ _
    ((upperSquareBound margin f).cross (inwardSquareBound margin f))

/-- Bound on the literal site form, with the same action and normalization. -/
theorem site_diagonal_bound :
    leEv (expectation w hw0 hw1 hsmall hd extent faces (fun _ hi => hi)
      (polyMul (reflectCorrectedSlabPolynomial extent (evenEvaluate margin (inward f))) (evenEvaluate margin (inward f))))
      (ofQ' (BF4ExactSlabPlaquetteUniformSquareBound.bound f)) :=
  leEv_trans (leEv_of_equiv (expectation_padded_congr w hw0 hw1 hsmall hd extent faces (fun _ hi => hi)
    (diagonal_pin margin f)
    (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (inwardSquareBound margin f).support)
    (supported_polyMul (upperSquareBound margin f).support (inwardSquareBound margin f).support)))
    (diagonal_bound w hw0 hw1 hsmall hd margin f)

/-- The actual site insertion, not a newly postulated bilinear form. -/
def mixedInsertion : RatPoly :=
  polyMul (reflectCorrectedSlabPolynomial extent (evenEvaluate margin (inward f)))
    (evenEvaluate margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e)))

theorem mixed_expectation_pin :
    Equiv (expectation w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) (mixedInsertion margin e f))
      (evenMean w hw0 hw1 hsmall hd
        (reflectedProduct (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e)) margin) :=
  expectation_padded_congr w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) (mixed_insertion_pin margin e f)
    (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _)
      (evenSquareBound margin (fromLower (bulkAtTime 1 ⟨0, by decide⟩ e))).support)
    (evenSquareBound margin _).support

def mixedSequence {base : Nat} (e f : PlaquetteExpression base) : Nat → CReal :=
  fun margin => expectation nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2
      (adjacentEvenExtent (base+1+margin)) (slabPhysicalFaceEdges (adjacentEvenExtent (base+1+margin)))
      (fun _ hi => hi) (mixedInsertion margin e f)

/-- Source-dependent volume threshold, retained as data rather than chosen from convergence. -/
def mixedVolumeModulus {base : Nat} (e f : PlaquetteExpression base) (epsilon : Q') : Nat :=
  evenVolumeModulus (reflectedProduct (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e))
    (HalfPow.half*epsilon)

theorem mixed_close {base : Nat} (e f : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat) (hm : mixedVolumeModulus e f epsilon ≤ margin) :
    ∃ N : Nat, ∀ n,N ≤ n →
      (mixedSequence e f margin).approx n ≤ (formLimit (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e)).approx n+epsilon ∧
      (formLimit (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e)).approx n ≤ (mixedSequence e f margin).approx n+epsilon := by
  have hh := ExpNeg.half_mul_pos epsilon he
  obtain ⟨N,hN⟩ := evenSequence_close _ (HalfPow.half*epsilon) hh margin hm
  obtain ⟨M,hM⟩ := (mixed_expectation_pin nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2 margin e f).symm
    (HalfPow.half*epsilon) hh
  have chain (a b c : Q') (hab : a ≤ b+HalfPow.half*epsilon) (hbc : b ≤ c+HalfPow.half*epsilon) :
      a ≤ c+epsilon :=
    Q'.le_trans' _ _ _ hab (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hbc)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)))))
  refine ⟨max N M, fun n hn => ?_⟩
  have hs := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hi := hM n (Nat.le_trans (Nat.le_max_right _ _) hn)
  exact ⟨chain _ _ _ hi.2 hs.1, chain _ _ _ hs.2 hi.1⟩

/-- At the existing fixed nome, the limit is the EXISTING original formLimit. -/
theorem mixed_thermodynamic_converges {base : Nat} (e f : PlaquetteExpression base) :
    ConvergesTo (mixedSequence e f)
      (formLimit (bulkAtTime 1 ⟨0, by decide⟩ f) (bulkAtTime 1 ⟨0, by decide⟩ e)) :=
  fun epsilon he => ⟨mixedVolumeModulus e f epsilon, fun margin hm => mixed_close e f epsilon he margin hm⟩

end YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm

#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.finite_upper
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.expectation_upper
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.expectation_padded_congr
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.upperSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.diagonal
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.diagonal_pin
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.diagonal_bound
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.site_diagonal_bound
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.mixedInsertion
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.mixed_expectation_pin
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.mixedSequence
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.mixedVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.mixed_close
#print axioms YMGap.Continuum.BF4ExactSlabSiteInwardTestNorm.mixed_thermodynamic_converges
