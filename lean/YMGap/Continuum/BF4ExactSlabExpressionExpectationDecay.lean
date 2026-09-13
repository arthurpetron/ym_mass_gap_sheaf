/-
# ORIGINAL inter-volume decay for arbitrary finite plaquette expressions

The connected finite-box probe is constructed, not assumed. Its fixed size
M(base) and link count determine an explicit support-dependent amplitude.
The original normalized expectations satisfy

  |E_(m+p)(e) - E_m(e)| <= A(w,base,e) * s(w)^(m+1-M(base)).

Natural subtraction truncates at zero. The exponent tends to infinity with
the INNER margin m, uniformly in further OUTER padding p. The statement
includes finite products and mixed plaquette moments, at explicitly guarded
small nome. It is not a beta-uniform or physical spectral-gap assertion.
-/

import YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression

namespace YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
open YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabActiveCoreCount
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

def boxSize (base : Nat) : Nat :=
  let n := centralExtent base+1
  (n*n*n*n)*6

def boxLinkCount (base : Nat) : Nat :=
  let n := centralExtent base+1
  (n*n*n*n)*24

def boxCount (base : Nat) : Nat := 2^boxSize base * 625^boxSize base

def boxBudget (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (base d : Nat) : Q' :=
  probePrefactor w hd (boxLinkCount base) * tailBudget (boxCount base) 625 d (adjustedCoreRate w hd) hs

def boxAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (base : Nat) : Q' :=
  (probePrefactor w hd (boxLinkCount base) * Q'.ofNat (boxCount base)) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)

def expressionAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (e : PlaquetteExpression base) : Q' :=
  ((bound e+1)+(bound e+1))*boxAmplitude w hd hs base

theorem shifted_budget_pin (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (base shift d : Nat) :
    summedBoundaryBudget (shiftedBoxProbe (centralExtent base+1) shift (Nat.zero_lt_succ _)) w hd hs d =
      boxBudget w hd hs base d := by
  unfold summedBoundaryBudget countPrefactor boxBudget
  rw [shiftedBoxLinks_length, shiftedBoxProbe_size]
  rfl

theorem boxBudget_factor (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (base d : Nat) :
    Q'.eqv (boxBudget w hd hs base d)
      (boxAmplitude w hd hs base * (entropyRate 625 (adjustedCoreRate w hd))^d) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun i => if i = 0 then probePrefactor w hd (boxLinkCount base) else if i = 1 then Q'.ofNat (boxCount base)
      else if i = 2 then (entropyRate 625 (adjustedCoreRate w hd))^d
      else Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs))

theorem origin_physical (base : Nat) : originFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base) :=
  (mem_boundaryCompleteSlabPlaquettes _ _).mpr ⟨origin_mem (Nat.zero_lt_succ _), Nat.zero_le _⟩

def expressionMean (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : CReal :=
  expectation w hw0 hw1 (base+margin) (shiftedExpression margin e)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

theorem expressionMean_difference_pin {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    Equiv (CReal.sub (expressionMean w hw0 hw1 e (margin+padding)) (expressionMean w hw0 hw1 e margin))
      (expectationDifference w hw0 hw1 (base+margin) padding (shiftedExpression margin e)) := by
  have ht : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length (shiftedExpression (margin+padding) e) := by
    simpa only [Nat.add_assoc] using shiftedExpression_supported (margin+padding) e
  have h := expectation_prefix w hw0 hw1 ((base+margin)+padding) (shiftedExpression_image margin padding e)
    ((slabEmbedding (base+margin) padding).polynomial_supported _) ht
  have hsub := CReal.sub_congr_left
    (y := expectation w hw0 hw1 (base+margin) (shiftedExpression margin e)) h.symm
  simpa only [expressionMean, expectationDifference, Nat.add_assoc] using hsub

/-- Every geometric and observable premise is constructed for the existing expression. -/
theorem expressionMean_difference_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    leEv (CReal.abs (CReal.sub (expressionMean w hw0 hw1 e (margin+padding)) (expressionMean w hw0 hw1 e margin)))
      (ofQ' (expressionAmplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base))) := by
  let extent := centralExtent ((base+margin)+padding)
  let q := shiftedExpression (margin+padding) e
  let c := bound e+1
  let links := (boxLinks (centralExtent base+1)).map (shiftLink (margin+padding) (margin+padding))
  let probe := shiftedBoxProbe (centralExtent base+1) (margin+padding) (Nat.zero_lt_succ _)
  let P : Interval (boundaryCompleteSlabLinks extent).length q c := by
    simpa only [extent, Nat.add_assoc] using Interval.ofSquare (shiftedExpressionBound (margin+padding) e)
  have hl : LinkLocal extent links q := by
    simpa only [extent, Nat.add_assoc] using shiftedExpression_local (margin+padding) e
  have hfinite (K : Nat) := shifted_base_boundary_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    hsmall hd hs K base margin padding originFace (origin_physical base) q c P links probe hl rfl
  have hb (K : Nat) : Q'.abs (boundaryNumerator w (base+margin) padding q K) ≤
      (expressionAmplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base)) *
        (fullMoment w K (base+margin) padding polyOne * interiorSequence w (base+margin) padding polyOne K) := by
    have h := hfinite K
    change Q'.abs _ ≤ ((c+c)*summedBoundaryBudget
      (shiftedBoxProbe (centralExtent base+1) (margin+padding) (Nat.zero_lt_succ _)) w hd hs
      (margin+1-(shiftedBoxProbe (centralExtent base+1) (margin+padding) (Nat.zero_lt_succ _)).animal.support.length))*_ at h
    rw [shiftedBoxProbe_size, shifted_budget_pin] at h
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (c+c) _ _ (boxBudget_factor w hd hs base _))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))
  have h := expectationDifference_bound_of_prefix w hw0 hw1 (base+margin) padding
    (shiftedExpression margin e) (shiftedExpression_supported margin e) q P.support
    (shiftedExpression_image margin padding e) _ hb
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (expressionMean_difference_pin w hw0 hw1 e margin padding))) h

theorem existingNome_expressionMean_difference_bound {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hw0 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    let hw1 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    leEv (CReal.abs (CReal.sub (expressionMean w hw0 hw1 e (margin+padding)) (expressionMean w hw0 hw1 e margin)))
      (ofQ' (expressionAmplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base))) :=
  expressionMean_difference_bound _ BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2 BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    e margin padding

end YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay

#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.boxSize
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.boxLinkCount
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.boxCount
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.boxBudget
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.boxAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.expressionAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.shifted_budget_pin
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.boxBudget_factor
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.origin_physical
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.expressionMean
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.expressionMean_difference_pin
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.expressionMean_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay.existingNome_expressionMean_difference_bound
