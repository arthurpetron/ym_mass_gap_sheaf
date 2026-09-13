/-
# ORIGINAL normalized comparison for finite spacetime plaquette expressions

Both sides of the reflection plane use the SAME original-action determinant,
partition cancellation and constructed connected box probe. The bound names
the coupling and fixed support explicitly and is uniform only in the further
outer padding. No new counting, positivity or analytic smallness input occurs.
-/

import YMGap.Continuum.BF4ExactSlabSpacetimeExpression

namespace YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
open YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

def amplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (e : SpacetimeExpression base) : Q' :=
  ((bound e+1)+(bound e+1))*boxAmplitude w hd hs base

def mean (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : SpacetimeExpression base) (margin : Nat) : CReal :=
  expectation w hw0 hw1 (base+margin) (evaluate margin e)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

theorem difference_pin {base : Nat} (e : SpacetimeExpression base) (margin padding : Nat) :
    Equiv (CReal.sub (mean w hw0 hw1 e (margin+padding)) (mean w hw0 hw1 e margin))
      (expectationDifference w hw0 hw1 (base+margin) padding (evaluate margin e)) := by
  have ht : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent ((base+margin)+padding))).length
      (evaluate (margin+padding) e) := by simpa only [Nat.add_assoc] using supported (margin+padding) e
  have h := expectation_prefix w hw0 hw1 ((base+margin)+padding) (image_prefix margin padding e)
    ((slabEmbedding (base+margin) padding).polynomial_supported _) ht
  have hsub := CReal.sub_congr_left (y := expectation w hw0 hw1 (base+margin) (evaluate margin e)) h.symm
  simpa only [mean, expectationDifference, Nat.add_assoc] using hsub

theorem difference_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (e : SpacetimeExpression base) (margin padding : Nat) :
    leEv (CReal.abs (CReal.sub (mean w hw0 hw1 e (margin+padding)) (mean w hw0 hw1 e margin)))
      (ofQ' (amplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base))) := by
  let extent := centralExtent ((base+margin)+padding)
  let q := evaluate (margin+padding) e
  let c := bound e+1
  let links := (boxLinks (centralExtent base+1)).map (shiftLink (margin+padding) (margin+padding))
  let probe := shiftedBoxProbe (centralExtent base+1) (margin+padding) (Nat.zero_lt_succ _)
  let P : Interval (boundaryCompleteSlabLinks extent).length q c := by
    simpa only [extent, Nat.add_assoc] using Interval.ofSquare (squareBound (margin+padding) e)
  have hl : LinkLocal extent links q := by simpa only [extent, Nat.add_assoc] using linkLocal (margin+padding) e
  have hfinite (K : Nat) := shifted_base_boundary_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    hsmall hd hs K base margin padding originFace (origin_physical base) q c P links probe hl rfl
  have hb (K : Nat) : Q'.abs (boundaryNumerator w (base+margin) padding q K) ≤
      (amplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base)) *
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
    (evaluate margin e) (supported margin e) q P.support (image_prefix margin padding e) _ hb
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (difference_pin w hw0 hw1 e margin padding))) h

theorem existingNome_difference_bound {base : Nat} (e : SpacetimeExpression base) (margin padding : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hw0 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    let hw1 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    leEv (CReal.abs (CReal.sub (mean w hw0 hw1 e (margin+padding)) (mean w hw0 hw1 e margin)))
      (ofQ' (amplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base))) :=
  difference_bound _ BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2 BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    e margin padding

end YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay.mean
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay.difference_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay.difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay.existingNome_difference_bound
