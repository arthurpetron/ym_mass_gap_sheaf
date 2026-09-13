/-
# The original law becomes insensitive to an off-center spacetime placement

All observable and geometric premises are constructed for the original
spacetime expression. The compared original normalized expectations satisfy

  |mean(embed(P,e),m) - mean(e,m)| <= A(w,e) s(w)^(m+1-M(base)).

The coefficient retains the ORIGINAL support size and is independent of
the placement's padding and time offset. The two finite slabs need not
define identical laws. This is their shrinking difference as the inner
margin grows, with the original coupling guard explicitly retained.
-/

import YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression
import YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison
import YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay

namespace YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison (expectation_prefix)
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier
open YMGap.Continuum.BF4ExactSlabOffsetSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison
open YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (SpacetimeExpression evaluate bound squareBound supported)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay (mean amplitude)
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
  (boxSize boxBudget boxBudget_factor origin_physical)
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabActiveCoreCount (countPrefactor)
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget (summedBoundaryBudget)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem shifted_budget_pin (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (base space time d : Nat) :
    summedBoundaryBudget (shiftedBoxProbe (centralExtent base+1) space time (Nat.zero_lt_succ _)) w hd hs d =
      boxBudget w hd hs base d := by
  unfold summedBoundaryBudget countPrefactor boxBudget
  rw [shiftedBoxLinks_length, shiftedBoxProbe_size]
  rfl

variable (P : Placement) (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

theorem difference_pin (e : SpacetimeExpression P.half) (margin : Nat) :
    Equiv (CReal.sub (mean w hw0 hw1 (embed P e) margin) (mean w hw0 hw1 e margin))
      (expectationDifference (grow P margin) w hw0 hw1 (evaluate margin e)) := by
  have ht : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (grow P margin).target).length
      (evaluate margin (embed P e)) := by
    simpa only [grow, Placement.target, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using supported margin (embed P e)
  have h := expectation_prefix w hw0 hw1 ((P.half+margin)+P.padding) (image_prefix P margin e)
    ((grow P margin).embedding.polynomial_supported _) ht
  have hsub := CReal.sub_congr_left (y := mean w hw0 hw1 e margin) h.symm
  simpa only [mean, expectationDifference, grow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsub

/-- No observable, locality or protected-root hypothesis remains unconstructed. -/
theorem difference_bound (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (e : SpacetimeExpression P.half) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (mean w hw0 hw1 (embed P e) margin) (mean w hw0 hw1 e margin)))
      (ofQ' (amplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize P.half))) := by
  let extent := (grow P margin).target
  let q := evaluate margin (embed P e)
  let c := bound e+1
  let links := (boxLinks (centralExtent P.half+1)).map (shiftLink (P.padding+margin) (P.time+margin))
  let probe := shiftedBoxProbe (centralExtent P.half+1) (P.padding+margin) (P.time+margin) (Nat.zero_lt_succ _)
  have hc : Interval (boundaryCompleteSlabLinks extent).length q c := by
    simpa only [extent, q, c, grow, Placement.target, bound_embed,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Interval.ofSquare (squareBound margin (embed P e))
  have hl : LinkLocal extent links q := by
    simpa only [extent, links, q, grow, Placement.target, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using evaluate_embed_local P margin e
  have hr : ProtectedRoot (grow P margin) margin probe.animal.root := by
    have h := shifted_base_protected (grow P margin) margin rfl (origin_physical P.half)
    simpa only [probe, shiftedBoxProbe_root, grow, shiftFace_comp, Nat.add_comm] using h
  have h := protected_expectationDifference_bound (grow P margin) w hw0 hw1 hsmall hd hs margin
    (evaluate margin e) (supported margin e) q hc.support (image_prefix P margin e) c hc links probe hl hr
  dsimp only [probe] at h
  rw [shiftedBoxProbe_size, shifted_budget_pin] at h
  have hb : Q'.eqv ((c+c)*boxBudget w hd hs P.half (margin+1-boxSize P.half))
      (amplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize P.half)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (c+c) _ _ (boxBudget_factor w hd hs P.half _))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (difference_pin P w hw0 hw1 e margin)))
    (leEv_trans h (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hb)))

theorem existingNome_difference_bound (e : SpacetimeExpression P.half) (margin : Nat) :
    let w := BF4ExactSlabPlaquetteSmallNomeCertificate.nome
    let hw0 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    let hw1 := BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one
    let hd := BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    let hs := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    leEv (CReal.abs (CReal.sub (mean w hw0 hw1 (embed P e) margin) (mean w hw0 hw1 e margin)))
      (ofQ' (amplitude w hd hs e * (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize P.half))) :=
  difference_bound P _ BF4ExactSlabPlaquetteSmallNomeCertificate.nome_pos
    BF4ExactSlabPlaquetteSmallNomeCertificate.nome_lt_one BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2 BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    e margin

end YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay

#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay.shifted_budget_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay.difference_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay.difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetSpacetimeDecay.existingNome_difference_bound
