/-
# The SAME spacetime expressions on odd and adjacent-even slabs

Evaluate the existing physical spacetime syntax at the same translated
coordinates in the adjacent even slab. Its original holonomies, square cap,
link locality and coordinate-inclusion image are proved by recursion.
The existing translated box probe has fixed size: the odd/even comparison
therefore has exactly the previous spacetime amplitude and geometric rate.

At nome 1/1024 the even expectations converge to the EXISTING odd-family
meanLimit, with an explicit volume threshold. No new thermodynamic state
or limit is chosen. This prepares the one-step site-positivity application;
that reflection identity and completed T1 positivity are separate consumers.
-/

import YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison
import YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit

namespace YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay (shiftedFace_physical shiftedCharacter)
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression (shifted_face_links)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabCoordinateInclusion
open YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabSummableCoreRate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

def evenEvaluate {base : Nat} (margin : Nat) : SpacetimeExpression base → RatPoly
  | .unit => polyOne
  | .character face _ spin => characterPolynomial
      (correctedSlabPlaquettePolynomial (adjacentEvenExtent (base+margin)) (shiftFace margin margin face)).scalar spin
  | .add e f => polyAdd (evenEvaluate margin e) (evenEvaluate margin f)
  | .mul e f => polyMul (evenEvaluate margin e) (evenEvaluate margin f)
  | .smul c e => polySmul c (evenEvaluate margin e)

def evenSquareBound {base : Nat} (margin : Nat) : ∀ e : SpacetimeExpression base,
    SquareBound (boundaryCompleteSlabLinks (adjacentEvenExtent (base+margin))).length (evenEvaluate margin e) (bound e)
  | .unit => .one _
  | .character _ hf spin => character_squareBound
      (.scalar (supported_slabPlaquette _ _)
        (haarNorm_slabPlaquette (face_mem (odd_even_room _) (shiftedFace_physical hf margin)))) spin
  | .add e f => (evenSquareBound margin e).add (evenSquareBound margin f)
  | .mul e f => (evenSquareBound margin e).mul (evenSquareBound margin f)
  | .smul c e => (evenSquareBound margin e).smul c

theorem evenLocal {base : Nat} (margin : Nat) : ∀ e : SpacetimeExpression base,
    LinkLocal (adjacentEvenExtent (base+margin))
      ((boxLinks (centralExtent base+1)).map (shiftLink margin margin)) (evenEvaluate margin e)
  | .unit => BlockLocal.one _ _
  | .character _ hf spin => LinkLocal.mono ((face_scalar_local _ _).character spin) (shifted_face_links hf margin)
  | .add e f => (evenLocal margin e).add (evenLocal margin f)
  | .mul e f => (evenLocal margin e).mul (evenLocal margin f)
  | .smul c e => (evenLocal margin e).smul c

theorem inclusion_pin {base : Nat} (margin : Nat) : ∀ e : SpacetimeExpression base,
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (adjacentEvenExtent (base+margin))).length
      ((embedding (odd_even_room (base+margin))).polynomial (evaluate margin e)) (evenEvaluate margin e)
  | .unit => (embedding (odd_even_room _)).polynomial_one_prefix
  | .character _ hf spin => character_pin (odd_even_room _) (shiftedFace_physical hf margin) spin
  | .add e f => by
      change QuaternionPrefixPolynomialEqv _ ((embedding _).polynomial (polyAdd _ _)) _
      rw [BlockEmbedding.polynomial_add]
      exact (inclusion_pin margin e).append (inclusion_pin margin f)
  | .mul e f => by
      change QuaternionPrefixPolynomialEqv _ ((embedding _).polynomial (polyMul _ _)) _
      rw [BlockEmbedding.polynomial_mul]
      exact (inclusion_pin margin e).mul (inclusion_pin margin f)
  | .smul c e => by
      change QuaternionPrefixPolynomialEqv _ ((embedding _).polynomial (polySmul c _)) _
      rw [BlockEmbedding.polynomial_smul]
      exact (inclusion_pin margin e).smul c

def evenMean (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    {base : Nat} (e : SpacetimeExpression base) (margin : Nat) : CReal :=
  expectation w hw0 hw1 hsmall hd (adjacentEvenExtent (base+margin))
    (slabPhysicalFaceEdges (adjacentEvenExtent (base+margin))) (fun _ hi => hi) (evenEvaluate margin e)

/-- A constructed, fixed-size probe supplies every geometric premise. -/
theorem parity_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (e : SpacetimeExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (evenMean w hw0 hw1 hsmall hd e margin)
      (BF4ExactSlabSpacetimeExpectationDecay.mean w hw0 hw1 e margin)))
      (ofQ' (BF4ExactSlabSpacetimeExpectationDecay.amplitude w hd hs e *
        (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base))) := by
  let probe := shiftedBoxProbe (centralExtent base+1) margin (Nat.zero_lt_succ _)
  have hr : RootCeiling (centralExtent (base+margin)) margin probe.animal.root :=
    shifted_base_ceiling margin (origin_physical base)
  have hb := odd_even_bound (base+margin) margin w hw0 hw1 hsmall hd hs
    (evaluate margin e) (supported margin e) (evenEvaluate margin e) (evenSquareBound margin e).support
    (inclusion_pin margin e) (bound e+1) (Interval.ofSquare (evenSquareBound margin e))
    _ probe (evenLocal margin e) hr
  change leEv _ (ofQ' (((bound e+1)+(bound e+1))*summedBoundaryBudget
    (shiftedBoxProbe (centralExtent base+1) margin (Nat.zero_lt_succ _)) w hd hs
      (margin+1-(shiftedBoxProbe (centralExtent base+1) margin (Nat.zero_lt_succ _)).animal.support.length))) at hb
  rw [shiftedBoxProbe_size, shifted_budget_pin] at hb
  exact leEv_trans hb (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (boxBudget_factor w hd hs base _))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

def evenSequence {base : Nat} (e : SpacetimeExpression base) : Nat → CReal :=
  evenMean nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2 e

/-- Reuse the original support delay and computed geometric modulus. -/
def evenVolumeModulus {base : Nat} (e : SpacetimeExpression base) (epsilon : Q') : Nat :=
  BF4ExactSlabSpacetimeThermodynamicLimit.volumeModulus e (HalfPow.half * (HalfPow.half * epsilon))

theorem evenSequence_close {base : Nat} (e : SpacetimeExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat) (hm : evenVolumeModulus e epsilon ≤ margin) :
    ∃ N : Nat, ∀ n, N ≤ n →
      (evenSequence e margin).approx n ≤ (BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit e).approx n + epsilon ∧
      (BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit e).approx n ≤ (evenSequence e margin).approx n + epsilon := by
  let d := HalfPow.half * (HalfPow.half * epsilon)
  have hd : (0 : Q') < d := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)
  have hb := parity_bound nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2
    existingNome_entropyRate.2 e margin
  have hb' := leEv_trans hb (leEv_le_ofQ'_of_approx_le (fun _ =>
    BF4ExactSlabSpacetimeThermodynamicLimit.coefficient_small e d hd margin hm))
  have hl := BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_error_le e d hd margin hm
  obtain ⟨N, hN⟩ := hb' d hd
  obtain ⟨M, hM⟩ := hl d hd
  refine ⟨max N M, fun n hn => ?_⟩
  have hab := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hlb := hM n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have chain (a b c : Q') (ha : Q'.abs (a + -b) ≤ d+d) (hc : Q'.abs (c + -b) ≤ d+d) : a ≤ c+epsilon := by
    have hbc := ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm b c)) hc)
    have hsum := Q'.le_trans' _ _ _ (ExpNeg.le_add_of_abs_sub_le ha) (Q'.add_le_add_right _ _ (d+d) hbc)
    exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*epsilon)) (ExpNeg.two_halves (HalfPow.half*epsilon)))
        (ExpNeg.two_halves epsilon)))))
  exact ⟨chain _ _ _ hab hlb, chain _ _ _ hlb hab⟩

/-- Same original limit, not a separately constructed even-volume state. -/
theorem evenSequence_converges {base : Nat} (e : SpacetimeExpression base) :
    ConvergesTo (evenSequence e) (BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit e) :=
  fun epsilon he => ⟨evenVolumeModulus e epsilon, fun margin hm => evenSequence_close e epsilon he margin hm⟩

end YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenEvaluate
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenSquareBound
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenLocal
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.inclusion_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenMean
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.parity_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenSequence
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeEvenComparison.evenSequence_converges
