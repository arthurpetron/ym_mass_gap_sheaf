/-
# Volume limit of the ORIGINAL full-channel scalar dual test

The actual upper plaquette expression and the lower scalar-link product are
translated together. Their mixed insertion has a fixed box support and a
volume-independent interval cap. The existing original boundary determinant
estimate therefore gives a geometric volume modulus, with all action factors
and the same partition normalization retained.

At the existing small nome, the resulting CReal limit has square bounded by
the ORIGINAL thermodynamic reflected norm. This is a bounded auxiliary test,
not a recoding into the original state algebra. It does not yet give a test on
the completed carrier, a time-translation identity, a range estimate, a
nonzero excited state, or a continuum/physical mass-gap statement.
-/

import YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit
import YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm

namespace YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
open YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (fromUpper)
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit
open YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression (shifted_face_links)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

theorem probeFace_physical (base : Nat) :
    probeFace base ∈ boundaryCompleteSlabPlaquettes (centralExtent base) := by
  unfold probeFace
  rw [← translatedId_pin (half := base) (id := 0)
    (mem_centralLowerFaceIds.mp BF4ExactSlabPlaquetteCoordinateChannels.probeId_lower).1]
  exact slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp (probeId_translated_lower base)).1

theorem probeLinks_shift (base padding : Nat) :
    (probeLinks base).map (shiftLink padding padding) = probeLinks (base+padding) := by
  unfold probeLinks probeFace
  rw [← edgesOf_shiftFace, shiftFace_comp]

private theorem scalarProduct_image (source padding : Nat) : ∀ links : List ClusterCount4DProgress.Z4Link,
    (∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks (centralExtent source)) →
    QuaternionPrefixPolynomialEqv (blocks (source+padding))
      ((slabEmbedding source padding).polynomial (scalarProduct (centralExtent source) links))
      (scalarProduct (centralExtent (source+padding)) (links.map (shiftLink padding padding)))
  | [], _ => (slabEmbedding source padding).polynomial_one_prefix
  | link :: links, hp => by
      simp only [scalarProduct, List.map_cons, BlockEmbedding.polynomial_mul]
      exact (scalar_link_embedding (hp link List.mem_cons_self)).mul
        (scalarProduct_image source padding links (fun l hl => hp l (List.mem_cons_of_mem link hl)))

theorem bulkScalar_image (source padding : Nat) :
    QuaternionPrefixPolynomialEqv (blocks (source+padding))
      ((slabEmbedding source padding).polynomial (bulkScalar source)) (bulkScalar (source+padding)) := by
  unfold bulkScalar
  rw [← probeLinks_shift]
  exact scalarProduct_image source padding _ (fun _ h => probeLinks_physical h)

/-- Fixed original state, translated together with the fixed scalar-link test. -/
def insertion {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : RatPoly :=
  polyMul (upper (enlarge margin e)) (bulkScalar (base+margin))

def insertionInterval {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    Interval (blocks (base+margin)) (insertion e margin)
      (BF4ExactSlabSpacetimeExpression.bound (fromUpper e)+1) := by
  unfold insertion
  rw [← BF4ExactSlabSpacetimeExpression.evaluate_fromUpper]
  exact ((Interval.ofSquare (BF4ExactSlabSpacetimeExpression.squareBound margin (fromUpper e))).mul
    (bulkScalarInterval (base+margin))).changeCap (Q'.mul_one_eqv _)

theorem insertion_local {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    LinkLocal (centralExtent (base+margin))
      ((boxLinks (centralExtent base+1)).map (shiftLink margin margin)) (insertion e margin) := by
  unfold insertion
  rw [← BF4ExactSlabSpacetimeExpression.evaluate_fromUpper]
  apply (BF4ExactSlabSpacetimeExpression.linkLocal margin (fromUpper e)).mul
  apply LinkLocal.mono (bulkScalar_local (base+margin))
  intro link hl
  have hp : probeFace (base+margin) = shiftFace margin margin (probeFace base) :=
    (shiftFace_comp base base margin margin (slabPlaquetteAt 1 0)).symm
  exact shifted_face_links (probeFace_physical base) margin link (by simpa only [probeLinks, hp] using hl)

theorem insertion_image {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    QuaternionPrefixPolynomialEqv (blocks ((base+margin)+padding))
      ((slabEmbedding (base+margin) padding).polynomial (insertion e margin))
      (insertion e (margin+padding)) := by
  unfold insertion
  rw [BlockEmbedding.polynomial_mul, ← BF4ExactSlabSpacetimeExpression.evaluate_fromUpper,
    ← BF4ExactSlabSpacetimeExpression.evaluate_fromUpper]
  exact (BF4ExactSlabSpacetimeExpression.image_prefix margin padding (fromUpper e)).mul
    (by simpa only [Nat.add_assoc] using bulkScalar_image (base+margin) padding)

def mean (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : CReal :=
  testLimit w hw0 hw1 (bulkScalar (base+margin)) (enlarge margin e)

theorem mean_difference_pin (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    Equiv (CReal.sub (mean w hw0 hw1 e (margin+padding)) (mean w hw0 hw1 e margin))
      (expectationDifference w hw0 hw1 (base+margin) padding (insertion e margin)) := by
  have ht : SupportedQuaternionBlocks (blocks ((base+margin)+padding)) (insertion e (margin+padding)) := by
    simpa only [Nat.add_assoc] using (insertionInterval e (margin+padding)).support
  have h := expectation_prefix w hw0 hw1 ((base+margin)+padding) (insertion_image e margin padding)
    ((slabEmbedding (base+margin) padding).polynomial_supported _) ht
  have hsub := CReal.sub_congr_left (y := expectation w hw0 hw1 (base+margin) (insertion e margin)) h.symm
  simpa only [mean, testLimit, insertion, expectationDifference, Nat.add_assoc] using hsub

/-- Original action, all later outer paddings, with coupling and fixed support explicit. -/
theorem mean_difference_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    leEv (CReal.abs (CReal.sub (mean w hw0 hw1 e (margin+padding)) (mean w hw0 hw1 e margin)))
      (ofQ' (BF4ExactSlabSpacetimeExpectationDecay.amplitude w hd hs (fromUpper e) *
        (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base))) := by
  let extent := centralExtent ((base+margin)+padding)
  let q := insertion e (margin+padding)
  let c := BF4ExactSlabSpacetimeExpression.bound (fromUpper e)+1
  let links := (boxLinks (centralExtent base+1)).map (shiftLink (margin+padding) (margin+padding))
  let probe := shiftedBoxProbe (centralExtent base+1) (margin+padding) (Nat.zero_lt_succ _)
  let P : Interval (boundaryCompleteSlabLinks extent).length q c := by
    simpa only [extent, Nat.add_assoc] using insertionInterval e (margin+padding)
  have hl : LinkLocal extent links q := by simpa only [extent, Nat.add_assoc] using insertion_local e (margin+padding)
  have hfinite (K : Nat) := shifted_base_boundary_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    hsmall hd hs K base margin padding originFace (origin_physical base) q c P links probe hl rfl
  have hb (K : Nat) : Q'.abs (boundaryNumerator w (base+margin) padding q K) ≤
      (BF4ExactSlabSpacetimeExpectationDecay.amplitude w hd hs (fromUpper e) *
        (entropyRate 625 (adjustedCoreRate w hd))^(margin+1-boxSize base)) *
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
    (insertion e margin) (insertionInterval e margin).support q P.support (insertion_image e margin padding) _ hb
  exact leEv_trans (leEv_of_equiv (abs_equiv_congr (mean_difference_pin w hw0 hw1 e margin padding))) h

def meanSequence {base : Nat} (e : PlaquetteExpression base) : Nat → CReal :=
  mean nome nome_pos nome_lt_one e

def meanSequenceCauchy {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    QCauchy (meanSequence e margin).approx :=
  testLimitCauchy nome nome_pos nome_lt_one (bulkScalar (base+margin)) (enlarge margin e)

/-- Reuse the existing expression modulus: the scalar factor has cap one. -/
def volumeModulus {base : Nat} (e : PlaquetteExpression base) : Q' → Nat :=
  BF4ExactSlabSpacetimeThermodynamicLimit.volumeModulus (fromUpper e)

def innerModulus {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : Q' → Nat :=
  (meanSequenceCauchy e margin).M

theorem inner_regular {base : Nat} (e : PlaquetteExpression base) : RegPred (meanSequence e) (innerModulus e) :=
  fun m => (meanSequenceCauchy e m).bound

theorem sequence_difference_bound {base : Nat} (e : PlaquetteExpression base) (margin padding : Nat) :
    leEv (CReal.abs (CReal.sub (meanSequence e (margin+padding)) (meanSequence e margin)))
      (ofQ' (BF4ExactSlabSpacetimeThermodynamicLimit.amplitude (fromUpper e) * rate^(margin+1-boxSize base))) :=
  mean_difference_bound nome nome_pos nome_lt_one BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2 BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
    e margin padding

private theorem two_sided_of_abs {x y : CReal} {b : Q'}
    (h : leEv (CReal.abs (CReal.sub x y)) (ofQ' b)) :
    leRat (CReal.sub x y) b ∧ leRat (CReal.sub y x) b := by
  constructor
  · intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (Q'.le_abs_self _) (hN n hn)⟩
  · intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm (y.approx n) (x.approx n))) (hN n hn))⟩

theorem outer_cauchy {base : Nat} (e : PlaquetteExpression base) : LeRatBound (meanSequence e) (volumeModulus e) := by
  intro epsilon he m n hm hn
  have step (i j : Nat) (hij : i ≤ j) (hi : volumeModulus e epsilon ≤ i) :
      leRat (CReal.sub (meanSequence e j) (meanSequence e i)) epsilon ∧
      leRat (CReal.sub (meanSequence e i) (meanSequence e j)) epsilon := by
    have h := sequence_difference_bound e i (j-i)
    rw [Nat.add_sub_of_le hij] at h
    exact two_sided_of_abs (leEv_trans h (leEv_le_ofQ'_of_approx_le
      (fun _ => BF4ExactSlabSpacetimeThermodynamicLimit.coefficient_small (fromUpper e) epsilon he i hi)))
  rcases Nat.le_total m n with hmn | hnm
  · exact (step m n hmn hm).symm
  · exact step n m hnm hn

def meanLimit {base : Nat} (e : PlaquetteExpression base) : CReal :=
  completeLimitFromRate (meanSequence e) (volumeModulus e) (innerModulus e) (inner_regular e) (outer_cauchy e)

theorem meanLimit_converges {base : Nat} (e : PlaquetteExpression base) :
    ConvergesTo (meanSequence e) (meanLimit e) :=
  convergesTo_completeLimitFromRate _ _ _ (inner_regular e) (outer_cauchy e)
    (BF4ExactSlabSpacetimeThermodynamicLimit.volumeModulus_antitone (fromUpper e))

def meanLimitCauchy {base : Nat} (e : PlaquetteExpression base) : QCauchy (meanLimit e).approx where
  M epsilon := (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · exact diagSeqR_directed _ _ _ (inner_regular e) (outer_cauchy e) epsilon he m n hmn hm
    · exact (diagSeqR_directed _ _ _ (inner_regular e) (outer_cauchy e) epsilon he n m hnm hn).symm

theorem meanLimit_geometric_bound {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin)))
      (ofQ' (BF4ExactSlabSpacetimeThermodynamicLimit.amplitude (fromUpper e) * rate^(margin+1-boxSize base))) := by
  have ht : ConvergesTo (fun p => meanSequence e (margin+p)) (meanLimit e) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := meanLimit_converges e epsilon he
    exact ⟨N, fun n hn => hN (margin+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩
  have hsub := convergesTo_add ht (TrigAddCReal.convergesTo_neg (convergesTo_const (meanSequence e margin)))
  exact leEv_of_convergesTo_le (convergesTo_abs hsub) (convergesTo_const _)
    (fun p => sequence_difference_bound e margin p)

theorem meanLimit_error_le {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat) (hm : volumeModulus e epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin))) (ofQ' epsilon) :=
  leEv_trans (meanLimit_geometric_bound e margin) (leEv_le_ofQ'_of_approx_le
    (fun _ => BF4ExactSlabSpacetimeThermodynamicLimit.coefficient_small (fromUpper e) epsilon he margin hm))

/-- The limiting test is bounded by the SAME original thermodynamic OS norm. -/
theorem meanLimit_bound {base : Nat} (e : PlaquetteExpression base) :
    leEv (CReal.mul (meanLimit e) (meanLimit e)) (formLimit e e) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (meanLimit_converges e) (meanLimit_converges e))
    (form_converges e e)
    (fun margin => bulkScalar_limit_bound nome nome_pos nome_lt_one
      BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
      BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2 (enlarge margin e))

theorem meanLimit_add {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (meanLimit (.add e f)) (CReal.add (meanLimit e) (meanLimit f)) :=
  Equiv_of_limit_of_equal
    (fun margin => testLimit_add nome nome_pos nome_lt_one (bulkScalar (base+margin))
      (enlarge margin e) (enlarge margin f))
    (meanLimit_converges (.add e f)) (convergesTo_add (meanLimit_converges e) (meanLimit_converges f))

theorem meanLimit_smul {base : Nat} (c : Q') (e : PlaquetteExpression base) :
    Equiv (meanLimit (.smul c e)) (CReal.mul (ofQ' c) (meanLimit e)) :=
  Equiv_of_limit_of_equal
    (fun margin => testLimit_smul nome nome_pos nome_lt_one (bulkScalar (base+margin)) c (enlarge margin e))
    (meanLimit_converges (.smul c e)) (convergesTo_const_mul (ofQ' c) (meanLimit_converges e))

end YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.probeFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.probeLinks_shift
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.bulkScalar_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.insertion
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.insertionInterval
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.insertion_local
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.insertion_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.mean
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.mean_difference_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.mean_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanSequence
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanSequenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.innerModulus
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.inner_regular
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.sequence_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.outer_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit_error_le
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest.meanLimit_smul
