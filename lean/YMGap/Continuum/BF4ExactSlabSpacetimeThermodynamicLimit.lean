/-
# Constructed ORIGINAL thermodynamic limits for spacetime plaquette expressions

Every finite expression on the physical faces of a base slab, including
reflected mixed products, has a constructed original expectation limit at
w=1/1024. Its support delay and outer/inner/representative moduli are data.
The same original geometric estimate bounds the actual limit error.

Normalization, rational linearity and ordinary-square positivity survive.
The restriction to lower expressions is proved equal to the previous limit,
not a separately chosen state. OS positivity is a separate reflected-form
consumer; time homogeneity, physical transfer/gap and continuum remain open.
-/

import YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay
import YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit

namespace YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSpacetimeExpectationDecay
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize boxLinkCount boxCount)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate rate_pos rate_le_half)
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.FiniteSizeGeometricSum

private theorem deltaGuard : QuaternionHaarCharacterInterval.heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
private theorem countGuard : entropyRate 625 (adjustedCoreRate nome deltaGuard) < 1 :=
  BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
local notation "hd" => deltaGuard
local notation "hs" => countGuard

def amplitude {base : Nat} (e : SpacetimeExpression base) : Q' := BF4ExactSlabSpacetimeExpectationDecay.amplitude nome hd hs e

theorem amplitude_nonnegative {base : Nat} (e : SpacetimeExpression base) : (0 : Q') ≤ amplitude e :=
  Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one)
      (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (probePrefactor_nonnegative nome hd (boxLinkCount base)) (ClusterCount.ofNat_nonneg _))
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- The finite support contributes a fixed delay, not a volume-dependent rate. -/
def volumeModulus {base : Nat} (e : SpacetimeExpression base) (epsilon : Q') : Nat :=
  boxSize base + geoOuterModulus (amplitude e) epsilon

theorem volumeModulus_antitone {base : Nat} (e : SpacetimeExpression base) : MmonoPred (volumeModulus e) :=
  fun epsilon delta hdelta he => Nat.add_le_add_left (geoOuterModulus_mono (amplitude e) epsilon delta hdelta he) (boxSize base)

theorem coefficient_small {base : Nat} (e : SpacetimeExpression base) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m : Nat) (hm : volumeModulus e epsilon ≤ m) : amplitude e * rate^(m+1-boxSize base) ≤ epsilon := by
  have hC := amplitude_nonnegative e
  have htwo : amplitude e ≤ Q'.ofNat 2 * amplitude e :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hC)
      (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide) (fun _ => amplitude e)))
  have hm' : geoOuterModulus (amplitude e) epsilon ≤ m+1-boxSize base := by
    change boxSize base + geoOuterModulus (amplitude e) epsilon ≤ m at hm
    omega
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (TotalMajorantClose.pow_le_pow_base (Q'.le_of_lt rate_pos) rate_le_half _) hC)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ htwo (Q'.pow_nonneg _ HalfPow.half_nonneg _))
      (geoTail_le_of_modulus (amplitude e) hC epsilon he _ hm'))

def meanSequence {base : Nat} (e : SpacetimeExpression base) : Nat → CReal :=
  mean nome nome_pos nome_lt_one e

def meanSequenceCauchy {base : Nat} (e : SpacetimeExpression base) (margin : Nat) :
    QCauchy (meanSequence e margin).approx :=
  expectationCauchy nome nome_pos nome_lt_one (base+margin) (evaluate margin e)

def innerModulus {base : Nat} (e : SpacetimeExpression base) (margin : Nat) : Q' → Nat :=
  (meanSequenceCauchy e margin).M

theorem inner_regular {base : Nat} (e : SpacetimeExpression base) : RegPred (meanSequence e) (innerModulus e) :=
  fun m => (meanSequenceCauchy e m).bound

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

theorem outer_cauchy {base : Nat} (e : SpacetimeExpression base) : LeRatBound (meanSequence e) (volumeModulus e) := by
  intro epsilon he m n hm hn
  have step (i j : Nat) (hij : i ≤ j) (hi : volumeModulus e epsilon ≤ i) :
      leRat (CReal.sub (meanSequence e j) (meanSequence e i)) epsilon ∧
      leRat (CReal.sub (meanSequence e i) (meanSequence e j)) epsilon := by
    have h := existingNome_difference_bound e i (j-i)
    dsimp only at h
    rw [Nat.add_sub_of_le hij] at h
    exact two_sided_of_abs (leEv_trans h
      (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small e epsilon he i hi)))
  rcases Nat.le_total m n with hmn | hnm
  · exact (step m n hmn hm).symm
  · exact step n m hnm hn

def meanLimit {base : Nat} (e : SpacetimeExpression base) : CReal :=
  completeLimitFromRate (meanSequence e) (volumeModulus e) (innerModulus e) (inner_regular e) (outer_cauchy e)

theorem meanLimit_converges {base : Nat} (e : SpacetimeExpression base) :
    ConvergesTo (meanSequence e) (meanLimit e) :=
  convergesTo_completeLimitFromRate _ _ _ (inner_regular e) (outer_cauchy e) (volumeModulus_antitone e)

def meanLimitCauchy {base : Nat} (e : SpacetimeExpression base) : QCauchy (meanLimit e).approx where
  M epsilon := (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · exact diagSeqR_directed _ _ _ (inner_regular e) (outer_cauchy e) epsilon he m n hmn hm
    · exact (diagSeqR_directed _ _ _ (inner_regular e) (outer_cauchy e) epsilon he n m hnm hn).symm

theorem meanLimit_geometric_bound {base : Nat} (e : SpacetimeExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin)))
      (ofQ' (amplitude e * rate^(margin+1-boxSize base))) := by
  have ht : ConvergesTo (fun p => meanSequence e (margin+p)) (meanLimit e) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := meanLimit_converges e epsilon he
    exact ⟨N, fun n hn => hN (margin+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩
  have hsub := convergesTo_add ht (TrigAddCReal.convergesTo_neg (convergesTo_const (meanSequence e margin)))
  exact leEv_of_convergesTo_le (convergesTo_abs hsub) (convergesTo_const _)
    (fun p => existingNome_difference_bound e margin p)

theorem meanLimit_error_le {base : Nat} (e : SpacetimeExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat) (hm : volumeModulus e epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin))) (ofQ' epsilon) :=
  leEv_trans (meanLimit_geometric_bound e margin)
    (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small e epsilon he margin hm))

theorem meanLimit_one (base : Nat) : Equiv (meanLimit (.unit : SpacetimeExpression base)) CReal.cone :=
  Equiv_of_limit_of_equal (fun margin => expectation_one nome nome_pos nome_lt_one (base+margin))
    (meanLimit_converges .unit) (convergesTo_const _)

theorem meanLimit_add {base : Nat} (e f : SpacetimeExpression base) :
    Equiv (meanLimit (.add e f)) (CReal.add (meanLimit e) (meanLimit f)) :=
  Equiv_of_limit_of_equal (fun margin => expectation_add nome nome_pos nome_lt_one (base+margin)
    (evaluate margin e) (evaluate margin f))
    (meanLimit_converges (.add e f)) (convergesTo_add (meanLimit_converges e) (meanLimit_converges f))

theorem meanLimit_smul {base : Nat} (c : Q') (e : SpacetimeExpression base) :
    Equiv (meanLimit (.smul c e)) (CReal.mul (ofQ' c) (meanLimit e)) :=
  Equiv_of_limit_of_equal (fun margin => expectation_smul nome nome_pos nome_lt_one (base+margin) c
    (evaluate margin e)) (meanLimit_converges (.smul c e))
    (convergesTo_const_mul (ofQ' c) (meanLimit_converges e))

/-- Ordinary-square positivity, not an OS transfer form or a spectral gap. -/
theorem meanLimit_square_nonnegative {base : Nat} (e : SpacetimeExpression base) :
    leEv (ofQ' 0) (meanLimit (.mul e e)) :=
  leEv_of_convergesTo_le (convergesTo_const _) (meanLimit_converges (.mul e e))
    (fun margin => expectation_square_nonnegative nome nome_pos nome_lt_one (base+margin)
      (evaluate margin e) (supported margin e))

/-- The full expression carrier agrees with the already-constructed lower means. -/
theorem lower_sequence_pin {base : Nat} (e : BF4ExactSlabPlaquetteObservableAlgebra.PlaquetteExpression base) (margin : Nat) :
    meanSequence (fromLower e) margin = BF4ExactSlabExpressionThermodynamicLimit.meanSequence e margin := by
  unfold meanSequence mean BF4ExactSlabExpressionThermodynamicLimit.meanSequence
    BF4ExactSlabExpressionExpectationDecay.expressionMean
  rw [evaluate_fromLower]

theorem lower_limit_pin {base : Nat} (e : BF4ExactSlabPlaquetteObservableAlgebra.PlaquetteExpression base) :
    Equiv (meanLimit (fromLower e)) (BF4ExactSlabExpressionThermodynamicLimit.meanLimit e) :=
  Equiv_of_limit_of_equal (fun margin => (lower_sequence_pin e margin) ▸ Equiv.refl _)
    (meanLimit_converges (fromLower e)) (BF4ExactSlabExpressionThermodynamicLimit.meanLimit_converges e)

end YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.amplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.volumeModulus_antitone
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.coefficient_small
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanSequence
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanSequenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.innerModulus
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.inner_regular
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.outer_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_error_le
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_one
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.meanLimit_square_nonnegative

#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.lower_sequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpacetimeThermodynamicLimit.lower_limit_pin
