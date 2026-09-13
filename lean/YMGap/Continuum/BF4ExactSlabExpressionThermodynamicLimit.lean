/-
# Constructed ORIGINAL thermodynamic limits for finite plaquette expressions

At the existing w=1/1024 pilot, every expression in the existing algebra
(including finite products and mixed moments) has an original expectation
limit. The support-size delay, outer volume modulus, per-volume approximation
moduli and limit-representative modulus are explicit data. The original
geometric comparison survives to the returned limit.

Unit normalization, addition, signed rational scaling and ordinary-square
positivity pass to these limits. No assertion of multiplicativity is made:
the limit of a mixed product is its interacting mixed moment.

This is fixed-coupling, fixed-spacing progress. A compatible full state,
time homogeneity, the physical transfer/vacuum/gap and continuum passage
remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
import YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit

namespace YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
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

def amplitude {base : Nat} (e : PlaquetteExpression base) : Q' := expressionAmplitude nome hd hs e

theorem amplitude_nonnegative {base : Nat} (e : PlaquetteExpression base) : (0 : Q') ≤ amplitude e :=
  Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one)
      (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (probePrefactor_nonnegative nome hd (boxLinkCount base)) (ClusterCount.ofNat_nonneg _))
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- The finite support contributes a fixed delay, not a volume-dependent rate. -/
def volumeModulus {base : Nat} (e : PlaquetteExpression base) (epsilon : Q') : Nat :=
  boxSize base + geoOuterModulus (amplitude e) epsilon

theorem volumeModulus_antitone {base : Nat} (e : PlaquetteExpression base) : MmonoPred (volumeModulus e) :=
  fun epsilon delta hdelta he => Nat.add_le_add_left (geoOuterModulus_mono (amplitude e) epsilon delta hdelta he) (boxSize base)

theorem coefficient_small {base : Nat} (e : PlaquetteExpression base) (epsilon : Q') (he : (0 : Q') < epsilon)
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

def meanSequence {base : Nat} (e : PlaquetteExpression base) : Nat → CReal :=
  expressionMean nome nome_pos nome_lt_one e

def meanSequenceCauchy {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    QCauchy (meanSequence e margin).approx :=
  expectationCauchy nome nome_pos nome_lt_one (base+margin) (shiftedExpression margin e)

def innerModulus {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : Q' → Nat :=
  (meanSequenceCauchy e margin).M

theorem inner_regular {base : Nat} (e : PlaquetteExpression base) : RegPred (meanSequence e) (innerModulus e) :=
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

theorem outer_cauchy {base : Nat} (e : PlaquetteExpression base) : LeRatBound (meanSequence e) (volumeModulus e) := by
  intro epsilon he m n hm hn
  have step (i j : Nat) (hij : i ≤ j) (hi : volumeModulus e epsilon ≤ i) :
      leRat (CReal.sub (meanSequence e j) (meanSequence e i)) epsilon ∧
      leRat (CReal.sub (meanSequence e i) (meanSequence e j)) epsilon := by
    have h := existingNome_expressionMean_difference_bound e i (j-i)
    dsimp only at h
    rw [Nat.add_sub_of_le hij] at h
    exact two_sided_of_abs (leEv_trans h
      (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small e epsilon he i hi)))
  rcases Nat.le_total m n with hmn | hnm
  · exact (step m n hmn hm).symm
  · exact step n m hnm hn

def meanLimit {base : Nat} (e : PlaquetteExpression base) : CReal :=
  completeLimitFromRate (meanSequence e) (volumeModulus e) (innerModulus e) (inner_regular e) (outer_cauchy e)

theorem meanLimit_converges {base : Nat} (e : PlaquetteExpression base) :
    ConvergesTo (meanSequence e) (meanLimit e) :=
  convergesTo_completeLimitFromRate _ _ _ (inner_regular e) (outer_cauchy e) (volumeModulus_antitone e)

def meanLimitCauchy {base : Nat} (e : PlaquetteExpression base) : QCauchy (meanLimit e).approx where
  M epsilon := (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · exact diagSeqR_directed _ _ _ (inner_regular e) (outer_cauchy e) epsilon he m n hmn hm
    · exact (diagSeqR_directed _ _ _ (inner_regular e) (outer_cauchy e) epsilon he n m hnm hn).symm

theorem meanLimit_geometric_bound {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin)))
      (ofQ' (amplitude e * rate^(margin+1-boxSize base))) := by
  have ht : ConvergesTo (fun p => meanSequence e (margin+p)) (meanLimit e) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := meanLimit_converges e epsilon he
    exact ⟨N, fun n hn => hN (margin+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩
  have hsub := convergesTo_add ht (TrigAddCReal.convergesTo_neg (convergesTo_const (meanSequence e margin)))
  exact leEv_of_convergesTo_le (convergesTo_abs hsub) (convergesTo_const _)
    (fun p => existingNome_expressionMean_difference_bound e margin p)

theorem meanLimit_error_le {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat) (hm : volumeModulus e epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (meanLimit e) (meanSequence e margin))) (ofQ' epsilon) :=
  leEv_trans (meanLimit_geometric_bound e margin)
    (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small e epsilon he margin hm))

theorem meanLimit_one (base : Nat) : Equiv (meanLimit (.unit : PlaquetteExpression base)) CReal.cone :=
  Equiv_of_limit_of_equal (fun margin => expectation_one nome nome_pos nome_lt_one (base+margin))
    (meanLimit_converges .unit) (convergesTo_const _)

theorem meanLimit_add {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (meanLimit (.add e f)) (CReal.add (meanLimit e) (meanLimit f)) :=
  Equiv_of_limit_of_equal (fun margin => expectation_add nome nome_pos nome_lt_one (base+margin)
    (shiftedExpression margin e) (shiftedExpression margin f))
    (meanLimit_converges (.add e f)) (convergesTo_add (meanLimit_converges e) (meanLimit_converges f))

theorem meanLimit_smul {base : Nat} (c : Q') (e : PlaquetteExpression base) :
    Equiv (meanLimit (.smul c e)) (CReal.mul (ofQ' c) (meanLimit e)) :=
  Equiv_of_limit_of_equal (fun margin => expectation_smul nome nome_pos nome_lt_one (base+margin) c
    (shiftedExpression margin e)) (meanLimit_converges (.smul c e))
    (convergesTo_const_mul (ofQ' c) (meanLimit_converges e))

/-- Ordinary-square positivity, not an OS transfer form or a spectral gap. -/
theorem meanLimit_square_nonnegative {base : Nat} (e : PlaquetteExpression base) :
    leEv (ofQ' 0) (meanLimit (.mul e e)) :=
  leEv_of_convergesTo_le (convergesTo_const _) (meanLimit_converges (.mul e e))
    (fun margin => expectation_square_nonnegative nome nome_pos nome_lt_one (base+margin)
      (shiftedExpression margin e) (shiftedExpression_supported margin e))

end YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit

#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.amplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.volumeModulus_antitone
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.coefficient_small
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanSequence
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanSequenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.innerModulus
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.inner_regular
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.outer_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_error_le
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_one
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit.meanLimit_square_nonnegative
