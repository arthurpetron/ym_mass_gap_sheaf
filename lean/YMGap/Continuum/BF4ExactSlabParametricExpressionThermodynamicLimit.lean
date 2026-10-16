/-
# Parametric ORIGINAL thermodynamic limits for finite plaquette expressions

For every nome satisfying the existing small-nome, remainder, entropy and
half-rate guards, every finite plaquette expression has an original
thermodynamic expectation limit.  The support delay, outer volume modulus,
per-volume approximation moduli and limit-representative modulus are explicit.
Normalization, addition, signed rational scaling and ordinary-square positivity
pass to the limit.

This is the volume-limit producer at one guarded lattice spacing.  It does not
compare different nomes, construct a continuum modulus, identify a continuum
Schwinger functional, or prove a physical Hamiltonian mass gap.
-/

import YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
import YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit

namespace YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.FiniteSizeGeometricSum

def rate (w : Q') (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1) : Q' :=
  entropyRate 625 (adjustedCoreRate w hd)

theorem rate_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1) :
    (0 : Q') ≤ rate w hd :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _)
    (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

def amplitude {w : Q'} (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) {base : Nat} (e : PlaquetteExpression base) : Q' :=
  expressionAmplitude w hd hs e

theorem amplitude_nonnegative {w : Q'}
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) {base : Nat} (e : PlaquetteExpression base) :
    (0 : Q') ≤ amplitude hd hs e :=
  Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one)
      (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (probePrefactor_nonnegative w hd (boxLinkCount base))
        (ClusterCount.ofNat_nonneg _))
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- The finite support contributes a fixed delay, not a volume-dependent rate. -/
def volumeModulus {w : Q'}
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) {base : Nat} (e : PlaquetteExpression base) (epsilon : Q') : Nat :=
  boxSize base + geoOuterModulus (amplitude hd hs e) epsilon

theorem volumeModulus_antitone {w : Q'}
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) {base : Nat} (e : PlaquetteExpression base) :
    MmonoPred (volumeModulus hd hs e) :=
  fun epsilon delta hdelta he =>
    Nat.add_le_add_left (geoOuterModulus_mono (amplitude hd hs e) epsilon delta hdelta he) (boxSize base)

theorem coefficient_small {w : Q'} (hw0 : (0 : Q') < w)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m : Nat) (hm : volumeModulus hd hs e epsilon ≤ m) :
    amplitude hd hs e * (rate w hd)^(m+1-boxSize base) ≤ epsilon := by
  have hC := amplitude_nonnegative hd hs e
  have htwo : amplitude hd hs e ≤ Q'.ofNat 2 * amplitude hd hs e :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hC)
      (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide)
        (fun _ => amplitude hd hs e)))
  have hm' : geoOuterModulus (amplitude hd hs e) epsilon ≤ m+1-boxSize base := by
    change boxSize base + geoOuterModulus (amplitude hd hs e) epsilon ≤ m at hm
    omega
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (TotalMajorantClose.pow_le_pow_base (rate_nonnegative hw0 hd) hrateHalf _) hC)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ htwo (Q'.pow_nonneg _ HalfPow.half_nonneg _))
      (geoTail_le_of_modulus (amplitude hd hs e) hC epsilon he _ hm'))

def meanSequence {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) : Nat → CReal :=
  expressionMean w hw0 hw1 e

def meanSequenceCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    QCauchy (meanSequence hw0 hw1 e margin).approx :=
  expectationCauchy w hw0 hw1 (base+margin) (shiftedExpression margin e)

def innerModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) : Q' → Nat :=
  (meanSequenceCauchy hw0 hw1 e margin).M

theorem inner_regular {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (e : PlaquetteExpression base) :
    RegPred (meanSequence hw0 hw1 e) (innerModulus hw0 hw1 e) :=
  fun margin => (meanSequenceCauchy hw0 hw1 e margin).bound

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

theorem outer_cauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) :
    LeRatBound (meanSequence hw0 hw1 e) (volumeModulus hd hs e) := by
  intro epsilon he m n hm hn
  have step (i j : Nat) (hij : i ≤ j) (hi : volumeModulus hd hs e epsilon ≤ i) :
      leRat (CReal.sub (meanSequence hw0 hw1 e j) (meanSequence hw0 hw1 e i)) epsilon ∧
      leRat (CReal.sub (meanSequence hw0 hw1 e i) (meanSequence hw0 hw1 e j)) epsilon := by
    have h := expressionMean_difference_bound w hw0 hw1 hsmall hd hs e i (j-i)
    rw [Nat.add_sub_of_le hij] at h
    exact two_sided_of_abs (leEv_trans h
      (leEv_le_ofQ'_of_approx_le
        (fun _ => coefficient_small hw0 hd hs hrateHalf e epsilon he i hi)))
  rcases Nat.le_total m n with hmn | hnm
  · exact (step m n hmn hm).symm
  · exact step n m hnm hn

/-- The original normalized expectation diagonal, with explicit outer and inner moduli. -/
def meanLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) : CReal :=
  completeLimitFromRate (meanSequence hw0 hw1 e) (volumeModulus hd hs e)
    (innerModulus hw0 hw1 e) (inner_regular hw0 hw1 e)
    (outer_cauchy hw0 hw1 hsmall hd hs hrateHalf e)

theorem meanLimit_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) :
    ConvergesTo (meanSequence hw0 hw1 e) (meanLimit hw0 hw1 hsmall hd hs hrateHalf e) :=
  convergesTo_completeLimitFromRate _ _ _ (inner_regular hw0 hw1 e)
    (outer_cauchy hw0 hw1 hsmall hd hs hrateHalf e) (volumeModulus_antitone hd hs e)

def meanLimitCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) :
    QCauchy (meanLimit hw0 hw1 hsmall hd hs hrateHalf e).approx where
  M epsilon := (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · exact diagSeqR_directed _ _ _ (inner_regular hw0 hw1 e)
        (outer_cauchy hw0 hw1 hsmall hd hs hrateHalf e) epsilon he m n hmn hm
    · exact (diagSeqR_directed _ _ _ (inner_regular hw0 hw1 e)
        (outer_cauchy hw0 hw1 hsmall hd hs hrateHalf e) epsilon he n m hnm hn).symm

theorem meanLimit_geometric_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) (margin : Nat) :
    leEv (CReal.abs (CReal.sub (meanLimit hw0 hw1 hsmall hd hs hrateHalf e)
      (meanSequence hw0 hw1 e margin)))
      (ofQ' (amplitude hd hs e * (rate w hd)^(margin+1-boxSize base))) := by
  have ht : ConvergesTo (fun padding => meanSequence hw0 hw1 e (margin+padding))
      (meanLimit hw0 hw1 hsmall hd hs hrateHalf e) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf e epsilon he
    exact ⟨N, fun n hn => hN (margin+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩
  have hsub := convergesTo_add ht
    (TrigAddCReal.convergesTo_neg (convergesTo_const (meanSequence hw0 hw1 e margin)))
  exact leEv_of_convergesTo_le (convergesTo_abs hsub) (convergesTo_const _)
    (fun padding => expressionMean_difference_bound w hw0 hw1 hsmall hd hs e margin padding)

theorem meanLimit_error_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : volumeModulus hd hs e epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (meanLimit hw0 hw1 hsmall hd hs hrateHalf e)
      (meanSequence hw0 hw1 e margin))) (ofQ' epsilon) :=
  leEv_trans (meanLimit_geometric_bound hw0 hw1 hsmall hd hs hrateHalf e margin)
    (leEv_le_ofQ'_of_approx_le
      (fun _ => coefficient_small hw0 hd hs hrateHalf e epsilon he margin hm))

theorem meanLimit_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half) (base : Nat) :
    Equiv (meanLimit hw0 hw1 hsmall hd hs hrateHalf (.unit : PlaquetteExpression base)) CReal.cone :=
  Equiv_of_limit_of_equal (fun margin => expectation_one w hw0 hw1 (base+margin))
    (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf .unit) (convergesTo_const _)

theorem meanLimit_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (meanLimit hw0 hw1 hsmall hd hs hrateHalf (.add e f))
      (CReal.add (meanLimit hw0 hw1 hsmall hd hs hrateHalf e)
        (meanLimit hw0 hw1 hsmall hd hs hrateHalf f)) :=
  Equiv_of_limit_of_equal (fun margin => expectation_add w hw0 hw1 (base+margin)
    (shiftedExpression margin e) (shiftedExpression margin f))
    (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf (.add e f))
    (convergesTo_add (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf e)
      (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf f))

theorem meanLimit_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (c : Q') (e : PlaquetteExpression base) :
    Equiv (meanLimit hw0 hw1 hsmall hd hs hrateHalf (.smul c e))
      (CReal.mul (ofQ' c) (meanLimit hw0 hw1 hsmall hd hs hrateHalf e)) :=
  Equiv_of_limit_of_equal (fun margin => expectation_smul w hw0 hw1 (base+margin) c
    (shiftedExpression margin e))
    (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf (.smul c e))
    (convergesTo_const_mul (ofQ' c) (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf e))

/-- Ordinary-square positivity, not an OS transfer form or a spectral gap. -/
theorem meanLimit_square_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
    (hd : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)
    (hs : rate w hd < 1) (hrateHalf : rate w hd ≤ HalfPow.half)
    {base : Nat} (e : PlaquetteExpression base) :
    leEv (ofQ' 0) (meanLimit hw0 hw1 hsmall hd hs hrateHalf (.mul e e)) :=
  leEv_of_convergesTo_le (convergesTo_const _)
    (meanLimit_converges hw0 hw1 hsmall hd hs hrateHalf (.mul e e))
    (fun margin => expectation_square_nonnegative w hw0 hw1 (base+margin)
      (shiftedExpression margin e) (shiftedExpression_supported margin e))

end YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit

#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.rate
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.rate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.amplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.volumeModulus_antitone
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.coefficient_small
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanSequence
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanSequenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.innerModulus
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.inner_regular
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.outer_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_error_le
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_one
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabParametricExpressionThermodynamicLimit.meanLimit_square_nonnegative
