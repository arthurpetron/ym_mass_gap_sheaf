/-
# Constructed temporal modulus and geometric envelope for ORIGINAL OS moments

The exact time-separation budget factors into a support-dependent amplitude
and a common rate power. The existing half-power envelope at nome 1/1024
returns an explicit temporal tolerance modulus. A positive rational
prefactor also absorbs the finite support offset, yielding P(e,f)*(1/2)^n
for every lag n, including the finite initial segment.

Neither construction changes the law, the covariance limit or the completed
time operator. The prefactor is still observable-dependent at this layer;
its removal and the completed form bound are downstream in
BF4ExactSlabThermodynamicDenseGap and BF4ExactSlabThermodynamicCompletedGap.
Continuum control is not asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecay
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression
open YMGap.Continuum.BF4ExactSlabTwoProbeSpacetimeDecay
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (boxSize boxLinkCount)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit (rate rate_pos rate_le_half)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.ClusteringImpliesGap (pow_pos)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

private theorem deltaGuard : QuaternionHaarCharacterInterval.heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
private theorem countGuard : rate < 1 := BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2
local notation "hd" => deltaGuard

def amplitude {base : Nat} (e f : PlaquetteExpression base) : Q' :=
  let c := bound (fromUpper e)+1
  let d := bound (fromLower f)+1
  (((c*d+c*d)*probePrefactor nome hd (boxLinkCount base+boxLinkCount base))*
    Q'.ofNat (2^(boxSize base+boxSize base)*625^(boxSize base+boxSize base)))*
      Q'.recipPos (1 + -rate) (HKPos.one_sub_pos countGuard)

theorem amplitude_nonnegative {base : Nat} (e f : PlaquetteExpression base) : (0 : Q') ≤ amplitude e f := by
  have hc := Q'.zero_le_add _ _ (bound_nonnegative (fromUpper e)) Q'.zero_le_one
  have hd' := Q'.zero_le_add _ _ (bound_nonnegative (fromLower f)) Q'.zero_le_one
  exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hc hd') (Q'.mul_nonneg _ _ hc hd'))
      (probePrefactor_nonnegative nome hd _)) (ClusterCount.ofNat_nonneg _)) (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem timeBudget_factor {base : Nat} (e f : PlaquetteExpression base) (lag : Nat) :
    Q'.eqv (timeBudget e f lag) (amplitude e f * rate^(lag+1-(boxSize base+boxSize base))) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun i => if i = 0 then ((bound (fromUpper e)+1)*(bound (fromLower f)+1)+(bound (fromUpper e)+1)*(bound (fromLower f)+1))*
          probePrefactor nome hd (boxLinkCount base+boxLinkCount base)
      else if i = 1 then Q'.ofNat (2^(boxSize base+boxSize base)*625^(boxSize base+boxSize base))
      else if i = 2 then rate^(lag+1-(boxSize base+boxSize base))
      else Q'.recipPos (1 + -rate) (HKPos.one_sub_pos countGuard))

/-- Computed time-separation threshold; distinct from the existing volume modulus. -/
def timeModulus {base : Nat} (e f : PlaquetteExpression base) (epsilon : Q') : Nat :=
  (boxSize base+boxSize base)+geoOuterModulus (amplitude e f) epsilon

theorem timeBudget_small {base : Nat} (e f : PlaquetteExpression base) (epsilon : Q')
    (he : (0 : Q') < epsilon) (lag : Nat) (hl : timeModulus e f epsilon ≤ lag) :
    timeBudget e f lag ≤ epsilon := by
  have hA := amplitude_nonnegative e f
  have htwo : amplitude e f ≤ Q'.ofNat 2*amplitude e f :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hA)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
        (.mul (.const 2) (.var 0)) (by decide) (fun _ => amplitude e f)))
  have hm : geoOuterModulus (amplitude e f) epsilon ≤ lag+1-(boxSize base+boxSize base) := by
    unfold timeModulus at hl
    omega
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (timeBudget_factor e f lag))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (TotalMajorantClose.pow_le_pow_base (Q'.le_of_lt rate_pos) rate_le_half _) hA)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ htwo (Q'.pow_nonneg _ HalfPow.half_nonneg _))
        (geoTail_le_of_modulus (amplitude e f) hA epsilon he _ hm)))

theorem timeCovariance_small {base : Nat} (e f : PlaquetteExpression base) (epsilon : Q')
    (he : (0 : Q') < epsilon) (s t : Nat) (hl : timeModulus e f epsilon ≤ s+t) :
    leEv (CReal.abs (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).1) (ofQ' epsilon) :=
  leEv_trans (timeCovariance_bound s t e f)
    (leEv_ofQ'_of_approx_ge (fun _ => timeBudget_small e f epsilon he (s+t) hl))

private theorem shifted_half_power (M n : Nat) :
    HalfPow.half^(n+1-M) ≤ Q'.recipPos (HalfPow.half^M) (pow_pos (by decide) M)*HalfPow.half^n := by
  let i := Q'.recipPos (HalfPow.half^M) (pow_pos (by decide) M)
  have h : HalfPow.half^M*HalfPow.half^(n+1-M) ≤ HalfPow.half^n :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.pow_add_eqv HalfPow.half M (n+1-M)))
      (half_pow_antitone n (M+(n+1-M)) (by omega))
  have he : Q'.eqv (i*(HalfPow.half^M*HalfPow.half^(n+1-M))) (HalfPow.half^(n+1-M)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _))) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ i h (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- Data returned for the moment argument, positive even for a zero observable. -/
def positivePrefactor {base : Nat} (e f : PlaquetteExpression base) : Q' :=
  amplitude e f * Q'.recipPos (HalfPow.half^(boxSize base+boxSize base)) (pow_pos (by decide) _) + 1

theorem positivePrefactor_pos {base : Nat} (e f : PlaquetteExpression base) : (0 : Q') < positivePrefactor e f :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _
      (Q'.mul_nonneg _ _ (amplitude_nonnegative e f) (Q'.le_of_lt (Q'.recipPos_pos _ _))))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem timeBudget_envelope {base : Nat} (e f : PlaquetteExpression base) (lag : Nat) :
    timeBudget e f lag ≤ positivePrefactor e f * HalfPow.half^lag := by
  have hA := amplitude_nonnegative e f
  have hb := Q'.le_trans' _ _ _ (Q'.le_of_eqv (timeBudget_factor e f lag))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (TotalMajorantClose.pow_le_pow_base (Q'.le_of_lt rate_pos) rate_le_half _) hA)
  have hshift := Q'.mul_le_mul_of_nonneg_left _ _ (amplitude e f) (shifted_half_power (boxSize base+boxSize base) lag) hA
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ hshift
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.pow_nonneg _ HalfPow.half_nonneg _))))

theorem timeCovariance_geometric_bound {base : Nat} (s t : Nat) (e f : PlaquetteExpression base) :
    leEv (CReal.abs (timeCovarianceRepresentative s t ⟨base,e⟩ ⟨base,f⟩).1)
      (ofQ' (positivePrefactor e f * HalfPow.half^(s+t))) :=
  leEv_trans (timeCovariance_bound s t e f)
    (leEv_ofQ'_of_approx_ge (fun _ => timeBudget_envelope e f (s+t)))

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.amplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.timeBudget_factor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.timeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.timeBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.timeCovariance_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.positivePrefactor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.positivePrefactor_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.timeBudget_envelope
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate.timeCovariance_geometric_bound
