/-
# Signed prefix and variation regions for the cumulative linear Abel payment

The complementary increment is now equipped with a rational peak threshold.
This module supplies the other half of the Abel geometry: the next-scale
linear carrier crosses zero at most once, its finite prefixes have exact step
laws, and the Abel variation term has certified signs on the rising head and
the falling suffix.  The only potentially adverse sign region is thereby
isolated between the carrier-prefix crossing and the derived peak threshold.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxLocation

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPrefixVariation

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxLocation
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem carrier_nonnegative_iterate
    {k i : Nat} (hi : (0 : Q') ≤ lowerSixRecoveryLinearCarrier k i) :
    ∀ d, (0 : Q') ≤ lowerSixRecoveryLinearCarrier k (i + d)
  | 0 => by simpa using hi
  | d + 1 => by
      have hd := carrier_nonnegative_iterate hi d
      have hs := lowerSixRecoveryLinearCarrier_nonnegative_succ hd
      simpa only [Nat.add_assoc] using hs

/-- Forward one-crossing law at arbitrary separation. -/
theorem lowerSixRecoveryLinearCarrier_nonnegative_mono
    {k i j : Nat} (hij : i ≤ j)
    (hi : (0 : Q') ≤ lowerSixRecoveryLinearCarrier k i) :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrier k j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact carrier_nonnegative_iterate hi d

private theorem carrier_nonpositive_iterate_back
    {k i : Nat} : ∀ d,
    lowerSixRecoveryLinearCarrier k (i + d) ≤ (0 : Q') →
      lowerSixRecoveryLinearCarrier k i ≤ (0 : Q')
  | 0, h => by simpa using h
  | d + 1, h => by
      have hpred : lowerSixRecoveryLinearCarrier k (i + d) ≤ (0 : Q') := by
        apply lowerSixRecoveryLinearCarrier_nonpositive_pred
        simpa only [Nat.add_assoc] using h
      exact carrier_nonpositive_iterate_back d hpred

/-- Backward one-crossing law at arbitrary separation. -/
theorem lowerSixRecoveryLinearCarrier_nonpositive_anti
    {k i j : Nat} (hij : i ≤ j)
    (hj : lowerSixRecoveryLinearCarrier k j ≤ (0 : Q')) :
    lowerSixRecoveryLinearCarrier k i ≤ (0 : Q') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact carrier_nonpositive_iterate_back d hj

private theorem signed_add_nonpositive {a b : Q'}
    (ha : a ≤ (0 : Q')) (hb : b ≤ (0 : Q')) :
    a + b ≤ (0 : Q') :=
  Q'.le_trans' _ _ _ (Q'.add_le_add ha hb) (by decide)

private theorem signed_finSum_nonpositive (f : Nat → Q') : ∀ N,
    (∀ j, j < N → f j ≤ (0 : Q')) → finSum f N ≤ (0 : Q')
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact signed_add_nonpositive
        (signed_finSum_nonpositive f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- Exact step law for the next-carrier prefix. -/
theorem lowerSixRecoveryNextCarrierPrefix_succ (k p : Nat) :
    lowerSixRecoveryNextCarrierPrefix k (p + 1) ≈
      lowerSixRecoveryNextCarrierPrefix k p +
        lowerSixRecoveryLinearCarrier (k + 1) (p + 1) := by
  unfold lowerSixRecoveryNextCarrierPrefix
  rw [show p + 1 + 1 = (p + 1) + 1 by omega, finSum_succ]
  exact Q'.eqv_refl _

/-- A nonpositive current carrier forces the whole prefix nonpositive. -/
theorem lowerSixRecoveryNextCarrierPrefix_nonpositive_of_carrier
    {k p : Nat}
    (hp : lowerSixRecoveryLinearCarrier (k + 1) p ≤ (0 : Q')) :
    lowerSixRecoveryNextCarrierPrefix k p ≤ (0 : Q') := by
  unfold lowerSixRecoveryNextCarrierPrefix
  apply signed_finSum_nonpositive
  intro j hj
  exact lowerSixRecoveryLinearCarrier_nonpositive_anti (by omega) hp

private theorem nextCarrierPrefix_tail_mono_aux
    {k p : Nat}
    (hp : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) p) :
    ∀ d,
      lowerSixRecoveryNextCarrierPrefix k p ≤
        lowerSixRecoveryNextCarrierPrefix k (p + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have ih := nextCarrierPrefix_tail_mono_aux hp d
      have hc : (0 : Q') ≤
          lowerSixRecoveryLinearCarrier (k + 1) (p + d + 1) :=
        lowerSixRecoveryLinearCarrier_nonnegative_mono (by omega) hp
      have hadd := Q'.add_le_self_of_nonneg
        (lowerSixRecoveryNextCarrierPrefix k (p + d))
        (lowerSixRecoveryLinearCarrier (k + 1) (p + d + 1)) hc
      have hstep := lowerSixRecoveryNextCarrierPrefix_succ k (p + d)
      have hlast : lowerSixRecoveryNextCarrierPrefix k (p + d) ≤
          lowerSixRecoveryNextCarrierPrefix k (p + d + 1) :=
        Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hstep)
      exact Q'.le_trans' _ _ _ ih hlast

/-- Once the carrier has crossed zero, all later prefixes are monotone. -/
theorem lowerSixRecoveryNextCarrierPrefix_tail_mono
    {k p q : Nat} (hpq : p ≤ q)
    (hp : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) p) :
    lowerSixRecoveryNextCarrierPrefix k p ≤
      lowerSixRecoveryNextCarrierPrefix k q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  exact nextCarrierPrefix_tail_mono_aux hp d

/-- A nonnegative prefix that occurs after the carrier crossing stays
nonnegative forever. -/
theorem lowerSixRecoveryNextCarrierPrefix_nonnegative_mono
    {k p q : Nat} (hpq : p ≤ q)
    (hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) p)
    (hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k p) :
    (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k q :=
  Q'.le_trans' _ _ _ hprefix
    (lowerSixRecoveryNextCarrierPrefix_tail_mono hpq hcarrier)

/-- Successive variation of the complementary scale increment in the exact
Abel formula. -/
def lowerSixRecoveryComplementVariation (k p : Nat) : Q' :=
  lowerSixRecoveryComplementScaleIncrement k p +
    -lowerSixRecoveryComplementScaleIncrement k (p + 1)

/-- The concrete prefix-variation summand. -/
def lowerSixRecoveryAbelVariationTerm (k p : Nat) : Q' :=
  lowerSixRecoveryNextCarrierPrefix k p *
    lowerSixRecoveryComplementVariation k p

theorem lowerSixRecoveryComplementVariation_nonnegative_of_descent
    {k p : Nat}
    (h : lowerSixRecoveryComplementScaleIncrement k (p + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k p) :
    (0 : Q') ≤ lowerSixRecoveryComplementVariation k p := by
  unfold lowerSixRecoveryComplementVariation
  exact Q'.sub_nonneg_of_le h

theorem lowerSixRecoveryComplementVariation_nonpositive_of_ascent
    {k p : Nat}
    (h : lowerSixRecoveryComplementScaleIncrement k p ≤
      lowerSixRecoveryComplementScaleIncrement k (p + 1)) :
    lowerSixRecoveryComplementVariation k p ≤ (0 : Q') := by
  unfold lowerSixRecoveryComplementVariation
  have hadd := Q'.add_le_add_right
    (lowerSixRecoveryComplementScaleIncrement k p)
    (lowerSixRecoveryComplementScaleIncrement k (p + 1))
    (-lowerSixRecoveryComplementScaleIncrement k (p + 1)) h
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.add_neg_self_eqv _))

/-- The derived quadratic threshold gives a nonnegative Abel variation. -/
theorem lowerSixRecoveryComplementVariation_nonnegative_of_exponent_ge_scale
    {k p : Nat}
    (hkp : k + 2 ≤ lowerSixRecoveryComplementExponent p) :
    (0 : Q') ≤ lowerSixRecoveryComplementVariation k p :=
  lowerSixRecoveryComplementVariation_nonnegative_of_descent
    (lowerSixRecoveryComplementScaleIncrement_descent_of_exponent_ge_scale hkp)

/-- On the rising side, a still-nonpositive carrier makes the Abel variation
summand nonnegative. -/
theorem lowerSixRecoveryAbelVariationTerm_nonnegative_on_rising_carrierHead
    {k p : Nat}
    (hcarrier : lowerSixRecoveryLinearCarrier (k + 1) p ≤ (0 : Q'))
    (hrise : lowerSixRecoveryComplementScaleIncrement k p ≤
      lowerSixRecoveryComplementScaleIncrement k (p + 1)) :
    (0 : Q') ≤ lowerSixRecoveryAbelVariationTerm k p := by
  unfold lowerSixRecoveryAbelVariationTerm
  exact Q'.mul_nonneg_of_nonpos_nonpos
    (lowerSixRecoveryNextCarrierPrefix_nonpositive_of_carrier hcarrier)
    (lowerSixRecoveryComplementVariation_nonpositive_of_ascent hrise)

/-- A nonpositive prefix paired with a falling increment is exactly the
negative middle band of the Abel variation. -/
theorem lowerSixRecoveryAbelVariationTerm_nonpositive_on_negativePrefix_fall
    {k p : Nat}
    (hprefix : lowerSixRecoveryNextCarrierPrefix k p ≤ (0 : Q'))
    (hfall : lowerSixRecoveryComplementScaleIncrement k (p + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k p) :
    lowerSixRecoveryAbelVariationTerm k p ≤ (0 : Q') := by
  have hvar := lowerSixRecoveryComplementVariation_nonnegative_of_descent hfall
  have hprod := Q'.mul_nonpos_of_nonneg_nonpos hvar hprefix
  unfold lowerSixRecoveryAbelVariationTerm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hprod

/-- After both the carrier prefix and the complementary increment have crossed,
the complete later Abel variation tail is termwise nonnegative. -/
theorem lowerSixRecoveryAbelVariationTerm_tail_nonnegative
    {k r : Nat} (hr1 : 1 ≤ r)
    (hthreshold : k + 2 ≤ lowerSixRecoveryComplementExponent r)
    (hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) r)
    (hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k r) :
    ∀ d, (0 : Q') ≤ lowerSixRecoveryAbelVariationTerm k (r + d) := by
  intro d
  have hp : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k (r + d) :=
    lowerSixRecoveryNextCarrierPrefix_nonnegative_mono (by omega)
      hcarrier hprefix
  have hfall :=
    lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale
      hr1 hthreshold d
  have hv := lowerSixRecoveryComplementVariation_nonnegative_of_descent
    (by simpa only [Nat.add_assoc] using hfall)
  unfold lowerSixRecoveryAbelVariationTerm
  exact Q'.mul_nonneg _ _ hp hv

/-! ## Kernel fence: carrier and prefix do not cross together -/

/-- At the first post-bootstrap scale the carrier is already nonnegative at
mode 17 while its prefix is still strictly negative.  Any splice must track a
separate prefix-crossing index; identifying it with the carrier crossing is
machine-refuted. -/
theorem lowerSixRecoveryCarrierPrefix_sameCrossing_648_17_fails :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrier (648 + 1) 17 ∧
      lowerSixRecoveryNextCarrierPrefix 648 17 < (0 : Q') := by
  constructor
  · unfold lowerSixRecoveryLinearCarrier lowerSixRecoveryModeSlope
      thetaResidualCellSlope harmW harmU ReciprocalBernoulliUpper.oneSub
      SummableInverseSquare.unit qpow
    decide
  · unfold lowerSixRecoveryNextCarrierPrefix
      lowerSixRecoveryLinearCarrier lowerSixRecoveryModeSlope
      thetaResidualCellSlope harmW harmU ReciprocalBernoulliUpper.oneSub
      SummableInverseSquare.unit finSum qpow
    decide

#print axioms lowerSixRecoveryLinearCarrier_nonnegative_mono
#print axioms lowerSixRecoveryLinearCarrier_nonpositive_anti
#print axioms lowerSixRecoveryNextCarrierPrefix_succ
#print axioms lowerSixRecoveryNextCarrierPrefix_nonpositive_of_carrier
#print axioms lowerSixRecoveryNextCarrierPrefix_tail_mono
#print axioms lowerSixRecoveryNextCarrierPrefix_nonnegative_mono
#print axioms lowerSixRecoveryComplementVariation_nonnegative_of_exponent_ge_scale
#print axioms lowerSixRecoveryAbelVariationTerm_nonnegative_on_rising_carrierHead
#print axioms lowerSixRecoveryAbelVariationTerm_nonpositive_on_negativePrefix_fall
#print axioms lowerSixRecoveryAbelVariationTerm_tail_nonnegative
#print axioms lowerSixRecoveryCarrierPrefix_sameCrossing_648_17_fails

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPrefixVariation
