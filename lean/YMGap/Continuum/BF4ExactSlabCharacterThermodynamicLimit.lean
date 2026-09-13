/-
# Constructed thermodynamic limit of ORIGINAL single-plaquette character means

At the existing w=1/1024 pilot, the proved normalized inter-volume estimate
constructs the limit for each physical base face and representation label.
The outer volume modulus and every per-volume approximation modulus are
returned as data. The limit is the existing completeness engine's explicit
diagonal of the SAME normalized expectations; no modulus is extracted from
an erased existential, and no new summability or compatibility input is used.

This is a single-observable thermodynamic limit at fixed coupling/spacing.
It does not construct a full state on the observable algebra, a physical
transfer/vacuum/gap, or a continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay
import YMGap.Continuum.RegularLinearGeometricModulus
import YMGap.Constructive.CRealCompleteRate
import YMGap.Constructive.CRealAbsContinuity

namespace YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.BF4ExactSlabGeometricBoundaryBudget
open YMGap.Continuum.BF4ExactSlabSummableCoreRate
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private theorem deltaGuard : QuaternionHaarCharacterInterval.heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2

private theorem countGuard : entropyRate 625 (adjustedCoreRate nome deltaGuard) < 1 :=
  existingNome_entropyRate.2

local notation "hd" => deltaGuard
local notation "hs" => countGuard

def rate : Q' := entropyRate 625 (adjustedCoreRate nome hd)

theorem rate_pos : (0 : Q') < rate := existingNome_entropyRate.1

/-- A proved half-power envelope at THIS coupling, used only for the modulus. -/
theorem rate_le_half : rate ≤ HalfPow.half := by
  have hr : adjustedCoreRate nome hd ≤ pairedHeatRate nome * 64 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ existingNome_inversePower_bound (Q'.le_of_lt existingNome_rate.1)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hr (by decide : (0 : Q') ≤ 625))
    (by change (625 : Q') * (pairedHeatRate nome * 64) ≤ HalfPow.half; decide)

def amplitude (spin : Nat) : Q' := characterAmplitude nome hd hs spin

theorem amplitude_nonnegative (spin : Nat) : (0 : Q') ≤ amplitude spin :=
  Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) spin))
      (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (by decide) spin)))
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (probePrefactor_nonnegative nome hd 4) (by decide))
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))

def volumeModulus (spin : Nat) (epsilon : Q') : Nat := geoOuterModulus (amplitude spin) epsilon

theorem volumeModulus_antitone (spin : Nat) : MmonoPred (volumeModulus spin) :=
  geoOuterModulus_mono (amplitude spin)

theorem coefficient_small (spin : Nat) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m : Nat) (hm : volumeModulus spin epsilon ≤ m) : amplitude spin * rate^m ≤ epsilon := by
  have hC := amplitude_nonnegative spin
  have htwo : amplitude spin ≤ Q'.ofNat 2 * amplitude spin :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hC)
      (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)) (by decide) (fun _ => amplitude spin)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (TotalMajorantClose.pow_le_pow_base (Q'.le_of_lt rate_pos) rate_le_half m) hC)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ htwo (Q'.pow_nonneg _ HalfPow.half_nonneg m))
      (geoTail_le_of_modulus (amplitude spin) hC epsilon he m hm))

def meanSequence (base : Nat) (face : Z4Plaq) (spin : Nat) : Nat → CReal :=
  characterMean nome nome_pos nome_lt_one base face spin

def meanSequenceCauchy (base : Nat) (face : Z4Plaq) (spin margin : Nat) :
    QCauchy (meanSequence base face spin margin).approx :=
  expectationCauchy nome nome_pos nome_lt_one (base+margin) (shiftedCharacter base margin face spin)

def innerModulus (base : Nat) (face : Z4Plaq) (spin margin : Nat) : Q' → Nat :=
  (meanSequenceCauchy base face spin margin).M

theorem inner_regular (base : Nat) (face : Z4Plaq) (spin : Nat) :
    RegPred (meanSequence base face spin) (innerModulus base face spin) :=
  fun m => (meanSequenceCauchy base face spin m).bound

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

theorem outer_cauchy {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (spin : Nat) :
    LeRatBound (meanSequence base face spin) (volumeModulus spin) := by
  intro epsilon he m n hm hn
  have step (i j : Nat) (hij : i ≤ j) (hi : volumeModulus spin epsilon ≤ i) :
      leRat (CReal.sub (meanSequence base face spin j) (meanSequence base face spin i)) epsilon ∧
      leRat (CReal.sub (meanSequence base face spin i) (meanSequence base face spin j)) epsilon := by
    have h := existingNome_characterMean_difference_bound hf i (j-i) spin
    dsimp only at h
    rw [Nat.add_sub_of_le hij] at h
    exact two_sided_of_abs (leEv_trans h
      (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small spin epsilon he i hi)))
  rcases Nat.le_total m n with hmn | hnm
  · exact (step m n hmn hm).symm
  · exact step n m hnm hn

/-- The original normalized expectation diagonal, with explicit outer and inner moduli. -/
def meanLimit {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (spin : Nat) : CReal :=
  completeLimitFromRate (meanSequence base face spin) (volumeModulus spin) (innerModulus base face spin)
    (inner_regular base face spin) (outer_cauchy hf spin)

theorem meanLimit_converges {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (spin : Nat) :
    ConvergesTo (meanSequence base face spin) (meanLimit hf spin) :=
  convergesTo_completeLimitFromRate _ _ _ (inner_regular base face spin) (outer_cauchy hf spin)
    (volumeModulus_antitone spin)

/-- Regularity of the returned limit representative is itself Type-level data. -/
def meanLimitCauchy {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (spin : Nat) :
    QCauchy (meanLimit hf spin).approx where
  M epsilon := (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · exact diagSeqR_directed _ _ _ (inner_regular base face spin) (outer_cauchy hf spin) epsilon he m n hmn hm
    · exact (diagSeqR_directed _ _ _ (inner_regular base face spin) (outer_cauchy hf spin) epsilon he n m hnm hn).symm

/-- The original geometric rate survives passage to thermodynamic volume. -/
theorem meanLimit_geometric_bound {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (spin margin : Nat) :
    leEv (CReal.abs (CReal.sub (meanLimit hf spin) (meanSequence base face spin margin)))
      (ofQ' (amplitude spin * rate^margin)) := by
  have ht : ConvergesTo (fun p => meanSequence base face spin (margin+p)) (meanLimit hf spin) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := meanLimit_converges hf spin epsilon he
    exact ⟨N, fun n hn => hN (margin+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩
  have hsub := convergesTo_add ht (TrigAddCReal.convergesTo_neg (convergesTo_const (meanSequence base face spin margin)))
  exact leEv_of_convergesTo_le (convergesTo_abs hsub) (convergesTo_const _)
    (fun p => existingNome_characterMean_difference_bound hf margin p spin)

/-- The returned volume modulus bounds the actual error to the returned limit. -/
theorem meanLimit_error_le {base : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (spin : Nat)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : volumeModulus spin epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (meanLimit hf spin) (meanSequence base face spin margin))) (ofQ' epsilon) :=
  leEv_trans (meanLimit_geometric_bound hf spin margin)
    (leEv_le_ofQ'_of_approx_le (fun _ => coefficient_small spin epsilon he margin hm))

end YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit

#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.rate
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.rate_pos
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.rate_le_half
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.amplitude
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.amplitude_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.volumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.volumeModulus_antitone
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.coefficient_small
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanSequence
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanSequenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.innerModulus
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.inner_regular
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.outer_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanLimit
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanLimit_converges
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanLimit_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabCharacterThermodynamicLimit.meanLimit_error_le
