/- Exact spacing-compatible mass ratios supplied by the fixed-twelve prefix. -/

import YMGap.Continuum.HarmonicFixedTwelvePrefix
import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicMassRatiosK3337

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFixedTwelvePrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction

theorem harmonic_prefix_upper_k33 : coordNormSq (harmW 33) 11 - adjCorr (harmW 33) 11 ≤
    Q'.mkPos 23 500 (by decide) * coordNormSq (harmW 33) 11 := by decide
theorem harmonic_mass_upper_k33 : harmonicMass 33 ≤ Q'.mkPos 23 500 (by decide) :=
  harmonicMass_le_of_prefix 33 11 1214 _ (by decide) harmonic_prefix_upper_k33
theorem harmonic_prefix_upper_k34 : coordNormSq (harmW 34) 11 - adjCorr (harmW 34) 11 ≤
    Q'.mkPos 9 200 (by decide) * coordNormSq (harmW 34) 11 := by decide
theorem harmonic_mass_upper_k34 : harmonicMass 34 ≤ Q'.mkPos 9 200 (by decide) :=
  harmonicMass_le_of_prefix 34 11 1285 _ (by decide) harmonic_prefix_upper_k34
theorem harmonic_prefix_upper_k35 : coordNormSq (harmW 35) 11 - adjCorr (harmW 35) 11 ≤
    Q'.mkPos 11 250 (by decide) * coordNormSq (harmW 35) 11 := by decide
theorem harmonic_mass_upper_k35 : harmonicMass 35 ≤ Q'.mkPos 11 250 (by decide) :=
  harmonicMass_le_of_prefix 35 11 1358 _ (by decide) harmonic_prefix_upper_k35
theorem harmonic_prefix_upper_k36 : coordNormSq (harmW 36) 11 - adjCorr (harmW 36) 11 ≤
    Q'.mkPos 43 1000 (by decide) * coordNormSq (harmW 36) 11 := by decide
theorem harmonic_mass_upper_k36 : harmonicMass 36 ≤ Q'.mkPos 43 1000 (by decide) :=
  harmonicMass_le_of_prefix 36 11 1433 _ (by decide) harmonic_prefix_upper_k36
theorem harmonic_prefix_upper_k37 : coordNormSq (harmW 37) 11 - adjCorr (harmW 37) 11 ≤
    Q'.mkPos 21 500 (by decide) * coordNormSq (harmW 37) 11 := by decide
theorem harmonic_mass_upper_k37 : harmonicMass 37 ≤ Q'.mkPos 21 500 (by decide) :=
  harmonicMass_le_of_prefix 37 11 1510 _ (by decide) harmonic_prefix_upper_k37

theorem harmonic_mass_lower_k34 : Q'.mkPos 41 1000 (by decide) ≤ harmonicMass 34 := by
  have h : Q'.mkPos 41 1000 (by decide) ≤ (1 : Q') - retuneCube (harmW 34) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k34_twelve_floor
theorem harmonic_mass_lower_k35 : Q'.mkPos 39 1000 (by decide) ≤ harmonicMass 35 := by
  have h : Q'.mkPos 39 1000 (by decide) ≤ (1 : Q') - retuneCube (harmW 35) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k35_twelve_floor
theorem harmonic_mass_lower_k36 : Q'.mkPos 19 500 (by decide) ≤ harmonicMass 36 := by
  have h : Q'.mkPos 19 500 (by decide) ≤ (1 : Q') - retuneCube (harmW 36) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k36_twelve_floor
theorem harmonic_mass_lower_k37 : Q'.mkPos 37 1000 (by decide) ≤ harmonicMass 37 := by
  have h : Q'.mkPos 37 1000 (by decide) ≤ (1 : Q') - retuneCube (harmW 37) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k37_twelve_floor
theorem harmonic_mass_lower_k38 : Q'.mkPos 37 1000 (by decide) ≤ harmonicMass 38 := by
  have h : Q'.mkPos 37 1000 (by decide) ≤ (1 : Q') - retuneCube (harmW 38) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k38_twelve_floor

theorem harmonicMass_ratio_k33 : Q'.ofNat 9889 * harmonicMass 33 ≤ Q'.ofNat 11664 * harmonicMass 34 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9889) harmonic_mass_upper_k33 (by decide)
  have hm : Q'.ofNat 9889 * Q'.mkPos 23 500 (by decide) ≤
      Q'.ofNat 11664 * Q'.mkPos 41 1000 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 11664) harmonic_mass_lower_k34 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)
theorem harmonicMass_ratio_k34 : Q'.ofNat 10496 * harmonicMass 34 ≤ Q'.ofNat 12321 * harmonicMass 35 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 10496) harmonic_mass_upper_k34 (by decide)
  have hm : Q'.ofNat 10496 * Q'.mkPos 9 200 (by decide) ≤
      Q'.ofNat 12321 * Q'.mkPos 39 1000 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 12321) harmonic_mass_lower_k35 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)
theorem harmonicMass_ratio_k35 : Q'.ofNat 11121 * harmonicMass 35 ≤ Q'.ofNat 12996 * harmonicMass 36 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 11121) harmonic_mass_upper_k35 (by decide)
  have hm : Q'.ofNat 11121 * Q'.mkPos 11 250 (by decide) ≤
      Q'.ofNat 12996 * Q'.mkPos 19 500 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 12996) harmonic_mass_lower_k36 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)
theorem harmonicMass_ratio_k36 : Q'.ofNat 11764 * harmonicMass 36 ≤ Q'.ofNat 13689 * harmonicMass 37 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 11764) harmonic_mass_upper_k36 (by decide)
  have hm : Q'.ofNat 11764 * Q'.mkPos 43 1000 (by decide) ≤
      Q'.ofNat 13689 * Q'.mkPos 37 1000 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 13689) harmonic_mass_lower_k37 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)
theorem harmonicMass_ratio_k37 : Q'.ofNat 12425 * harmonicMass 37 ≤ Q'.ofNat 14400 * harmonicMass 38 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 12425) harmonic_mass_upper_k37 (by decide)
  have hm : Q'.ofNat 12425 * Q'.mkPos 21 500 (by decide) ≤
      Q'.ofNat 14400 * Q'.mkPos 37 1000 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 14400) harmonic_mass_lower_k38 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

end YMGap.Continuum.HarmonicMassRatiosK3337

#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_prefix_upper_k33
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_prefix_upper_k34
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_prefix_upper_k35
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_prefix_upper_k36
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_prefix_upper_k37
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_upper_k33
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_upper_k34
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_upper_k35
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_upper_k36
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_upper_k37
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_lower_k34
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_lower_k35
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_lower_k36
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_lower_k37
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonic_mass_lower_k38
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonicMass_ratio_k33
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonicMass_ratio_k34
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonicMass_ratio_k35
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonicMass_ratio_k36
#print axioms YMGap.Continuum.HarmonicMassRatiosK3337.harmonicMass_ratio_k37
