/- Exact spacing-compatible mass ratios supplied by the fixed-eleven prefix. -/

import YMGap.Continuum.HarmonicFixedElevenPrefix
import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicMassRatiosK2832

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFixedElevenPrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

theorem harmonic_prefix_upper_k28 :
    coordNormSq (harmW 28) 10 - adjCorr (harmW 28) 10 ≤
      Q'.mkPos 13 250 (by decide) * coordNormSq (harmW 28) 10 := by decide
theorem harmonic_mass_upper_k28 : harmonicMass 28 ≤ Q'.mkPos 13 250 (by decide) :=
  harmonicMass_le_of_prefix 28 10 890 _ (by decide) harmonic_prefix_upper_k28

theorem harmonic_prefix_upper_k29 :
    coordNormSq (harmW 29) 10 - adjCorr (harmW 29) 10 ≤
      Q'.mkPos 1 20 (by decide) * coordNormSq (harmW 29) 10 := by decide
theorem harmonic_mass_upper_k29 : harmonicMass 29 ≤ Q'.mkPos 1 20 (by decide) :=
  harmonicMass_le_of_prefix 29 10 951 _ (by decide) harmonic_prefix_upper_k29

theorem harmonic_prefix_upper_k30 :
    coordNormSq (harmW 30) 10 - adjCorr (harmW 30) 10 ≤
      Q'.mkPos 49 1000 (by decide) * coordNormSq (harmW 30) 10 := by decide
theorem harmonic_mass_upper_k30 : harmonicMass 30 ≤ Q'.mkPos 49 1000 (by decide) :=
  harmonicMass_le_of_prefix 30 10 1014 _ (by decide) harmonic_prefix_upper_k30

theorem harmonic_prefix_upper_k31 :
    coordNormSq (harmW 31) 10 - adjCorr (harmW 31) 10 ≤
      Q'.mkPos 6 125 (by decide) * coordNormSq (harmW 31) 10 := by decide
theorem harmonic_mass_upper_k31 : harmonicMass 31 ≤ Q'.mkPos 6 125 (by decide) :=
  harmonicMass_le_of_prefix 31 10 1079 _ (by decide) harmonic_prefix_upper_k31

theorem harmonic_prefix_upper_k32 :
    coordNormSq (harmW 32) 10 - adjCorr (harmW 32) 10 ≤
      Q'.mkPos 47 1000 (by decide) * coordNormSq (harmW 32) 10 := by decide
theorem harmonic_mass_upper_k32 : harmonicMass 32 ≤ Q'.mkPos 47 1000 (by decide) :=
  harmonicMass_le_of_prefix 32 10 1146 _ (by decide) harmonic_prefix_upper_k32

theorem harmonic_mass_lower_k29 : Q'.mkPos 47 1000 (by decide) ≤ harmonicMass 29 := by
  have h : Q'.mkPos 47 1000 (by decide) ≤ (1 : Q') - retuneCube (harmW 29) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k29_eleven_floor
theorem harmonic_mass_lower_k30 : Q'.mkPos 23 500 (by decide) ≤ harmonicMass 30 := by
  have h : Q'.mkPos 23 500 (by decide) ≤ (1 : Q') - retuneCube (harmW 30) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k30_eleven_floor
theorem harmonic_mass_lower_k31 : Q'.mkPos 11 250 (by decide) ≤ harmonicMass 31 := by
  have h : Q'.mkPos 11 250 (by decide) ≤ (1 : Q') - retuneCube (harmW 31) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k31_eleven_floor
theorem harmonic_mass_lower_k32 : Q'.mkPos 43 1000 (by decide) ≤ harmonicMass 32 := by
  have h : Q'.mkPos 43 1000 (by decide) ≤ (1 : Q') - retuneCube (harmW 32) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k32_eleven_floor
theorem harmonic_mass_lower_k33 : Q'.mkPos 21 500 (by decide) ≤ harmonicMass 33 := by
  have h : Q'.mkPos 21 500 (by decide) ≤ (1 : Q') - retuneCube (harmW 33) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k33_eleven_floor

theorem harmonicMass_ratio_k28 :
    Q'.ofNat 7124 * harmonicMass 28 ≤ Q'.ofNat 8649 * harmonicMass 29 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 7124)
    harmonic_mass_upper_k28 (by decide)
  have hm : Q'.ofNat 7124 * Q'.mkPos 13 250 (by decide) ≤
      Q'.ofNat 8649 * Q'.mkPos 47 1000 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8649)
    harmonic_mass_lower_k29 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k29 :
    Q'.ofNat 7641 * harmonicMass 29 ≤ Q'.ofNat 9216 * harmonicMass 30 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 7641)
    harmonic_mass_upper_k29 (by decide)
  have hm : Q'.ofNat 7641 * Q'.mkPos 1 20 (by decide) ≤
      Q'.ofNat 9216 * Q'.mkPos 23 500 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9216)
    harmonic_mass_lower_k30 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k30 :
    Q'.ofNat 8176 * harmonicMass 30 ≤ Q'.ofNat 9801 * harmonicMass 31 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8176)
    harmonic_mass_upper_k30 (by decide)
  have hm : Q'.ofNat 8176 * Q'.mkPos 49 1000 (by decide) ≤
      Q'.ofNat 9801 * Q'.mkPos 11 250 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9801)
    harmonic_mass_lower_k31 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k31 :
    Q'.ofNat 8729 * harmonicMass 31 ≤ Q'.ofNat 10404 * harmonicMass 32 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8729)
    harmonic_mass_upper_k31 (by decide)
  have hm : Q'.ofNat 8729 * Q'.mkPos 6 125 (by decide) ≤
      Q'.ofNat 10404 * Q'.mkPos 43 1000 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 10404)
    harmonic_mass_lower_k32 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k32 :
    Q'.ofNat 9300 * harmonicMass 32 ≤ Q'.ofNat 11025 * harmonicMass 33 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9300)
    harmonic_mass_upper_k32 (by decide)
  have hm : Q'.ofNat 9300 * Q'.mkPos 47 1000 (by decide) ≤
      Q'.ofNat 11025 * Q'.mkPos 21 500 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 11025)
    harmonic_mass_lower_k33 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

end YMGap.Continuum.HarmonicMassRatiosK2832

#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_prefix_upper_k28
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_prefix_upper_k29
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_prefix_upper_k30
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_prefix_upper_k31
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_prefix_upper_k32
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_upper_k28
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_upper_k29
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_upper_k30
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_upper_k31
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_upper_k32
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_lower_k29
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_lower_k30
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_lower_k31
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_lower_k32
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonic_mass_lower_k33
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonicMass_ratio_k28
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonicMass_ratio_k29
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonicMass_ratio_k30
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonicMass_ratio_k31
#print axioms YMGap.Continuum.HarmonicMassRatiosK2832.harmonicMass_ratio_k32
