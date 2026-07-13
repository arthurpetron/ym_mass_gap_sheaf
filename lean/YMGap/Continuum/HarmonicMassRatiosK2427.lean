/- Exact spacing-compatible mass ratios supplied by the fixed-ten prefix. -/

import YMGap.Continuum.HarmonicFixedTenPrefix
import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicMassRatiosK2427

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFixedTenPrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

theorem harmonic_prefix_upper_k24 :
    coordNormSq (harmW 24) 9 - adjCorr (harmW 24) 9 ≤
      Q'.mkPos 3 50 (by decide) * coordNormSq (harmW 24) 9 := by decide
theorem harmonic_mass_upper_k24 : harmonicMass 24 ≤ Q'.mkPos 3 50 (by decide) :=
  harmonicMass_le_of_prefix 24 9 667 _ (by decide) harmonic_prefix_upper_k24

theorem harmonic_prefix_upper_k25 :
    coordNormSq (harmW 25) 9 - adjCorr (harmW 25) 9 ≤
      Q'.mkPos 23 400 (by decide) * coordNormSq (harmW 25) 9 := by decide
theorem harmonic_mass_upper_k25 : harmonicMass 25 ≤ Q'.mkPos 23 400 (by decide) :=
  harmonicMass_le_of_prefix 25 9 720 _ (by decide) harmonic_prefix_upper_k25

theorem harmonic_prefix_upper_k26 :
    coordNormSq (harmW 26) 9 - adjCorr (harmW 26) 9 ≤
      Q'.mkPos 11 200 (by decide) * coordNormSq (harmW 26) 9 := by decide
theorem harmonic_mass_upper_k26 : harmonicMass 26 ≤ Q'.mkPos 11 200 (by decide) :=
  harmonicMass_le_of_prefix 26 9 775 _ (by decide) harmonic_prefix_upper_k26

theorem harmonic_prefix_upper_k27 :
    coordNormSq (harmW 27) 9 - adjCorr (harmW 27) 9 ≤
      Q'.mkPos 27 500 (by decide) * coordNormSq (harmW 27) 9 := by decide
theorem harmonic_mass_upper_k27 : harmonicMass 27 ≤ Q'.mkPos 27 500 (by decide) :=
  harmonicMass_le_of_prefix 27 9 832 _ (by decide) harmonic_prefix_upper_k27

theorem harmonic_mass_lower_k25 : Q'.mkPos 1 20 (by decide) ≤ harmonicMass 25 := by
  have h : Q'.mkPos 1 20 (by decide) ≤ (1 : Q') - retuneCube (harmW 25) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k25_ten_floor
theorem harmonic_mass_lower_k26 : Q'.mkPos 1 20 (by decide) ≤ harmonicMass 26 := by
  have h : Q'.mkPos 1 20 (by decide) ≤ (1 : Q') - retuneCube (harmW 26) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k26_ten_floor
theorem harmonic_mass_lower_k27 : Q'.mkPos 1 20 (by decide) ≤ harmonicMass 27 := by
  have h : Q'.mkPos 1 20 (by decide) ≤ (1 : Q') - retuneCube (harmW 27) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k27_ten_floor
theorem harmonic_mass_lower_k28 : Q'.mkPos 6 125 (by decide) ≤ harmonicMass 28 := by
  have h : Q'.mkPos 6 125 (by decide) ≤ (1 : Q') - retuneCube (harmW 28) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ h harmonicMass_k28_ten_floor

theorem harmonicMass_ratio_k24 :
    Q'.ofNat 5236 * harmonicMass 24 ≤ Q'.ofNat 6561 * harmonicMass 25 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 5236)
    harmonic_mass_upper_k24 (by decide)
  have hm : Q'.ofNat 5236 * Q'.mkPos 3 50 (by decide) ≤
      Q'.ofNat 6561 * Q'.mkPos 1 20 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6561)
    harmonic_mass_lower_k25 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k25 :
    Q'.ofNat 5681 * harmonicMass 25 ≤ Q'.ofNat 7056 * harmonicMass 26 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 5681)
    harmonic_mass_upper_k25 (by decide)
  have hm : Q'.ofNat 5681 * Q'.mkPos 23 400 (by decide) ≤
      Q'.ofNat 7056 * Q'.mkPos 1 20 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 7056)
    harmonic_mass_lower_k26 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k26 :
    Q'.ofNat 6144 * harmonicMass 26 ≤ Q'.ofNat 7569 * harmonicMass 27 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6144)
    harmonic_mass_upper_k26 (by decide)
  have hm : Q'.ofNat 6144 * Q'.mkPos 11 200 (by decide) ≤
      Q'.ofNat 7569 * Q'.mkPos 1 20 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 7569)
    harmonic_mass_lower_k27 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

theorem harmonicMass_ratio_k27 :
    Q'.ofNat 6625 * harmonicMass 27 ≤ Q'.ofNat 8100 * harmonicMass 28 := by
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6625)
    harmonic_mass_upper_k27 (by decide)
  have hm : Q'.ofNat 6625 * Q'.mkPos 27 500 (by decide) ≤
      Q'.ofNat 8100 * Q'.mkPos 6 125 (by decide) := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8100)
    harmonic_mass_lower_k28 (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hm hl)

end YMGap.Continuum.HarmonicMassRatiosK2427

#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_prefix_upper_k24
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_prefix_upper_k25
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_prefix_upper_k26
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_prefix_upper_k27
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_upper_k24
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_upper_k25
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_upper_k26
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_upper_k27
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_lower_k25
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_lower_k26
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_lower_k27
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonic_mass_lower_k28
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonicMass_ratio_k24
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonicMass_ratio_k25
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonicMass_ratio_k26
#print axioms YMGap.Continuum.HarmonicMassRatiosK2427.harmonicMass_ratio_k27
