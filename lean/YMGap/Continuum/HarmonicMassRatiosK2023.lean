/- Exact spacing-compatible mass ratios supplied by the fixed-nine prefix. -/

import YMGap.Continuum.HarmonicFixedNinePrefix
import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicMassRatiosK2023

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFixedNinePrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

/-! ## Fixed-prefix upper certificates -/

theorem harmonic_prefix_upper_k20 :
    coordNormSq (harmW 20) 8 - adjCorr (harmW 20) 8 ≤
      Q'.mkPos 7 100 (by decide) * coordNormSq (harmW 20) 8 := by
  decide

theorem harmonic_mass_upper_k20 :
    harmonicMass 20 ≤ Q'.mkPos 7 100 (by decide) :=
  harmonicMass_le_of_prefix 20 8 476 _ (by decide) harmonic_prefix_upper_k20

theorem harmonic_prefix_upper_k21 :
    coordNormSq (harmW 21) 8 - adjCorr (harmW 21) 8 ≤
      Q'.mkPos 17 250 (by decide) * coordNormSq (harmW 21) 8 := by
  decide

theorem harmonic_mass_upper_k21 :
    harmonicMass 21 ≤ Q'.mkPos 17 250 (by decide) :=
  harmonicMass_le_of_prefix 21 8 521 _ (by decide) harmonic_prefix_upper_k21

theorem harmonic_prefix_upper_k22 :
    coordNormSq (harmW 22) 8 - adjCorr (harmW 22) 8 ≤
      Q'.mkPos 13 200 (by decide) * coordNormSq (harmW 22) 8 := by
  decide

theorem harmonic_mass_upper_k22 :
    harmonicMass 22 ≤ Q'.mkPos 13 200 (by decide) :=
  harmonicMass_le_of_prefix 22 8 568 _ (by decide) harmonic_prefix_upper_k22

theorem harmonic_prefix_upper_k23 :
    coordNormSq (harmW 23) 8 - adjCorr (harmW 23) 8 ≤
      Q'.mkPos 1 16 (by decide) * coordNormSq (harmW 23) 8 := by
  decide

theorem harmonic_mass_upper_k23 :
    harmonicMass 23 ≤ Q'.mkPos 1 16 (by decide) :=
  harmonicMass_le_of_prefix 23 8 617 _ (by decide) harmonic_prefix_upper_k23

/-! ## Rational consequences of the fixed-nine floors -/

theorem harmonic_mass_lower_k21 :
    Q'.mkPos 3 50 (by decide) ≤ harmonicMass 21 := by
  have hfloor : Q'.mkPos 3 50 (by decide) ≤
      (1 : Q') - retuneCube (harmW 21) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k21_nine_floor

theorem harmonic_mass_lower_k22 :
    Q'.mkPos 3 50 (by decide) ≤ harmonicMass 22 := by
  have hfloor : Q'.mkPos 3 50 (by decide) ≤
      (1 : Q') - retuneCube (harmW 22) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k22_nine_floor

theorem harmonic_mass_lower_k23 :
    Q'.mkPos 1 18 (by decide) ≤ harmonicMass 23 := by
  have hfloor : Q'.mkPos 1 18 (by decide) ≤
      (1 : Q') - retuneCube (harmW 23) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k23_nine_floor

theorem harmonic_mass_lower_k24 :
    Q'.mkPos 1 18 (by decide) ≤ harmonicMass 24 := by
  have hfloor : Q'.mkPos 1 18 (by decide) ≤
      (1 : Q') - retuneCube (harmW 24) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k24_nine_floor

/-! ## Exact rotation ratios -/

theorem harmonicMass_ratio_k20 :
    Q'.ofNat 3636 * harmonicMass 20 ≤ Q'.ofNat 4761 * harmonicMass 21 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3636)
    harmonic_mass_upper_k20 (by decide)
  have hmiddle :
      Q'.ofNat 3636 * Q'.mkPos 7 100 (by decide) ≤
        Q'.ofNat 4761 * Q'.mkPos 3 50 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4761)
    harmonic_mass_lower_k21 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

theorem harmonicMass_ratio_k21 :
    Q'.ofNat 4009 * harmonicMass 21 ≤ Q'.ofNat 5184 * harmonicMass 22 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4009)
    harmonic_mass_upper_k21 (by decide)
  have hmiddle :
      Q'.ofNat 4009 * Q'.mkPos 17 250 (by decide) ≤
        Q'.ofNat 5184 * Q'.mkPos 3 50 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 5184)
    harmonic_mass_lower_k22 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

theorem harmonicMass_ratio_k22 :
    Q'.ofNat 4400 * harmonicMass 22 ≤ Q'.ofNat 5625 * harmonicMass 23 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4400)
    harmonic_mass_upper_k22 (by decide)
  have hmiddle :
      Q'.ofNat 4400 * Q'.mkPos 13 200 (by decide) ≤
        Q'.ofNat 5625 * Q'.mkPos 1 18 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 5625)
    harmonic_mass_lower_k23 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

theorem harmonicMass_ratio_k23 :
    Q'.ofNat 4809 * harmonicMass 23 ≤ Q'.ofNat 6084 * harmonicMass 24 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4809)
    harmonic_mass_upper_k23 (by decide)
  have hmiddle :
      Q'.ofNat 4809 * Q'.mkPos 1 16 (by decide) ≤
        Q'.ofNat 6084 * Q'.mkPos 1 18 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6084)
    harmonic_mass_lower_k24 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

end YMGap.Continuum.HarmonicMassRatiosK2023

#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_prefix_upper_k20
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_prefix_upper_k21
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_prefix_upper_k22
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_prefix_upper_k23
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_upper_k20
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_upper_k21
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_upper_k22
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_upper_k23
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_lower_k21
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_lower_k22
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_lower_k23
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonic_mass_lower_k24
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonicMass_ratio_k20
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonicMass_ratio_k21
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonicMass_ratio_k22
#print axioms YMGap.Continuum.HarmonicMassRatiosK2023.harmonicMass_ratio_k23
