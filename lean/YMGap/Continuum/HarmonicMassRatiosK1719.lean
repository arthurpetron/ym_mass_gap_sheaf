/- Exact spacing-compatible mass ratios supplied by the fixed-eight prefix. -/

import YMGap.Continuum.HarmonicFixedEightPrefix
import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicMassRatiosK1719

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFixedEightPrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

/-! ## Opaque fixed-prefix upper bounds -/

theorem harmonic_prefix_upper_k17 :
    coordNormSq (harmW 17) 6 - adjCorr (harmW 17) 6 ≤
      Q'.mkPos 9 100 (by decide) * coordNormSq (harmW 17) 6 := by
  decide

theorem harmonic_mass_upper_k17 :
    harmonicMass 17 ≤ Q'.mkPos 9 100 (by decide) :=
  harmonicMass_le_of_prefix 17 6 355 _ (by decide) harmonic_prefix_upper_k17

theorem harmonic_prefix_upper_k18 :
    coordNormSq (harmW 18) 6 - adjCorr (harmW 18) 6 ≤
      Q'.mkPos 17 200 (by decide) * coordNormSq (harmW 18) 6 := by
  decide

theorem harmonic_mass_upper_k18 :
    harmonicMass 18 ≤ Q'.mkPos 17 200 (by decide) :=
  harmonicMass_le_of_prefix 18 6 394 _ (by decide) harmonic_prefix_upper_k18

theorem harmonic_prefix_upper_k19 :
    coordNormSq (harmW 19) 7 - adjCorr (harmW 19) 7 ≤
      Q'.mkPos 3 40 (by decide) * coordNormSq (harmW 19) 7 := by
  decide

theorem harmonic_mass_upper_k19 :
    harmonicMass 19 ≤ Q'.mkPos 3 40 (by decide) :=
  harmonicMass_le_of_prefix 19 7 434 _ (by decide) harmonic_prefix_upper_k19

/-! ## Rational consequences of the fixed-eight retune floors -/

theorem harmonic_mass_lower_k18 :
    Q'.mkPos 7 100 (by decide) ≤ harmonicMass 18 := by
  have hfloor : Q'.mkPos 7 100 (by decide) ≤
      (1 : Q') - retuneCube (harmW 18) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k18_eight_floor

theorem harmonic_mass_lower_k19 :
    Q'.mkPos 1 15 (by decide) ≤ harmonicMass 19 := by
  have hfloor : Q'.mkPos 1 15 (by decide) ≤
      (1 : Q') - retuneCube (harmW 19) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k19_eight_floor

theorem harmonic_mass_lower_k20 :
    Q'.mkPos 1 16 (by decide) ≤ harmonicMass 20 := by
  have hfloor : Q'.mkPos 1 16 (by decide) ≤
      (1 : Q') - retuneCube (harmW 20) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor harmonicMass_k20_eight_floor

/-! ## Exact coefficients required by the rotated spacing stages -/

theorem harmonicMass_ratio_k17 :
    Q'.ofNat 2625 * harmonicMass 17 ≤ Q'.ofNat 3600 * harmonicMass 18 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2625)
    harmonic_mass_upper_k17 (by decide)
  have hmiddle :
      Q'.ofNat 2625 * Q'.mkPos 9 100 (by decide) ≤
        Q'.ofNat 3600 * Q'.mkPos 7 100 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3600)
    harmonic_mass_lower_k18 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

theorem harmonicMass_ratio_k18 :
    Q'.ofNat 2944 * harmonicMass 18 ≤ Q'.ofNat 3969 * harmonicMass 19 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2944)
    harmonic_mass_upper_k18 (by decide)
  have hmiddle :
      Q'.ofNat 2944 * Q'.mkPos 17 200 (by decide) ≤
        Q'.ofNat 3969 * Q'.mkPos 1 15 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3969)
    harmonic_mass_lower_k19 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

theorem harmonicMass_ratio_k19 :
    Q'.ofNat 3281 * harmonicMass 19 ≤ Q'.ofNat 4356 * harmonicMass 20 := by
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3281)
    harmonic_mass_upper_k19 (by decide)
  have hmiddle :
      Q'.ofNat 3281 * Q'.mkPos 3 40 (by decide) ≤
        Q'.ofNat 4356 * Q'.mkPos 1 16 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4356)
    harmonic_mass_lower_k20 (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

end YMGap.Continuum.HarmonicMassRatiosK1719

#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_prefix_upper_k17
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_prefix_upper_k18
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_prefix_upper_k19
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_mass_upper_k17
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_mass_upper_k18
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_mass_upper_k19
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_mass_lower_k18
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_mass_lower_k19
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonic_mass_lower_k20
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonicMass_ratio_k17
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonicMass_ratio_k18
#print axioms YMGap.Continuum.HarmonicMassRatiosK1719.harmonicMass_ratio_k19
