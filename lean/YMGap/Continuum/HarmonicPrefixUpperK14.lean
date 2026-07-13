import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicPrefixUpperK14

set_option maxHeartbeats 7000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

theorem harmonic_prefix_upper_k14 :
    coordNormSq (harmW 14) 5 - adjCorr (harmW 14) 5 ≤
      Q'.mkPos 3 25 (by decide) * coordNormSq (harmW 14) 5 := by
  decide

theorem harmonic_mass_upper_k14 :
    harmonicMass 14 ≤ Q'.mkPos 3 25 (by decide) :=
  harmonicMass_le_of_prefix 14 5 251 _ (by decide) harmonic_prefix_upper_k14

theorem harmonic_mass_lower_k15 :
    Q'.mkPos 1 12 (by decide) ≤ harmonicMass 15 := by
  have hfloor : Q'.mkPos 1 12 (by decide) ≤
      (1 : Q') - retuneCube (harmW 15) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor
    SevenAnchorWindowRetune.harmonicMass_k15_retune_floor

end YMGap.Continuum.HarmonicPrefixUpperK14

#print axioms YMGap.Continuum.HarmonicPrefixUpperK14.harmonic_prefix_upper_k14
#print axioms YMGap.Continuum.HarmonicPrefixUpperK14.harmonic_mass_upper_k14
#print axioms YMGap.Continuum.HarmonicPrefixUpperK14.harmonic_mass_lower_k15
