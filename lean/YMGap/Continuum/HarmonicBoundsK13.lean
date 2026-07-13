import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicBoundsK13

open YMGap.Constructive
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

theorem harmonic_prefix_upper_k13 :
    coordNormSq (harmW 13) 5 - adjCorr (harmW 13) 5 ≤
      Q'.mkPos 1 8 (by decide) * coordNormSq (harmW 13) 5 := by
  decide

theorem harmonic_mass_upper_k13 :
    harmonicMass 13 ≤ Q'.mkPos 1 8 (by decide) :=
  harmonicMass_le_of_prefix 13 5 220 _ (by decide) harmonic_prefix_upper_k13

theorem harmonic_mass_lower_k14 :
    Q'.mkPos 9 100 (by decide) ≤ harmonicMass 14 := by
  have hfloor : Q'.mkPos 9 100 (by decide) ≤
      (1 : Q') - retuneCube (harmW 14) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor
    SevenAnchorWindowRetune.harmonicMass_k14_retune_floor

end YMGap.Continuum.HarmonicBoundsK13

#print axioms YMGap.Continuum.HarmonicBoundsK13.harmonic_prefix_upper_k13
#print axioms YMGap.Continuum.HarmonicBoundsK13.harmonic_mass_upper_k13
#print axioms YMGap.Continuum.HarmonicBoundsK13.harmonic_mass_lower_k14
