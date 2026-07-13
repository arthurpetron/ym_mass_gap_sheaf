import YMGap.Continuum.HarmonicDABoundTransport

namespace YMGap.Continuum.HarmonicBoundsK15

open YMGap.Constructive
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.RGTransport

theorem harmonic_prefix_upper_k15 :
    coordNormSq (harmW 15) 6 - adjCorr (harmW 15) 6 ≤
      Q'.mkPos 1 10 (by decide) * coordNormSq (harmW 15) 6 := by
  decide

theorem harmonic_mass_upper_k15 :
    harmonicMass 15 ≤ Q'.mkPos 1 10 (by decide) :=
  harmonicMass_le_of_prefix 15 6 283 _ (by decide) harmonic_prefix_upper_k15

theorem harmonic_mass_lower_k16 :
    Q'.mkPos 2 25 (by decide) ≤ harmonicMass 16 := by
  have hfloor : Q'.mkPos 2 25 (by decide) ≤
      (1 : Q') - retuneCube (harmW 16) := by
    unfold retuneCube retuneBase harmW harmU
      ReciprocalBernoulliUpper.oneSub SummableInverseSquare.unit qpow
    decide
  exact Q'.le_trans' _ _ _ hfloor
    SevenAnchorWindowRetune.harmonicMass_k16_retune_floor

end YMGap.Continuum.HarmonicBoundsK15

#print axioms YMGap.Continuum.HarmonicBoundsK15.harmonic_prefix_upper_k15
#print axioms YMGap.Continuum.HarmonicBoundsK15.harmonic_mass_upper_k15
#print axioms YMGap.Continuum.HarmonicBoundsK15.harmonic_mass_lower_k16
