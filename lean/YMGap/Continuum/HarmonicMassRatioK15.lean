import YMGap.Continuum.HarmonicBoundsK15

namespace YMGap.Continuum.HarmonicMassRatioK15

set_option maxHeartbeats 7000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicBoundsK15
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ArbitraryTruncationRetuneCorr

theorem harmonicMass_ratio_k15 :
    Q'.ofNat 2041 * harmonicMass 15 ≤ Q'.ofNat 2916 * harmonicMass 16 := by
  have hu : harmonicMass 15 ≤ Q'.mkPos 1 10 (by decide) :=
    harmonic_mass_upper_k15
  have hl : Q'.mkPos 2 25 (by decide) ≤ harmonicMass 16 :=
    harmonic_mass_lower_k16
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2041) hu (by decide)
  have hmiddle :
      Q'.ofNat 2041 * Q'.mkPos 1 10 (by decide) ≤
        Q'.ofNat 2916 * Q'.mkPos 2 25 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2916) hl (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

end YMGap.Continuum.HarmonicMassRatioK15

#print axioms YMGap.Continuum.HarmonicMassRatioK15.harmonicMass_ratio_k15
