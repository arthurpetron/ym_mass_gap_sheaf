import YMGap.Continuum.HarmonicBoundsK13

namespace YMGap.Continuum.HarmonicMassRatioK13

set_option maxHeartbeats 7000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicBoundsK13
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ArbitraryTruncationRetuneCorr

theorem harmonicMass_ratio_k13 :
    Q'.ofNat 1529 * harmonicMass 13 ≤ Q'.ofNat 2304 * harmonicMass 14 := by
  have hu : harmonicMass 13 ≤ Q'.mkPos 1 8 (by decide) :=
    harmonic_mass_upper_k13
  have hl : Q'.mkPos 9 100 (by decide) ≤ harmonicMass 14 :=
    harmonic_mass_lower_k14
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 1529) hu (by decide)
  have hmiddle :
      Q'.ofNat 1529 * Q'.mkPos 1 8 (by decide) ≤
        Q'.ofNat 2304 * Q'.mkPos 9 100 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2304) hl (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

end YMGap.Continuum.HarmonicMassRatioK13

#print axioms YMGap.Continuum.HarmonicMassRatioK13.harmonicMass_ratio_k13
