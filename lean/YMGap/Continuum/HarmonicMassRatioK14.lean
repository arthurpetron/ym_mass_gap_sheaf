import YMGap.Continuum.HarmonicPrefixUpperK14

namespace YMGap.Continuum.HarmonicMassRatioK14

set_option maxHeartbeats 7000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicPrefixUpperK14
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ArbitraryTruncationRetuneCorr

theorem harmonicMass_ratio_k14 :
    Q'.ofNat 1776 * harmonicMass 14 ≤ Q'.ofNat 2601 * harmonicMass 15 := by
  have hu : harmonicMass 14 ≤ Q'.mkPos 3 25 (by decide) :=
    harmonic_mass_upper_k14
  have hl : Q'.mkPos 1 12 (by decide) ≤ harmonicMass 15 :=
    harmonic_mass_lower_k15
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 1776) hu (by decide)
  have hmiddle :
      Q'.ofNat 1776 * Q'.mkPos 3 25 (by decide) ≤
        Q'.ofNat 2601 * Q'.mkPos 1 12 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2601) hl (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

end YMGap.Continuum.HarmonicMassRatioK14

#print axioms YMGap.Continuum.HarmonicMassRatioK14.harmonicMass_ratio_k14
