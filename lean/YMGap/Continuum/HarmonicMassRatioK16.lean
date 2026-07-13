import YMGap.Continuum.HarmonicDABoundTransport
import YMGap.Continuum.HarmonicFixedSixFloorK17

namespace YMGap.Continuum.HarmonicMassRatioK16

set_option maxHeartbeats 7000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicFixedSixFloorK17
open YMGap.Continuum.HarmonicWeightDriftFence

theorem harmonicMass_ratio_k16 :
    Q'.ofNat 2324 * harmonicMass 16 ≤ Q'.ofNat 3249 * harmonicMass 17 := by
  have hu : harmonicMass 16 ≤ Q'.mkPos 9 100 (by decide) :=
    harmonicMass_le_of_prefix 16 6 318 _ (by decide) (by decide)
  have hup := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2324) hu (by decide)
  have hmiddle :
      Q'.ofNat 2324 * Q'.mkPos 9 100 (by decide) ≤
        Q'.ofNat 3249 * Q'.mkPos 1 15 (by decide) := by
    decide
  have hlo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3249)
    harmonicMass_k17_fixed_floor (by decide)
  exact Q'.le_trans' _ _ _ hup (Q'.le_trans' _ _ _ hmiddle hlo)

end YMGap.Continuum.HarmonicMassRatioK16

#print axioms YMGap.Continuum.HarmonicMassRatioK16.harmonicMass_ratio_k16
