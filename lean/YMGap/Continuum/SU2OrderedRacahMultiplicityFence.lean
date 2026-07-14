/-
# Multiplicity audit for the raw ordered F / Racah comparison
-/

import YMGap.Continuum.SU2OrderedFixedOutputFKernel

namespace YMGap.Continuum.SU2OrderedRacahMultiplicityFence

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

def zeroLeft : FixedLeftCGChannel 0 1 1 0 where
  k := 0
  k_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

def zeroRight : FixedRightCGChannel 0 1 1 0 where
  p := 1
  p_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

theorem zero_raw_F_eq_one :
    fixedOrderedFCoefficient zeroLeft zeroRight ≈ 1 := by
  decide

theorem zero_racahKernel_eq_one :
    racahKernel6 0 1 1 0 1 0 ≈ 1 := by
  decide

/-- **Dimension-only normalization is false outside the fundamental block.**
Here it would equate `dim(0)*1 = 1` with `dim(1)*1² = 2`. -/
theorem dimension_only_bridge_refuted :
    ¬ FixedOrderedRacahBridgeAt zeroLeft zeroRight := by
  unfold FixedOrderedRacahBridgeAt
  decide

/-- The all-label raw normalization uses the actual invariant channel Gram
weights, not the intermediate dimensions alone. -/
def GramWeightedRacahBridgeAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Prop :=
  triRightChannelWeight a b c d qR.intermediate *
      racahKernel6 a b c d qL.intermediate qR.intermediate ≈
    triLeftChannelWeight a b c d qL.intermediate *
      (@fixedOrderedFCoefficient a b c d qL qR *
        @fixedOrderedFCoefficient a b c d qL qR)

/-- The corrected Gram-weighted identity passes the zero-leg counterexample. -/
theorem zero_gramWeighted_bridge :
    @GramWeightedRacahBridgeAt 0 1 1 0 zeroLeft zeroRight := by
  unfold GramWeightedRacahBridgeAt
  decide

private def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d := by
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c hab)
    (Q'.mul_eqv_congr_left b c d hcd)

theorem fundamental_channel_weights :
    triLeftChannelWeight 1 1 1 1 0 ≈ 4 ∧
    triLeftChannelWeight 1 1 1 1 2 ≈ 12 ∧
    triRightChannelWeight 1 1 1 1 0 ≈ 4 ∧
    triRightChannelWeight 1 1 1 1 2 ≈ 12 := by
  decide

theorem fundamental_racahKernel_entries :
    racahKernel6 1 1 1 1 0 0 ≈ oneQuarter ∧
    racahKernel6 1 1 1 1 0 2 ≈ threeQuarters ∧
    racahKernel6 1 1 1 1 2 0 ≈ threeQuarters ∧
    racahKernel6 1 1 1 1 2 2 ≈ oneQuarter := by
  decide

theorem fundamental_fixedF_entries :
    @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ≈ -fundamentalHalf ∧
    @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ≈ fundamentalThreeHalves ∧
    @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ≈ fundamentalHalf ∧
    @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet ≈ fundamentalHalf := by
  decide

/-- The corrected Gram-weighted identity also passes all four entries of the
fundamental block. -/
theorem fundamental_gramWeighted_bridges :
    @GramWeightedRacahBridgeAt 1 1 1 1 fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ∧
    @GramWeightedRacahBridgeAt 1 1 1 1 fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ∧
    @GramWeightedRacahBridgeAt 1 1 1 1 fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ∧
    @GramWeightedRacahBridgeAt 1 1 1 1 fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet := by
  constructor
  · have hL : triRightChannelWeight 1 1 1 1 0 *
        racahKernel6 1 1 1 1 0 0 ≈ 1 :=
      Q'.eqv_trans _ _ _
        (mul_eqv_congr fundamental_channel_weights.2.2.1
          fundamental_racahKernel_entries.1) (by decide)
    have hF := fundamental_fixedF_entries.1
    have hR : triLeftChannelWeight 1 1 1 1 0 *
        (@fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftSinglet
            fundamentalFixedRightSinglet *
          @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftSinglet
            fundamentalFixedRightSinglet) ≈ 1 :=
      Q'.eqv_trans _ _ _
        (mul_eqv_congr fundamental_channel_weights.1
          (mul_eqv_congr hF hF)) (by decide)
    exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)
  · constructor
    · have hL : triRightChannelWeight 1 1 1 1 2 *
          racahKernel6 1 1 1 1 0 2 ≈ 9 :=
        Q'.eqv_trans _ _ _
          (mul_eqv_congr fundamental_channel_weights.2.2.2
            fundamental_racahKernel_entries.2.1) (by decide)
      have hF := fundamental_fixedF_entries.2.1
      have hR : triLeftChannelWeight 1 1 1 1 0 *
          (@fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftSinglet
              fundamentalFixedRightTriplet *
            @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftSinglet
              fundamentalFixedRightTriplet) ≈ 9 :=
        Q'.eqv_trans _ _ _
          (mul_eqv_congr fundamental_channel_weights.1
            (mul_eqv_congr hF hF)) (by decide)
      exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)
    · constructor
      · have hL : triRightChannelWeight 1 1 1 1 0 *
            racahKernel6 1 1 1 1 2 0 ≈ 3 :=
          Q'.eqv_trans _ _ _
            (mul_eqv_congr fundamental_channel_weights.2.2.1
              fundamental_racahKernel_entries.2.2.1) (by decide)
        have hF := fundamental_fixedF_entries.2.2.1
        have hR : triLeftChannelWeight 1 1 1 1 2 *
            (@fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftTriplet
                fundamentalFixedRightSinglet *
              @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftTriplet
                fundamentalFixedRightSinglet) ≈ 3 :=
          Q'.eqv_trans _ _ _
            (mul_eqv_congr fundamental_channel_weights.2.1
              (mul_eqv_congr hF hF)) (by decide)
        exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)
      · have hL : triRightChannelWeight 1 1 1 1 2 *
            racahKernel6 1 1 1 1 2 2 ≈ 3 :=
          Q'.eqv_trans _ _ _
            (mul_eqv_congr fundamental_channel_weights.2.2.2
              fundamental_racahKernel_entries.2.2.2) (by decide)
        have hF := fundamental_fixedF_entries.2.2.2
        have hR : triLeftChannelWeight 1 1 1 1 2 *
            (@fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftTriplet
                fundamentalFixedRightTriplet *
              @fixedOrderedFCoefficient 1 1 1 1 fundamentalFixedLeftTriplet
                fundamentalFixedRightTriplet) ≈ 3 :=
          Q'.eqv_trans _ _ _
            (mul_eqv_congr fundamental_channel_weights.2.1
              (mul_eqv_congr hF hF)) (by decide)
        exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

end YMGap.Continuum.SU2OrderedRacahMultiplicityFence

#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.zero_raw_F_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.zero_racahKernel_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.dimension_only_bridge_refuted
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.zero_gramWeighted_bridge
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.fundamental_channel_weights
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.fundamental_racahKernel_entries
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.fundamental_fixedF_entries
#print axioms YMGap.Continuum.SU2OrderedRacahMultiplicityFence.fundamental_gramWeighted_bridges
