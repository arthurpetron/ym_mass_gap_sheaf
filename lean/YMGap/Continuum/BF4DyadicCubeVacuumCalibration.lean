/-
# Dyadic AF tail calibration from the physical lower-cube row

The exact dyadic same-action nome is

    2^n / (2^n + 1).

It is at least `3/4` for every `n >= 2`.  Combining this closed arithmetic
fact with the constructive lower-cube row domination proves the stationary
vacuum bound `pi(0) <= 5/6` uniformly on the dyadic AF tail.

The first two scales are deliberately not absorbed into this theorem:
their nomes are `1/2` and `2/3`, so the one-cube `1/5` activity certificate
is numerically false there.  They remain two finite prefix checks (or require
a multi-cube carrier argument).

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubeRowDomination
import YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
import YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

namespace YMGap.Continuum.BF4DyadicCubeVacuumCalibration

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4FarautAFCutoffGrowth
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact dyadic tail enters the `3/4` window -/

theorem four_le_dyadicHeatDenominator
    {scale : Nat} (hscale : 2 ≤ scale) :
    4 ≤ dyadicHeatDenominator scale := by
  unfold dyadicHeatDenominator
  have hpow :
      2 ^ 2 ≤ 2 ^ scale :=
    Nat.pow_le_pow_right (by decide) hscale
  simpa using hpow

theorem cubeActivityWeightFloor_le_dyadicPadeNome
    {scale : Nat} (hscale : 2 ≤ scale) :
    cubeActivityWeightFloor ≤ dyadicPadeNome scale := by
  have hden :
      4 ≤ dyadicHeatDenominator scale :=
    four_le_dyadicHeatDenominator hscale
  unfold cubeActivityWeightFloor
  show
    (Q'.mkPos 3 4 (by decide)).num *
        ((dyadicPadeNome scale).den : Int) ≤
      (dyadicPadeNome scale).num *
        ((Q'.mkPos 3 4 (by decide)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den,
    dyadicPadeNome_num, dyadicPadeNome_den]
  have hthree :
      3 ≤ dyadicHeatDenominator scale :=
    Nat.le_trans (by decide) hden
  have hnat :
      3 * (dyadicHeatDenominator scale + 1) ≤
        dyadicHeatDenominator scale * 4 := by
    calc
      3 * (dyadicHeatDenominator scale + 1) =
          3 * dyadicHeatDenominator scale + 3 := by
        rw [Nat.mul_add]
      _ ≤ 3 * dyadicHeatDenominator scale +
          dyadicHeatDenominator scale :=
        Nat.add_le_add_left hthree _
      _ = dyadicHeatDenominator scale * 4 := by
        simp only [Nat.mul_succ, Nat.succ_mul,
          Nat.zero_mul, Nat.mul_zero, Nat.zero_add,
          Nat.add_assoc]
  change
    Int.ofNat
        (3 * (dyadicHeatDenominator scale + 1)) ≤
      Int.ofNat
        (dyadicHeatDenominator scale * 4)
  exact Int.ofNat_le.mpr hnat

theorem eight_le_dyadicHeatDenominator
    {scale : Nat} (hscale : 3 ≤ scale) :
    8 ≤ dyadicHeatDenominator scale := by
  unfold dyadicHeatDenominator
  have hpow :
      2 ^ 3 ≤ 2 ^ scale :=
    Nat.pow_le_pow_right (by decide) hscale
  simpa using hpow

theorem cubeActivitySevenWeightFloor_le_dyadicPadeNome
    {scale : Nat} (hscale : 3 ≤ scale) :
    cubeActivitySevenWeightFloor ≤ dyadicPadeNome scale := by
  have hden :
      8 ≤ dyadicHeatDenominator scale :=
    eight_le_dyadicHeatDenominator hscale
  unfold cubeActivitySevenWeightFloor
  show
    (Q'.mkPos 8 9 (by decide)).num *
        ((dyadicPadeNome scale).den : Int) ≤
      (dyadicPadeNome scale).num *
        ((Q'.mkPos 8 9 (by decide)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den,
    dyadicPadeNome_num, dyadicPadeNome_den]
  have hnat :
      8 * (dyadicHeatDenominator scale + 1) ≤
        dyadicHeatDenominator scale * 9 := by
    calc
      8 * (dyadicHeatDenominator scale + 1) =
          8 * dyadicHeatDenominator scale + 8 := by
        rw [Nat.mul_add]
      _ ≤ 8 * dyadicHeatDenominator scale +
          dyadicHeatDenominator scale :=
        Nat.add_le_add_left hden _
      _ = dyadicHeatDenominator scale * 9 := by
        simp only [Nat.mul_succ, Nat.succ_mul,
          Nat.zero_mul, Nat.mul_zero, Nat.zero_add,
          Nat.add_assoc]
  change
    Int.ofNat
        (8 * (dyadicHeatDenominator scale + 1)) ≤
      Int.ofNat
        (dyadicHeatDenominator scale * 9)
  exact Int.ofNat_le.mpr hnat

/-! ## 2. Transport through the exact same-action bridge -/

theorem cubeActivityWeightFloor_le_matchedWeight
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    {scale : Nat} (hscale : 2 ≤ scale) :
    cubeActivityWeightFloor ≤
      matchedAllSpinWeight family coupling scale := by
  have hdyadic :=
    cubeActivityWeightFloor_le_dyadicPadeNome hscale
  have hnome := bridge.nome scale
  change
    matchedAllSpinWeight family coupling scale ≈
      dyadicPadeNome scale at hnome
  exact Q'.le_trans' _ _ _ hdyadic
    (Q'.ge_of_eqv hnome)

theorem cubeActivitySevenWeightFloor_le_matchedWeight
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    {scale : Nat} (hscale : 3 ≤ scale) :
    cubeActivitySevenWeightFloor ≤
      matchedAllSpinWeight family coupling scale := by
  have hdyadic :=
    cubeActivitySevenWeightFloor_le_dyadicPadeNome hscale
  have hnome := bridge.nome scale
  change
    matchedAllSpinWeight family coupling scale ≈
      dyadicPadeNome scale at hnome
  exact Q'.le_trans' _ _ _ hdyadic
    (Q'.ge_of_eqv hnome)

theorem one_le_matchedAllSpinCutoff
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) :
    1 ≤ matchedAllSpinCutoff family coupling scale := by
  unfold matchedAllSpinCutoff
    matchedPhysicalSpacingBits
  exact one_le_spacingLabelCutoff
    (matchedAllSpinWeight_pos family coupling scale)
    (matchedPhysicalWeight_lt_one bridge scale)

/-- Uniform stationary-vacuum calibration on every dyadic AF scale `>= 2`,
for the one-step central reflected slab. -/
theorem matchedVacuumRowMarginal_le_fiveSixths_tail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    {scale : Nat} (hscale : 2 ≤ scale) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        0 zeroEdgeLabelling ≤
      Q'.mkPos 5 6 (by decide) := by
  exact
    centralVacuumRowMarginal_le_fiveSixths_of_threeQuarters_le
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (cubeActivityWeightFloor_le_matchedWeight
        bridge hscale)
      (one_le_matchedAllSpinCutoff bridge scale)

/-- Exact activity-sensitive form, valid at every dyadic scale without a
prefix exception. -/
theorem matchedVacuumRowMarginal_le_cubeActivityReciprocal
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative
      family coupling scale
    let activity := (coeffW w 1) ^ 6
    let denominator := 1 + activity
    centralPhysicalRowMarginal
        w hw
        (matchedAllSpinCutoff family coupling scale)
        0 zeroEdgeLabelling ≤
      Q'.divPos 1 denominator
        (Q'.pos_add_nonneg (by decide)
          (Q'.pow_nonneg _ (coeffW_nonneg hw 1) 6)) := by
  exact
    centralVacuumRowMarginal_le_cubeActivityReciprocal
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)

/-- From scale three onward, the literal one-cube activity already forces
the stationary vacuum row below `1/8`. -/
theorem matchedVacuumRowMarginal_le_oneEighth_tail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    {scale : Nat} (hscale : 3 ≤ scale) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        0 zeroEdgeLabelling ≤
      Q'.mkPos 1 8 (by decide) := by
  exact
    centralVacuumRowMarginal_le_oneEighth_of_eightNinths_le
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (cubeActivitySevenWeightFloor_le_matchedWeight
        bridge hscale)
      (one_le_matchedAllSpinCutoff bridge scale)

/-! ## 3. The `9/50` centered detour is incompatible with this tail -/

/-- The vacuum entry itself rules out the proposed intermediate estimate
`r_centered <= 9/50` whenever `pi0 <= 5/6`.

Indeed the exact centered Gram has vacuum entry one, so its already-proved
vacuum fence gives

    1 - pi0^2 <= r_centered * pi0.

The displayed assumptions would instead make the left side at least
`11/36` and the right side at most `3/20`.  This theorem is important:
the calibrated spectral eighth must be estimated *directly*; it cannot be
obtained from the `9/50` centered detour on the lower-cube tail. -/
theorem centered_rate_nineFiftieths_impossible_of_vacuum_le_fiveSixths
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat)
    (hpi0 :
      centralPhysicalRowMarginal
          w hw K halfExtent zeroEdgeLabelling ≤
        Q'.mkPos 5 6 (by decide))
    (hrate :
      exactCenteredMehlerGramRate
          w hw K halfExtent diagonalOrder crossOrder ≤
        Q'.mkPos 9 50 (by decide)) :
    False := by
  let pi0 :=
    centralPhysicalRowMarginal
      w hw K halfExtent zeroEdgeLabelling
  let rate :=
    exactCenteredMehlerGramRate
      w hw K halfExtent diagonalOrder crossOrder
  have hpi0nonnegative : (0 : Q') ≤ pi0 :=
    centralPhysicalRowMarginal_nonnegative
      hw K halfExtent zeroEdgeLabelling
  have hsquare :
      pi0 * pi0 ≤
        Q'.mkPos 5 6 (by decide) *
          Q'.mkPos 5 6 (by decide) :=
    Q'.mul_le_mul_of_nonneg
      hpi0 hpi0 (by decide) hpi0nonnegative
  have hleft :
      Q'.mkPos 11 36 (by decide) ≤
        1 + (-(pi0 * pi0)) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide))
      (Q'.add_le_add_left 1 _ _
        (Q'.neg_le_neg hsquare))
  have hvacuumFence :
      1 + (-(pi0 * pi0)) ≤ rate * pi0 :=
    one_sub_vacuumMarginal_square_le_centeredRate_mul
      w hw K halfExtent diagonalOrder crossOrder
  have hrateNonnegative : (0 : Q') ≤ rate :=
    exactCenteredMehlerGramRate_nonnegative
      w hw K halfExtent diagonalOrder crossOrder
  have hrateScaled :
      rate * pi0 ≤
        Q'.mkPos 9 50 (by decide) * pi0 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hrate hpi0nonnegative
  have hpiScaled :
      Q'.mkPos 9 50 (by decide) * pi0 ≤
        Q'.mkPos 9 50 (by decide) *
          Q'.mkPos 5 6 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hpi0 (by decide)
  have himpossible :
      Q'.mkPos 11 36 (by decide) ≤
        Q'.mkPos 9 50 (by decide) *
          Q'.mkPos 5 6 (by decide) :=
    Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _ hvacuumFence
        (Q'.le_trans' _ _ _ hrateScaled hpiScaled))
  exact
    (show ¬
      Q'.mkPos 11 36 (by decide) ≤
        Q'.mkPos 9 50 (by decide) *
          Q'.mkPos 5 6 (by decide) by decide)
      himpossible

/-- Consequently, every dyadic AF tail scale covered by the lower-cube
certificate refutes, rather than proves, the `9/50` centered-rate premise. -/
theorem matched_centered_rate_nineFiftieths_impossible_tail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (diagonalOrder crossOrder : Nat → Nat)
    {scale : Nat} (hscale : 2 ≤ scale)
    (hrate :
      exactCenteredMehlerGramRate
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          0
          (diagonalOrder scale)
          (crossOrder scale) ≤
        Q'.mkPos 9 50 (by decide)) :
    False := by
  exact
    centered_rate_nineFiftieths_impossible_of_vacuum_le_fiveSixths
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      0
      (diagonalOrder scale)
      (crossOrder scale)
      (matchedVacuumRowMarginal_le_fiveSixths_tail
        bridge hscale)
      hrate

end YMGap.Continuum.BF4DyadicCubeVacuumCalibration

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.cubeActivityWeightFloor_le_dyadicPadeNome
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.cubeActivitySevenWeightFloor_le_dyadicPadeNome
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.cubeActivityWeightFloor_le_matchedWeight
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.cubeActivitySevenWeightFloor_le_matchedWeight
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.one_le_matchedAllSpinCutoff
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.matchedVacuumRowMarginal_le_fiveSixths_tail
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.matchedVacuumRowMarginal_le_cubeActivityReciprocal
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.matchedVacuumRowMarginal_le_oneEighth_tail
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.centered_rate_nineFiftieths_impossible_of_vacuum_le_fiveSixths
#print axioms YMGap.Continuum.BF4DyadicCubeVacuumCalibration.matched_centered_rate_nineFiftieths_impossible_tail
