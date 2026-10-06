/-
# Dead end: X2 at the Doeblin `mixRate` is FALSE along the AF-padded trajectory

Companion to `audits/SCOPE-WILSON-CARRIER-GAP-RETARGET-2026-10-06.md` (§Dead end). ADDITIVE.

THEOREM. `not_wilsonLowerMargin_mixRate_afPadded`: for EVERY `m`,
`¬ WilsonLowerMargin (exprMixRateFamily trAF) m`.
* Consequently the X2 hypothesis of `wilsonGapBranch_afPadded` (937f9e38) is UNSATISFIABLE.
  That theorem is vacuous: true, but it says nothing.

The proof uses only existing, w-uniform facts:
* `mixFraction_le_width_power` (`BF4ExactSlabFixedSpatialRateWidthObstruction`):
  `mixFraction(w, width) ≤ (1/32)^width` for EVERY `0<w<1`. It combines:
  * `headFloor ≤ 1/32`;
  * `prefixCap ≥ 1`, because the cap includes the constant Haar mode;
  * `#temporalFaces width ≥ width`.
  This bound is uniform in `w`, so `w_j → 1` does not rescue it.
* Along `trAF`, `width_j = trajWidth j = 4^j + 1 ≥ 2j`. With `K = powBaseCutoff(1/32, m/2)`
  and `j = K`:
  `m·2^-K ≤ mixFraction_K ≤ (1/32)^(2K) = (1/32)^K·(1/32)^K ≤ (m/2)·2^-K < m·2^-K`.
  This is a contradiction.
* The generic form is `not_wilsonLowerMargin_mixRate_of_width` (for any trajectory with
  `j + j ≤ width_j`).

WHAT THIS DOES NOT SAY.
* It is a statement about the COMPUTED Doeblin bound `mixRate = 1 − kineticFloor/kineticCap`
  only. It is not a lower bound on actual correlations or on the true spectral gap of the
  Wilson transfer.
* It does not refute a Yang–Mills mass gap.

FRONTIER (restated). Gap side: `WilsonAFPaddedGapInput`. There exists a rate family `r_j`
with an all-vector `WilsonVacuumSqContraction` on `trAF` and `m·2^-j ≤ 1 − r_j`. It is fed to
the generic `wilsonGapBranch_of_stepRatio_lowerMargin`; on `trAF` this is packaged as
`wilsonGapBranch_afPadded_generic`, with H-var and H-ray discharged. It stays OPEN. No
producer exists.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeWilsonGapBranchAFPadded
import YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction

namespace YMGap.Continuum.BF4WilsonAllNomeWilsonMixRateDeadEnd

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing spacing_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixFraction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction
  (marginBase mixFraction_le_width_power)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (trajWidth)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afPaddedZeroMomentumTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage (ExprShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression
  (paddedVar paddedRho afPaddedZeroMomentumExpr_hvar afPaddedZeroMomentumExpr_hray)
open YMGap.Continuum.BF4WilsonAllNomeExprAFCalibrated (afPaddedZeroMomentumAFExpr)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
open YMGap.Continuum.BF4WilsonAllNomeWilsonGapBranchAFPadded (WilsonFamilyDecay wilsonFamilyDecay)

local notation "trAF" => afPaddedZeroMomentumAFExpr.toExprAnchorTrajectory

private theorem dd_double_le (K : Nat) : K + K ≤ trajWidth K := by
  show K + K ≤ 2^K * 2^K + 1
  have hlt : K < 2^K := Nat.lt_two_pow_self
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · omega
  · have h2 : 2 ≤ 2^K := Nat.pow_le_pow_right (n := 2) (by decide) hpos
    have hm : 2 * 2^K ≤ 2^K * 2^K := Nat.mul_le_mul_right (2^K) h2
    omega

/-! ## 1. Generic: no lower margin at `mixRate` once `j + j ≤ width_j` -/

/-- **Dead end (generic).** On any Expr trajectory with `j + j ≤ width_j`, the Doeblin
`mixRate` family admits NO lower margin `m·2^-j ≤ 1 − mixRate_j`, for any `m`. -/
theorem not_wilsonLowerMargin_mixRate_of_width (tr : ExprAnchorTrajectory)
    (hw : ∀ j, j + j ≤ tr.width j) (m : Q') :
    ¬ WilsonLowerMargin (exprMixRateFamily tr) m := by
  intro hX2
  have hm : (0 : Q') < m := hX2.1
  let δ : Q' := HalfPow.half * m
  have hδ : (0 : Q') < δ := ExpNeg.half_mul_pos _ hm
  have hδm : δ < m := ClusteringImpliesGap.lt_of_lt_of_le
    (ClusteringImpliesGap.mul_lt_mul_of_pos_right hm (by decide : HalfPow.half < (1 : Q')))
    (Q'.le_of_eqv (Q'.one_mul_eqv m))
  let K : Nat := HKConvGen.powBaseCutoff marginBase δ
  let f : Q' := mixFraction (tr.schedule.nome_pos K) (tr.schedule.nome_lt_one K) (tr.width K)
  have hmb0 : (0 : Q') ≤ marginBase := by decide
  -- X2 at scale K, as `m·spacing_K ≤ f`
  have h1 : m * spacing K ≤ f :=
    Q'.le_trans' _ _ _ (hX2.2 K)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (.var 0) (by decide)
        (fun _ => f)))
  -- `f ≤ (1/32)^width_K ≤ (1/32)^(K+K) ≈ (1/32)^K·(1/32)^K`
  have h2 : f ≤ marginBase ^ (K + K) :=
    Q'.le_trans' _ _ _ (mixFraction_le_width_power _ _ (tr.width K))
      (HKConvGen.pow_base_antitone hmb0 (by decide) (hw K))
  have h3 : marginBase ^ (K + K) ≤ marginBase ^ K * marginBase ^ K :=
    Q'.le_of_eqv (QDivArctanSeries.pow_add_split marginBase K K)
  -- `(1/32)^K ≤ δ` and `(1/32)^K ≤ (1/2)^K = spacing_K`
  have hA : marginBase ^ K ≤ δ :=
    HKConvGen.pow_base_le_cutoff (by decide : (0 : Q') < marginBase)
      (by decide : marginBase < (1 : Q')) hδ
  have hB : marginBase ^ K ≤ spacing K :=
    HKConv.pow_le_pow_base hmb0 (by decide : marginBase ≤ HalfPow.half) K
  have h4 : marginBase ^ K * marginBase ^ K ≤ δ * spacing K :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hA (Q'.pow_nonneg _ hmb0 K))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hB (Q'.le_of_lt hδ))
  have hle : m * spacing K ≤ δ * spacing K :=
    Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ h3 h4))
  have hlt : δ * spacing K < m * spacing K :=
    ClusteringImpliesGap.mul_lt_mul_of_pos_right (spacing_positive K) hδm
  exact Int.not_lt.mpr hle hlt

/-! ## 2. On the AF-padded `Y_j` trajectory -/

/-- **Dead end on `trAF`.** `width_j = 4^j + 1`; X2 at `mixRate` fails for every `m`. -/
theorem not_wilsonLowerMargin_mixRate_afPadded (m : Q') :
    ¬ WilsonLowerMargin (exprMixRateFamily trAF) m :=
  not_wilsonLowerMargin_mixRate_of_width trAF dd_double_le m

/-! ## 3. The restated gap frontier on `trAF` (generic rate family) -/

/-- **Gap-side frontier on `trAF` (OPEN).** Some rate family `r_j` has an all-vector Wilson
vacuum-square contraction at `(w_j, width_j)` and a lower margin `m·2^-j ≤ 1 − r_j`. -/
def WilsonAFPaddedGapInput : Prop :=
  ∃ (r : Nat → Q') (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction ((trAF).schedule.nome_pos j)
      ((trAF).schedule.nome_lt_one j) ((trAF).width j) (r j)) (m : Q'),
    WilsonLowerMargin (exprWilsonFamily trAF r hr0 hr1 Hc) m

/-- **Wilson gap branch on `trAF`, generic rate family.**
Open analytic hypotheses:
* the step ratio (`H`, `hc`, `hrho'0`, `hrho'1`);
* a rate family `r` with `Hc` and the lower margin `hX2`, i.e. a witness of
  `WilsonAFPaddedGapInput`.
H-var and H-ray are discharged. -/
theorem wilsonGapBranch_afPadded_generic (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction ((trAF).schedule.nome_pos j)
      ((trAF).schedule.nome_lt_one j) ((trAF).width j) (r j))
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio trAF rho' k) (m : Q')
    (hX2 : WilsonLowerMargin (exprWilsonFamily trAF r hr0 hr1 Hc) m) :
    ExprShiftedAnchorPackage trAF delta hdelta a
        (exprNondegFloor trAF (paddedVar afPaddedZeroMomentumTrajectory)
          (paddedRho afPaddedZeroMomentumTrajectory))
        (exprNondegFloor_pos trAF _ _ afPaddedZeroMomentumExpr_hvar
          afPaddedZeroMomentumExpr_hray) ∧
      WilsonPhysicalRateBand (exprWilsonFamily trAF r hr0 hr1 Hc) ∧
      WilsonFamilyDecay (exprWilsonFamily trAF r hr0 hr1 Hc) ∧
      m ≤ Q'.ofNat (2^(2*C+3)) :=
  have h := wilsonGapBranch_of_stepRatio_lowerMargin trAF r hr0 hr1 Hc c delta C j0 a ha hC hcC
    hj0 hj0' hdelta0 hdelta hcd (paddedVar afPaddedZeroMomentumTrajectory)
    (paddedRho afPaddedZeroMomentumTrajectory) afPaddedZeroMomentumExpr_hvar
    afPaddedZeroMomentumExpr_hray rho' k hrho'0 hrho'1 hk hc H m hX2
  ⟨h.1, h.2.1, wilsonFamilyDecay _, h.2.2.2⟩

/-- `mixRate` is NOT a witness of the frontier Prop on `trAF` (dead end). -/
theorem mixRate_not_witness (m : Q') :
    ¬ WilsonLowerMargin (exprMixRateFamily trAF) m :=
  not_wilsonLowerMargin_mixRate_afPadded m

#print axioms not_wilsonLowerMargin_mixRate_of_width
#print axioms not_wilsonLowerMargin_mixRate_afPadded
#print axioms WilsonAFPaddedGapInput
#print axioms wilsonGapBranch_afPadded_generic
#print axioms mixRate_not_witness

end YMGap.Continuum.BF4WilsonAllNomeWilsonMixRateDeadEnd
