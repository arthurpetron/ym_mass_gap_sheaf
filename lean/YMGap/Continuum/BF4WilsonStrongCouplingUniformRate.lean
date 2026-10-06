/-
# Strong-coupling width-uniform vacuum-square rate (INTERFACE TEST; PLUMBING)

Companion to `audits/SCOPE-WILSON-STRONG-COUPLING-UNIFORM-RATE-2026-10-06.md`. ADDITIVE.

THIS IS AN INTERFACE TEST. It makes NO progress on the Clay gap and does NOT give the AF
margin on `afPaddedZeroMomentumAFExpr`.

What is proved here:
* The existing Descent rate `twoStepRate ≈ 1/16` is WIDTH-INDEPENDENT. Under the three
  strong-coupling guards it yields an all-vector vacuum-square contraction on the Spatial
  Union carrier (`StrongCouplingVacuumSqContraction`), for EVERY base. This is a restatement
  of `BF4WilsonDescentCompletedGap.oneStep_norm_gap`.
* The dyadic lower margin holds at this constant rate: `m = 1 − twoStepRate` satisfies
  `m·2^-j ≤ 1 − twoStepRate` for every `j`.
* Non-vacuity: the package (contraction under the Descent guards) + (lower margin) is
  inhabited as a Prop for every `w` in the window. Concretely, `smallNome = 1/16` satisfies
  `heatRatio ≤ 1/2` and `heatRemainderBound < 1` by `decide`; the entropy-rate guard remains a
  hypothesis, as in every existing Descent consumer.
* Obstruction: a constant rate `r ≤ rMax < 1` cannot satisfy the B04 upper half
  `side_j(1−r) ≤ M` for all `j` (side unbounded). So this rate must NOT be fed into
  `wilsonGapBranch_afPadded_generic` on any `NomeSchedule` trajectory.

What is NOT proved:
* `WilsonVacuumSqContraction` on the all-nome literal-width `Completion`. Descent lives on
  `UnionCompletion`. The carrier bridge is OPEN.
* Any witness of `WilsonAFPaddedGapInput` on AF: every `NomeSchedule` has `w_j → 1` and leaves
  the strong-coupling window.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonDescentCompletedGap
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
import YMGap.Continuum.BF4DyadicWilsonSquare
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.BF4WilsonStrongCouplingUniformRate

set_option autoImplicit false


open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate (adjustedCoreRate)
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
  (twoStepRate twoStepRate_positive twoStepRate_lt_one twoStepRate_eq)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
  (UnionCompletion completedTime completedUnit)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonDescentCompletedGap (oneStep_norm_gap)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_pos)
open YMGap.Continuum.ClusteringImpliesGap (exists_succ_mul_gt)
open YMGap.Continuum (one_sub_pos_of_lt_one)

/-! ## 0. Helpers -/

private theorem sc_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem sc_n_le_two_pow (n : Nat) : n ≤ 2 ^ n :=
  Nat.le_of_lt Nat.lt_two_pow_self

/-! ## 1. The width-independent rate and its vacuum-square contraction -/

/-- The Descent two-step rate: a constant, ≈ 1/16, independent of width and of `w`. -/
def strongCouplingTwoStepRate : Q' := twoStepRate

theorem strongCouplingTwoStepRate_pos : (0 : Q') < strongCouplingTwoStepRate :=
  twoStepRate_positive

theorem strongCouplingTwoStepRate_lt_one : strongCouplingTwoStepRate < (1 : Q') :=
  twoStepRate_lt_one

theorem strongCouplingTwoStepRate_eq_oneSixteenth :
    Q'.eqv strongCouplingTwoStepRate (Q'.mkPos 1 16 (by decide)) :=
  twoStepRate_eq

/-- All-vector vacuum-square contraction on the Spatial Union carrier, at a rate independent
of the spatial base. Same shape as `WilsonVacuumSqContraction`, DIFFERENT carrier. -/
def StrongCouplingVacuumSqContraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (r : Q') : Prop :=
  ∀ x : UnionCompletion hw0 hw1 hsmall hd hs,
    completedInner hw0 hw1 hsmall hd hs x (completedUnit hw0 hw1 hsmall hd hs) = RCzero →
      RCle (completedInner hw0 hw1 hsmall hd hs
          (completedTime hw0 hw1 hsmall hd hs 1 x)
          (completedTime hw0 hw1 hsmall hd hs 1 x))
        (RCscale r (completedInner hw0 hw1 hsmall hd hs x x))

/-- **Kernel piece.** Descent's `oneStep_norm_gap` is exactly this Prop at rate
`strongCouplingTwoStepRate`, for every `w` in the window and every spatial base. -/
theorem strongCoupling_vacuumSq {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    StrongCouplingVacuumSqContraction hw0 hw1 hsmall hd hs strongCouplingTwoStepRate :=
  fun x hx => oneStep_norm_gap hw0 hw1 hsmall hd hs x hx

/-! ## 2. Dyadic lower margin at the constant rate -/

theorem spacing_le_one (j : Nat) : spacing j ≤ (1 : Q') := by
  induction j with
  | zero => decide
  | succ j ih =>
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ half ih (by decide))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv half)) (by decide))

/-- Lattice margin of the constant Descent rate. -/
def strongCouplingMargin : Q' := (1 : Q') - strongCouplingTwoStepRate

theorem strongCouplingMargin_pos : (0 : Q') < strongCouplingMargin :=
  one_sub_pos_of_lt_one strongCouplingTwoStepRate_lt_one

/-- **Lower margin at constant rate.** `m · 2^-j ≤ 1 − twoStepRate` for every `j`, with
`m = 1 − twoStepRate`. -/
theorem strongCoupling_lowerMargin_dyadic (j : Nat) :
    strongCouplingMargin * spacing j ≤ strongCouplingMargin :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (spacing_le_one j)
      (Q'.le_of_lt strongCouplingMargin_pos))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-- The package (contraction under guards) + (dyadic lower margin) is non-vacuous as a Prop:
for every `w` satisfying the Descent guards, both halves hold. -/
theorem strongCoupling_package_nonvacuous {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    StrongCouplingVacuumSqContraction hw0 hw1 hsmall hd hs strongCouplingTwoStepRate ∧
      ((0 : Q') < strongCouplingMargin ∧
        ∀ j, strongCouplingMargin * spacing j ≤ strongCouplingMargin) :=
  ⟨strongCoupling_vacuumSq hw0 hw1 hsmall hd hs,
    strongCouplingMargin_pos, strongCoupling_lowerMargin_dyadic⟩

/-! ## 3. Concrete window fragments at `smallNome = 1/16` -/

theorem smallNome_lt_one : smallNome < (1 : Q') := by decide

theorem smallNome_heatRatio : heatRatio smallNome ≤ HalfPow.half := by decide

theorem smallNome_heatRemainder : heatRemainderBound smallNome < (1 : Q') := by decide

/-- The first two Descent guards hold at `smallNome`. The entropy-rate guard is the remaining
concrete check; existing Descent consumers leave it as a hypothesis too. -/
theorem smallNome_two_guards :
    (0 : Q') < smallNome ∧ smallNome < (1 : Q') ∧
      heatRatio smallNome ≤ HalfPow.half ∧ heatRemainderBound smallNome < (1 : Q') :=
  ⟨smallNome_pos, smallNome_lt_one, smallNome_heatRatio, smallNome_heatRemainder⟩

/-- Conditional non-vacuity at `smallNome`: given the entropy-rate guard, the full package
inhabits. -/
theorem smallNome_package_of_entropy
    (hs : entropyRate 625 (adjustedCoreRate smallNome smallNome_heatRemainder) < (1 : Q')) :
    StrongCouplingVacuumSqContraction smallNome_pos smallNome_lt_one
        smallNome_heatRatio smallNome_heatRemainder hs strongCouplingTwoStepRate ∧
      ((0 : Q') < strongCouplingMargin ∧
        ∀ j, strongCouplingMargin * spacing j ≤ strongCouplingMargin) :=
  strongCoupling_package_nonvacuous _ _ _ _ hs

/-! ## 4. Obstruction: constant rate ⇏ B04 upper half for all scales -/

/-- For any constant ceiling `M` and any rate ceiling `rMax < 1`, some scale has
`side_j · (1 − rMax) > M`. A constant rate therefore cannot satisfy the B04 upper half on
every scale of a dyadic trajectory. -/
theorem constant_rate_not_all_scale_upper (rMax M : Q') (hr : rMax < (1 : Q')) :
    ∃ j : Nat, ¬ (Q'.ofNat (side j) * ((1 : Q') - rMax) ≤ M) := by
  have hδ : (0 : Q') < (1 : Q') - rMax := one_sub_pos_of_lt_one hr
  obtain ⟨m, hm⟩ := exists_succ_mul_gt M ((1 : Q') - rMax) hδ
  refine ⟨m + 1, ?_⟩
  intro hle
  have hmono : Q'.ofNat (m + 1) * ((1 : Q') - rMax) ≤
      Q'.ofNat (side (m + 1)) * ((1 : Q') - rMax) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (sc_ofNat_le (sc_n_le_two_pow (m + 1))) (Q'.le_of_lt hδ)
  exact Int.not_lt.mpr (Q'.le_trans' _ _ _ hmono hle) hm

/-- In particular the Descent rate itself cannot serve as an all-scale B04 rate on a dyadic
`NomeSchedule` trajectory (upper half fails). -/
theorem strongCoupling_rate_not_all_scale_upper (M : Q') :
    ∃ j : Nat, ¬ (Q'.ofNat (side j) * strongCouplingMargin ≤ M) :=
  constant_rate_not_all_scale_upper strongCouplingTwoStepRate M
    strongCouplingTwoStepRate_lt_one

#print axioms strongCouplingTwoStepRate
#print axioms strongCouplingTwoStepRate_pos
#print axioms strongCouplingTwoStepRate_lt_one
#print axioms strongCouplingTwoStepRate_eq_oneSixteenth
#print axioms StrongCouplingVacuumSqContraction
#print axioms strongCoupling_vacuumSq
#print axioms spacing_le_one
#print axioms strongCouplingMargin_pos
#print axioms strongCoupling_lowerMargin_dyadic
#print axioms strongCoupling_package_nonvacuous
#print axioms smallNome_two_guards
#print axioms smallNome_package_of_entropy
#print axioms constant_rate_not_all_scale_upper
#print axioms strongCoupling_rate_not_all_scale_upper

end YMGap.Continuum.BF4WilsonStrongCouplingUniformRate
