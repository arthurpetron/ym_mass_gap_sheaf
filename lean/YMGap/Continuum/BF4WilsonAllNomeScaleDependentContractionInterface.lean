/-
# Open H1 / Clay dimensional-transmutation conjecture interface (shifted-H1 anchor chain)

**Labels: CONDITIONAL / OPEN Clay-level dimensional-transmutation input. NOT a proof of the
conjecture; NOT mass-gap evidence.**

Companion to `BF4WilsonAllNomeShiftedH1Anchor` and `BF4WilsonAllNomeShiftedH1UniformRateNoGo`.
ADDITIVE. `BF4WilsonAllNomeShiftedH1UniformRateNoGo` proved that under `PathShiftedEpsBound tr c0`
and nondegeneracy, any scale-uniform rate `r_j ≤ r < 1` is impossible (`1 - r_j ≤ c0 / side_j`).
This file packages the exact scale-dependent contraction / step-ratio hypothesis at lag
`side_j` needed to satisfy `PathShiftedEpsBound tr c0` (and compatible with the uniform-rate
no-go) as a single named, audited open conjecture structure
`ScaleDependentShiftedH1Conjecture`, and proves that this single open input closes the
shifted-H1 anchor chain:

* `PathScaleDependentShiftedContraction tr r c0`: for every positive scale `j ≥ 1`,
  `r_j ≤ 1`, `r_j · R_j(side_j) ≤ R_j(side_j + 1)`, and `side_j · (1 - r_j) ≤ c0`.
* `pathShiftedEpsBound_of_scaleDependentContraction` and
  `scaleDependentContraction_of_pathShiftedEpsBound`: equivalence between scale-dependent
  contraction at lag `side_j` and `PathShiftedEpsBound tr c0` (via `canonicalShiftedRate`).
* `ScaleDependentShiftedH1Conjecture tr c0` and `conjecture_iff_pathShiftedEpsBound`.
* `conjecture_closes_shifted_anchor` and `conjecture_closes_padded_shifted_anchor`: the
  single open conjecture closes `ShiftedAnchorPackage` (with nondegeneracy discharged on
  any padded trajectory).
* `conjecture_forces_rayleigh_rate` and `conjecture_forbids_uniform_rayleigh_rate`:
  compatibility with `shiftedH1_forbids_uniformRate`.
* `afPadded_closed_by_conjecture`: concrete closure on `afPaddedZeroMomentumTrajectory`.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedH1UniformRateNoGo
import YMGap.Continuum.BF4WilsonAllNomeExprPropagatedEnergy

namespace YMGap.Continuum.BF4WilsonAllNomeScaleDependentContractionInterface

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeH1FixedScale (WilsonVacuumRayleighRate)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
  (DyadicSmoothedTrajectory trajWidth)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor
  (OneStepEpsBound PathShiftedEpsBound PathShiftedNondegenerate ShiftedAnchorPackage
   NomeScheduleAFCalibrated path_normalized_anchor_shifted path_shiftedEps_forces_rate)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (oneStepEpsBound_one)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1UniformRateNoGo (shiftedH1_forbids_uniformRate)
open YMGap.Continuum.BF4WilsonAllNomeShiftedPaddedNondegenerate
  (PathFacesPadded paddedNondegFloor paddedNondegFloor_pos path_normalized_anchor_shifted_padded)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afA afKappa afC afHalf afPaddedZeroMomentumTrajectory afPaddedZeroMomentum_AFCalibrated
   afPaddedZeroMomentum_padded)
open YMGap.Continuum.BF4WilsonAllNomeExprPropagatedEnergy
  (propagated_norm propagated_response energy_of_stepRatio stepRatio_of_energy energy_rate_side)

/-! ## 0. Rational helpers -/

private theorem sd_ofNat_pos (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int) * 1 < (n : Int) * 1
  rw [Int.zero_mul, Int.mul_one]
  exact Int.ofNat_lt.mpr hn

private theorem sd_one_sub_le_one {x : Q'} (h0 : (0 : Q') ≤ x) : (1 : Q') - x ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv ((1 : Q') - x)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left ((1 : Q') - x) 0 x h0)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
        (fun | 0 => (1 : Q') | _ => x))))

private theorem sd_two_mul_half (j : Nat) (hj : 1 ≤ j) : 2 * (side j / 2) = side j := by
  cases j with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hj)
  | succ i =>
      change 2 * ((2 ^ i * 2) / 2) = 2 ^ i * 2
      rw [Nat.mul_div_cancel (2 ^ i) (by decide : 0 < 2), Nat.mul_comm]

/-! ## 1. Scale-dependent shifted contraction hypothesis and open conjecture interface -/

/-- **Scale-dependent shifted contraction hypothesis (OPEN).**
Along a dyadic smoothed trajectory `tr`, at each positive scale `j ≥ 1`, the rate `r j ≤ 1`
retains at least fraction `r j` of the lag-`side_j` response across one time step
(`r j · R_j(side_j) ≤ R_j(side_j + 1)`), and its one-step deficit `1 - r j` scales like
`O(1 / side_j)` with `side_j · (1 - r j) ≤ c0`. -/
def PathScaleDependentShiftedContraction (tr : DyadicSmoothedTrajectory)
    (r : Nat → Q') (c0 : Q') : Prop :=
  ∀ j, 1 ≤ j →
    r j ≤ (1 : Q') ∧
    RCle (RCscale (r j) (tr.response j (side j))) (tr.response j (side j + 1)) ∧
    Q'.ofNat (side j) * ((1 : Q') - r j) ≤ c0

/-- **Audited open H1 / Clay dimensional-transmutation conjecture interface (OPEN).**
Packages the single open scale-dependent contraction input needed to close the shifted-H1
anchor chain along `tr` with energy constant `c0 ≥ 1`. -/
structure ScaleDependentShiftedH1Conjecture (tr : DyadicSmoothedTrajectory) (c0 : Q') : Prop where
  one_le_c0 : (1 : Q') ≤ c0
  witness : ∃ r : Nat → Q', PathScaleDependentShiftedContraction tr r c0

/-- The canonical scale-dependent rate schedule `1 - c0 / side_j` associated with energy
constant `c0`. -/
def canonicalShiftedRate (c0 : Q') (j : Nat) : Q' :=
  (1 : Q') - c0 * Q'.recipPos (Q'.ofNat (side j)) (sd_ofNat_pos (side j) (side_positive j))

/-! ## 2. Equivalence with `PathShiftedEpsBound` -/

/-- One-step response retention `r · R_j(side_j) ≤ R_j(side_j + 1)` with
`side_j · (1 - r) ≤ c0` implies the shifted `OneStepEpsBound` at positive scale `j ≥ 1`. -/
theorem oneStepEpsBound_shifted_of_rate (tr : DyadicSmoothedTrajectory)
    (j : Nat) (hj : 1 ≤ j) (r c0 : Q')
    (hstep : RCle (RCscale r (tr.response j (side j))) (tr.response j (side j + 1)))
    (hrate : Q'.ofNat (side j) * ((1 : Q') - r) ≤ c0) :
    OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
      (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j / 2)
        (tr.state j)) (side j) c0 := by
  refine energy_of_stepRatio (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) _ (side j) r c0 ?_ hrate
  rw [propagated_norm, propagated_response, sd_two_mul_half j hj]
  exact hstep

/-- **Scale-dependent contraction ⇒ `PathShiftedEpsBound`.**
For `1 ≤ c0`, `PathScaleDependentShiftedContraction tr r c0` implies `PathShiftedEpsBound tr c0`
at all scales `j` (scale `0` is automatic from `oneStepEpsBound_one`). -/
theorem pathShiftedEpsBound_of_scaleDependentContraction (tr : DyadicSmoothedTrajectory)
    (r : Nat → Q') (c0 : Q') (hc0 : (1 : Q') ≤ c0)
    (H : PathScaleDependentShiftedContraction tr r c0) :
    PathShiftedEpsBound tr c0 := by
  intro j
  cases j with
  | zero =>
      exact oneStepEpsBound_one (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0)
        (trajWidth 0) _ c0 hc0
  | succ k =>
      have hj : 1 ≤ k + 1 := Nat.succ_pos k
      rcases H (k + 1) hj with ⟨_, hstep, hrate⟩
      exact oneStepEpsBound_shifted_of_rate tr (k + 1) hj (r (k + 1)) c0 hstep hrate

/-- **Converse (`PathShiftedEpsBound` ⇒ canonical scale-dependent contraction).**
If `PathShiftedEpsBound tr c0` holds with `0 ≤ c0`, then `canonicalShiftedRate c0`
satisfies `PathScaleDependentShiftedContraction tr (canonicalShiftedRate c0) c0`. -/
theorem scaleDependentContraction_of_pathShiftedEpsBound (tr : DyadicSmoothedTrajectory)
    (c0 : Q') (hc0 : (0 : Q') ≤ c0) (H1s : PathShiftedEpsBound tr c0) :
    PathScaleDependentShiftedContraction tr (canonicalShiftedRate c0) c0 := by
  intro j hj
  have hpos := sd_ofNat_pos (side j) (side_positive j)
  have hrec0 := Q'.le_of_lt (Q'.recipPos_pos (Q'.ofNat (side j)) hpos)
  refine ⟨sd_one_sub_le_one (Q'.mul_nonneg _ _ hc0 hrec0), ?_,
    energy_rate_side (side j) (side_positive j) c0⟩
  have hs := stepRatio_of_energy (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) _ (side j) (side_positive j) c0 (H1s j)
  rw [propagated_norm, propagated_response, sd_two_mul_half j hj] at hs
  exact hs

/-- **Equivalence theorem.** For `1 ≤ c0`, the open `ScaleDependentShiftedH1Conjecture tr c0`
is equivalent to `PathShiftedEpsBound tr c0`. -/
theorem conjecture_iff_pathShiftedEpsBound (tr : DyadicSmoothedTrajectory)
    (c0 : Q') (hc0 : (1 : Q') ≤ c0) :
    ScaleDependentShiftedH1Conjecture tr c0 ↔ PathShiftedEpsBound tr c0 := by
  constructor
  · intro H
    rcases H.witness with ⟨r, hr⟩
    exact pathShiftedEpsBound_of_scaleDependentContraction tr r c0 H.one_le_c0 hr
  · intro H1s
    have hc00 : (0 : Q') ≤ c0 := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hc0
    exact ⟨hc0, ⟨canonicalShiftedRate c0,
      scaleDependentContraction_of_pathShiftedEpsBound tr c0 hc00 H1s⟩⟩

/-! ## 3. Closing the shifted-H1 anchor chain and compatibility with uniform-rate No-Go -/

/-- **Closing the shifted-H1 anchor chain (general trajectory).**
The single open `ScaleDependentShiftedH1Conjecture tr c0` together with qualitative
nondegeneracy `PathShiftedNondegenerate tr fl` implies `ShiftedAnchorPackage`. -/
theorem conjecture_closes_shifted_anchor (tr : DyadicSmoothedTrajectory)
    (c0 delta : Q') (a : Nat) (ha : 1 ≤ a)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hconj : ScaleDependentShiftedH1Conjecture tr c0)
    (Hnd : PathShiftedNondegenerate tr fl) :
    ShiftedAnchorPackage tr delta hdelta a fl hfl := by
  rcases Hconj.witness with ⟨r, hr⟩
  exact path_normalized_anchor_shifted tr c0 delta a ha hdelta0 hdelta hcd fl hfl
    (pathShiftedEpsBound_of_scaleDependentContraction tr r c0 Hconj.one_le_c0 hr) Hnd

/-- **Closing the shifted-H1 anchor chain (padded trajectory, nondegeneracy discharged).**
On any padded trajectory (`PathFacesPadded tr`), `ScaleDependentShiftedH1Conjecture tr c0`
is the ONLY open input required to obtain `ShiftedAnchorPackage`. -/
theorem conjecture_closes_padded_shifted_anchor (tr : DyadicSmoothedTrajectory)
    (c0 delta : Q') (a : Nat) (ha : 1 ≤ a)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (hpad : PathFacesPadded tr)
    (Hconj : ScaleDependentShiftedH1Conjecture tr c0) :
    ShiftedAnchorPackage tr delta hdelta a
      (paddedNondegFloor tr) (paddedNondegFloor_pos tr) := by
  rcases Hconj.witness with ⟨r, hr⟩
  exact path_normalized_anchor_shifted_padded tr c0 delta a ha hdelta0 hdelta hcd hpad
    (pathShiftedEpsBound_of_scaleDependentContraction tr r c0 Hconj.one_le_c0 hr)

/-- **Rayleigh-rate screen under the conjecture.**
Under `ScaleDependentShiftedH1Conjecture tr c0` and nondegeneracy, any certified vacuum
Rayleigh rate family `rj` must also obey the `O(1 / side_j)` law `side_j · (1 - rj_j) ≤ c0`. -/
theorem conjecture_forces_rayleigh_rate (tr : DyadicSmoothedTrajectory) (c0 : Q')
    (rj fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hconj : ScaleDependentShiftedH1Conjecture tr c0)
    (Hnd : PathShiftedNondegenerate tr fl)
    (Hr : ∀ j, WilsonVacuumRayleighRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (rj j))
    (j : Nat) (hj : 1 ≤ j) :
    Q'.ofNat (side j) * ((1 : Q') + -rj j) ≤ c0 := by
  rcases Hconj.witness with ⟨r, hr⟩
  exact path_shiftedEps_forces_rate tr c0 rj fl hfl
    (pathShiftedEpsBound_of_scaleDependentContraction tr r c0 Hconj.one_le_c0 hr)
    Hnd Hr j hj

/-- **Compatibility with the uniform-rate No-Go (`shiftedH1_forbids_uniformRate`).**
Under `ScaleDependentShiftedH1Conjecture tr c0` and nondegeneracy, no uniform rate `r < 1`
can bound a certified vacuum Rayleigh rate family `rj` across all scales. -/
theorem conjecture_forbids_uniform_rayleigh_rate (tr : DyadicSmoothedTrajectory)
    (c0 r : Q') (rj fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hconj : ScaleDependentShiftedH1Conjecture tr c0)
    (Hnd : PathShiftedNondegenerate tr fl)
    (Hr : ∀ j, WilsonVacuumRayleighRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (trajWidth j) (rj j))
    (hr1 : r < (1 : Q')) :
    ¬ (∀ j : Nat, rj j ≤ r) := by
  rcases Hconj.witness with ⟨rwit, hrwit⟩
  exact shiftedH1_forbids_uniformRate tr c0 r rj fl hfl
    (pathShiftedEpsBound_of_scaleDependentContraction tr rwit c0 Hconj.one_le_c0 hrwit)
    Hnd Hr hr1

/-- **Concrete AF-calibrated padded trajectory closure.**
On `afPaddedZeroMomentumTrajectory`, the single open conjecture
`ScaleDependentShiftedH1Conjecture afPaddedZeroMomentumTrajectory 2` yields both the
two-loop AF-calibrated nome schedule and the full `ShiftedAnchorPackage` at `a = 2`,
`delta = 1/2`. -/
theorem afPadded_closed_by_conjecture
    (Hconj : ScaleDependentShiftedH1Conjecture afPaddedZeroMomentumTrajectory (Q'.ofNat 2)) :
    NomeScheduleAFCalibrated afPaddedZeroMomentumTrajectory.schedule afA afKappa afC ∧
      ShiftedAnchorPackage afPaddedZeroMomentumTrajectory afHalf (by decide) 2
        (paddedNondegFloor afPaddedZeroMomentumTrajectory)
        (paddedNondegFloor_pos afPaddedZeroMomentumTrajectory) :=
  ⟨afPaddedZeroMomentum_AFCalibrated,
    conjecture_closes_padded_shifted_anchor afPaddedZeroMomentumTrajectory
      (Q'.ofNat 2) afHalf 2 (by decide) (by decide) (by decide) (by decide)
      afPaddedZeroMomentum_padded Hconj⟩

end YMGap.Continuum.BF4WilsonAllNomeScaleDependentContractionInterface
