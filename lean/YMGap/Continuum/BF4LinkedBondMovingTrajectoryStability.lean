/-
# Stability of a linked BF4 bond-moving trajectory

`BF4PhysicalTrajectoryFence` repairs the local RG interface by requiring

    |fullStepWeight - decimatedWeight| <= delta

and then identifies the full-step output with the next input weight.  This
module proves the missing deterministic propagation theorem.  On the unit
interval the exact heat-semigroup map `w |-> w^b` is `b`-Lipschitz.  Therefore
the distance from an inexact linked trajectory to the ideal decimation orbit is
bounded by the explicit recurrence

    E 0       = 0,
    E (n + 1) = delta n + b * E n.

The result is deliberately conditional on the actual trajectory remaining in
`[0,1]`.  It constructs no four-dimensional trajectory and proves no smallness
of its residuals.  What it closes is the exact compiler from certified local
block-map errors to a certified accumulated error and hence to strong-corridor
entry.

## Axiom gate

Pure `Q'` arithmetic and structural induction.  The declarations printed at
the end use only `propext` / `Quot.sound`.  No classical choice and no hidden
existence claim.
-/

import YMGap.Continuum.BF4PhysicalTrajectoryFence
import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BF4PhysicalTrajectoryFence
open YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             try ac_rfl))

/-! ## 1. One-step control and the heat-semigroup Lipschitz bound -/

private def powerDifferenceStepL :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  let px := YMGap.Continuum.RingNormaliser.PolyExpr.var 0
  let py := YMGap.Continuum.RingNormaliser.PolyExpr.var 1
  let x := YMGap.Continuum.RingNormaliser.PolyExpr.var 2
  let y := YMGap.Continuum.RingNormaliser.PolyExpr.var 3
  .add (.mul px x) (.neg (.mul py y))

private def powerDifferenceStepR :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  let px := YMGap.Continuum.RingNormaliser.PolyExpr.var 0
  let py := YMGap.Continuum.RingNormaliser.PolyExpr.var 1
  let x := YMGap.Continuum.RingNormaliser.PolyExpr.var 2
  let y := YMGap.Continuum.RingNormaliser.PolyExpr.var 3
  .add
    (.mul px (.add x (.neg y)))
    (.mul y (.add px (.neg py)))

private theorem powerDifferenceStep_normal :
    YMGap.Continuum.RingNormaliser.normalize powerDifferenceStepL =
      YMGap.Continuum.RingNormaliser.normalize powerDifferenceStepR := by
  decide

private theorem power_difference_step
    (px py x y : Q') :
    px * x + -(py * y) ≈
      px * (x + -y) + y * (px + -py) := by
  simpa [powerDifferenceStepL, powerDifferenceStepR,
    YMGap.Continuum.RingNormaliser.eval] using
    (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      powerDifferenceStepL powerDifferenceStepR
      powerDifferenceStep_normal
      (fun | 0 => px | 1 => py | 2 => x | _ => y))

/-- The repaired local residual and iterate identification give the intended
one-step estimate on the linked trajectory. -/
theorem linked_step_deviation_le
    {b : Nat} (T : LinkedBondMovingTrajectory b) (k : Nat) :
    Q'.abs
        (T.weight (k + 1) - mkDecimate b (T.weight k)) ≤
      (T.step k).base.delta := by
  have hdifference :
      (T.weight (k + 1) - mkDecimate b (T.weight k)) ≈
        ((T.step k).base.fullStepWeight -
          (T.step k).base.decimatedWeight) := by
    apply Q'.add_eqv_congr'
    · exact T.next_identification k
    · apply Q'.neg_eqv_congr
      exact Q'.eqv_symm (Q'.eqv_of_eq (T.step k).base.decimated_eq)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (T.step k).deviation_control

/-- Powers are Lipschitz in their base on the unit interval:
`|x^n - y^n| <= n |x-y|`.

This is the constructive induction behind stability of repeated exact
heat-semigroup decimation. -/
theorem qpow_abs_sub_le_nat_mul
    {x y : Q'}
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (0 : Q') ≤ y) (hy1 : y ≤ (1 : Q')) :
    ∀ n,
      Q'.abs (qpow x n - qpow y n) ≤
        Q'.ofNat n * Q'.abs (x - y)
  | 0 => by
      have hleft : Q'.abs (qpow x 0 - qpow y 0) ≈ (0 : Q') := by
        refine Q'.eqv_trans _ _ _
          (Q'.abs_eqv_congr (Q'.add_neg_self_eqv (1 : Q'))) ?_
        exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
          (Q'.le_refl' 0)
      have hright :
          (Q'.ofNat 0 * Q'.abs (x - y)) ≈ (0 : Q') := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv) ?_
        exact q_zero_mul (Q'.abs (x - y))
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hleft (Q'.eqv_symm hright))
  | n + 1 => by
      let difference := x - y
      let previous := qpow x n - qpow y n
      have hdecompose :
          (qpow x (n + 1) - qpow y (n + 1)) ≈
            qpow x n * difference + y * previous := by
        dsimp [difference, previous]
        change
          (qpow x n * x + -(qpow y n * y)) ≈
            qpow x n * (x + -y) +
              y * (qpow x n + -qpow y n)
        exact power_difference_step (qpow x n) (qpow y n) x y
      have htriangle :
          Q'.abs (qpow x (n + 1) - qpow y (n + 1)) ≤
            Q'.abs (qpow x n * difference) +
              Q'.abs (y * previous) := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose)) ?_
        exact YMGap.Continuum.TsumDeriv.abs_add_le _ _
      have hxpowAbs : Q'.abs (qpow x n) ≤ (1 : Q') := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
              (qpow_nonneg x hx0 n))) ?_
        exact YMGap.Continuum.HeatKernelGap.qpow_le_one hx0 hx1 n
      have hyAbs : Q'.abs y ≤ (1 : Q') := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hy0)) ?_
        exact hy1
      have hfirst :
          Q'.abs (qpow x n * difference) ≤ Q'.abs difference := by
        refine Q'.le_trans' _ _ _
          (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
            (qpow x n) difference) ?_
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hxpowAbs
            (Q'.abs_nonneg difference)) ?_
        exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs difference))
      have hprevious :
          Q'.abs previous ≤
            Q'.ofNat n * Q'.abs difference := by
        exact qpow_abs_sub_le_nat_mul hx0 hx1 hy0 hy1 n
      have hsecond :
          Q'.abs (y * previous) ≤
            Q'.ofNat n * Q'.abs difference := by
        refine Q'.le_trans' _ _ _
          (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le y previous) ?_
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hyAbs
            (Q'.abs_nonneg previous)) ?_
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hprevious (by decide)) ?_
        exact Q'.le_of_eqv
          (Q'.one_mul_eqv (Q'.ofNat n * Q'.abs difference))
      refine Q'.le_trans' _ _ _ htriangle ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hfirst hsecond) ?_
      have halgebra :
          Q'.abs difference + Q'.ofNat n * Q'.abs difference ≈
            (Q'.ofNat n + 1) * Q'.abs difference := by
        ring_qeqv
      have hsuccessor :
          (Q'.ofNat n + 1) * Q'.abs difference ≈
            Q'.ofNat (n + 1) * Q'.abs (x - y) := by
        dsimp [difference]
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ halgebra hsuccessor)

/-! ## 2. Ideal orbit and explicit accumulated defect -/

/-- The exact heat-semigroup orbit starting from `initial`. -/
def idealDecimationOrbit (b : Nat) (initial : Q') : Nat → Q'
  | 0 => initial
  | n + 1 => mkDecimate b (idealDecimationOrbit b initial n)

/-- The explicit error recurrence forced by the `b`-Lipschitz block map. -/
def accumulatedDefect (b : Nat) (delta : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => delta n + Q'.ofNat b * accumulatedDefect b delta n

/-- The defect sequence extracted from a linked trajectory. -/
def trajectoryAccumulatedDefect
    {b : Nat} (T : LinkedBondMovingTrajectory b) (n : Nat) : Q' :=
  accumulatedDefect b (fun k => (T.step k).base.delta) n

theorem idealDecimationOrbit_nonnegative
    (b : Nat) {initial : Q'} (h0 : (0 : Q') ≤ initial) :
    ∀ n, (0 : Q') ≤ idealDecimationOrbit b initial n
  | 0 => h0
  | n + 1 =>
      mkDecimate_nonneg b (idealDecimationOrbit_nonnegative b h0 n)

theorem idealDecimationOrbit_le_one
    (b : Nat) {initial : Q'}
    (h0 : (0 : Q') ≤ initial) (h1 : initial ≤ (1 : Q')) :
    ∀ n, idealDecimationOrbit b initial n ≤ (1 : Q')
  | 0 => h1
  | n + 1 =>
      mkDecimate_le_one b
        (idealDecimationOrbit_nonnegative b h0 n)
        (idealDecimationOrbit_le_one b h0 h1 n)

theorem accumulatedDefect_nonnegative
    (b : Nat) {delta : Nat → Q'}
    (hdelta : ∀ k, (0 : Q') ≤ delta k) :
    ∀ n, (0 : Q') ≤ accumulatedDefect b delta n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _ (hdelta n)
        (Q'.mul_nonneg _ _
          (zero_le_ofNat b)
          (accumulatedDefect_nonnegative b hdelta n))

/-- The recursively defined ideal orbit is the single power with exponent
`b^n`.  This exposes the exact heat-semigroup depth reached after `n` linked
block steps. -/
theorem idealDecimationOrbit_eqv_qpow_natPow
    (b : Nat) (initial : Q') :
    ∀ n,
      idealDecimationOrbit b initial n ≈
        qpow initial (b ^ n)
  | 0 => by
      change initial ≈ qpow initial 1
      exact Q'.eqv_symm (Q'.one_mul_eqv initial)
  | n + 1 => by
      change
        qpow (idealDecimationOrbit b initial n) b ≈
          qpow initial (b ^ (n + 1))
      refine Q'.eqv_trans _ _ _
        (qpow_eqv_congr_base
          (idealDecimationOrbit_eqv_qpow_natPow b initial n) b) ?_
      rw [Nat.pow_succ]
      exact qpow_qpow initial (b ^ n) b

/-- The geometric sum can be read in the recurrence order appropriate to
propagated local errors: `G(n+1) = 1 + r G(n)`. -/
theorem geomSum_succ_eqv_one_add_mul (r : Q') :
    ∀ n,
      geomSum r (n + 1) ≈
        (1 : Q') + r * geomSum r n
  | 0 => by
      change ((0 : Q') + 1) ≈ (1 : Q') + r * 0
      refine Q'.eqv_trans _ (1 : Q') _
        (q_zero_add_eqv 1) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ ((1 : Q') + 0) _
        (Q'.add_eqv_congr_left 1 _ _ (q_mul_zero r)) ?_
      exact q_add_zero_eqv 1
  | n + 1 => by
      change
        geomSum r (n + 1) + qpow r (n + 1) ≈
          (1 : Q') + r * (geomSum r n + qpow r n)
      refine Q'.eqv_trans _
        (((1 : Q') + r * geomSum r n) + qpow r n * r) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (geomSum_succ_eqv_one_add_mul r n)
          (Q'.eqv_refl _)
      refine Q'.eqv_trans _
        ((1 : Q') + (r * geomSum r n + qpow r n * r)) _
        (Q'.add_assoc_eqv _ _ _) ?_
      apply Q'.add_eqv_congr_left
      refine Q'.eqv_trans _
        (r * geomSum r n + r * qpow r n) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_comm_eqv (qpow r n) r)
      exact Q'.eqv_symm
        (Q'.mul_add_eqv r (geomSum r n) (qpow r n))

private def uniformDefectStepL :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  let ceiling := YMGap.Continuum.RingNormaliser.PolyExpr.var 0
  let base := YMGap.Continuum.RingNormaliser.PolyExpr.var 1
  let previous := YMGap.Continuum.RingNormaliser.PolyExpr.var 2
  .add ceiling (.mul base (.mul ceiling previous))

private def uniformDefectStepR :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  let ceiling := YMGap.Continuum.RingNormaliser.PolyExpr.var 0
  let base := YMGap.Continuum.RingNormaliser.PolyExpr.var 1
  let previous := YMGap.Continuum.RingNormaliser.PolyExpr.var 2
  .mul ceiling (.add (.const 1) (.mul base previous))

private theorem uniformDefectStep_normal :
    YMGap.Continuum.RingNormaliser.normalize uniformDefectStepL =
      YMGap.Continuum.RingNormaliser.normalize uniformDefectStepR := by
  decide

private theorem uniform_defect_step
    (ceiling base previous : Q') :
    ceiling + base * (ceiling * previous) ≈
      ceiling * ((1 : Q') + base * previous) := by
  simpa [uniformDefectStepL, uniformDefectStepR,
    YMGap.Continuum.RingNormaliser.eval] using
    (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      uniformDefectStepL uniformDefectStepR
      uniformDefectStep_normal
      (fun | 0 => ceiling | 1 => base | _ => previous))

/-- A uniform local residual ceiling gives the closed geometric accumulated
budget `ceiling * (1 + b + ... + b^(n-1))`. -/
theorem accumulatedDefect_le_ceiling_mul_geomSum
    (b : Nat) {delta : Nat → Q'} (ceiling : Q')
    (hdelta : ∀ k, delta k ≤ ceiling) :
    ∀ n,
      accumulatedDefect b delta n ≤
        ceiling * geomSum (Q'.ofNat b) n
  | 0 => by
      change (0 : Q') ≤ ceiling * 0
      exact Q'.le_of_eqv (Q'.eqv_symm (q_mul_zero ceiling))
  | n + 1 => by
      have hinduction :=
        accumulatedDefect_le_ceiling_mul_geomSum
          b ceiling hdelta n
      have hscaled :
          Q'.ofNat b * accumulatedDefect b delta n ≤
            Q'.ofNat b *
              (ceiling * geomSum (Q'.ofNat b) n) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hinduction
          (zero_le_ofNat b)
      refine Q'.le_trans' _
        (ceiling + Q'.ofNat b *
          (ceiling * geomSum (Q'.ofNat b) n)) _ ?_ ?_
      · exact Q'.add_le_add (hdelta n) hscaled
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _
        (ceiling *
          ((1 : Q') + Q'.ofNat b * geomSum (Q'.ofNat b) n)) _
        (uniform_defect_step ceiling (Q'.ofNat b)
          (geomSum (Q'.ofNat b) n)) ?_
      apply Q'.mul_eqv_congr_left
      exact Q'.eqv_symm
        (geomSum_succ_eqv_one_add_mul (Q'.ofNat b) n)

/-- **Linked-trajectory stability.**  Local certified block-map errors propagate
to the explicit recurrence `E(n+1) = delta(n) + b E(n)`.

The two unit-interval hypotheses refer to the actual physical iterate.  The
ideal orbit remains in the interval by construction. -/
theorem linked_weight_close_to_idealDecimationOrbit
    {b : Nat} (T : LinkedBondMovingTrajectory b)
    (hweight0 : ∀ k, (0 : Q') ≤ T.weight k)
    (hweight1 : ∀ k, T.weight k ≤ (1 : Q')) :
    ∀ n,
      Q'.abs
          (T.weight n - idealDecimationOrbit b (T.weight 0) n) ≤
        trajectoryAccumulatedDefect T n
  | 0 => by
      change Q'.abs (T.weight 0 - T.weight 0) ≤ (0 : Q')
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.abs_eqv_congr (Q'.add_neg_self_eqv (T.weight 0)))
          (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
            (Q'.le_refl' 0)))
  | n + 1 => by
      let actualDecimated := mkDecimate b (T.weight n)
      let idealPrevious := idealDecimationOrbit b (T.weight 0) n
      have hsplit :
          (T.weight (n + 1) -
              idealDecimationOrbit b (T.weight 0) (n + 1)) ≈
            (T.weight (n + 1) - actualDecimated) +
              (actualDecimated - mkDecimate b idealPrevious) := by
        change
          (T.weight (n + 1) - mkDecimate b idealPrevious) ≈
            (T.weight (n + 1) - actualDecimated) +
              (actualDecimated - mkDecimate b idealPrevious)
        exact YMGap.Continuum.TsumDeriv.sub_split
          (T.weight (n + 1)) actualDecimated
          (mkDecimate b idealPrevious)
      have htriangle :
          Q'.abs
              (T.weight (n + 1) -
                idealDecimationOrbit b (T.weight 0) (n + 1)) ≤
            Q'.abs (T.weight (n + 1) - actualDecimated) +
              Q'.abs (actualDecimated - mkDecimate b idealPrevious) := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)) ?_
        exact YMGap.Continuum.TsumDeriv.abs_add_le _ _
      have hlocal :
          Q'.abs (T.weight (n + 1) - actualDecimated) ≤
            (T.step n).base.delta := by
        exact linked_step_deviation_le T n
      have hideal0 : (0 : Q') ≤ idealPrevious :=
        idealDecimationOrbit_nonnegative b (hweight0 0) n
      have hideal1 : idealPrevious ≤ (1 : Q') :=
        idealDecimationOrbit_le_one b (hweight0 0) (hweight1 0) n
      have hpropagated :
          Q'.abs (actualDecimated - mkDecimate b idealPrevious) ≤
            Q'.ofNat b * trajectoryAccumulatedDefect T n := by
        change
          Q'.abs (qpow (T.weight n) b - qpow idealPrevious b) ≤
            Q'.ofNat b * trajectoryAccumulatedDefect T n
        refine Q'.le_trans' _ _ _
          (qpow_abs_sub_le_nat_mul
            (hweight0 n) (hweight1 n) hideal0 hideal1 b) ?_
        exact Q'.mul_le_mul_of_nonneg_left _ _ _
          (linked_weight_close_to_idealDecimationOrbit
            T hweight0 hweight1 n)
          (zero_le_ofNat b)
      refine Q'.le_trans' _ _ _ htriangle ?_
      exact Q'.add_le_add hlocal hpropagated

/-! ## 3. Corridor-entry compiler -/

/-- A certified ideal-orbit margin pays the entire accumulated interacting
defect and places the actual linked trajectory below the requested corridor. -/
theorem linked_weight_le_of_ideal_add_defect_le
    {b : Nat} (T : LinkedBondMovingTrajectory b)
    (hweight0 : ∀ k, (0 : Q') ≤ T.weight k)
    (hweight1 : ∀ k, T.weight k ≤ (1 : Q'))
    (n : Nat) (corridor : Q')
    (hbudget :
      idealDecimationOrbit b (T.weight 0) n +
          trajectoryAccumulatedDefect T n ≤ corridor) :
    T.weight n ≤ corridor := by
  have hclose :=
    linked_weight_close_to_idealDecimationOrbit T hweight0 hweight1 n
  exact Q'.le_trans' _ _ _
    (YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le hclose)
    hbudget

/-- The strong-coupling version of the compiler, with the repository's named
`anchorCoupling = 1/400` corridor made explicit in the statement. -/
theorem linked_weight_le_anchorCoupling
    {b : Nat} (T : LinkedBondMovingTrajectory b)
    (hweight0 : ∀ k, (0 : Q') ≤ T.weight k)
    (hweight1 : ∀ k, T.weight k ≤ (1 : Q'))
    (n : Nat)
    (hbudget :
      idealDecimationOrbit b (T.weight 0) n +
          trajectoryAccumulatedDefect T n ≤ anchorCoupling) :
    T.weight n ≤ anchorCoupling :=
  linked_weight_le_of_ideal_add_defect_le
    T hweight0 hweight1 n anchorCoupling hbudget

/-- **Closed-form strong-corridor criterion.**  If every local interacting
residual is at most `ceiling`, then `n` block steps enter the named strong
corridor whenever

`initial^(b^n) + ceiling * (1 + b + ... + b^(n-1)) <= 1/400`.

Thus the remaining physical task is an estimate on the actual linked BF4
residuals; no trajectory or residual bound is manufactured here. -/
theorem linked_weight_le_anchorCoupling_of_uniform_residual
    {b : Nat} (T : LinkedBondMovingTrajectory b)
    (hweight0 : ∀ k, (0 : Q') ≤ T.weight k)
    (hweight1 : ∀ k, T.weight k ≤ (1 : Q'))
    (ceiling : Q')
    (hdelta : ∀ k, (T.step k).base.delta ≤ ceiling)
    (n : Nat)
    (hbudget :
      qpow (T.weight 0) (b ^ n) +
          ceiling * geomSum (Q'.ofNat b) n ≤ anchorCoupling) :
    T.weight n ≤ anchorCoupling := by
  apply linked_weight_le_anchorCoupling T hweight0 hweight1 n
  refine Q'.le_trans' _
    (qpow (T.weight 0) (b ^ n) +
      ceiling * geomSum (Q'.ofNat b) n) _ ?_ hbudget
  exact Q'.add_le_add
    (Q'.le_of_eqv
      (idealDecimationOrbit_eqv_qpow_natPow b (T.weight 0) n))
    (accumulatedDefect_le_ceiling_mul_geomSum
      b ceiling hdelta n)

end YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability

#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.linked_step_deviation_le
#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.qpow_abs_sub_le_nat_mul
#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.idealDecimationOrbit_eqv_qpow_natPow
#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.accumulatedDefect_le_ceiling_mul_geomSum
#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.linked_weight_close_to_idealDecimationOrbit
#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.linked_weight_le_anchorCoupling
#print axioms YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability.linked_weight_le_anchorCoupling_of_uniform_residual
