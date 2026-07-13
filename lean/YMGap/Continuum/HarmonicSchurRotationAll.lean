/-
Conditional all-scale assembly for the harmonic Schur/spacing route.

The sole analytic input is the uniform second-order signed-chord moment cap.
Everything after that input is finite exact rational algebra.
-/

import YMGap.Continuum.HarmonicSignedChordQuantitative
import YMGap.Continuum.HarmonicThetaPascalClosure
import YMGap.Continuum.HarmonicSchurRotationIdentity
import YMGap.Continuum.HarmonicBulkThetaTail
import YMGap.Continuum.HarmonicSchurRotationK3337

namespace YMGap.Continuum.HarmonicSchurRotationAll

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK89
open YMGap.Continuum.HarmonicSchurRotationK101112
open YMGap.Continuum.HarmonicSchurRotationK1316
open YMGap.Continuum.HarmonicSchurRotationK1719
open YMGap.Continuum.HarmonicSchurRotationK2023
open YMGap.Continuum.HarmonicSchurRotationK2427
open YMGap.Continuum.HarmonicSchurRotationK2832
open YMGap.Continuum.HarmonicSchurRotationK3337
open YMGap.Continuum.HarmonicSignedChordAbsorption
open YMGap.Continuum.HarmonicSignedChordBudgetBridge
open YMGap.Continuum.HarmonicSignedChordQuantitative
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv
private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- The sole all-scale analytic input left by the second-order signed-chord
reduction.  The first-crossing hypotheses are exactly those produced by the
constructive crossing search in `HarmonicSignedChordAbsorption`. -/
def UniformQuadraticNodeCap : Prop :=
  ∀ k s : Nat, 5 ≤ k → s ≤ Ncut k - 1 →
    (∀ p, p < s →
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k p) ≤ (0 : Q')) →
    (0 : Q') ≤ trapezoidNodeCumulative k (Ncut k - 1) +
      -(trapezoidNodeCumulative k s) →
    signedChordQuadraticNodeMoment k s (Ncut k - 1 - s) +
        (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≤
      signedChordMomentCap k

/-- The quadratic-node cap implies the exact doubled signed-crossing budget
used by the compensated Abel bridge at every scale `k ≥ 5`. -/
theorem signed_crossing_budget_of_quadratic_cap
    (H : UniformQuadraticNodeCap) {k : Nat} (hk : 5 ≤ k)
    (s : Nat) (hsL : s ≤ Ncut k - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k p) ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k s)) :
    signedChordSum k (Ncut k - 1) s +
          (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≤
        (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative k (Ncut k - 1) *
              driftSqFactor k 0))) +
          (Q'.mkPos 24 25 (by decide) *
            (-(trapezoidNodeCumulative k (Ncut k - 1) *
              driftSqFactor k 0))) := by
  have hnode := signedChordNodeMoment_le_quadraticNodeMoment
    k (Ncut k - 1) s hsL hboundary
  have hcap := H k s hk hsL hfirst hboundary
  have hadd := Q'.add_le_add_right _ _
    (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) hnode
  have hsum := signedChordSum_eq_nodeMoment k (Ncut k - 1) s hsL
  have hsumadd :
      signedChordSum k (Ncut k - 1) s +
          (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) ≈
        signedChordNodeMoment k s (Ncut k - 1 - s) +
          (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) :=
    Q'.add_eqv_congr_right _ _ _ hsum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsumadd)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ hcap
        (signedChordMomentCap_le_target k (by omega))))

/-- The uniform quadratic cap closes the weighted trapezoid residual at every
scale.  Scales zero through four use the exact rational anchors already banked
in the signed-chord development. -/
theorem weightedTrapezoidResidual_nonpos_all
    (H : UniformQuadraticNodeCap) (k : Nat) :
    weightedTrapezoidResidual k ≤ (0 : Q') := by
  by_cases hk : 5 ≤ k
  · exact weightedTrapezoidResidual_nonpos_of_signed_crossing_budget k
      (signed_crossing_budget_of_quadratic_cap H hk)
  · have hsmall : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl | rfl
    · exact weightedTrapezoidResidual_nonpos_k0
    · exact weightedTrapezoidResidual_nonpos_k1
    · exact weightedTrapezoidResidual_nonpos_k2
    · exact weightedTrapezoidResidual_nonpos_k3
    · exact weightedTrapezoidResidual_nonpos_k4

private theorem le_of_sub_nonpos {a b : Q'}
    (h : a + (-b) ≤ (0 : Q')) : a ≤ b := by
  have hadd := Q'.add_le_add_right (a + (-b)) 0 b h
  have hleft : (a + (-b)) + b ≈ a := by
    have hb : -b + b ≈ (0 : Q') := by
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-b) b) ?_
      exact Q'.add_neg_self_eqv b
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a _ _ hb) ?_
    exact QPoly.q_add_zero_eqv a
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (QPoly.q_zero_add_eqv b)))

/-- The terminal-corrected trapezoid residual is precisely strong enough to
bound the fixed-cutoff harmonic weight covariance by the coefficient-two
inverse-square budget. -/
theorem harmonicWeightCross_le_twoInvSq_of_weightedResidual
    (k : Nat) (hres : weightedTrapezoidResidual k ≤ (0 : Q')) :
    harmonicWeightCross k ≤
      twoInvSq k * (harmonicD k * harmonicMidD k) := by
  let D := harmonicD k
  let A := harmonicA k
  let lam := twoInvSq k
  let X := harmonicDriftA k
  let P := driftDiagPrefix k
  let Y := harmonicDriftD k
  let T := trapezoidDriftA k
  let B := (A + lam * D) + (A + lam * D)
  have henergy : D * T + -(B * P) ≤ (0 : Q') := by
    have he := weightedTrapezoidResidual_eq_energy k
    have hform :
        harmonicD k * trapezoidDriftA k +
            -(((harmonicA k + twoInvSq k * harmonicD k) +
                (harmonicA k + twoInvSq k * harmonicD k)) * driftDiagPrefix k) ≈
          D * T + -(B * P) := by
      dsimp only [D, A, lam, X, P, Y, T, B]
      exact Q'.eqv_refl _
    have hER : D * T + -(B * P) ≤ weightedTrapezoidResidual k :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hform) (Q'.ge_of_eqv he)
    exact Q'.le_trans' _ _ _ hER hres
  have hDT : D * T ≤ B * P := le_of_sub_nonpos henergy
  have htrap : X + X ≤ T := by
    unfold X T
    exact harmonicDriftA_twice_le_trapezoid k
  have hD0 : (0 : Q') ≤ D := Q'.le_of_lt (harmonicD_pos k)
  have hscaled : D * (X + X) ≤ D * T :=
    Q'.mul_le_mul_of_nonneg_left _ _ D htrap hD0
  have hdouble : D * X + D * X ≤
      (A + lam * D) * P + (A + lam * D) * P := by
    have hleft : D * (X + X) ≈ D * X + D * X := Q'.mul_add_eqv _ _ _
    have hright : B * P ≈
        (A + lam * D) * P + (A + lam * D) * P := by
      unfold B
      exact Q'.add_mul_eqv _ _ _
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ hDT (Q'.le_of_eqv hright)))
  have htwo : Q'.ofNat 2 * (D * X) ≤
      Q'.ofNat 2 * ((A + lam * D) * P) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv (D * X)))
      (Q'.le_trans' _ _ _ hdouble
        (Q'.ge_of_eqv
          (CubeRatioBounds.ofNat_two_mul_eqv ((A + lam * D) * P))))
  have hDX : D * X ≤ (A + lam * D) * P :=
    FusionQuotientCollapse.le_of_mul_le_mul_left_pos
      (show (0 : Q') < Q'.ofNat 2 by decide) htwo
  have hPY : P ≤ Y := by
    have hpre : driftDiagPrefix k ≤ harmonicDriftD k := by
      unfold driftDiagPrefix harmonicDriftD oldDiag driftSqFactor
      exact AFRateCalibration.fsum_le_of_le
        (fun i => Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (coeffW_nonneg (harmW_nonneg k) i)
            (coeffW_nonneg (harmW_nonneg k) i))
          (Q'.mul_nonneg _ _
            (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)
            (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _))) (by omega)
    exact hpre
  have hcoef0 : (0 : Q') ≤ A + lam * D := by
    have hA0 : (0 : Q') ≤ A := by
      unfold A harmonicA
      exact adjCorr_nonneg (harmW_nonneg k) (Ncut k)
    have hlam0 : (0 : Q') ≤ lam := by
      unfold lam twoInvSq
      exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k)
    exact Q'.zero_le_add _ _ hA0
      (Q'.mul_nonneg _ _ hlam0 (Q'.le_of_lt (harmonicD_pos k)))
  have hDXfull : D * X ≤ (A + lam * D) * Y :=
    Q'.le_trans' _ _ _ hDX
      (Q'.mul_le_mul_of_nonneg_left _ _ (A + lam * D) hPY hcoef0)
  have hadd := Q'.add_le_add_right _ _ (-(A * Y)) hDXfull
  have hleft : D * X + -(A * Y) ≈ harmonicWeightCross k := by
    refine Q'.eqv_trans _
      (harmonicDriftA k * harmonicD k -
        harmonicA k * harmonicDriftD k) _ ?_ ?_
    · dsimp only [D, A, X, Y]
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv (harmonicD k) (harmonicDriftA k))
    · exact Q'.eqv_symm (harmonicWeightCross_eq_driftCovariance k)
  have hright : (A + lam * D) * Y + -(A * Y) ≈
      lam * (D * Y) := by
    let U := A * Y
    let V := (lam * D) * Y
    have hdist : (A + lam * D) * Y ≈ U + V := by
      unfold U V
      exact Q'.add_mul_eqv _ _ _
    refine Q'.eqv_trans _ ((U + V) + (-U)) _
      (Q'.add_eqv_congr_right _ _ (-U) hdist) ?_
    refine Q'.eqv_trans _ (U + (V + -U)) _
      (Q'.add_assoc_eqv U V (-U)) ?_
    refine Q'.eqv_trans _ (U + (-U + V)) _
      (Q'.add_eqv_congr_left U _ _ (Q'.add_comm_eqv V (-U))) ?_
    refine Q'.eqv_trans _ ((U + -U) + V) _
      (Q'.eqv_symm (Q'.add_assoc_eqv U (-U) V)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + V) _
      (Q'.add_eqv_congr_right _ _ V (Q'.add_neg_self_eqv U)) ?_
    refine Q'.eqv_trans _ V _ (QPoly.q_zero_add_eqv V) ?_
    unfold V
    exact Q'.mul_assoc_eqv lam D Y
  have hmid : lam * (D * Y) ≈
      twoInvSq k * (harmonicD k * harmonicMidD k) := by
    unfold lam D Y
    exact Q'.mul_eqv_congr_left (twoInvSq k) _ _
      (Q'.mul_eqv_congr_left (harmonicD k) _ _
        (Q'.eqv_symm (harmonicMidD_eq_driftSum k)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) (Q'.le_of_eqv hmid)))

/-! ## The shifted cutoff shell at the next harmonic weight -/

def shiftedCoeffSqTerm (k s : Nat) : Q' :=
  coeffW (harmW (k + 1)) s * coeffW (harmW (k + 1)) s

def shiftedSqWindow (k M : Nat) : Q' :=
  finSum (fun j => shiftedCoeffSqTerm k (Ncut k + j)) M

def shiftedAdjWindow (k M : Nat) : Q' :=
  finSum (fun j =>
    coeffW (harmW (k + 1)) (Ncut k + j) *
      coeffW (harmW (k + 1)) (Ncut k + j + 1)) M

private theorem shifted_eight_le_ratioBernDen (k : Nat) :
    Q'.ofNat 8 ≤
      bernDen (harmU (k + 1)) (2 * (2 * Ncut k + 3)) := by
  have h2 : 2 ≤ k + 2 := by omega
  have hN : 2 * (k + 2) ≤ Ncut k := by
    unfold Ncut
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (k + 2) h2
  have hnat : 8 * (k + 3) ≤ (k + 3) + 2 * (2 * Ncut k + 3) := by
    omega
  show (Q'.ofNat 8).num *
      ((bernDen (harmU (k + 1)) (2 * (2 * Ncut k + 3))).den : Int) ≤
    (bernDen (harmU (k + 1)) (2 * (2 * Ncut k + 3))).num *
      (Q'.ofNat 8).den
  unfold bernDen harmU unit
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  exact_mod_cast hnat

private theorem shifted_four_mul_mul_two_eqv_eight_mul (p : Q') :
    (Q'.ofNat 4 * p) * Q'.ofNat 2 ≈ Q'.ofNat 8 * p := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 4) p (Q'.ofNat 2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
      (Q'.mul_comm_eqv p (Q'.ofNat 2))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat 2) p)) ?_
  exact Q'.mul_eqv_congr_right _ _ p (by decide)

private theorem shifted_squaredBase_ratio_le_half (k : Nat) :
    Q'.ofNat 4 *
        qpow (harmW (k + 1) * harmW (k + 1)) (2 * Ncut k + 3) ≤
      HalfPow.half := by
  let n := 2 * Ncut k + 3
  let e := n + n
  let p := qpow (harmW (k + 1) * harmW (k + 1)) n
  let D := bernDen (harmU (k + 1)) e
  have hpow : p ≈ qpow (harmW (k + 1)) e := by
    dsimp only [p, e]
    refine Q'.eqv_trans _ _ _ (qpow_mul_self (harmW (k + 1)) n) ?_
    exact Q'.eqv_symm (qpow_add (harmW (k + 1)) n n)
  have hbern : qpow (harmW (k + 1)) e * D ≤ (1 : Q') := by
    dsimp only [D]
    unfold harmW
    exact oneSub_pow_mul_bernDen_le
      (harmU_nonneg (k + 1)) (harmU_le_one (k + 1)) e
  have hD8 : Q'.ofNat 8 ≤ D := by
    dsimp only [D, e, n]
    rw [show 2 * Ncut k + 3 + (2 * Ncut k + 3) =
      2 * (2 * Ncut k + 3) by omega]
    exact shifted_eight_le_ratioBernDen k
  have hp0 : (0 : Q') ≤ p :=
    qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg (k + 1)) (harmW_nonneg (k + 1))) n
  have hp8D : p * Q'.ofNat 8 ≤ p * D :=
    Q'.mul_le_mul_of_nonneg_left _ _ p hD8 hp0
  have h8p : Q'.ofNat 8 * p ≤ (1 : Q') := by
    have hpD : p * D ≤ (1 : Q') :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ D
          (Q'.le_of_eqv hpow)
          (Q'.le_of_lt (bernDen_pos (harmU_nonneg (k + 1)) e))) hbern
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hp8D hpD)
  have hmul : (Q'.ofNat 4 * p) * Q'.ofNat 2 ≤
      HalfPow.half * Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (shifted_four_mul_mul_two_eqv_eight_mul p))
      (Q'.le_trans' _ _ _ h8p
        (Q'.ge_of_eqv (by decide :
          HalfPow.half * Q'.ofNat 2 ≈ (1 : Q'))))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide) hmul

private theorem shifted_dim_boundary_cleared (k : Nat) :
    dimQ (Ncut k) ≤
      (Q'.mkPos 3 2 (by decide) * harmU k) *
        bernDen (harmU (k + 1)) (c4 (Ncut k)) := by
  let m := k + 2
  have hm2 : 2 ≤ m := by dsimp only [m]; omega
  have hfactor : 2 * (m + 1) ≤ 3 * m := by omega
  let x := m * m
  have hrest : x ≤ 2 * x + (m + 1) := by omega
  have hcore : (x + 1) * x ≤ (m + 1) + x * (x + 2) := by
    calc
      (x + 1) * x = x * x + x := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ x * x + (2 * x + (m + 1)) := Nat.add_le_add_left hrest _
      _ = (m + 1) + x * (x + 2) := by
        rw [Nat.mul_add]
        ac_rfl
  have hpoly :
      2 * (m * m + 1) * (m * (m + 1)) ≤
        3 * ((m + 1) + (m * m) * (m * m + 2)) := by
    calc
      2 * (m * m + 1) * (m * (m + 1)) =
          ((m * m + 1) * m) * (2 * (m + 1)) := by ac_rfl
      _ ≤ ((m * m + 1) * m) * (3 * m) :=
        Nat.mul_le_mul_left ((m * m + 1) * m) hfactor
      _ = 3 * ((x + 1) * x) := by dsimp only [x]; ac_rfl
      _ ≤ 3 * ((m + 1) + x * (x + 2)) := Nat.mul_le_mul_left 3 hcore
      _ = 3 * ((m + 1) + (m * m) * (m * m + 2)) := by rfl
  have hnat :
      (Ncut k + 1) *
          (2 * (k + 1 + 1) * (k + 1 + 1 + 1)) ≤
        3 * ((k + 1 + 1 + 1) + c4 (Ncut k)) := by
    have hraw :
        2 * (Ncut k + 1) * ((k + 2) * (k + 3)) ≤
          3 * ((k + 3) + c4 (Ncut k)) := by
      simpa only [Ncut, c4, m,
        show k + 3 = (k + 2) + 1 by omega] using hpoly
    simpa only [show k + 1 + 1 = k + 2 by omega,
      show k + 1 + 1 + 1 = k + 3 by omega,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hraw
  show (dimQ (Ncut k)).num *
      (((Q'.mkPos 3 2 (by decide) * harmU k) *
        bernDen (harmU (k + 1)) (c4 (Ncut k))).den : Int) ≤
    ((Q'.mkPos 3 2 (by decide) * harmU k) *
        bernDen (harmU (k + 1)) (c4 (Ncut k))).num *
      (dimQ (Ncut k)).den
  unfold dimQ harmU unit bernDen
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  exact_mod_cast hnat

private theorem shifted_boundary_coeff_le (k : Nat) :
    coeffW (harmW (k + 1)) (Ncut k) ≤
      Q'.mkPos 3 2 (by decide) * harmU k := by
  let u := harmU (k + 1)
  let n := c4 (Ncut k)
  let D := bernDen u n
  let C := Q'.mkPos 3 2 (by decide) * harmU k
  have hbern : qpow (harmW (k + 1)) n * D ≤ (1 : Q') := by
    dsimp only [D, u]
    unfold harmW
    exact oneSub_pow_mul_bernDen_le
      (harmU_nonneg (k + 1)) (harmU_le_one (k + 1)) n
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ (Ncut k)) hbern
    (dimQ_nonneg (Ncut k))
  have hleft : dimQ (Ncut k) * (qpow (harmW (k + 1)) n * D) ≈
      coeffW (harmW (k + 1)) (Ncut k) * D := by
    dsimp only [n, D]
    unfold coeffW
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hcD : dimQ (Ncut k) ≤ C * D := by
    dsimp only [C, D, u, n]
    exact shifted_dim_boundary_cleared k
  have hcleared : coeffW (harmW (k + 1)) (Ncut k) * D ≤ C * D :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscale
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hcD))
  exact BakryEmery.le_of_mul_le_mul_right_pos
    (bernDen_pos (harmU_nonneg (k + 1)) n) hcleared

private theorem shifted_boundary_sq_le (k : Nat) :
    shiftedCoeffSqTerm k (Ncut k) ≤
      Q'.mkPos 9 4 (by decide) * invSqTerm 2 (by decide) k := by
  have hc0 : (0 : Q') ≤ coeffW (harmW (k + 1)) (Ncut k) :=
    coeffW_nonneg (harmW_nonneg (k + 1)) _
  have hsq := Q'.mul_le_mul_of_nonneg
    (shifted_boundary_coeff_le k) (shifted_boundary_coeff_le k)
    (Q'.mul_nonneg _ _ (by decide) (harmU_nonneg k)) hc0
  refine Q'.le_trans' _ _ _ hsq ?_
  have huSq : harmU k * harmU k ≈ invSqTerm 2 (by decide) k := by
    have hm : 0 < k + 2 := by omega
    have hmm : 0 < (k + 2) * (k + 2) := Nat.mul_pos hm hm
    unfold harmU unit invSqTerm
    show (Q'.mkPos 1 (k + 2) hm *
        Q'.mkPos 1 (k + 2) hm).num *
        ((Q'.mkPos 1 ((k + 2) * (k + 2)) hmm).den : Int) =
      (Q'.mkPos 1 ((k + 2) * (k + 2)) hmm).num *
        ((Q'.mkPos 1 (k + 2) hm *
          Q'.mkPos 1 (k + 2) hm).den : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.mkPos_num, Q'.mkPos_den]
    push_cast
    omega
  have hc :
      Q'.mkPos 3 2 (by decide) * Q'.mkPos 3 2 (by decide) ≈
        Q'.mkPos 9 4 (by decide) := by decide
  exact Q'.le_of_eqv (Q'.eqv_trans _
    ((Q'.mkPos 3 2 (by decide) * Q'.mkPos 3 2 (by decide)) *
      (harmU k * harmU k)) _
    (by ring_qeqv)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (harmU k * harmU k) hc)
      (Q'.mul_eqv_congr_left (Q'.mkPos 9 4 (by decide)) _ _ huSq)))

private theorem shiftedCoeffSqTerm_eqv_tailTerm (k s : Nat) :
    shiftedCoeffSqTerm k s ≈
      tailTerm (harmW (k + 1) * harmW (k + 1)) 2 s := by
  refine Q'.eqv_trans _ _ _ (coeffW_sq_eqv (harmW (k + 1)) s) ?_
  unfold tailTerm dimQ
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat (s + 1)) (Q'.ofNat (s + 1)) _)) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  rw [Nat.pow_two]
  exact Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (s + 1) (s + 1))

private theorem shifted_double_recurrence (A : Q') :
    A + HalfPow.half * (A + A) ≤ A + A := by
  refine Q'.le_of_eqv (Q'.add_eqv_congr_left A _ _ ?_)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half A A) ?_
  exact ExpNeg.two_halves A

theorem shiftedSqWindow_le (k M : Nat) :
    shiftedSqWindow k M ≤
      (Q'.mkPos 9 4 (by decide) * invSqTerm 2 (by decide) k) +
        (Q'.mkPos 9 4 (by decide) * invSqTerm 2 (by decide) k) := by
  let A := Q'.mkPos 9 4 (by decide) * invSqTerm 2 (by decide) k
  let f : Nat → Q' := fun j => shiftedCoeffSqTerm k (Ncut k + j)
  have hA : (0 : Q') ≤ A :=
    Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k)
  have hf0 : f 0 ≤ A := by
    dsimp only [f, A]
    simpa only [Nat.add_zero] using shifted_boundary_sq_le k
  have hdom : ∀ j, f (j + 1) ≤ HalfPow.half * f j := by
    intro j
    have hv0 : (0 : Q') ≤ harmW (k + 1) * harmW (k + 1) :=
      Q'.mul_nonneg _ _ (harmW_nonneg (k + 1)) (harmW_nonneg (k + 1))
    have hv1 : harmW (k + 1) * harmW (k + 1) ≤ (1 : Q') := by
      have hmul := Q'.mul_le_mul_of_nonneg
        (harmW_le_one (k + 1)) (harmW_le_one (k + 1))
        (by decide) (harmW_nonneg (k + 1))
      exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))
    have ht := tailTerm_ratio hv0 hv1 2 (Ncut k) j
    have ht' := Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (shifted_squaredBase_ratio_le_half k)
        (tailTerm_nonneg hv0 _ _))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (shiftedCoeffSqTerm_eqv_tailTerm k (Ncut k + (j + 1))))
      (Q'.le_trans' _ _ _ ht'
        (Q'.ge_of_eqv
          (Q'.mul_eqv_congr_left HalfPow.half _ _
            (shiftedCoeffSqTerm_eqv_tailTerm k (Ncut k + j)))))
  exact CharacterTail.geom_series_le f A HalfPow.half (A + A)
    HalfPow.half_nonneg (Q'.zero_le_add _ _ hA hA) hf0 hdom
    (shifted_double_recurrence A) M

private theorem shiftedSqWindow_succ_le (k M : Nat) :
    finSum (fun j => shiftedCoeffSqTerm k (Ncut k + j + 1)) M ≤
      (Q'.mkPos 9 4 (by decide) * invSqTerm 2 (by decide) k) +
        (Q'.mkPos 9 4 (by decide) * invSqTerm 2 (by decide) k) := by
  let f := fun j => shiftedCoeffSqTerm k (Ncut k + j)
  have hf0 : ∀ j, (0 : Q') ≤ f j := by
    intro j
    unfold f shiftedCoeffSqTerm
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg (k + 1)) _)
      (coeffW_nonneg (harmW_nonneg (k + 1)) _)
  have hsplit := YMGap.Constructive.finSum_split f 1 M
  have hhead : (0 : Q') ≤ finSum f 1 := by
    show (0 : Q') ≤ (0 : Q') + f 0
    exact Q'.zero_le_add _ _ (Q'.le_refl' 0) (hf0 0)
  have hshift : finSum (fun j => f (1 + j)) M ≤ finSum f (1 + M) := by
    have h := Q'.add_le_self_of_nonneg
      (finSum (fun j => f (1 + j)) M) (finSum f 1) hhead
    exact Q'.le_trans' _ _ _ h
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
        (Q'.ge_of_eqv hsplit))
  have hre :
      finSum (fun j => shiftedCoeffSqTerm k (Ncut k + j + 1)) M ≈
        finSum (fun j => f (1 + j)) M := by
    exact finSum_eqv_congr _ _ (fun j => by
      unfold f
      rw [show Ncut k + j + 1 = Ncut k + (1 + j) by omega]
      exact Q'.eqv_refl _) M
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hre)
    (Q'.le_trans' _ _ _ hshift (shiftedSqWindow_le k (1 + M)))

/-- The entire newly added adjacent shell at weight `harmW (k+1)` is bounded
by `9/2` inverse-square units.  The factor `1/2` is retained by summing the
doubled AM--GM inequality before cancellation. -/
theorem shiftedAdjWindow_le (k M : Nat) :
    shiftedAdjWindow k M ≤
      Q'.mkPos 9 2 (by decide) * invSqTerm 2 (by decide) k := by
  let X := fun j => shiftedCoeffSqTerm k (Ncut k + j)
  let Y := fun j => shiftedCoeffSqTerm k (Ncut k + j + 1)
  let E := fun j =>
    coeffW (harmW (k + 1)) (Ncut k + j) *
      coeffW (harmW (k + 1)) (Ncut k + j + 1)
  have hterm : ∀ j, E j + E j ≤ X j + Y j := by
    intro j
    unfold E X Y shiftedCoeffSqTerm
    exact CRealAlg.amgm_two _ _
  have hsum := CharacterTail.finSum_le_termwise
    (fun j => E j + E j) (fun j => X j + Y j) hterm M
  have hL : finSum (fun j => E j + E j) M ≈
      shiftedAdjWindow k M + shiftedAdjWindow k M := by
    refine Q'.eqv_trans _ _ _ (RationalTail.finSum_add E E M) ?_
    exact Q'.add_eqv_congr'
      (finSum_eqv_congr E _ (fun _ => Q'.eqv_refl _) M)
      (finSum_eqv_congr E _ (fun _ => Q'.eqv_refl _) M)
  have hR : finSum (fun j => X j + Y j) M ≈
      finSum X M + finSum Y M := RationalTail.finSum_add X Y M
  let B := Q'.mkPos 9 2 (by decide) * invSqTerm 2 (by decide) k
  have hX : finSum X M ≤ B := by
    unfold X B
    exact Q'.le_trans' _ _ _ (shiftedSqWindow_le k M)
      (Q'.le_of_eqv (by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ _ (by decide)))
  have hY : finSum Y M ≤ B := by
    unfold Y B
    exact Q'.le_trans' _ _ _ (shiftedSqWindow_succ_le k M)
      (Q'.le_of_eqv (by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
        exact Q'.mul_eqv_congr_right _ _ _ (by decide)))
  have hdouble : shiftedAdjWindow k M + shiftedAdjWindow k M ≤ B + B :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hsum
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hR)
          (AFRateCalibration.q_add_le_add hX hY)))
  have htwo : Q'.ofNat 2 * shiftedAdjWindow k M ≤ Q'.ofNat 2 * B :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv _))
      (Q'.le_trans' _ _ _ hdouble
        (Q'.ge_of_eqv (CubeRatioBounds.ofNat_two_mul_eqv B)))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (by decide : (0 : Q') < Q'.ofNat 2) htwo

private theorem harmonic_adjacent_shell_eqv (k : Nat) :
    harmonicA (k + 1) - harmonicMidA k ≈
      shiftedAdjWindow k (Ncut (k + 1) - Ncut k) := by
  have hN : Ncut k ≤ Ncut (k + 1) := by
    unfold Ncut
    exact Nat.mul_le_mul (by omega) (by omega)
  let M := Ncut (k + 1) - Ncut k
  have hNM : Ncut k + M = Ncut (k + 1) := Nat.add_sub_of_le hN
  have hsplit : harmonicA (k + 1) ≈
      harmonicMidA k + shiftedAdjWindow k M := by
    unfold harmonicA harmonicMidA adjCorr shiftedAdjWindow
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    rw [← hNM]
    exact YMGap.Constructive.finSum_split
      (fun s => coeffW (harmW (k + 1)) s *
        coeffW (harmW (k + 1)) (s + 1)) (Ncut k) M
  change harmonicA (k + 1) - harmonicMidA k ≈ shiftedAdjWindow k M
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(harmonicMidA k)) hsplit) ?_
  let A := harmonicMidA k
  let T := shiftedAdjWindow k M
  change (A + T) + (-A) ≈ T
  refine Q'.eqv_trans _ (A + (T + -A)) _
    (Q'.add_assoc_eqv A T (-A)) ?_
  refine Q'.eqv_trans _ (A + (-A + T)) _
    (Q'.add_eqv_congr_left A _ _ (Q'.add_comm_eqv T (-A))) ?_
  refine Q'.eqv_trans _ ((A + -A) + T) _
    (Q'.eqv_symm (Q'.add_assoc_eqv A (-A) T)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + T) _
    (Q'.add_eqv_congr_right _ _ T (Q'.add_neg_self_eqv A)) ?_
  exact QPoly.q_zero_add_eqv T

theorem harmonic_adjacent_shell_le (k : Nat) :
    harmonicA (k + 1) - harmonicMidA k ≤
      Q'.mkPos 9 2 (by decide) * invSqTerm 2 (by decide) k := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (harmonic_adjacent_shell_eqv k))
    (shiftedAdjWindow_le k (Ncut (k + 1) - Ncut k))

/-! ## Uniform determinant and mass-drop bounds -/

def harmonicMassDropCoeff : Q' := Q'.mkPos 13 2 (by decide)

theorem harmonicMassCross_le_uniform (H : UniformQuadraticNodeCap) (k : Nat) :
    harmonicMassCross k ≤
      (harmonicMassDropCoeff * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) := by
  let I := invSqTerm 2 (by decide) k
  let P := harmonicD k * harmonicD (k + 1)
  let W := Q'.ofNat 2 * I
  let B := Q'.mkPos 9 2 (by decide) * I
  have hweight0 := harmonicWeightCross_le_twoInvSq_of_weightedResidual k
    (weightedTrapezoidResidual_nonpos_all H k)
  have hD0 : (0 : Q') ≤ harmonicD k := Q'.le_of_lt (harmonicD_pos k)
  have hD10 : (0 : Q') ≤ harmonicD (k + 1) :=
    Q'.le_of_lt (harmonicD_pos (k + 1))
  have hmidprod : harmonicD k * harmonicMidD k ≤ P := by
    unfold P
    exact Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD k)
      (harmonicMidD_le_next k) hD0
  have hW0 : (0 : Q') ≤ W := by
    unfold W I
    exact Q'.mul_nonneg _ _ (by decide)
      (invSqTerm_nonneg 2 (by decide) k)
  have hweight : harmonicWeightCross k ≤ W * P := by
    exact Q'.le_trans' _ _ _ hweight0
      (Q'.mul_le_mul_of_nonneg_left _ _ W hmidprod hW0)
  have hcut0 := harmonicCutoffCross_le_adjShell_mul_D k
  have hshellD :
      (harmonicA (k + 1) - harmonicMidA k) * harmonicD k ≤
        B * harmonicD k := by
    unfold B I
    exact Q'.mul_le_mul_of_nonneg_right _ _ (harmonicD k)
      (harmonic_adjacent_shell_le k) hD0
  have hDle : harmonicD k ≤ P := by
    have h1 := EndpointCutoffTwoParameter.coordNormSq_ge_one
      (harmW_nonneg (k + 1)) (Ncut (k + 1))
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD k) h1 hD0
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hm
  have hB0 : (0 : Q') ≤ B := by
    unfold B I
    exact Q'.mul_nonneg _ _ (by decide)
      (invSqTerm_nonneg 2 (by decide) k)
  have hcut : harmonicCutoffCross k ≤ B * P := by
    exact Q'.le_trans' _ _ _ hcut0
      (Q'.le_trans' _ _ _ hshellD
        (Q'.mul_le_mul_of_nonneg_left _ _ B hDle hB0))
  have hadd : harmonicWeightCross k + harmonicCutoffCross k ≤
      W * P + B * P := AFRateCalibration.q_add_le_add hweight hcut
  have hcoef : W + B ≈ harmonicMassDropCoeff * I := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 + Q'.mkPos 9 2 (by decide)) * I) _ ?_ ?_
    · unfold W B
      exact Q'.eqv_symm (Q'.add_mul_eqv _ _ I)
    · unfold harmonicMassDropCoeff
      exact Q'.mul_eqv_congr_right _ _ I (by decide)
  have hcollapse : W * P + B * P ≈
      (harmonicMassDropCoeff * I) * P := by
    refine Q'.eqv_trans _ ((W + B) * P) _
      (Q'.eqv_symm (Q'.add_mul_eqv W B P)) ?_
    exact Q'.mul_eqv_congr_right _ _ P hcoef
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (harmonicMassCross_eq_weight_add_cutoff k))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hcollapse))

theorem harmonicMass_drop_le_uniform (H : UniformQuadraticNodeCap) (k : Nat) :
    harmonicMass k - harmonicMass (k + 1) ≤
      harmonicMassDropCoeff * invSqTerm 2 (by decide) k := by
  have hq := Q'.divPos_le_of_le_mul
    (harmonicMassCross k)
    (harmonicD k * harmonicD (k + 1))
    (Q'.mul_pos (harmonicD_pos k) (harmonicD_pos (k + 1)))
    (harmonicMassCross_le_uniform H k)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (harmonicMass_drop_eq_cross k)) hq

/-! ## Large-scale spacing payment -/

private def spacingBridgeUnit (k : Nat) : Q' :=
  unit (Ncut k * (k + 3))
    (Nat.mul_pos (Ncut_pos k) (by omega))

private theorem seven_fifths_unit_le_quadratic_floor
    {k : Nat} (hk : 38 ≤ k) :
    Q'.mkPos 7 5 (by decide) * harmU k ≤
      (Q'.mkPos 1 2 (by decide) * harmU k) *
        (Q'.ofNat 3 +
          -(Q'.ofNat 3 * (Q'.mkPos 1 2 (by decide) * harmU k))) := by
  show (Q'.mkPos 7 5 (by decide) * harmU k).num *
      (((Q'.mkPos 1 2 (by decide) * harmU k) *
        (Q'.ofNat 3 +
          -(Q'.ofNat 3 * (Q'.mkPos 1 2 (by decide) * harmU k)))).den : Int) ≤
    ((Q'.mkPos 1 2 (by decide) * harmU k) *
        (Q'.ofNat 3 +
          -(Q'.ofNat 3 * (Q'.mkPos 1 2 (by decide) * harmU k)))).num *
      ((Q'.mkPos 7 5 (by decide) * harmU k).den : Int)
  unfold harmU unit
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.add_mul,
    Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul, Int.mul_one]
  push_cast
  have hbase : 15 ≤ 2 * (k + 2) := by omega
  have hscaled := Nat.mul_le_mul_right (k + 2) hbase
  have hscaled' : 15 * (k + 2) ≤ 2 * ((k + 2) * (k + 2)) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled
  have hnat :
      7 * (2 * (k + 2) * (2 * (k + 2))) + 3 * (5 * (k + 2)) ≤
        3 * (2 * (k + 2)) * (5 * (k + 2)) := by
    let m := k + 2
    have hL : 7 * (2 * m * (2 * m)) = 28 * (m * m) := by
      calc
        7 * (2 * m * (2 * m)) = (7 * 2 * 2) * (m * m) := by ac_rfl
        _ = 28 * (m * m) := by
          rw [show 7 * 2 * 2 = 28 by decide]
    have hT : 3 * (5 * m) = 15 * m := by
      calc
        3 * (5 * m) = (3 * 5) * m := by ac_rfl
        _ = 15 * m := by rw [show 3 * 5 = 15 by decide]
    have hR : 3 * (2 * m) * (5 * m) = 30 * (m * m) := by
      calc
        3 * (2 * m) * (5 * m) = (3 * 2 * 5) * (m * m) := by ac_rfl
        _ = 30 * (m * m) := by rw [show 3 * 2 * 5 = 30 by decide]
    rw [show k + 2 = m by rfl, hL, hT, hR]
    calc
      28 * (m * m) + 15 * m ≤
          28 * (m * m) + 2 * (m * m) :=
        Nat.add_le_add_left (by simpa only [m] using hscaled') _
      _ = 30 * (m * m) := by
        rw [← Nat.add_mul]
  have hint :
      (7 * (2 * (k + 2) * (2 * (k + 2))) : Int) +
          3 * (5 * (k + 2)) ≤
        3 * (2 * (k + 2)) * (5 * (k + 2)) := by
    exact_mod_cast hnat
  push_cast at hint
  rw [show (k : Int) + 1 + 1 = (k : Int) + 2 by omega]
  omega

private theorem spacing_drop_bridge_lower {k : Nat} (hk : 38 ≤ k) :
    Q'.mkPos 19 10 (by decide) * spacingBridgeUnit k ≤
      harmonicSpacing k - harmonicSpacing (k + 1) := by
  unfold spacingBridgeUnit harmonicSpacing Ncut unit
  change Q'.mkPos 19 10 (by decide) *
      Q'.mkPos 1 (((k + 2) * (k + 2)) * (k + 3))
        (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) ≤
    Q'.mkPos 1 ((k + 2) * (k + 2))
        (Nat.mul_pos (by omega) (by omega)) +
      -(Q'.mkPos 1 ((k + 3) * (k + 3))
        (Nat.mul_pos (by omega) (by omega)))
  show (Q'.mkPos 19 10 (by decide) *
      Q'.mkPos 1 (((k + 2) * (k + 2)) * (k + 3))
        (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).num *
      ((Q'.mkPos 1 ((k + 2) * (k + 2))
          (Nat.mul_pos (by omega) (by omega)) +
        -(Q'.mkPos 1 ((k + 3) * (k + 3))
          (Nat.mul_pos (by omega) (by omega)))).den : Int) ≤
    (Q'.mkPos 1 ((k + 2) * (k + 2))
          (Nat.mul_pos (by omega) (by omega)) +
        -(Q'.mkPos 1 ((k + 3) * (k + 3))
          (Nat.mul_pos (by omega) (by omega)))).num *
      ((Q'.mkPos 19 10 (by decide) *
        Q'.mkPos 1 (((k + 2) * (k + 2)) * (k + 3))
          (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.add_mul, Int.neg_mul,
    Int.one_mul, Int.mul_one]
  push_cast
  let m := k + 2
  let m1 := k + 3
  let x := m * m
  let d := 2 * m + 1
  let C := 10 * (x * m1)
  have hm1 : m1 = m + 1 := by rfl
  have hsq : m1 * m1 = x + d := by
    rw [hm1]
    unfold x d
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  have hbase : 19 * m1 ≤ 10 * d := by
    dsimp only [m, m1, d]
    omega
  have hmul := Nat.mul_le_mul_left (x * m1) hbase
  have hcore : 19 * (x * (m1 * m1)) ≤ d * C := by
    unfold C
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hnat :
      19 * (x * (m1 * m1)) ≤ (m1 * m1) * C - x * C := by
    calc
      19 * (x * (m1 * m1)) ≤ d * C := hcore
      _ = (x + d) * C - x * C := by
        have hdist : (x + d) * C = x * C + d * C := Nat.add_mul x d C
        rw [hdist]
        omega
      _ = (m1 * m1) * C - x * C := by rw [hsq]
  have hint0 :
      (19 * (x * (m1 * m1)) : Int) ≤
        ((m1 * m1) * C - x * C : Nat) := by
    exact_mod_cast hnat
  have hx : x ≤ m1 * m1 := by
    rw [hsq]
    omega
  have hxc : x * C ≤ (m1 * m1) * C := Nat.mul_le_mul_right C hx
  have hsubcast :
      (((m1 * m1) * C - x * C : Nat) : Int) =
        ((m1 * m1) * C : Nat) - (x * C : Nat) := by
    exact Int.ofNat_sub hxc
  rw [hsubcast] at hint0
  dsimp only [m, m1, x, C] at hint0
  push_cast at hint0
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hint0

private theorem large_scale_scalar_payment {k : Nat} (hk : 38 ≤ k) :
    (Q'.mkPos 9 25 (by decide) *
        (harmonicMassDropCoeff * invSqTerm 2 (by decide) k)) *
          harmonicSpacing k ≤
      (Q'.mkPos 7 5 (by decide) * harmU k) *
        (Q'.mkPos 19 10 (by decide) * spacingBridgeUnit k) := by
  show ((Q'.mkPos 9 25 (by decide) *
        (harmonicMassDropCoeff * invSqTerm 2 (by decide) k)) *
          harmonicSpacing k).num *
      (((Q'.mkPos 7 5 (by decide) * harmU k) *
        (Q'.mkPos 19 10 (by decide) * spacingBridgeUnit k)).den : Int) ≤
    ((Q'.mkPos 7 5 (by decide) * harmU k) *
        (Q'.mkPos 19 10 (by decide) * spacingBridgeUnit k)).num *
      (((Q'.mkPos 9 25 (by decide) *
        (harmonicMassDropCoeff * invSqTerm 2 (by decide) k)) *
          harmonicSpacing k).den : Int)
  unfold harmonicMassDropCoeff invSqTerm harmonicSpacing harmU
    spacingBridgeUnit Ncut unit
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.mul_one]
  push_cast
  have hbase : 117 * (k + 3) ≤ 133 * (k + 2) := by omega
  have hnat :
      117 * (5 * (k + 2) *
        (10 * ((k + 2) * (k + 2) * (k + 3)))) ≤
      133 * (25 * (2 * ((k + 2) * (k + 2))) *
        ((k + 2) * (k + 2))) := by
    let m := k + 2
    have hmul := Nat.mul_le_mul_left
      ((5 * 10) * (m * m * m)) hbase
    have h50 : 5 * 10 = 25 * 2 := by decide
    calc
      117 * (5 * (k + 2) *
          (10 * ((k + 2) * (k + 2) * (k + 3)))) =
        ((5 * 10) * (m * m * m)) * (117 * (k + 3)) := by
          dsimp only [m]
          ac_rfl
      _ ≤ ((5 * 10) * (m * m * m)) * (133 * (k + 2)) := hmul
      _ = 133 * (25 * (2 * ((k + 2) * (k + 2))) *
          ((k + 2) * (k + 2))) := by
        rw [h50]
        dsimp only [m]
        ac_rfl
  exact_mod_cast hnat

private theorem large_scale_mass_spacing_payment
    (H : UniformQuadraticNodeCap) {k : Nat} (hk : 38 ≤ k) :
    (Q'.mkPos 9 25 (by decide) *
        (harmonicMass k - harmonicMass (k + 1))) * harmonicSpacing k ≤
      harmonicMass k *
        (harmonicSpacing k - harmonicSpacing (k + 1)) := by
  let R := Q'.mkPos 9 25 (by decide)
  let C := harmonicMassDropCoeff * invSqTerm 2 (by decide) k
  let S := harmonicSpacing k
  let L := Q'.mkPos 7 5 (by decide) * harmU k
  let J := Q'.mkPos 19 10 (by decide) * spacingBridgeUnit k
  have hR0 : (0 : Q') ≤ R := by decide
  have hS0 : (0 : Q') ≤ S := Q'.le_of_lt (harmonicSpacing_pos k)
  have hdropR :
      R * (harmonicMass k - harmonicMass (k + 1)) ≤ R * C :=
    Q'.mul_le_mul_of_nonneg_left _ _ R (harmonicMass_drop_le_uniform H k) hR0
  have hdropRS :
      (R * (harmonicMass k - harmonicMass (k + 1))) * S ≤
        (R * C) * S :=
    Q'.mul_le_mul_of_nonneg_right _ _ S hdropR hS0
  have hscalar : (R * C) * S ≤ L * J := by
    unfold R C S L J
    exact large_scale_scalar_payment hk
  have hL0 : (0 : Q') ≤ L := by
    unfold L
    exact Q'.mul_nonneg _ _ (by decide) (harmU_nonneg k)
  have hJ : J ≤ harmonicSpacing k - harmonicSpacing (k + 1) := by
    unfold J
    exact spacing_drop_bridge_lower hk
  have hLJ : L * J ≤ L *
      (harmonicSpacing k - harmonicSpacing (k + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ L hJ hL0
  have hdiff0 : (0 : Q') ≤ harmonicSpacing k - harmonicSpacing (k + 1) :=
    Q'.sub_nonneg_of_le (harmonicSpacing_contracts k)
  have hLmass : L ≤ harmonicMass k := by
    exact Q'.le_trans' _ _ _ (seven_fifths_unit_le_quadratic_floor hk)
      (harmonic_quadratic_mass_floor (by omega))
  have hfinal : L * (harmonicSpacing k - harmonicSpacing (k + 1)) ≤
      harmonicMass k * (harmonicSpacing k - harmonicSpacing (k + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hLmass hdiff0
  exact Q'.le_trans' _ _ _ hdropRS
    (Q'.le_trans' _ _ _ hscalar (Q'.le_trans' _ _ _ hLJ hfinal))

private theorem le_of_add_le_add_left_local {p a b : Q'}
    (h : p + a ≤ p + b) : a ≤ b := by
  have hadd := Q'.add_le_add_left (-p) (p + a) (p + b) h
  have hleft : -p + (p + a) ≈ a := by
    refine Q'.eqv_trans _ ((-p + p) + a) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-p) p a)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + a) _
      (Q'.add_eqv_congr_right _ _ a (Q'.neg_add_self_eqv p)) ?_
    exact QPoly.q_zero_add_eqv a
  have hright : -p + (p + b) ≈ b := by
    refine Q'.eqv_trans _ ((-p + p) + b) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-p) p b)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + b) _
      (Q'.add_eqv_congr_right _ _ b (Q'.neg_add_self_eqv p)) ?_
    exact QPoly.q_zero_add_eqv b
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

private theorem harmonicShell_convex_eqv (k : Nat) :
    harmonicShell k ≈
      Q'.mkPos 16 25 (by decide) * harmonicMass k +
        Q'.mkPos 9 25 (by decide) * harmonicMass (k + 1) := by
  unfold harmonicShell FusedOffDiagonalCompression.rot11
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (by decide))
    (Q'.mul_eqv_congr_right _ _ _ (by decide))

private theorem shell_conservation_eqv (k : Nat) :
    (Q'.mkPos 9 25 (by decide) *
        (harmonicMass k - harmonicMass (k + 1))) * harmonicSpacing k +
      harmonicShell k * harmonicSpacing k ≈
        harmonicMass k * harmonicSpacing k := by
  let r := Q'.mkPos 9 25 (by decide)
  let c := Q'.mkPos 16 25 (by decide)
  let a := harmonicMass k
  let b := harmonicMass (k + 1)
  let s := harmonicSpacing k
  let X := (r * a) * s
  let Y := (r * b) * s
  let Z := (c * a) * s
  have hp : (r * (a - b)) * s ≈ X + -Y := by
    refine Q'.eqv_trans _ ((r * a + r * (-b)) * s) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ s (Q'.mul_add_eqv r a (-b))
    refine Q'.eqv_trans _ ((r * a + -(r * b)) * s) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ s
        (Q'.add_eqv_congr_left (r * a) _ _ (Q'.mul_neg_eqv r b))
    refine Q'.eqv_trans _ ((r * a) * s + (-(r * b)) * s) _
      (Q'.add_mul_eqv _ _ s) ?_
    exact Q'.add_eqv_congr_left X _ _ (Q'.neg_mul_eqv (r * b) s)
  have hs : harmonicShell k * s ≈ Z + Y := by
    refine Q'.eqv_trans _
      ((c * a + r * b) * s) _
      (Q'.mul_eqv_congr_right _ _ s (harmonicShell_convex_eqv k)) ?_
    exact Q'.add_mul_eqv _ _ s
  change (r * (a - b)) * s + harmonicShell k * s ≈ a * s
  refine Q'.eqv_trans _ ((X + -Y) + (Z + Y)) _
    (Q'.add_eqv_congr' hp hs) ?_
  refine Q'.eqv_trans _ ((-Y + Y) + (X + Z)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ ((0 : Q') + (X + Z)) _
    (Q'.add_eqv_congr_right _ _ (X + Z) (Q'.neg_add_self_eqv Y)) ?_
  refine Q'.eqv_trans _ (X + Z) _ (QPoly.q_zero_add_eqv _) ?_
  refine Q'.eqv_trans _ ((r * a + c * a) * s) _
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ s)) ?_
  refine Q'.mul_eqv_congr_right _ _ s ?_
  refine Q'.eqv_trans _ ((r + c) * a) _
    (Q'.eqv_symm (Q'.add_mul_eqv r c a)) ?_
  refine Q'.eqv_trans _ ((1 : Q') * a) _
    (Q'.mul_eqv_congr_right _ _ a (by decide)) ?_
  exact Q'.one_mul_eqv a

private theorem large_scale_shell_spacing_stage
    (H : UniformQuadraticNodeCap) {k : Nat} (hk : 38 ≤ k) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k := by
  let p := (Q'.mkPos 9 25 (by decide) *
    (harmonicMass k - harmonicMass (k + 1))) * harmonicSpacing k
  let q := harmonicMass k *
    (harmonicSpacing k - harmonicSpacing (k + 1))
  let t := harmonicMass k * harmonicSpacing (k + 1)
  have hpay : p ≤ q := by
    unfold p q
    exact large_scale_mass_spacing_payment H hk
  have hadd := Q'.add_le_add_right p q t hpay
  have hqt : q + t ≈ harmonicMass k * harmonicSpacing k := by
    unfold q t
    refine Q'.eqv_trans _
      (harmonicMass k *
        ((harmonicSpacing k - harmonicSpacing (k + 1)) +
          harmonicSpacing (k + 1))) _
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
    refine Q'.mul_eqv_congr_left (harmonicMass k) _ _ ?_
    let s := harmonicSpacing k
    let u := harmonicSpacing (k + 1)
    change (s + -u) + u ≈ s
    refine Q'.eqv_trans _ (s + (-u + u)) _
      (Q'.add_assoc_eqv s (-u) u) ?_
    refine Q'.eqv_trans _ (s + (0 : Q')) _
      (Q'.add_eqv_congr_left s _ _ (Q'.neg_add_self_eqv u)) ?_
    exact QPoly.q_add_zero_eqv s
  have hcons := shell_conservation_eqv k
  have hpc : p + harmonicShell k * harmonicSpacing k ≈
      harmonicMass k * harmonicSpacing k := by
    unfold p
    exact hcons
  have hpadded : p + t ≤ p + harmonicShell k * harmonicSpacing k :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hqt)
        (Q'.le_of_eqv (Q'.eqv_symm hpc)))
  exact le_of_add_le_add_left_local hpadded

/-! ## All-scale mass, Schur, and operator spacing laws -/

theorem harmonicMass_unit_floor_all (k : Nat) :
    harmU k ≤ harmonicMass k := by
  by_cases hk : k = 0
  · subst k
    decide
  · exact harmonic_unit_le_mass (by omega)

theorem harmonicMass_quadratic_floor_all (k : Nat) :
    (Q'.mkPos 1 2 (by decide) * harmU k) *
        (Q'.ofNat 3 +
          -(Q'.ofNat 3 * (Q'.mkPos 1 2 (by decide) * harmU k))) ≤
      harmonicMass k := by
  by_cases hk : k = 0
  · subst k
    decide
  · exact harmonic_quadratic_mass_floor (by omega)

theorem harmonicMass_shell_spacing_all
    (H : UniformQuadraticNodeCap) (k : Nat) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k := by
  by_cases hk : 38 ≤ k
  · exact large_scale_shell_spacing_stage H hk
  · have hcases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
      k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨
      k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨
      k = 36 ∨ k = 37 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact harmonicMass_shell_spacing_stage_k6
    · exact harmonicMass_shell_spacing_stage_k7
    · exact harmonicMass_shell_spacing_stage_k8
    · exact harmonicMass_shell_spacing_stage_k9
    · exact harmonicMass_shell_spacing_stage_k10
    · exact harmonicMass_shell_spacing_stage_k11
    · exact harmonicMass_shell_spacing_stage_k12
    · exact harmonicMass_shell_spacing_stage_k13
    · exact harmonicMass_shell_spacing_stage_k14
    · exact harmonicMass_shell_spacing_stage_k15
    · exact harmonicMass_shell_spacing_stage_k16
    · exact harmonicMass_shell_spacing_stage_k17
    · exact harmonicMass_shell_spacing_stage_k18
    · exact harmonicMass_shell_spacing_stage_k19
    · exact harmonicMass_shell_spacing_stage_k20
    · exact harmonicMass_shell_spacing_stage_k21
    · exact harmonicMass_shell_spacing_stage_k22
    · exact harmonicMass_shell_spacing_stage_k23
    · exact harmonicMass_shell_spacing_stage_k24
    · exact harmonicMass_shell_spacing_stage_k25
    · exact harmonicMass_shell_spacing_stage_k26
    · exact harmonicMass_shell_spacing_stage_k27
    · exact harmonicMass_shell_spacing_stage_k28
    · exact harmonicMass_shell_spacing_stage_k29
    · exact harmonicMass_shell_spacing_stage_k30
    · exact harmonicMass_shell_spacing_stage_k31
    · exact harmonicMass_shell_spacing_stage_k32
    · exact harmonicMass_shell_spacing_stage_k33
    · exact harmonicMass_shell_spacing_stage_k34
    · exact harmonicMass_shell_spacing_stage_k35
    · exact harmonicMass_shell_spacing_stage_k36
    · exact harmonicMass_shell_spacing_stage_k37

theorem harmonicSchur_spacing_all
    (H : UniformQuadraticNodeCap) (k : Nat) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k :=
  harmonicSchur_spacing_of_stage k (harmonicMass_shell_spacing_all H k)

theorem harmonic_operator_spacing_all
    (H : UniformQuadraticNodeCap) (k : Nat) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) *
        harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_all H k)

end YMGap.Continuum.HarmonicSchurRotationAll

#print axioms YMGap.Continuum.HarmonicSchurRotationAll.signed_crossing_budget_of_quadratic_cap
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.weightedTrapezoidResidual_nonpos_all
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicWeightCross_le_twoInvSq_of_weightedResidual
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.shiftedSqWindow_le
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.shiftedAdjWindow_le
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonic_adjacent_shell_le
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicMassCross_le_uniform
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicMass_drop_le_uniform
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicMass_unit_floor_all
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicMass_quadratic_floor_all
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicMass_shell_spacing_all
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonicSchur_spacing_all
#print axioms YMGap.Continuum.HarmonicSchurRotationAll.harmonic_operator_spacing_all
