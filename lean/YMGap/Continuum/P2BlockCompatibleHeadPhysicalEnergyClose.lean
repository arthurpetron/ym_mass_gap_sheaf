/-
Track 11.7-fusion / R3o -- close the physical all-cutoff head energy.

The growing finite computation is compiled into four constant-cost cells:
the first endpoint, the exceptional first interior edge, the uniform broad
interior stencil, and the terminal endpoint.  No peak search or enumeration
up to `blockNcut k` occurs.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadBroadStencil
import YMGap.Continuum.HarmonicSymbolicAnchorRatio
import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Continuum.MovingCutoff

namespace YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergyClose

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.P2BlockCompatibleHeadBroadStencil
open YMGap.Continuum.P2BlockCompatibleHeadDirichletCompiler
open YMGap.Continuum.P2BlockCompatibleHeadLocalEnergyCompiler
open YMGap.Continuum.P2BlockCompatibleHeadPhysicalBoundary
open YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergy
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den, Q'.neg_den, neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def q2 : Q' := Q'.ofNat 2
private def q3 : Q' := Q'.ofNat 3
private def q4 : Q' := Q'.ofNat 4
private def q7 : Q' := Q'.ofNat 7
private def q8 : Q' := Q'.ofNat 8
private def q12 : Q' := Q'.ofNat 12
private def q7e4 : Q' := Q'.mkPos 7 4 (by decide)
private def q11e4 : Q' := Q'.mkPos 11 4 (by decide)
private def q3e2 : Q' := Q'.mkPos 3 2 (by decide)
private def q127 : Q' := Q'.mkPos 127 128 (by decide)

private theorem ofNat_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ m => exact Q'.ofNat_succ_pos m

private theorem scaled_slack_cancel {c a b : Q'} (hc : (0 : Q') < c)
    (h : (0 : Q') <= c * (b + (-a))) : a <= b := by
  have hre : c * (b + (-a)) ≈ c * b + (-(c * a)) := by
    ring_qeqv
  have hsub : (0 : Q') <= c * b + (-(c * a)) :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv hre)
  exact Q'.le_of_mul_le_mul_left (Q'.le_of_sub_nonneg hsub) hc

private theorem span_seven_fourths {d L : Q'}
    (h : q7 * d <= q4 * L) : q7e4 * d <= L := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 1 4 (by decide)) h (by decide)
  have hleft : Q'.mkPos 1 4 (by decide) * (q7 * d) ≈ q7e4 * d := by
    unfold q7 q7e4
    ring_qeqv
  have hright : Q'.mkPos 1 4 (by decide) * (q4 * L) ≈ L := by
    unfold q4
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))

private def terminalSpanL : RingNormaliser.PolyExpr :=
  let n := RingNormaliser.PolyExpr.var 0
  let x := RingNormaliser.PolyExpr.var 1
  let y := RingNormaliser.PolyExpr.var 2
  let z := RingNormaliser.PolyExpr.var 3
  .add
    (.add
      (.mul (.const 4)
        (.add
          (.mul (.add n (.const (-3))) x)
          (.neg (.mul n y))))
      (.mul (.const 3)
        (.add (.mul n z)
          (.neg (.mul (.add n (.const (-4))) y)))))
    (.mul (.const 12) (.add x (.neg y)))

private def terminalSpanR : RingNormaliser.PolyExpr :=
  let n := RingNormaliser.PolyExpr.var 0
  let x := RingNormaliser.PolyExpr.var 1
  let y := RingNormaliser.PolyExpr.var 2
  let z := RingNormaliser.PolyExpr.var 3
  .mul n
    (.add
      (.mul (.const 4) (.add x (.neg z)))
      (.neg (.mul (.const 7) (.add y (.neg z)))))

private theorem terminalSpan_normal :
    RingNormaliser.normalize terminalSpanL =
      RingNormaliser.normalize terminalSpanR := by decide

private theorem terminalSpan_eqv (n x y z : Q') :
    q4 * (((n + (-(q3 : Q'))) * x) + (-(n * y))) +
        q3 * (n * z + (-((n + (-(q4 : Q'))) * y))) +
        q12 * (x + (-y)) ≈
      n * (q4 * (x + (-z)) + (-(q7 * (y + (-z))))) := by
  simpa [terminalSpanL, terminalSpanR, RingNormaliser.eval,
    q3, q4, q7, q12,
    show Q'.ofInt 3 = Q'.ofNat 3 from rfl,
    show Q'.ofInt 4 = Q'.ofNat 4 from rfl,
    show Q'.ofInt 7 = Q'.ofNat 7 from rfl,
    show Q'.ofInt 12 = Q'.ofNat 12 from rfl] using
    (RingNormaliser.poly_identity_of_normal_eq
      terminalSpanL terminalSpanR terminalSpan_normal
      (fun | 0 => n | 1 => x | 2 => y | _ => z))

private theorem coeffW_zero_eqv (w : Q') : coeffW w 0 ≈ (1 : Q') := by
  change Q'.ofNat 1 * (1 : Q') ≈ (1 : Q')
  exact Q'.eqv_trans _ (Q'.ofNat 1) _ (Q'.mul_one_eqv _)
    (by decide)

private theorem coeffW_one_eqv (w : Q') :
    coeffW w 1 ≈ q2 * qpow w 3 := by
  change Q'.ofNat 2 * qpow w 3 ≈ q2 * qpow w 3
  exact Q'.eqv_refl _

private theorem coeffW_two_eqv (w : Q') :
    coeffW w 2 ≈ q3 * qpow w 8 := by
  change Q'.ofNat 3 * qpow w 8 ≈ q3 * qpow w 8
  exact Q'.eqv_refl _

private theorem physical_c1_lower (r : Nat) :
    (1 : Q') <= coeffW (blockWeight (r + 8)) 1 := by
  let w := blockWeight (r + 8)
  have hpow : qpow q127 3 <= qpow w 3 :=
    qpow_mono (by decide) (physicalWeight_ge_127 r) 3
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q2 hpow (by decide)
  have hconst : (1 : Q') <= q2 * qpow q127 3 := by decide
  exact Q'.le_trans' _ _ _ hconst
    (Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv (coeffW_one_eqv w)))

private theorem physical_c1_upper (r : Nat) :
    coeffW (blockWeight (r + 8)) 1 <= q2 := by
  let w := blockWeight (r + 8)
  have hpow : qpow w 3 <= (1 : Q') :=
    qpow_le_one (blockWeight_nonneg (r + 8))
      (blockWeight_le_one (r + 8)) 3
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q2 hpow (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coeffW_one_eqv w))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_one_eqv q2)))

private theorem physical_c2_lower (r : Nat) :
    q11e4 <= coeffW (blockWeight (r + 8)) 2 := by
  let w := blockWeight (r + 8)
  have hpow : qpow q127 8 <= qpow w 8 :=
    qpow_mono (by decide) (physicalWeight_ge_127 r) 8
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ q3 hpow (by decide)
  have hconst : q11e4 <= q3 * qpow q127 8 := by decide
  exact Q'.le_trans' _ _ _ hconst
    (Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv (coeffW_two_eqv w)))

/-- The physical heat string has the mild successor cap consumed by the
broad-peak stencil, uniformly in both the cutoff and the interior index. -/
theorem physical_coeff_successor_cap (r s : Nat) (hs : 1 <= s) :
    q2 * coeffW (blockWeight (r + 8)) (s + 1) <=
      q3 * coeffW (blockWeight (r + 8)) s := by
  let w := blockWeight (r + 8)
  have hp : qpow w (2 * s + 3) <= (1 : Q') :=
    qpow_le_one (blockWeight_nonneg (r + 8))
      (blockWeight_le_one (r + 8)) (2 * s + 3)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (s + 2)) hp
      (HeatKernelRGStep.zero_le_ofNat (s + 2))
  have hnat : Q'.ofNat (s + 2) <= q3e2 * Q'.ofNat (s + 1) := by
    show
      (Q'.ofNat (s + 2)).num *
          ((q3e2 * Q'.ofNat (s + 1)).den : Int) <=
        (q3e2 * Q'.ofNat (s + 1)).num *
          ((Q'.ofNat (s + 2)).den : Int)
    unfold q3e2
    simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
      Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one]
    push_cast
    exact_mod_cast (show (s + 2) * 2 <= 3 * (s + 1) by omega)
  have hcross :
      Q'.ofNat (s + 2) * qpow w (2 * s + 3) <=
        q3e2 * Q'.ofNat (s + 1) :=
    Q'.le_trans' _ _ _ hscale
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hnat)
  have hsucc := coeffW_succ_le_of_cross (w := w) (R := q3e2) s
    (blockWeight_nonneg (r + 8)) hcross
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ q2 hsucc (by decide)
  have hright : q2 * (q3e2 * coeffW w s) ≈
      q3 * coeffW w s := by
    unfold q2 q3 q3e2
    ring_qeqv
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)

/-- The first non-vacuum pair is already on the high increasing side of the
broad-peak split. -/
theorem physical_first_interior_high (r : Nat) :
    q4 * coeffW (blockWeight (r + 8)) 1 <=
      q3 * coeffW (blockWeight (r + 8)) 2 := by
  let w := blockWeight (r + 8)
  have hu := Q'.mul_le_mul_of_nonneg_left _ _ q4
    (physical_c1_upper r) (by decide)
  have hc : q4 * q2 <= q3 * q11e4 := by decide
  have hl := Q'.mul_le_mul_of_nonneg_left _ _ q3
    (physical_c2_lower r) (by decide)
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _ hc hl)

/-- The unique first adjacent edge is paid by the first distance-two edge. -/
theorem physical_first_endpoint_stencil (r : Nat) :
    q3 * dirichletTerm
        (coeffW (blockWeight (r + 8)) 0)
        (coeffW (blockWeight (r + 8)) 1) <=
      dirichletTerm
        (coeffW (blockWeight (r + 8)) 0)
        (coeffW (blockWeight (r + 8)) 2) := by
  let w := blockWeight (r + 8)
  let c0 := coeffW w 0
  let c1 := coeffW w 1
  let c2 := coeffW w 2
  have h0 : c0 ≈ (1 : Q') := coeffW_zero_eqv w
  have h1lo : (1 : Q') <= c1 := physical_c1_lower r
  have h1up : c1 <= q2 := physical_c1_upper r
  have h2lo : q11e4 <= c2 := physical_c2_lower r
  have hxy : c0 <= c1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv h0) h1lo
  have hxz : c0 <= c2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv h0)
      (Q'.le_trans' _ _ _ (by decide : (1 : Q') <= q11e4) h2lo)
  have hupper := Q'.add_le_add_right _ _ (-c0) h1up
  have hupperScaled := Q'.mul_le_mul_of_nonneg_left _ _ q7e4 hupper
    (by decide)
  have htwoSub : q2 + (-c0) ≈ (1 : Q') := by
    refine Q'.eqv_trans _ (q2 + (-(1 : Q'))) _ ?_ (by decide)
    exact Q'.add_eqv_congr_left q2 _ _ (Q'.neg_eqv_congr _ _ h0)
  have hupperEnd : q7e4 * (q2 + (-c0)) ≈ q7e4 :=
    Q'.eqv_trans _ (q7e4 * (1 : Q')) _
      (Q'.mul_eqv_congr_left q7e4 _ _ htwoSub) (Q'.mul_one_eqv q7e4)
  have hlower := Q'.add_le_add_right _ _ (-c0) h2lo
  have helevenSub : q11e4 + (-c0) ≈ q7e4 := by
    refine Q'.eqv_trans _ (q11e4 + (-(1 : Q'))) _ ?_ (by decide)
    exact Q'.add_eqv_congr_left q11e4 _ _ (Q'.neg_eqv_congr _ _ h0)
  have hspan : q7e4 * (c1 + (-c0)) <= c2 + (-c0) :=
    Q'.le_trans' _ _ _ hupperScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hupperEnd)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv helevenSub) hlower))
  simpa only [w, c0, c1, c2] using
    (forward_endpoint_stencil hxy hxz hspan)

/-- The exceptional first interior edge needs only the right reverse
curvature; the left `s=0` reverse bound is neither assumed nor true. -/
theorem physical_first_interior_stencil (r : Nat) :
    q3 * dirichletTerm
        (coeffW (blockWeight (r + 8)) 1)
        (coeffW (blockWeight (r + 8)) 2) <=
      dirichletTerm
          (coeffW (blockWeight (r + 8)) 0)
          (coeffW (blockWeight (r + 8)) 2) +
        dirichletTerm
          (coeffW (blockWeight (r + 8)) 1)
          (coeffW (blockWeight (r + 8)) 3) := by
  let w := blockWeight (r + 8)
  have hhigh := physical_first_interior_high r
  have hyz : coeffW w 1 <= coeffW w 2 := by
    have h3y : q3 * coeffW w 1 <= q4 * coeffW w 1 :=
      Q'.mul_le_mul_of_nonneg_right _ _ (coeffW w 1)
        (by decide) (coeffW_nonneg (blockWeight_nonneg (r + 8)) 1)
    have hscaled := Q'.le_trans' _ _ _ h3y hhigh
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)
  exact broadPeak_increasing_high_stencil
    (coeffW_nonneg (blockWeight_nonneg (r + 8)) 0)
    (YMGap.Continuum.FusionResidualBound.coeffW_pos
      (blockWeight_pos (r + 8)) 1)
    (YMGap.Continuum.FusionResidualBound.coeffW_pos
      (blockWeight_pos (r + 8)) 2)
    hyz hhigh
    (coeffW_logConcave (blockWeight_nonneg (r + 8))
      (blockWeight_le_one (r + 8)) 0)
    (physical_coeff_reverse_curvature r 1 (by decide))
    (physical_coeff_successor_cap r 1 (by decide))

/-- Every later interior edge is discharged by the uniform broad stencil. -/
theorem physical_interior_stencil (r i : Nat) (hi : 1 <= i) :
    q3 * dirichletTerm
        (coeffW (blockWeight (r + 8)) (i + 1))
        (coeffW (blockWeight (r + 8)) (i + 2)) <=
      dirichletTerm
          (coeffW (blockWeight (r + 8)) i)
          (coeffW (blockWeight (r + 8)) (i + 2)) +
        dirichletTerm
          (coeffW (blockWeight (r + 8)) (i + 1))
          (coeffW (blockWeight (r + 8)) (i + 3)) := by
  exact broadPeak_local_stencil
    (coeffW_nonneg (blockWeight_nonneg (r + 8)) i)
    (YMGap.Continuum.FusionResidualBound.coeffW_pos
      (blockWeight_pos (r + 8)) (i + 1))
    (YMGap.Continuum.FusionResidualBound.coeffW_pos
      (blockWeight_pos (r + 8)) (i + 2))
    (coeffW_nonneg (blockWeight_nonneg (r + 8)) (i + 3))
    (coeffW_logConcave (blockWeight_nonneg (r + 8))
      (blockWeight_le_one (r + 8)) i)
    (by
      simpa only [show i + 1 + 2 = i + 3 by omega,
        show i + 1 + 1 = i + 2 by omega] using
        coeffW_logConcave (blockWeight_nonneg (r + 8))
          (blockWeight_le_one (r + 8)) (i + 1))
    (physical_coeff_reverse_curvature r i hi)
    (by
      simpa only [show i + 1 + 1 = i + 2 by omega,
        show i + 1 + 2 = i + 3 by omega] using
        physical_coeff_reverse_curvature r (i + 1) (by omega))
    (physical_coeff_successor_cap r (i + 1) (by omega))

/-! ## Terminal schedule: two symbolic ratio bounds -/

/-- The pure polynomial inequality left after substituting
`25 D = 12 (N+1)^2` in the reciprocal-Bernoulli penultimate ratio. -/
theorem physical_penultimate_pure (r : Nat) :
    let N := blockNcut (r + 8)
    12 * (4 * N - 3) * (N + 1) * (N + 1) <=
      25 * (N - 3) * (N - 1) * (2 * N - 1) := by
  let N := blockNcut (r + 8)
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hplus : 1000 * (N + 1) <= 1001 * N := by omega
  have hminus3 : 997 * N <= 1000 * (N - 3) := by omega
  have hminus1 : 999 * N <= 1000 * (N - 1) := by omega
  have htwominus : 1999 * N <= 1000 * (2 * N - 1) := by omega
  have hfour : 4 * N - 3 <= 4 * N := by omega
  have hplusSq := Nat.mul_le_mul hplus hplus
  have hleft0 := Nat.mul_le_mul (Nat.mul_le_mul_left 12 hfour) hplusSq
  have hleft1 := Nat.mul_le_mul_left 1000 hleft0
  have hleft :
      (1000 * 1000 * 1000) *
          (12 * (4 * N - 3) * (N + 1) * (N + 1)) <=
        (1000 * 12 * 4 * 1001 * 1001) * (N * N * N) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hleft1
  have hright01 := Nat.mul_le_mul hminus3 hminus1
  have hright02 := Nat.mul_le_mul hright01 htwominus
  have hright0 := Nat.mul_le_mul_left 25 hright02
  have hright :
      (25 * 997 * 999 * 1999) * (N * N * N) <=
        (1000 * 1000 * 1000) *
          (25 * (N - 3) * (N - 1) * (2 * N - 1)) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hright0
  have hconst : 1000 * 12 * 4 * 1001 * 1001 <=
      25 * 997 * 999 * 1999 := by decide
  have hmiddle := Nat.mul_le_mul_right (N * N * N) hconst
  have hscaled := Nat.le_trans hleft (Nat.le_trans hmiddle hright)
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

/-- Cleared reciprocal-Bernoulli condition for the penultimate ratio. -/
theorem physical_penultimate_cleared (r : Nat) :
    let N := blockNcut (r + 8)
    let D := physicalWeightDen (r + 8)
    N * N * D <= (N - 3) * (N - 1) * (D + (2 * N - 1)) := by
  let N := blockNcut (r + 8)
  let D := physicalWeightDen (r + 8)
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hcoord := physicalWeightDen_cutoff_square (r + 8)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have hpure :
      12 * (4 * N - 3) * (N + 1) * (N + 1) <=
        25 * (N - 3) * (N - 1) * (2 * N - 1) := by
    simpa only [N] using physical_penultimate_pure r
  have hlossScaled :
      25 * ((4 * N - 3) * D) <=
        25 * ((N - 3) * (N - 1) * (2 * N - 1)) := by
    calc
      25 * ((4 * N - 3) * D) = (4 * N - 3) * (25 * D) := by ac_rfl
      _ = (4 * N - 3) * (12 * (N + 1) * (N + 1)) := by rw [hcoord]
      _ = 12 * (4 * N - 3) * (N + 1) * (N + 1) := by ac_rfl
      _ <= 25 * (N - 3) * (N - 1) * (2 * N - 1) := hpure
      _ = 25 * ((N - 3) * (N - 1) * (2 * N - 1)) := by ac_rfl
  have hloss :
      (4 * N - 3) * D <= (N - 3) * (N - 1) * (2 * N - 1) :=
    Nat.le_of_mul_le_mul_left hlossScaled (by decide)
  have hdec : N * N = (N - 3) * (N - 1) + (4 * N - 3) := by
    have hrepr : N = (N - 3) + 3 := by omega
    rw [hrepr]
    simp [Nat.add_mul, Nat.mul_add]
    omega
  calc
    N * N * D = ((N - 3) * (N - 1) + (4 * N - 3)) * D := by rw [hdec]
    _ = (N - 3) * (N - 1) * D + (4 * N - 3) * D := by
      rw [Nat.add_mul]
    _ <= (N - 3) * (N - 1) * D +
        (N - 3) * (N - 1) * (2 * N - 1) :=
      Nat.add_le_add_left hloss _
    _ = (N - 3) * (N - 1) * (D + (2 * N - 1)) := by
      rw [Nat.mul_add]

/-- Cleared lower-Bernoulli condition for the last ratio. -/
theorem physical_terminal_lower_cleared (r : Nat) :
    let N := blockNcut (r + 8)
    let D := physicalWeightDen (r + 8)
    (N + 1) * (2 * N + 1) <= 5 * D := by
  let N := blockNcut (r + 8)
  let D := physicalWeightDen (r + 8)
  have hcoord := physicalWeightDen_cutoff_square (r + 8)
  change 25 * D = 12 * (N + 1) * (N + 1) at hcoord
  have hlin : 25 * (2 * N + 1) <= 60 * (N + 1) := by omega
  have hmul := Nat.mul_le_mul_left (N + 1) hlin
  have hscaled : 25 * ((N + 1) * (2 * N + 1)) <= 25 * (5 * D) := by
    calc
      25 * ((N + 1) * (2 * N + 1)) =
          (N + 1) * (25 * (2 * N + 1)) := by ac_rfl
      _ <= (N + 1) * (60 * (N + 1)) := hmul
      _ = 5 * (12 * (N + 1) * (N + 1)) := by
        rw [show 60 = 5 * 12 by decide]
        ac_rfl
      _ = 5 * (25 * D) := by rw [hcoord]
      _ = 25 * (5 * D) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (by decide)

private theorem bernDen_cover_of_cleared (A B n D : Nat) (hD : 0 < D)
    (hcleared : A * D <= B * (D + n)) :
    Q'.ofNat A <=
      Q'.ofNat B * bernDen (Q'.mkPos 1 D hD) n := by
  show (Q'.ofNat A).num *
      ((Q'.ofNat B * bernDen (Q'.mkPos 1 D hD) n).den : Int) <=
    (Q'.ofNat B * bernDen (Q'.mkPos 1 D hD) n).num *
      (Q'.ofNat A).den
  unfold bernDen
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  exact_mod_cast hcleared

private theorem bernoulli_lower_cover_of_cleared
    (A B n D : Nat) (hD : 0 < D) (hnD : n <= D)
    (hcleared : A * D <= B * (D - n)) :
    Q'.ofNat A <=
      Q'.ofNat B *
        ((1 : Q') - Q'.ofNat n * Q'.mkPos 1 D hD) := by
  show (Q'.ofNat A).num *
      ((Q'.ofNat B *
        ((1 : Q') +
          (-(Q'.ofNat n * Q'.mkPos 1 D hD)))).den : Int) <=
    (Q'.ofNat B *
      ((1 : Q') +
        (-(Q'.ofNat n * Q'.mkPos 1 D hD)))).num *
      (Q'.ofNat A).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.add_num_cast, Q'.add_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Q'.neg_den, neg_num_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one]
  push_cast
  have hcasted : (A : Int) * (D : Int) <=
      (B : Int) * ((D - n : Nat) : Int) := by
    exact_mod_cast hcleared
  have hsub : ((D - n : Nat) : Int) = (D : Int) - (n : Int) := by
    omega
  rw [hsub] at hcasted
  exact hcasted

private theorem ofNat_mul_eqv_local (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show (Q'.ofNat (a * b)).num *
      ((Q'.ofNat a * Q'.ofNat b).den : Int) =
    (Q'.ofNat a * Q'.ofNat b).num * (Q'.ofNat (a * b)).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Int.mul_one]
  push_cast
  rfl

private theorem ofNat_sub_eqv_local (a b : Nat) (h : b <= a) :
    Q'.ofNat (a - b) ≈ Q'.ofNat a + (-(Q'.ofNat b)) := by
  show (Q'.ofNat (a - b)).num *
      ((Q'.ofNat a + (-(Q'.ofNat b))).den : Int) =
    (Q'.ofNat a + (-(Q'.ofNat b))).num * (Q'.ofNat (a - b)).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.neg_den, neg_num_cast, Int.mul_one]
  push_cast
  omega

/-- Reciprocal Bernoulli converts the schedule polynomial into the required
penultimate heat-power ratio. -/
theorem physical_penultimate_power_cross (r : Nat) :
    let N := blockNcut (r + 8)
    Q'.ofNat (N * N) *
        qpow (blockWeight (r + 8)) (2 * N - 1) <=
      Q'.ofNat ((N - 3) * (N - 1)) := by
  let k := r + 8
  let N := blockNcut k
  let D := physicalWeightDen k
  let u := blockMargin k
  let n := 2 * N - 1
  let A := N * N
  let B := (N - 3) * (N - 1)
  have hu0 : (0 : Q') <= u := blockMargin_nonneg k
  have hu1 : u <= (1 : Q') := blockMargin_le_one k
  have hw0 : (0 : Q') <= blockWeight k := blockWeight_nonneg k
  have hclosed : u ≈ Q'.mkPos 1 D (physicalWeightDen_pos k) := by
    simpa only [u, D] using blockMargin_eqv_closed k
  have hden : bernDen u n ≈
      bernDen (Q'.mkPos 1 D (physicalWeightDen_pos k)) n := by
    unfold bernDen
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hclosed)
  have hcoverClosed : Q'.ofNat A <=
      Q'.ofNat B * bernDen (Q'.mkPos 1 D (physicalWeightDen_pos k)) n :=
    bernDen_cover_of_cleared A B n D (physicalWeightDen_pos k) (by
      simpa only [k, N, D, n, A, B] using physical_penultimate_cleared r)
  have hcover : Q'.ofNat A <= Q'.ofNat B * bernDen u n :=
    Q'.le_trans' _ _ _ hcoverClosed
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat B) _ _ hden))
  have hbern : qpow (blockWeight k) n * bernDen u n <= (1 : Q') := by
    have h := oneSub_pow_mul_bernDen_le hu0 hu1 n
    have hweight : blockWeight k = oneSub u := rfl
    simpa only [hweight] using h
  have hcoverScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (blockWeight k) n) hcover (qpow_nonneg _ hw0 n)
  have hbernScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat B) hbern (HeatKernelRGStep.zero_le_ofNat B)
  have hleft : qpow (blockWeight k) n * Q'.ofNat A ≈
      Q'.ofNat A * qpow (blockWeight k) n := Q'.mul_comm_eqv _ _
  have hmiddle :
      qpow (blockWeight k) n * (Q'.ofNat B * bernDen u n) ≈
        Q'.ofNat B * (qpow (blockWeight k) n * bernDen u n) := by
    refine Q'.eqv_trans _
      ((qpow (blockWeight k) n * Q'.ofNat B) * bernDen u n) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat B * qpow (blockWeight k) n) * bernDen u n) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hright : Q'.ofNat B * (1 : Q') ≈ Q'.ofNat B :=
    Q'.mul_one_eqv _
  dsimp only [k, N, n, A, B] at hleft hmiddle hright hcoverScaled hbernScaled ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hcoverScaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle)
        (Q'.le_trans' _ _ _ hbernScaled (Q'.le_of_eqv hright))))

/-- Lower Bernoulli converts the physical schedule into the final heat-power
ratio from below. -/
theorem physical_terminal_lower_power_cross (r : Nat) :
    let N := blockNcut (r + 8)
    Q'.ofNat (N - 4) <=
      Q'.ofNat (N + 1) *
        qpow (blockWeight (r + 8)) (2 * N + 1) := by
  let k := r + 8
  let N := blockNcut k
  let D := physicalWeightDen k
  let n := 2 * N + 1
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hshape : (N + 1) * n <= 5 * D := by
    simpa only [k, N, D, n] using physical_terminal_lower_cleared r
  have hfive : 5 <= N + 1 := by omega
  have hfiveScaled := Nat.mul_le_mul_right n hfive
  have hnD : n <= D := by
    have h5n : 5 * n <= 5 * D := Nat.le_trans hfiveScaled hshape
    exact Nat.le_of_mul_le_mul_left h5n (by decide)
  have hsum : (N - 4) * D + (N + 1) * n <= (N + 1) * D := by
    have hadd := Nat.add_le_add_left hshape ((N - 4) * D)
    have hrepr : N + 1 = (N - 4) + 5 := by omega
    calc
      (N - 4) * D + (N + 1) * n
          <= (N - 4) * D + 5 * D := hadd
      _ = (N + 1) * D := by rw [hrepr, Nat.add_mul]
  have hcleared : (N - 4) * D <= (N + 1) * (D - n) := by
    have hsub := Nat.le_sub_of_add_le hsum
    rw [Nat.mul_sub_left_distrib]
    exact hsub
  have hcoverClosed : Q'.ofNat (N - 4) <=
      Q'.ofNat (N + 1) *
        ((1 : Q') - Q'.ofNat n *
          Q'.mkPos 1 D (physicalWeightDen_pos k)) :=
    bernoulli_lower_cover_of_cleared (N - 4) (N + 1) n D
      (physicalWeightDen_pos k) hnD hcleared
  have hmargin :
      ((1 : Q') - blockWeight k) ≈
        Q'.mkPos 1 D (physicalWeightDen_pos k) :=
    Q'.eqv_trans _ _ _ (one_sub_blockWeight_eqv_margin k)
      (blockMargin_eqv_closed k)
  have hcover : Q'.ofNat (N - 4) <=
      Q'.ofNat (N + 1) *
        ((1 : Q') - Q'.ofNat n * ((1 : Q') - blockWeight k)) := by
    have hinside :
        ((1 : Q') - Q'.ofNat n *
            Q'.mkPos 1 D (physicalWeightDen_pos k)) ≈
          ((1 : Q') - Q'.ofNat n * ((1 : Q') - blockWeight k)) := by
      exact Q'.add_eqv_congr_left 1 _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat n) _ _
            (Q'.eqv_symm hmargin)))
    exact Q'.le_trans' _ _ _ hcoverClosed
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat (N + 1)) _ _ hinside))
  have hbern := MovingCutoff.qpow_ge_bernoulli
    (blockWeight_nonneg k) (blockWeight_le_one k) n
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (N + 1)) hbern
    (HeatKernelRGStep.zero_le_ofNat (N + 1))
  exact Q'.le_trans' _ _ _ hcover hscaled

/-- The penultimate coefficient drops by at least `3/N` in cleared form. -/
theorem physical_penultimate_coeff_cross (r : Nat) :
    let N := blockNcut (r + 8)
    Q'.ofNat N *
        coeffW (blockWeight (r + 8)) (N - 1) <=
      Q'.ofNat (N - 3) *
        coeffW (blockWeight (r + 8)) (N - 2) := by
  let w := blockWeight (r + 8)
  let N := blockNcut (r + 8)
  let x := coeffW w (N - 2)
  let y := coeffW w (N - 1)
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hp := physical_penultimate_power_cross r
  have hcross := coeffW_succ_cross_eqv w (N - 2)
  have hcross' : Q'.ofNat (N - 1) * y ≈
      (Q'.ofNat N * qpow w (2 * N - 1)) * x := by
    simpa only [x, y, show N - 2 + 1 = N - 1 by omega,
      show N - 2 + 2 = N by omega,
      show 2 * (N - 2) + 3 = 2 * N - 1 by omega] using hcross
  have hcrossScaled := Q'.mul_eqv_congr_left (Q'.ofNat N) _ _ hcross'
  have hpScaled := Q'.mul_le_mul_of_nonneg_right _ _ x hp
    (coeffW_nonneg (blockWeight_nonneg (r + 8)) (N - 2))
  have hmiddle :
      Q'.ofNat N *
          ((Q'.ofNat N * qpow w (2 * N - 1)) * x) ≈
        (Q'.ofNat (N * N) * qpow w (2 * N - 1)) * x := by
    refine Q'.eqv_trans _
      (Q'.ofNat N * (Q'.ofNat N * qpow w (2 * N - 1)) * x) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat N * Q'.ofNat N) * qpow w (2 * N - 1) * x) _
      (Q'.mul_eqv_congr_right _ _ x
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) ?_
    exact Q'.mul_eqv_congr_right _ _ x
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm (ofNat_mul_eqv_local N N)))
  have hraw :
      Q'.ofNat N * (Q'.ofNat (N - 1) * y) <=
        Q'.ofNat ((N - 3) * (N - 1)) * x :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hcrossScaled)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle) hpScaled)
  have hleft : Q'.ofNat N * (Q'.ofNat (N - 1) * y) ≈
      Q'.ofNat (N - 1) * (Q'.ofNat N * y) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat N * Q'.ofNat (N - 1)) * y) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat (N - 1) * Q'.ofNat N) * y) _
      (Q'.mul_eqv_congr_right _ _ y (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hright : Q'.ofNat ((N - 3) * (N - 1)) * x ≈
      Q'.ofNat (N - 1) * (Q'.ofNat (N - 3) * x) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat (N - 3) * Q'.ofNat (N - 1)) * x) _
      (Q'.mul_eqv_congr_right _ _ x (ofNat_mul_eqv_local _ _)) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat (N - 1) * Q'.ofNat (N - 3)) * x) _
      (Q'.mul_eqv_congr_right _ _ x (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hcancel :
      Q'.ofNat (N - 1) * (Q'.ofNat N * y) <=
        Q'.ofNat (N - 1) * (Q'.ofNat (N - 3) * x) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright))
  exact Q'.le_of_mul_le_mul_left hcancel
    (by simpa only [show N - 1 = (N - 2) + 1 by omega] using
      Q'.ofNat_succ_pos (N - 2))

/-- The last coefficient retains at least the cleared `1-4/N` ratio. -/
theorem physical_terminal_coeff_lower_cross (r : Nat) :
    let N := blockNcut (r + 8)
    Q'.ofNat (N - 4) *
        coeffW (blockWeight (r + 8)) (N - 1) <=
      Q'.ofNat N *
        coeffW (blockWeight (r + 8)) N := by
  let w := blockWeight (r + 8)
  let N := blockNcut (r + 8)
  let y := coeffW w (N - 1)
  let z := coeffW w N
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hp := physical_terminal_lower_power_cross r
  have hpScaled := Q'.mul_le_mul_of_nonneg_right _ _ y hp
    (coeffW_nonneg (blockWeight_nonneg (r + 8)) (N - 1))
  have hcross := coeffW_succ_cross_eqv w (N - 1)
  have hcross' : Q'.ofNat N * z ≈
      (Q'.ofNat (N + 1) * qpow w (2 * N + 1)) * y := by
    simpa only [y, z, show N - 1 + 1 = N by omega,
      show N - 1 + 2 = N + 1 by omega,
      show 2 * (N - 1) + 3 = 2 * N + 1 by omega] using hcross
  exact Q'.le_trans' _ _ _ hpScaled (Q'.ge_of_eqv hcross')

/-- The two terminal coefficient ratios form a `7/4` backward span, so the
last adjacent edge is paid by its unique distance-two edge. -/
theorem physical_terminal_endpoint_stencil (r : Nat) :
    let N := blockNcut (r + 8)
    q3 * dirichletTerm
        (coeffW (blockWeight (r + 8)) (N - 1))
        (coeffW (blockWeight (r + 8)) N) <=
      dirichletTerm
        (coeffW (blockWeight (r + 8)) (N - 2))
        (coeffW (blockWeight (r + 8)) N) := by
  let w := blockWeight (r + 8)
  let N := blockNcut (r + 8)
  let n := Q'.ofNat N
  let x := coeffW w (N - 2)
  let y := coeffW w (N - 1)
  let z := coeffW w N
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hA : n * y <= Q'.ofNat (N - 3) * x := by
    simpa only [w, N, n, x, y] using physical_penultimate_coeff_cross r
  have hB : Q'.ofNat (N - 4) * y <= n * z := by
    simpa only [w, N, n, y, z] using physical_terminal_coeff_lower_cross r
  have hfactor : Q'.ofNat (N - 3) <= n := by
    show (Q'.ofNat (N - 3)).num * ((n).den : Int) <=
      n.num * (Q'.ofNat (N - 3)).den
    dsimp only [n]
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one]
    push_cast
    exact_mod_cast (Nat.sub_le N 3)
  have hfactorScaled := Q'.mul_le_mul_of_nonneg_right _ _ x hfactor
    (coeffW_nonneg (blockWeight_nonneg (r + 8)) (N - 2))
  have hnyx : n * y <= n * x :=
    Q'.le_trans' _ _ _ hA hfactorScaled
  have hnpos : (0 : Q') < n := by
    exact ofNat_pos_local (by omega)
  have hxy : y <= x := Q'.le_of_mul_le_mul_left hnyx hnpos
  have hzy : z <= y := by
    simpa only [w, N, y, z] using physical_terminal_coeff_descending r
  have hminus3 := ofNat_sub_eqv_local N 3 (by omega)
  have hminus4 := ofNat_sub_eqv_local N 4 (by omega)
  have hA' : n * y <= (n + (-(q3 : Q'))) * x := by
    have hre : Q'.ofNat (N - 3) * x ≈
        (n + (-(q3 : Q'))) * x := by
      exact Q'.mul_eqv_congr_right _ _ x (by
        simpa only [n, q3] using hminus3)
    exact Q'.le_trans' _ _ _ hA (Q'.le_of_eqv hre)
  have hB' : (n + (-(q4 : Q'))) * y <= n * z := by
    have hre : Q'.ofNat (N - 4) * y ≈
        (n + (-(q4 : Q'))) * y := by
      exact Q'.mul_eqv_congr_right _ _ y (by
        simpa only [n, q4] using hminus4)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hre) hB
  have hs1 : (0 : Q') <=
      (n + (-(q3 : Q'))) * x + (-(n * y)) :=
    Q'.sub_nonneg_of_le hA'
  have hs2 : (0 : Q') <=
      n * z + (-((n + (-(q4 : Q'))) * y)) :=
    Q'.sub_nonneg_of_le hB'
  have hs3 : (0 : Q') <= x + (-y) := Q'.sub_nonneg_of_le hxy
  have hsum : (0 : Q') <=
      q4 * (((n + (-(q3 : Q'))) * x) + (-(n * y))) +
        q3 * (n * z + (-((n + (-(q4 : Q'))) * y))) +
        q12 * (x + (-y)) :=
    Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hs1)
        (Q'.mul_nonneg _ _ (by decide) hs2))
      (Q'.mul_nonneg _ _ (by decide) hs3)
  have hscaled : (0 : Q') <=
      n * (q4 * (x + (-z)) + (-(q7 * (y + (-z))))) :=
    Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (terminalSpan_eqv n x y z))
  have hspanCleared : q7 * (y + (-z)) <= q4 * (x + (-z)) := by
    apply scaled_slack_cancel hnpos
    exact hscaled
  have hspan : q7e4 * (y + (-z)) <= x + (-z) :=
    span_seven_fourths hspanCleared
  have hzx : z <= x := Q'.le_trans' _ _ _ hzy hxy
  simpa only [w, N, x, y, z] using
    (backward_endpoint_stencil hzy hzx hspan)

/-! ## The physical all-cutoff head -/

/-- The four constant-cost local cells sum to the all-cutoff physical head
energy inequality.  The proof does not inspect any of the `N` coefficients. -/
theorem physical_head_energy (r : Nat) :
    let w := blockWeight (r + 8)
    let N := blockNcut (r + 8)
    q3 * dirichletEnergy w N <= q2 * headTwoStepEnergy w N := by
  let w := blockWeight (r + 8)
  let N := blockNcut (r + 8)
  let edge : Nat -> Q' := fun i =>
    dirichletTerm (coeffW w i) (coeffW w (i + 1))
  let jump : Nat -> Q' := fun i =>
    dirichletTerm (coeffW w i) (coeffW w (i + 2))
  let M := N - 2
  have hN : 1279 <= N := blockNcut_ge_1279 r
  have hdata : TwoStepLocalEnergyData edge jump M := {
    first := by
      simpa only [edge, jump, w] using physical_first_endpoint_stencil r
    middle := by
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simpa only [edge, jump, w] using physical_first_interior_stencil r
      · have hi1 : 1 <= i := Nat.one_le_iff_ne_zero.mpr hi0
        simpa only [edge, jump, w] using physical_interior_stencil r i hi1
    last := by
      simpa only [edge, jump, M, w,
        show N - 2 + 1 = N - 1 by omega,
        show N - 2 + 1 + 1 = N by omega,
        show N - 2 + 2 = N by omega] using
        physical_terminal_endpoint_stencil r
  }
  have hglobal := twoStepEnergy_of_localData hdata
  simpa only [edge, jump, M, dirichletEnergy, headTwoStepEnergy,
    show N - 2 + 2 = N by omega,
    show N - 2 + 1 = N - 1 by omega] using hglobal

/-- The checked energy and boundary certificates packaged for the abstract
Dirichlet head compiler. -/
def physical_head_dirichlet_data (r : Nat) :
    P2RetunedHeadDirichletData
      (blockNcut (r + 8)) (blockWeight (r + 8)) := {
  cutoff := Nat.le_trans (by decide) (blockNcut_ge_1279 r)
  energy := by simpa only using physical_head_energy r
  boundary := physical_head_boundary r
}

/-- The genuine physical sparse-parity box head at every open scale
`k = r+8`. -/
theorem physical_box_head (r : Nat) :
    dimQ 1 * SelfFusionLogConcave.boxSum
        (blockWeight (r + 8)) (blockNcut (r + 8)) 2 <=
      qpow (P2RetunedRatioCompiler.p2RetunedWeight
        (blockWeight (r + 8))) 5 *
        (dimQ 2 * SelfFusionLogConcave.boxSum
          (blockWeight (r + 8)) (blockNcut (r + 8)) 1) :=
  boxHead_of_dirichletData (physical_head_dirichlet_data r)

#print axioms physical_coeff_successor_cap
#print axioms physical_first_endpoint_stencil
#print axioms physical_first_interior_stencil
#print axioms physical_interior_stencil
#print axioms physical_terminal_endpoint_stencil
#print axioms physical_head_energy
#print axioms physical_head_dirichlet_data
#print axioms physical_box_head

end YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergyClose
