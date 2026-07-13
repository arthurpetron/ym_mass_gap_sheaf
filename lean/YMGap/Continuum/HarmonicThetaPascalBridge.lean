/-
# Harmonic theta residual in the Pascal coefficient carrier

This module gives public coefficient formulas for the cleared theta
residual and identifies them exactly with the reverse-tail carrier proved
positive in `ThetaResidualPascalTelescope`.  The terminal integer block is
then removed explicitly, matching the growing-head residual.
-/

import YMGap.Continuum.HarmonicThetaCumulativeResidual
import YMGap.Continuum.BernsteinMonomialReconstruction
import YMGap.Continuum.ThetaResidualPascalTelescope

namespace YMGap.Continuum.HarmonicThetaPascalBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.ThetaResidualPascalTelescope

local infix:50 " ≈ " => Q'.eqv

/-- Coefficient of `t^j` in
`t^e (1+t)^(D-e)`, using the Pascal-path binomial coefficient. -/
def thetaMonoBernCoeff (D e j : Nat) : Int :=
  if e ≤ j then Int.ofNat (PNPaths.choose (D - e) (j - e)) else 0

/-- Bernstein/Pascal coefficient of the integer block
`n² w^(2n²-2) (1+w)^3`. -/
def thetaDiagBernCoeff (D n j : Nat) : Int :=
  Int.ofNat (n * n) *
    (thetaMonoBernCoeff D (2 * n * n - 2) j +
      3 * thetaMonoBernCoeff D (2 * n * n - 1) j +
      3 * thetaMonoBernCoeff D (2 * n * n) j +
      thetaMonoBernCoeff D (2 * n * n + 1) j)

/-- Bernstein/Pascal coefficient of the half-integer block
`8n(n+1) w^(2n(n+1)-1)`. -/
def thetaOffBernCoeff (D n j : Nat) : Int :=
  Int.ofNat (8 * n * (n + 1)) *
    thetaMonoBernCoeff D (2 * n * (n + 1) - 1) j

/-- Public reverse-cumulative coefficient recursion for a tail beginning at
cell `n` and containing `c` off-diagonal cells. -/
def cumulativeThetaBernCoeff (D n j : Nat) : Nat → Int
  | 0 => thetaDiagBernCoeff D n j
  | c + 1 =>
      thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j +
        cumulativeThetaBernCoeff D (n + 1) j c

/-- Exact coefficient agreement with the Pascal telescope's public carrier.
This is definitional after exposing the identical local coefficient
formulas, and holds for every degree, start cell, coefficient, and length. -/
theorem cumulativeThetaBernCoeff_eq_reverseTailCoeff
    (D n j c : Nat) :
    cumulativeThetaBernCoeff D n j c =
      reverseTailCoeff D n j c := by
  induction c generalizing n with
  | zero => rfl
  | succ c ih =>
      simp only [cumulativeThetaBernCoeff, reverseTailCoeff, ih]
      rfl

/-- Coefficient of the growing-head residual with terminal integer cell `m`
removed from the common-cutoff residual. -/
def growingHeadThetaBernCoeff (D m j : Nat) : Int :=
  cumulativeThetaBernCoeff D 1 j (m - 1) - thetaDiagBernCoeff D m j

/-- Exact agreement of the growing-head coefficient with the public reverse
tail minus its terminal diagonal block. -/
theorem growingHeadThetaBernCoeff_eq_reverse_minus_terminal
    (D m j : Nat) :
    growingHeadThetaBernCoeff D m j =
      reverseTailCoeff D 1 j (m - 1) - thetaDiagBernCoeff D m j := by
  rw [growingHeadThetaBernCoeff,
    cumulativeThetaBernCoeff_eq_reverseTailCoeff]

/-- At the minimal supported degree, the removed terminal block has no
coefficient at deficit four or later. -/
theorem terminal_diag_zero_from_deficit_four
    (m r : Nat) (hm : 2 ≤ m) (hr : 4 ≤ r) :
    thetaDiagBernCoeff (2 * m * m + 1) m
      ((2 * m * m + 1) - r) = 0 := by
  have hsq : 4 ≤ m * m := Nat.mul_le_mul hm hm
  have hbase : 4 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hsq
    exact Nat.le_trans (by decide : 4 ≤ 8) (by
      simpa only [Nat.mul_assoc, Nat.mul_one] using h)
  have h0 : ¬ 2 * m * m - 2 ≤ (2 * m * m + 1) - r := by omega
  have h1 : ¬ 2 * m * m - 1 ≤ (2 * m * m + 1) - r := by omega
  have h2 : ¬ 2 * m * m ≤ (2 * m * m + 1) - r := by omega
  have h3 : ¬ 2 * m * m + 1 ≤ (2 * m * m + 1) - r := by omega
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, h0, h1, h2, h3]

private theorem terminal_diag_deficit_zero (m : Nat) (hm : 1 ≤ m) :
    thetaDiagBernCoeff (2 * m * m + 1) m (2 * m * m + 1) =
      8 * (m : Int) * (m : Int) := by
  have hmm : 1 ≤ m * m := Nat.mul_pos hm hm
  have hprod : 2 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hmm
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have ha : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  have hb : 2 * m * m + 1 - (2 * m * m - 1) = 2 := by omega
  have h0 : 2 * m * m - 2 ≤ 2 * m * m + 1 := by omega
  have h1 : 2 * m * m - 1 ≤ 2 * m * m + 1 := by omega
  have h2 : 2 * m * m ≤ 2 * m * m + 1 := by omega
  have h3 : 2 * m * m + 1 ≤ 2 * m * m + 1 := Nat.le_refl _
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, h0, h1, h2,
    PNPaths.choose]
  rw [ha, hb]
  simp [PNPaths.choose] <;> ac_rfl

private theorem terminal_diag_deficit_one (m : Nat) (hm : 1 ≤ m) :
    thetaDiagBernCoeff (2 * m * m + 1) m (2 * m * m) =
      12 * (m : Int) * (m : Int) := by
  have hmm : 1 ≤ m * m := Nat.mul_pos hm hm
  have hprod : 2 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hmm
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have ha : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  have ha' : 2 * m * m - (2 * m * m - 2) = 2 := by omega
  have hb : 2 * m * m + 1 - (2 * m * m - 1) = 2 := by omega
  have hb' : 2 * m * m - (2 * m * m - 1) = 1 := by omega
  have h0 : 2 * m * m - 2 ≤ 2 * m * m := by omega
  have h1 : 2 * m * m - 1 ≤ 2 * m * m := by omega
  have h2 : 2 * m * m ≤ 2 * m * m := Nat.le_refl _
  have h3 : ¬ 2 * m * m + 1 ≤ 2 * m * m := by omega
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, h0, h1, h3,
    PNPaths.choose]
  rw [ha, ha', hb, hb']
  simp [PNPaths.choose] <;> ac_rfl

private theorem terminal_diag_deficit_two (m : Nat) (hm : 1 ≤ m) :
    thetaDiagBernCoeff (2 * m * m + 1) m (2 * m * m - 1) =
      6 * (m : Int) * (m : Int) := by
  have hmm : 1 ≤ m * m := Nat.mul_pos hm hm
  have hprod : 2 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hmm
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have ha : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  have ha' : 2 * m * m - 1 - (2 * m * m - 2) = 1 := by omega
  have h0 : 2 * m * m - 2 ≤ 2 * m * m - 1 := by omega
  have h1 : 2 * m * m - 1 ≤ 2 * m * m - 1 := Nat.le_refl _
  have h2 : ¬ 2 * m * m ≤ 2 * m * m - 1 := by omega
  have h3 : ¬ 2 * m * m + 1 ≤ 2 * m * m - 1 := by omega
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, h0, h2, h3,
    PNPaths.choose]
  rw [ha, ha']
  simp [PNPaths.choose] <;> ac_rfl

private theorem terminal_diag_deficit_three (m : Nat) (hm : 1 ≤ m) :
    thetaDiagBernCoeff (2 * m * m + 1) m (2 * m * m - 2) =
      (m : Int) * (m : Int) := by
  have hmm : 1 ≤ m * m := Nat.mul_pos hm hm
  have hprod : 2 ≤ 2 * m * m := by
    have h := Nat.mul_le_mul_left 2 hmm
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have h0 : 2 * m * m - 2 ≤ 2 * m * m - 2 := Nat.le_refl _
  have h1 : ¬ 2 * m * m - 1 ≤ 2 * m * m - 2 := by omega
  have h2 : ¬ 2 * m * m ≤ 2 * m * m - 2 := by omega
  have h3 : ¬ 2 * m * m + 1 ≤ 2 * m * m - 2 := by omega
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, h1, h2, h3,
    PNPaths.choose]

private theorem growing_head_top_algebra (x : Int) :
    4 * (2 * x + (x - 1) * x) - 8 * x * x =
      -(4 * x * (x - 1)) := by
  simp only [Int.mul_add, Int.add_mul,
    Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg, Int.neg_add,
    Int.neg_neg]
  simp only [Int.one_mul, Int.mul_one]
  have hlin : 4 * (2 * x) = 4 * x + 4 * x := by
    rw [show 2 * x = x + x by omega, Int.mul_add]
  have hquad : 8 * x * x = 4 * x * x + 4 * x * x := by
    rw [show (8 : Int) = 4 + 4 by decide, Int.add_mul, Int.add_mul]
  rw [hlin, hquad]
  simp only [Int.mul_assoc]
  omega

/-! The four exceptional top coordinates are not separately nonnegative.
On the harmonic projective ray their Bernstein weights occur in the ratio
`t³ : t² : t : 1`.  The following small constructive normaliser bridge is
used only to certify the resulting exact integer polynomial identity. -/

private def bridgeIntPow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => bridgeIntPow x n * x

private def bridgeIntEval (rho : Nat → Int) :
    RingNormaliser.PolyExpr → Int
  | .const c => c
  | .var i => rho i
  | .add x y => bridgeIntEval rho x + bridgeIntEval rho y
  | .mul x y => bridgeIntEval rho x * bridgeIntEval rho y
  | .neg x => -(bridgeIntEval rho x)
  | .pow x n => bridgeIntPow (bridgeIntEval rho x) n

private theorem bridge_ofInt_neg (x : Int) :
    (-(Q'.ofInt x)).eqv (Q'.ofInt (-x)) := by
  rfl

private theorem bridge_qpow_ofInt (x : Int) : ∀ n,
    (RingNormaliser.qpow (Q'.ofInt x) n).eqv
      (Q'.ofInt (bridgeIntPow x n))
  | 0 => by exact Q'.eqv_refl _
  | n + 1 => by
      exact Q'.eqv_trans _ (Q'.ofInt (bridgeIntPow x n) * Q'.ofInt x) _
        (Q'.mul_eqv_congr_right _ _ _ (bridge_qpow_ofInt x n))
        (Q'.eqv_symm (RingNormaliser.ofInt_mul (bridgeIntPow x n) x))

private theorem bridge_eval_ofInt (rho : Nat → Int) : ∀ e,
    (RingNormaliser.eval (fun i => Q'.ofInt (rho i)) e).eqv
      (Q'.ofInt (bridgeIntEval rho e))
  | .const _ => Q'.eqv_refl _
  | .var _ => Q'.eqv_refl _
  | .add x y => by
      exact Q'.eqv_trans _
        (Q'.ofInt (bridgeIntEval rho x) +
          RingNormaliser.eval (fun i => Q'.ofInt (rho i)) y) _
        (Q'.add_eqv_congr_right _ _ _ (bridge_eval_ofInt rho x))
        (Q'.eqv_trans _
          (Q'.ofInt (bridgeIntEval rho x) + Q'.ofInt (bridgeIntEval rho y)) _
          (Q'.add_eqv_congr_left _ _ _ (bridge_eval_ofInt rho y))
          (Q'.eqv_symm (RingNormaliser.ofInt_add _ _)))
  | .mul x y => by
      exact Q'.eqv_trans _
        (Q'.ofInt (bridgeIntEval rho x) *
          RingNormaliser.eval (fun i => Q'.ofInt (rho i)) y) _
        (Q'.mul_eqv_congr_right _ _ _ (bridge_eval_ofInt rho x))
        (Q'.eqv_trans _
          (Q'.ofInt (bridgeIntEval rho x) * Q'.ofInt (bridgeIntEval rho y)) _
          (Q'.mul_eqv_congr_left _ _ _ (bridge_eval_ofInt rho y))
          (Q'.eqv_symm (RingNormaliser.ofInt_mul _ _)))
  | .neg x => by
      exact Q'.eqv_trans _ (-(Q'.ofInt (bridgeIntEval rho x))) _
        (Q'.neg_eqv_congr _ _ (bridge_eval_ofInt rho x))
        (bridge_ofInt_neg _)
  | .pow x n => by
      exact Q'.eqv_trans _
        (RingNormaliser.qpow (Q'.ofInt (bridgeIntEval rho x)) n) _
        (RingNormaliser.qpow_eqv_congr (bridge_eval_ofInt rho x) n)
        (bridge_qpow_ofInt _ n)

private theorem bridge_int_poly_identity
    (e₁ e₂ : RingNormaliser.PolyExpr)
    (hn : RingNormaliser.normalize e₁ = RingNormaliser.normalize e₂)
    (rho : Nat → Int) : bridgeIntEval rho e₁ = bridgeIntEval rho e₂ := by
  have h := RingNormaliser.poly_identity_of_normal_eq e₁ e₂ hn
    (fun i => Q'.ofInt (rho i))
  have hl := bridge_eval_ofInt rho e₁
  have hr := bridge_eval_ofInt rho e₂
  have hi := Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ h hr)
  unfold Q'.eqv at hi
  change bridgeIntEval rho e₁ * 1 = bridgeIntEval rho e₂ * 1 at hi
  simpa using hi

private def bridgeAdd (x y : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .add x y
private def bridgeMul (x y : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .mul x y
private def bridgeNeg (x : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := .neg x
private def bridgeSub (x y : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := bridgeAdd x (bridgeNeg y)
private def bridgeConst (z : Int) : RingNormaliser.PolyExpr := .const z
private def bridgeScale (z : Int) (x : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr := bridgeMul (bridgeConst z) x

private def harmonicBoundaryLHS : RingNormaliser.PolyExpr :=
  let t := RingNormaliser.PolyExpr.var 0
  let m := bridgeAdd (bridgeScale 2 t) (bridgeConst 4)
  let h₀ := bridgeNeg (bridgeScale 4 (bridgeMul m (bridgeSub m (bridgeConst 1))))
  let h₁ := bridgeSub
    (bridgeNeg (bridgeScale 2
      (bridgeMul (bridgeMul m (bridgeAdd m (bridgeConst 1)))
        (bridgeSub (bridgeScale 2 m) (bridgeConst 5)))))
    (bridgeScale 12 (.pow m 2))
  let h₂ := bridgeSub
    (bridgeNeg (bridgeScale 3
      (bridgeMul (bridgeMul m (bridgeAdd m (bridgeConst 1)))
        (bridgeSub (bridgeScale 2 m) (bridgeConst 3)))))
    (bridgeScale 6 (.pow m 2))
  let h₃scaled := bridgeSub
    (bridgeMul (bridgeMul m (bridgeAdd m (bridgeConst 1)))
      (bridgeAdd (bridgeScale 96 (.pow m 3))
        (bridgeAdd (bridgeScale (-96) (.pow m 2))
          (bridgeAdd (bridgeScale (-94) m) (bridgeConst 109)))))
    (bridgeScale 30 (.pow m 2))
  bridgeAdd (bridgeScale 30 (bridgeMul h₀ (.pow t 3)))
    (bridgeAdd (bridgeScale 30 (bridgeMul h₁ (.pow t 2)))
      (bridgeAdd (bridgeScale 30 (bridgeMul h₂ t)) h₃scaled))

private def harmonicBoundaryRHS : RingNormaliser.PolyExpr :=
  let t := RingNormaliser.PolyExpr.var 0
  let m := bridgeAdd (bridgeScale 2 t) (bridgeConst 4)
  bridgeMul (bridgeMul m (bridgeSub m (bridgeConst 1)))
    (bridgeAdd (bridgeScale 51 (.pow m 3))
      (bridgeAdd (bridgeScale 351 (.pow m 2))
        (bridgeAdd (bridgeScale (-469) m) (bridgeConst 191))))

private theorem harmonicBoundary_normal :
    RingNormaliser.normalize harmonicBoundaryLHS =
      RingNormaliser.normalize harmonicBoundaryRHS := by
  decide

private theorem harmonic_boundary_algebra (t : Int) :
    let m := 2 * t + 4
    30 * (-(4 * m * (m - 1))) * (t * t * t) +
      30 * (-(2 * m * (m + 1) * (2 * m - 5)) - 12 * m * m) *
        (t * t) +
      30 * (-(3 * m * (m + 1) * (2 * m - 3)) - 6 * m * m) * t +
      (m * (m + 1) * (96 * (m * m * m) - 96 * (m * m) - 94 * m + 109) -
        30 * (m * m)) =
      m * (m - 1) * (51 * (m * m * m) + 351 * (m * m) - 469 * m + 191) := by
  have h := bridge_int_poly_identity harmonicBoundaryLHS harmonicBoundaryRHS
    harmonicBoundary_normal (fun _ => t)
  dsimp [harmonicBoundaryLHS, harmonicBoundaryRHS, bridgeAdd, bridgeMul,
    bridgeNeg, bridgeSub, bridgeConst, bridgeScale, bridgeIntEval,
    bridgeIntPow] at h
  simp only [Int.sub_eq_add_neg] at h ⊢
  simpa only [Int.one_mul, Int.mul_assoc, Int.add_assoc, Int.neg_mul]
    using h

private theorem bridge_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

private theorem bridge_ofInt_num_cast (z : Int) :
    (Q'.ofInt z).num = z := rfl

private theorem bridge_ofInt_den_cast (z : Int) :
    ((Q'.ofInt z).den : Int) = 1 := rfl

private theorem bridge_one_den_cast : (((1 : Q').den : Int)) = 1 := rfl

local macro "bridge_ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, bridge_neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

local macro "bridge_integer_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, bridge_neg_num_cast,
               bridge_ofInt_num_cast, bridge_ofInt_den_cast,
               bridge_one_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.natCast_one,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Exact leading coefficient of the growing-head carrier.  It is negative;
therefore coefficientwise positivity is impossible and the four boundary
coordinates must be evaluated together on the harmonic ray. -/
theorem growing_head_deficit_zero (m : Nat) (hm : 1 ≤ m) :
    growingHeadThetaBernCoeff (2 * m * m + 1) m (2 * m * m + 1) =
      -(4 * (m : Int) * ((m : Int) - 1)) := by
  rw [growingHeadThetaBernCoeff_eq_reverse_minus_terminal]
  have hend : 1 + (m - 1) = m := by omega
  have hD : 2 * (1 + (m - 1)) * (1 + (m - 1)) + 1 ≤
      2 * m * m + 1 := by
    rw [hend]
    exact Nat.le_refl _
  rw [reverseTailCoeff_top (2 * m * m + 1) 1 (m - 1) hD]
  rw [terminal_diag_deficit_zero m hm]
  unfold reverseTopFluxNat
  rw [hend]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
  have hmcast : (((m - 1 : Nat) : Int)) = (m : Int) - 1 := by omega
  rw [hmcast]
  have h1 : ((1 : Nat) : Int) = (1 : Int) := rfl
  have h2 : ((2 : Nat) : Int) = (2 : Int) := rfl
  have h4 : ((4 : Nat) : Int) = (4 : Int) := rfl
  rw [h1, h2, h4]
  have hback : (m : Int) - 1 + 1 = (m : Int) := by omega
  rw [hback]
  exact growing_head_top_algebra (m : Int)

/-- Exact deficit-one coefficient after removing the terminal integer
block. -/
theorem growing_head_deficit_one (m : Nat) (hm : 1 ≤ m) :
    growingHeadThetaBernCoeff (2 * m * m + 1) m (2 * m * m) =
      -(2 * (m : Int) * ((m : Int) + 1) * (2 * (m : Int) - 5)) -
        12 * (m : Int) * (m : Int) := by
  rw [growingHeadThetaBernCoeff_eq_reverse_minus_terminal]
  rw [minimalBase_deficit_one m (by omega)]
  rw [terminal_diag_deficit_one m hm]

/-- Exact deficit-two coefficient after removing the terminal integer
block. -/
theorem growing_head_deficit_two (m : Nat) (hm : 1 ≤ m) :
    growingHeadThetaBernCoeff (2 * m * m + 1) m (2 * m * m - 1) =
      -(3 * (m : Int) * ((m : Int) + 1) * (2 * (m : Int) - 3)) -
        6 * (m : Int) * (m : Int) := by
  rw [growingHeadThetaBernCoeff_eq_reverse_minus_terminal]
  rw [minimalBase_deficit_two m (by omega)]
  rw [terminal_diag_deficit_two m hm]

/-- Division-free exact deficit-three coefficient after removing the
terminal integer block. -/
theorem growing_head_deficit_three_scaled (m : Nat) (hm : 1 ≤ m) :
    30 * growingHeadThetaBernCoeff (2 * m * m + 1) m
        (2 * m * m - 2) =
      (m : Int) * ((m : Int) + 1) *
          (96 * ((m : Int) * (m : Int) * (m : Int)) -
            96 * ((m : Int) * (m : Int)) - 94 * (m : Int) + 109) -
        30 * ((m : Int) * (m : Int)) := by
  rw [growingHeadThetaBernCoeff_eq_reverse_minus_terminal]
  rw [Int.mul_sub]
  rw [minimalBase_deficit_three_mul m (by omega)]
  rw [terminal_diag_deficit_three m hm]

/-- Thirty times the four-coordinate boundary evaluation.  These are the
deficits `0,1,2,3`, with their exact harmonic projective weights
`t³,t²,t,1`.  The factor `30` clears the deficit-three formula. -/
def growingHeadBoundary30 (m t : Nat) : Int :=
  30 * growingHeadThetaBernCoeff (2 * m * m + 1) m
      (2 * m * m + 1) * ((t : Int) * (t : Int) * (t : Int)) +
    30 * growingHeadThetaBernCoeff (2 * m * m + 1) m
      (2 * m * m) * ((t : Int) * (t : Int)) +
    30 * growingHeadThetaBernCoeff (2 * m * m + 1) m
      (2 * m * m - 1) * (t : Int) +
    30 * growingHeadThetaBernCoeff (2 * m * m + 1) m
      (2 * m * m - 2)

/-- The unscaled four-coordinate boundary bracket over `Q'`. -/
def growingHeadBoundaryBracketQ (m t : Nat) : Q' :=
  let D := 2 * m * m + 1
  let x := Q'.ofNat t
  Q'.ofInt (growingHeadThetaBernCoeff D m D) * x ^ 3 +
    (Q'.ofInt (growingHeadThetaBernCoeff D m (D - 1)) * x ^ 2 +
      (Q'.ofInt (growingHeadThetaBernCoeff D m (D - 2)) * x +
        Q'.ofInt (growingHeadThetaBernCoeff D m (D - 3))))

/-- A generic four-coordinate projective bracket. -/
def projectiveBoundaryBracket (D : Nat) (c : Nat → Int) (x : Q') : Q' :=
  Q'.ofInt (c D) * x ^ 3 +
    (Q'.ofInt (c (D - 1)) * x ^ 2 +
      (Q'.ofInt (c (D - 2)) * x + Q'.ofInt (c (D - 3))))

/-- The first four projective coordinates factor out their common lowest
power.  This is the exact reason the integer weights are `t³,t²,t,1`. -/
theorem projectiveBoundaryFour_eqv_factor
    (D : Nat) (c : Nat → Int) (x : Q') (hD : 3 ≤ D) :
    projectiveBoundaryFour D c x ≈
      x ^ (D - 3) * projectiveBoundaryBracket D c x := by
  have h0n : D = (D - 3) + 3 := by omega
  have h1n : D - 1 = (D - 3) + 2 := by omega
  have h2n : D - 2 = (D - 3) + 1 := by omega
  have h0 : x ^ D ≈ x ^ (D - 3) * x ^ 3 := by
    rw [h0n]
    exact Q'.pow_add_eqv x (D - 3) 3
  have h1 : x ^ (D - 1) ≈ x ^ (D - 3) * x ^ 2 := by
    rw [h1n]
    exact Q'.pow_add_eqv x (D - 3) 2
  have h2 : x ^ (D - 2) ≈ x ^ (D - 3) * x := by
    rw [h2n]
    refine Q'.eqv_trans _ _ _ (Q'.pow_add_eqv x (D - 3) 1) ?_
    exact Q'.mul_eqv_congr_left (x ^ (D - 3)) _ _
      (Q'.mul_one_eqv x)
  unfold projectiveBoundaryFour
  simp only [finSum_succ, finSum_zero, Nat.sub_zero, Q'.zero_add']
  refine Q'.eqv_trans _
    (((Q'.ofInt (c D) * (x ^ (D - 3) * x ^ 3) +
      Q'.ofInt (c (D - 1)) * (x ^ (D - 3) * x ^ 2)) +
      Q'.ofInt (c (D - 2)) * (x ^ (D - 3) * x)) +
      Q'.ofInt (c (D - 3)) * x ^ (D - 3)) _ ?_ ?_
  · refine Q'.add_eqv_congr' (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ h0)
        (Q'.mul_eqv_congr_left _ _ _ h1))
      (Q'.mul_eqv_congr_left _ _ _ h2)) (Q'.eqv_refl _)
  · unfold projectiveBoundaryBracket
    bridge_ring_qeqv

private theorem scaled_growing_boundary_bracket_eqv (m t : Nat) :
    Q'.ofNat 30 * growingHeadBoundaryBracketQ m t ≈
      Q'.ofInt (growingHeadBoundary30 m t) := by
  have h1 : 2 * m * m + 1 - 1 = 2 * m * m := by omega
  have h2 : 2 * m * m + 1 - 2 = 2 * m * m - 1 := by omega
  have h3 : 2 * m * m + 1 - 3 = 2 * m * m - 2 := by omega
  dsimp only [growingHeadBoundaryBracketQ, growingHeadBoundary30]
  rw [h1, h2, h3]
  simp only [Q'.pow_succ, Q'.pow_zero]
  bridge_integer_qeqv

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

private theorem ofNat_nonnegative (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg, Q'.ofNat_num_cast]
  exact Int.natCast_nonneg n

private theorem growing_boundary_bracket_nonnegative
    (m t : Nat) (hboundary : (0 : Int) ≤ growingHeadBoundary30 m t) :
    (0 : Q') ≤ growingHeadBoundaryBracketQ m t := by
  have hscaled :
      (0 : Q') ≤ Q'.ofNat 30 * growingHeadBoundaryBracketQ m t :=
    Q'.le_trans' _ _ _ (ofInt_nonnegative hboundary)
      (Q'.ge_of_eqv (scaled_growing_boundary_bracket_eqv m t))
  have hmul :
      Q'.ofNat 30 * (0 : Q') ≤
        Q'.ofNat 30 * growingHeadBoundaryBracketQ m t :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 30)))
      hscaled
  exact Q'.le_of_mul_le_mul_left hmul (Q'.ofNat_succ_pos 29)

/-- Exact harmonic-ray payment identity for all four exceptional boundary
coordinates.  Although the leading coefficient is negative, their weighted
sum factors into a manifestly positive polynomial. -/
theorem growing_head_boundary30_harmonic_identity (t : Nat) :
    growingHeadBoundary30 (2 * t + 4) t =
      (2 * (t : Int) + 4) * (2 * (t : Int) + 4 - 1) *
        (51 * ((2 * (t : Int) + 4) * (2 * (t : Int) + 4) *
            (2 * (t : Int) + 4)) +
          351 * ((2 * (t : Int) + 4) * (2 * (t : Int) + 4)) -
          469 * (2 * (t : Int) + 4) + 191) := by
  have hm : 1 ≤ 2 * t + 4 := by omega
  unfold growingHeadBoundary30
  rw [growing_head_deficit_zero (2 * t + 4) hm]
  rw [growing_head_deficit_one (2 * t + 4) hm]
  rw [growing_head_deficit_two (2 * t + 4) hm]
  rw [growing_head_deficit_three_scaled (2 * t + 4) hm]
  have hcast : (((2 * t + 4 : Nat) : Int)) = 2 * (t : Int) + 4 := by
    omega
  rw [hcast]
  exact harmonic_boundary_algebra (t : Int)

/-- The complete exceptional boundary band is nonnegative on every point
of the harmonic ray. -/
theorem growing_head_boundary30_harmonic_nonnegative (t : Nat) :
    (0 : Int) ≤ growingHeadBoundary30 (2 * t + 4) t := by
  rw [growing_head_boundary30_harmonic_identity]
  let m : Int := 2 * (t : Int) + 4
  have hm0 : (0 : Int) ≤ m := by
    dsimp [m]
    have ht : (0 : Int) ≤ (t : Int) := Int.natCast_nonneg t
    omega
  have hm1 : (0 : Int) ≤ m - 1 := by
    dsimp [m]
    have ht : (0 : Int) ≤ (t : Int) := Int.natCast_nonneg t
    omega
  have hlin : (0 : Int) ≤ 351 * m - 469 := by
    dsimp [m]
    have ht : (0 : Int) ≤ (t : Int) := Int.natCast_nonneg t
    omega
  have hcube : (0 : Int) ≤ m * m * m :=
    Int.mul_nonneg (Int.mul_nonneg hm0 hm0) hm0
  have hweightedCube : (0 : Int) ≤ 51 * (m * m * m) :=
    Int.mul_nonneg (by decide) hcube
  have hlinearPayment : (0 : Int) ≤ m * (351 * m - 469) :=
    Int.mul_nonneg hm0 hlin
  have hpolyEq :
      51 * (m * m * m) + 351 * (m * m) - 469 * m + 191 =
        51 * (m * m * m) + m * (351 * m - 469) + 191 := by
    rw [Int.mul_sub]
    simp only [Int.sub_eq_add_neg]
    ac_rfl
  have hpoly :
      (0 : Int) ≤ 51 * (m * m * m) + 351 * (m * m) - 469 * m + 191 := by
    rw [hpolyEq]
    exact Int.add_nonneg
      (Int.add_nonneg hweightedCube hlinearPayment) (by decide)
  change (0 : Int) ≤ m * (m - 1) *
    (51 * (m * m * m) + 351 * (m * m) - 469 * m + 191)
  exact Int.mul_nonneg (Int.mul_nonneg hm0 hm1) hpoly

/-- The closed Pascal bulk theorem transfers verbatim to every growing-head
coefficient at deficit at least four. -/
theorem growing_head_bulk_coefficient_nonnegative
    (m r : Nat) (hm : 2 ≤ m) (hr : 4 ≤ r)
    (hrD : r ≤ 2 * m * m + 1) :
    (0 : Int) ≤ growingHeadThetaBernCoeff (2 * m * m + 1) m
      ((2 * m * m + 1) - r) := by
  rw [growingHeadThetaBernCoeff_eq_reverse_minus_terminal]
  rw [terminal_diag_zero_from_deficit_four m r hm hr]
  simp only [Int.sub_zero]
  exact minimalBase_bulk_nonnegative m r hm hr hrD

/-- Complete nonnegativity of the projective growing-head polynomial on the
harmonic ray.  The four mixed-sign top coordinates are paid by
`growing_head_boundary30_harmonic_nonnegative`; every later coordinate is
covered coefficientwise by the closed Pascal bulk theorem. -/
theorem growing_head_projective_deficit_nonnegative (t : Nat) :
    let m := 2 * t + 4
    let D := 2 * m * m + 1
    (0 : Q') ≤ projectiveDeficitEval D
      (growingHeadThetaBernCoeff D m) (Q'.ofNat t) := by
  let m := 2 * t + 4
  let D := 2 * m * m + 1
  have hm : 2 ≤ m := by
    dsimp [m]
    omega
  have hD : 3 ≤ D := by
    dsimp [D]
    have hmm : 4 ≤ m * m := Nat.mul_le_mul hm hm
    have htwice : 8 ≤ 2 * m * m := by
      have h := Nat.mul_le_mul_left 2 hmm
      simpa only [Nat.mul_assoc] using h
    omega
  have ht : (0 : Q') ≤ Q'.ofNat t := ofNat_nonnegative t
  have hbracket : (0 : Q') ≤ growingHeadBoundaryBracketQ m t := by
    apply growing_boundary_bracket_nonnegative
    dsimp [m]
    exact growing_head_boundary30_harmonic_nonnegative t
  have hbracketEq :
      projectiveBoundaryBracket D (growingHeadThetaBernCoeff D m)
          (Q'.ofNat t) = growingHeadBoundaryBracketQ m t := by
    rfl
  have hfactor := projectiveBoundaryFour_eqv_factor D
    (growingHeadThetaBernCoeff D m) (Q'.ofNat t) hD
  have hboundaryProduct :
      (0 : Q') ≤ (Q'.ofNat t) ^ (D - 3) *
        projectiveBoundaryBracket D (growingHeadThetaBernCoeff D m)
          (Q'.ofNat t) := by
    rw [hbracketEq]
    exact Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ht (D - 3)) hbracket
  have hboundary :
      (0 : Q') ≤ projectiveBoundaryFour D
        (growingHeadThetaBernCoeff D m) (Q'.ofNat t) :=
    Q'.le_trans' _ _ _ hboundaryProduct (Q'.ge_of_eqv hfactor)
  exact projectiveDeficitEval_nonnegative_of_boundary_bulk D
    (growingHeadThetaBernCoeff D m) (Q'.ofNat t) hD ht hboundary
    (fun r hr hrD => by
      dsimp [D]
      exact growing_head_bulk_coefficient_nonnegative m r hm hr (by
        simpa [D] using hrD))

/-- Schedule-facing specialization: the removed terminal integer cell is
exactly two units beyond the retained growing anchor, and the projective
coordinate is `k+1`. -/
theorem growing_head_projective_deficit_schedule_nonnegative (k : Nat) :
    let m := growingAnchor k + 2
    let D := 2 * m * m + 1
    (0 : Q') ≤ projectiveDeficitEval D
      (growingHeadThetaBernCoeff D m) (Q'.ofNat (k + 1)) := by
  simpa [growingAnchor, Nat.mul_add, Nat.add_assoc] using
    (growing_head_projective_deficit_nonnegative (k + 1))

#print axioms cumulativeThetaBernCoeff_eq_reverseTailCoeff
#print axioms growingHeadThetaBernCoeff_eq_reverse_minus_terminal
#print axioms terminal_diag_zero_from_deficit_four
#print axioms growing_head_deficit_zero
#print axioms growing_head_deficit_one
#print axioms growing_head_deficit_two
#print axioms growing_head_deficit_three_scaled
#print axioms growing_head_boundary30_harmonic_identity
#print axioms growing_head_boundary30_harmonic_nonnegative
#print axioms growing_head_bulk_coefficient_nonnegative
#print axioms projectiveBoundaryFour_eqv_factor
#print axioms growing_head_projective_deficit_nonnegative
#print axioms growing_head_projective_deficit_schedule_nonnegative

end YMGap.Continuum.HarmonicThetaPascalBridge
