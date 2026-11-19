/-
# Robust3 width-2 electric form bound → fineAt at step 2

Additive.  Hypothesis structure `Width2Model` (not an axiom).  Authorised live
adaptation of certificate MM to `width2_model.md` L3: `ℓ := B(Ω,·)` with
`κ := 1 - ρ`, so vac-kill on `VacuumComplement` is free (`y.property`).

Numeric certificates use `179221/100000` (not `17923/10000`).  `etaR3 2 = 1/64`,
`r3Nome 3 = 14/25`.  Mathlib-free; no `sorry`/`omega`/`simpa`/`native_decide`.
Not chart closure / not gap evidence.
-/

import YMGap.RG.Robust3CrossUniform
import YMGap.RG.Robust3UndershootCrossoverInstance
import YMGap.RG.Robust3UndershootAfSchedule
import YMGap.RG.DyadicCrossoverSchedule
import YMGap.RG.Robust3SchurRankOne
import YMGap.RG.CoarseConstantZero
import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
import YMGap.Continuum.BF4WilsonAllNomeLinear
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
import YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen
import YMGap.Continuum.ReconstructionCapstone
import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
import YMGap.Constructive.Geometric
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.Sqrt
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.QPoly

namespace YMGap.RG.Robust3Width2Electric

set_option autoImplicit false
set_option maxRecDepth 16384

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Constructive.QPoly (q_add_zero_eqv)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule r3Nome)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3)
open YMGap.RG.DyadicCrossoverSchedule (dyTable)
open YMGap.RG.Robust3CrossUniform (fineAt)
open YMGap.RG.Robust3SchurRankOne (SchurBudget)
open YMGap.RG.CoarseConstantZero (schurBudget_fine_zero)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner completedInner_nonnegative completedInner_symm Completion unitState
    unitState_norm_one)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (VacuumComplement completedTime completedTime_add completedTime_preserves_vacuumComplement
    completedInner_oneStep_nonnegative completedInner_time_sum completedInner_time_balance
    completedUnit_fixed)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_add_left completedInner_add_right completedInner_smul_left
    completedInner_smul_right completedTime_additive completedTime_smul)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (WilsonVacuumSqFactor WilsonVacuumSqTwoStepFactor vacuumSq_implies_twoStepFactor
    wilsonVacuumSq_of_factor)
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity (completedInner_cauchySchwarz)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (oneStep_cauchySchwarz)
-- RCscale_mono_scalar / RCscale_mono / RCscale_RCzero / RCscale_RCscale live in
-- YMGap.Constructive.CReal (exported by ReconstructionCapstone / RCScaleClose /
-- BoundedTransferCalculus imports above).
-- Cancel / mono lemmas are in YMGap.Constructive.CReal via OperatorNormGap.

/-! ## Schedule pins -/

theorem etaR3_two : etaR3 2 = Q'.mkPos 1 64 (by decide) := rfl

theorem r3Nome_three : r3Nome 3 = Q'.mkPos 14 25 (by decide) := by
  unfold r3Nome
  have h : (3 : Nat) < 6 := by decide
  simp only [h, ↓reduceIte, dyTable]

/-! ## Series -/

def termF (w : Q') (s : Nat) : Q' :=
  (Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * w ^ (s * (s + 2))

def partialF (w : Q') : Nat → Q'
  | 0 => termF w 0
  | N + 1 => partialF w N + termF w (N + 1)

def tailFrom (w : Q') (N : Nat) : Nat → Q'
  | 0 => termF w N
  | k + 1 => tailFrom w N k + termF w (N + (k + 1))

def tailPartial (w : Q') (N M : Nat) : Q' :=
  if _h : N ≤ M then tailFrom w N (M - N) else 0

def geomSum (q : Q') : Nat → Q'
  | 0 => 1
  | k + 1 => 1 + q * geomSum q k

def wStep2 : Q' := Q'.mkPos 14 25 (by decide)
def fOneBound : Q' := Q'.mkPos 179221 100000 (by decide)
def pad40 : Q' := Q'.mkPos 1 (10 ^ 40) (by decide)
def rhoBound : Q' := Q'.mkPos 316 10000 (by decide)
def qGeom : Q' := Q'.mkPos 1 1000000 (by decide)
def geomCap : Q' := Q'.mkPos 1000000 999999 (by decide)

theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int) * 1 ≤ Int.ofNat n * 1
  exact Int.mul_le_mul_of_nonneg_right (Int.natCast_nonneg n) (by decide)

theorem ofNat_pos {n : Nat} (h : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int) * 1 < Int.ofNat n * 1
  exact Int.mul_lt_mul_of_pos_right (Int.natCast_pos.mpr h) (by decide)

theorem wStep2_nonneg : (0 : Q') ≤ wStep2 := by
  change (0 : Int) * 25 ≤ (14 : Int) * 1; decide

theorem wStep2_pos : (0 : Q') < wStep2 := by
  change (0 : Int) * 25 < (14 : Int) * 1; decide

theorem termF_nonneg (s : Nat) : (0 : Q') ≤ termF wStep2 s :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (ofNat_nonneg _) (ofNat_nonneg _))
    (Q'.pow_nonneg wStep2 wStep2_nonneg _)

theorem qGeom_nonneg : (0 : Q') ≤ qGeom := by
  change (0 : Int) * 1000000 ≤ (1 : Int) * 1; decide

theorem ofNat_mul_eq (n m : Nat) : Q'.ofNat (n * m) = Q'.ofNat n * Q'.ofNat m := rfl

private theorem eqv_of_eq' {a b : Q'} (h : a = b) : a.eqv b := by
  subst h; exact Q'.eqv_refl a

/-! ### Closed numeric facts -/

theorem fOne_cert : partialF wStep2 11 + pad40 ≤ fOneBound := by decide

theorem termF_twelve_le_pad : termF wStep2 12 ≤ pad40 := by decide

theorem termF_ratio_at_twelve :
    termF wStep2 13 ≤ termF wStep2 12 * qGeom := by decide

theorem term12_geomCap_le_pad :
    termF wStep2 12 * geomCap ≤ pad40 := by decide

theorem geomCap_closed :
    (1 : Q') + qGeom * geomCap ≤ geomCap ∧ geomCap ≤ (1 : Q') + qGeom * geomCap := by
  decide

theorem rho_cert :
    ((wStep2 ^ 3) ^ 4) * (fOneBound ^ 6) ≤ rhoBound := by decide

theorem rho4_cert : rhoBound ^ 4 ≤ Q'.mkPos 1 64 (by decide) := by decide

theorem f12_raw_le_qGeom :
    Q'.ofNat (14 * 14) * wStep2 ^ 27 ≤ qGeom * Q'.ofNat (13 * 13) := by
  decide

theorem geomSum_zero_le_cap : geomSum qGeom 0 ≤ geomCap := by decide

/-! ### Linear antitone `14(s+3) ≤ 25(s+2)` -/

private theorem linear_anti_id (s : Nat) :
    14 * (s + 3) + (11 * s + 8) = 25 * (s + 2) := by
  have e14 : 14 * (s + 3) = 14 * s + 42 := by
    rw [Nat.mul_add, show 14 * 3 = 42 from rfl]
  have e25 : 25 * (s + 2) = 25 * s + 50 := by
    rw [Nat.mul_add, show 25 * 2 = 50 from rfl]
  rw [e14, e25]
  have h1 : 14 * s + 11 * s = 25 * s := (Nat.add_mul 14 11 s).symm
  rw [Nat.add_assoc (14 * s) 42 (11 * s + 8)]
  rw [← Nat.add_assoc 42 (11 * s) 8]
  rw [Nat.add_comm 42 (11 * s)]
  rw [← Nat.add_assoc (11 * s) 42 8]
  rw [← Nat.add_assoc (14 * s) (11 * s) (42 + 8)]
  rw [h1, show (42 + 8 = 50) from rfl]

theorem linear_anti (s : Nat) : 14 * (s + 3) ≤ 25 * (s + 2) :=
  Nat.le.intro (linear_anti_id s)

theorem linear_anti_sq (s : Nat) :
    (14 * (s + 3)) * (14 * (s + 3)) ≤ (25 * (s + 2)) * (25 * (s + 2)) :=
  Nat.mul_le_mul (linear_anti s) (linear_anti s)

/-! ### Exact ratio majorant and `termF_succ_ratio_le` -/

/-- Raw one-step factor `(s+2)^2 · w^(2s+3)`. -/
def exactRatioRaw (s : Nat) : Q' :=
  (Q'.ofNat (s + 2) * Q'.ofNat (s + 2)) * wStep2 ^ (2 * s + 3)

/-- `(s+3)^2 · w^2 ≤ (s+2)^2` at `w = 14/25`, from `linear_anti`. -/
theorem anti_w_sq (s : Nat) :
    Q'.ofNat ((s + 3) * (s + 3)) * (wStep2 * wStep2) ≤
      Q'.ofNat ((s + 2) * (s + 2)) := by
  have hsq := linear_anti_sq s
  have hw : wStep2 * wStep2 = Q'.mkPos 196 625 (by decide) := by decide
  rw [hw]
  have hL :
      (14 * (s + 3)) * (14 * (s + 3)) =
        ((s + 3) * (s + 3)) * 196 := by
    have e1 : (14 * (s + 3)) * (14 * (s + 3)) =
        14 * ((s + 3) * (14 * (s + 3))) := Nat.mul_assoc _ _ _
    have e2 : (s + 3) * (14 * (s + 3)) = 14 * ((s + 3) * (s + 3)) :=
      Nat.mul_left_comm (s + 3) 14 (s + 3)
    have e3 : 14 * (14 * ((s + 3) * (s + 3))) =
        (14 * 14) * ((s + 3) * (s + 3)) := (Nat.mul_assoc 14 14 _).symm
    calc (14 * (s + 3)) * (14 * (s + 3))
        = 14 * ((s + 3) * (14 * (s + 3))) := e1
      _ = 14 * (14 * ((s + 3) * (s + 3))) := by rw [e2]
      _ = (14 * 14) * ((s + 3) * (s + 3)) := e3
      _ = 196 * ((s + 3) * (s + 3)) := rfl
      _ = ((s + 3) * (s + 3)) * 196 := Nat.mul_comm _ _
  have hR :
      (25 * (s + 2)) * (25 * (s + 2)) =
        ((s + 2) * (s + 2)) * 625 := by
    have e1 : (25 * (s + 2)) * (25 * (s + 2)) =
        25 * ((s + 2) * (25 * (s + 2))) := Nat.mul_assoc _ _ _
    have e2 : (s + 2) * (25 * (s + 2)) = 25 * ((s + 2) * (s + 2)) :=
      Nat.mul_left_comm (s + 2) 25 (s + 2)
    have e3 : 25 * (25 * ((s + 2) * (s + 2))) =
        (25 * 25) * ((s + 2) * (s + 2)) := (Nat.mul_assoc 25 25 _).symm
    calc (25 * (s + 2)) * (25 * (s + 2))
        = 25 * ((s + 2) * (25 * (s + 2))) := e1
      _ = 25 * (25 * ((s + 2) * (s + 2))) := by rw [e2]
      _ = (25 * 25) * ((s + 2) * (s + 2)) := e3
      _ = 625 * ((s + 2) * (s + 2)) := rfl
      _ = ((s + 2) * (s + 2)) * 625 := Nat.mul_comm _ _
  have hN :
      ((s + 3) * (s + 3)) * 196 ≤ ((s + 2) * (s + 2)) * 625 := by
    rw [← hL, ← hR]; exact hsq
  change
    (Int.ofNat ((s + 3) * (s + 3)) * (196 : Int)) * (1 : Int) ≤
      Int.ofNat ((s + 2) * (s + 2)) * (625 : Int)
  rw [Int.mul_one]
  have hN' : (↑(((s + 3) * (s + 3)) * 196) : Int) ≤
      ↑(((s + 2) * (s + 2)) * 625) := Int.ofNat_le.mpr hN
  have eL : (↑(((s + 3) * (s + 3)) * 196) : Int) =
      Int.ofNat ((s + 3) * (s + 3)) * 196 := by
    rw [Int.natCast_mul]; rfl
  have eR : (↑(((s + 2) * (s + 2)) * 625) : Int) =
      Int.ofNat ((s + 2) * (s + 2)) * 625 := by
    rw [Int.natCast_mul]; rfl
  rw [← eL, ← eR]; exact hN'

/-- `q^n * (q*q) ≃ q^(n+2)`. -/
theorem pow_mul_sq_eqv (q : Q') (n : Nat) :
    (q ^ n * (q * q)).eqv (q ^ (n + 2)) := by
  have hsucc : q ^ (n + 2) = q * (q * q ^ n) := by
    rw [show n + 2 = Nat.succ (Nat.succ n) from rfl, Q'.pow_succ, Q'.pow_succ]
  refine Q'.eqv_trans _ _ _ ?_ (eqv_of_eq' hsucc.symm)
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (q ^ n) (q * q)) ?_
  exact Q'.mul_assoc_eqv q q (q ^ n)

private theorem exact_exp_step (s : Nat) :
    2 * (s + 1) + 3 = (2 * s + 3) + 2 := by
  -- 2*(s+1)+3 = 2*s+2+3 = 2*s+5 = 2*s+3+2
  have h1 : 2 * (s + 1) = 2 * s + 2 := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h1, Nat.add_assoc (2 * s) 2 3, show (2 + 3 = 5) from rfl,
    Nat.add_assoc (2 * s) 3 2, show (3 + 2 = 5) from rfl]

/-- `exactRatioRaw` is nonincreasing. -/
theorem exactRatioRaw_anti (s : Nat) :
    exactRatioRaw (s + 1) ≤ exactRatioRaw s := by
  unfold exactRatioRaw
  have hanti := anti_w_sq s
  have ofL : Q'.ofNat ((s + 3) * (s + 3)) =
      Q'.ofNat (s + 3) * Q'.ofNat (s + 3) := ofNat_mul_eq _ _
  have ofR : Q'.ofNat ((s + 2) * (s + 2)) =
      Q'.ofNat (s + 2) * Q'.ofNat (s + 2) := ofNat_mul_eq _ _
  -- Rewrite anti_w_sq into ofNat(s+3)*ofNat(s+3) form
  have hanti' :
      (Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) * (wStep2 * wStep2) ≤
        Q'.ofNat (s + 2) * Q'.ofNat (s + 2) := by
    rw [← ofL, ← ofR]; exact hanti
  have hwpow : (0 : Q') ≤ wStep2 ^ (2 * s + 3) :=
    Q'.pow_nonneg wStep2 wStep2_nonneg _
  have hmul :
      ((Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) * (wStep2 * wStep2)) *
          wStep2 ^ (2 * s + 3) ≤
        (Q'.ofNat (s + 2) * Q'.ofNat (s + 2)) * wStep2 ^ (2 * s + 3) :=
    Q'.mul_le_mul_of_nonneg_right
      ((Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) * (wStep2 * wStep2))
      (Q'.ofNat (s + 2) * Q'.ofNat (s + 2))
      (wStep2 ^ (2 * s + 3)) hanti' hwpow
  have hexp : 2 * (s + 1) + 3 = (2 * s + 3) + 2 := exact_exp_step s
  have hpow : (wStep2 ^ (2 * s + 3) * (wStep2 * wStep2)).eqv
      (wStep2 ^ (2 * (s + 1) + 3)) := by
    refine Q'.eqv_trans _ _ _ (pow_mul_sq_eqv wStep2 (2 * s + 3)) ?_
    exact eqv_of_eq' (congrArg (fun n => wStep2 ^ n) hexp)
  -- Reassociate: (a*(w*w))*w^n ≃ a*(w^n*(w*w)) ≃ a*w^(n+2)
  have hre :
      (((Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) * (wStep2 * wStep2)) *
          wStep2 ^ (2 * s + 3)).eqv
        ((Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) * wStep2 ^ (2 * (s + 1) + 3)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (s + 3) * Q'.ofNat (s + 3))
        (wStep2 * wStep2) (wStep2 ^ (2 * s + 3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) _ _
        (Q'.mul_comm_eqv (wStep2 * wStep2) (wStep2 ^ (2 * s + 3)))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat (s + 3) * Q'.ofNat (s + 3)) _ _ hpow
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hre) hmul


/-! ### Exponent / power algebra -/

theorem term_exp_step (s : Nat) :
    (s + 1) * (s + 3) = s * (s + 2) + (2 * s + 3) := by
  have h4 : 3 * s + s = 4 * s := by
    conv => lhs; rhs; rw [← Nat.one_mul s]
    rw [← Nat.add_mul 3 1 s]
  have h4' : 2 * s + 2 * s = 4 * s := by
    rw [← Nat.add_mul 2 2 s]
  -- LHS
  have a1 : (s + 1) * (s + 3) = s * (s + 3) + (s + 3) := by
    rw [show s + 1 = Nat.succ s from rfl, Nat.succ_mul]
  have a2 : s * (s + 3) = s * s + 3 * s := by
    rw [Nat.mul_add, Nat.mul_comm s 3]
  have a3 : s * (s + 3) + (s + 3) = (s * s + 3 * s) + (s + 3) := by rw [a2]
  have a4 : (s * s + 3 * s) + (s + 3) = (s * s + 3 * s) + s + 3 :=
    (Nat.add_assoc (s * s + 3 * s) s 3).symm
  have a5 : (s * s + 3 * s) + s = s * s + (3 * s + s) :=
    Nat.add_assoc (s * s) (3 * s) s
  have a6 : (s * s + 3 * s) + s + 3 = s * s + (3 * s + s) + 3 := by
    rw [a5]
  have a7 : s * s + (3 * s + s) + 3 = s * s + 4 * s + 3 := by rw [h4]
  have hL : (s + 1) * (s + 3) = s * s + 4 * s + 3 := by
    rw [a1, a3, a4, a6, a7]
  -- RHS
  have b1 : s * (s + 2) = s * s + 2 * s := by
    rw [Nat.mul_add, Nat.mul_comm s 2]
  have b2 : s * (s + 2) + (2 * s + 3) = (s * s + 2 * s) + (2 * s + 3) := by rw [b1]
  have b3 : (s * s + 2 * s) + (2 * s + 3) = (s * s + 2 * s) + 2 * s + 3 :=
    (Nat.add_assoc (s * s + 2 * s) (2 * s) 3).symm
  have b4 : (s * s + 2 * s) + 2 * s = s * s + (2 * s + 2 * s) :=
    Nat.add_assoc (s * s) (2 * s) (2 * s)
  have b5 : (s * s + 2 * s) + 2 * s + 3 = s * s + (2 * s + 2 * s) + 3 := by
    rw [b4]
  have b6 : s * s + (2 * s + 2 * s) + 3 = s * s + 4 * s + 3 := by rw [h4']
  have hR : s * (s + 2) + (2 * s + 3) = s * s + 4 * s + 3 := by
    rw [b2, b3, b5, b6]
  rw [hL, hR]


/-! ### Exponent / power algebra (continued) -/

/-- Power additivity up to `eqv`. -/
theorem pow_add_eqv (q : Q') (m n : Nat) :
    (q ^ (m + n)).eqv (q ^ m * q ^ n) := by
  induction n with
  | zero =>
    have e1 : q ^ (m + 0) = q ^ m := by rw [Nat.add_zero]
    refine Q'.eqv_trans _ _ _ (eqv_of_eq' e1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv (q ^ m))) ?_
    exact Q'.mul_eqv_congr_left (q ^ m) _ _
      (Q'.eqv_symm (eqv_of_eq' (Q'.pow_zero q)))
  | succ k ih =>
    have eadd : m + Nat.succ k = Nat.succ (m + k) := Nat.add_succ m k
    refine Q'.eqv_trans _ _ _ (eqv_of_eq' (by rw [eadd, Q'.pow_succ])) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ ih) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q (q ^ m) (q ^ k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (q ^ k) (Q'.mul_comm_eqv q (q ^ m))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (q ^ m) q (q ^ k)) ?_
    exact Q'.mul_eqv_congr_left (q ^ m) _ _
      (eqv_of_eq' (Q'.pow_succ q k).symm)

/-! ### Ratio majorant to geometric tail -/

theorem exactRatioRaw_twelve_le :
    exactRatioRaw 12 ≤ qGeom * Q'.ofNat (13 * 13) := by
  unfold exactRatioRaw
  have e1 : Q'.ofNat (12 + 2) * Q'.ofNat (12 + 2) = Q'.ofNat (14 * 14) :=
    (ofNat_mul_eq 14 14).symm
  have e2 : (2 * 12 + 3 : Nat) = 27 := rfl
  rw [e1, e2]
  exact f12_raw_le_qGeom

private theorem exactRatioRaw_le_twelve_offset (k : Nat) :
    exactRatioRaw (12 + k) ≤ exactRatioRaw 12 := by
  induction k with
  | zero => exact Q'.le_refl' _
  | succ k ih =>
    exact Q'.le_trans' _ _ _ (exactRatioRaw_anti (12 + k)) ih

theorem exactRatioRaw_le_twelve {s : Nat} (hs : 12 ≤ s) :
    exactRatioRaw s ≤ exactRatioRaw 12 := by
  have e : s = 12 + (s - 12) := (Nat.add_sub_of_le hs).symm
  rw [e]; exact exactRatioRaw_le_twelve_offset (s - 12)

theorem exactRatioRaw_le_qGeom_sq {s : Nat} (hs : 12 ≤ s) :
    exactRatioRaw s ≤ qGeom * (Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) := by
  have h12 : exactRatioRaw s ≤ qGeom * Q'.ofNat (13 * 13) :=
    Q'.le_trans' _ _ _ (exactRatioRaw_le_twelve hs) exactRatioRaw_twelve_le
  have hsq : Q'.ofNat (13 * 13) ≤ Q'.ofNat (s + 1) * Q'.ofNat (s + 1) := by
    have hnat : 13 * 13 ≤ (s + 1) * (s + 1) :=
      Nat.mul_le_mul (Nat.succ_le_succ hs) (Nat.succ_le_succ hs)
    have e : Q'.ofNat ((s + 1) * (s + 1)) =
        Q'.ofNat (s + 1) * Q'.ofNat (s + 1) := ofNat_mul_eq _ _
    rw [← e]
    change (Int.ofNat (13 * 13)) * 1 ≤ Int.ofNat ((s + 1) * (s + 1)) * 1
    exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hnat) (by decide)
  exact Q'.le_trans' _ _ _ h12
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq qGeom_nonneg)

private theorem add_eqv_congr_both {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') : (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem add_le_add {a b c d : Q'} (h1 : a ≤ c) (h2 : b ≤ d) :
    a + b ≤ c + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a c b h1) (Q'.add_le_add_left c b d h2)

/-- Link exactRatioRaw to consecutive termF values. -/
theorem termF_exact_ratio_link (s : Nat) :
    (exactRatioRaw s * termF wStep2 s).eqv
      ((Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * termF wStep2 (s + 1)) := by
  -- Expand definitions manually to control indices
  change
    (((Q'.ofNat (s + 2) * Q'.ofNat (s + 2)) * wStep2 ^ (2 * s + 3)) *
        ((Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * wStep2 ^ (s * (s + 2)))).eqv
      ((Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) *
        ((Q'.ofNat (s + 2) * Q'.ofNat (s + 2)) *
          wStep2 ^ ((s + 1) * (s + 3))))
  have hexp := term_exp_step s
  have hpow : (wStep2 ^ ((s + 1) * (s + 3))).eqv
      (wStep2 ^ (s * (s + 2)) * wStep2 ^ (2 * s + 3)) := by
    refine Q'.eqv_trans _ _ _
      (eqv_of_eq' (congrArg (fun n => wStep2 ^ n) hexp)) ?_
    exact pow_add_eqv wStep2 (s * (s + 2)) (2 * s + 3)
  -- Intermediate: b * (a * (v * u))
  let a : Q' := Q'.ofNat (s + 2) * Q'.ofNat (s + 2)
  let b : Q' := Q'.ofNat (s + 1) * Q'.ofNat (s + 1)
  let u : Q' := wStep2 ^ (2 * s + 3)
  let v : Q' := wStep2 ^ (s * (s + 2))
  have lhs : ((a * u) * (b * v)).eqv (b * (a * (v * u))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a u (b * v)) ?_
    have hu : (u * (b * v)).eqv (b * (u * v)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv u b v)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (u * b) (b * u) v (Q'.mul_comm_eqv u b)) ?_
      exact Q'.mul_assoc_eqv b u v
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a (u * (b * v)) (b * (u * v)) hu) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b (u * v))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (a * b) (b * a) (u * v) (Q'.mul_comm_eqv a b)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv b a (u * v)) ?_
    exact Q'.mul_eqv_congr_left b (a * (u * v)) (a * (v * u))
      (Q'.mul_eqv_congr_left a (u * v) (v * u) (Q'.mul_comm_eqv u v))
  have rhs : (b * (a * wStep2 ^ ((s + 1) * (s + 3)))).eqv (b * (a * (v * u))) :=
    Q'.mul_eqv_congr_left b _ _
      (Q'.mul_eqv_congr_left a _ _ hpow)
  exact Q'.eqv_trans _ _ _ lhs (Q'.eqv_symm rhs)

theorem termF_succ_ratio_le {s : Nat} (hs : 12 ≤ s) :
    termF wStep2 (s + 1) ≤ termF wStep2 s * qGeom := by
  have hlink := termF_exact_ratio_link s
  have hrat := exactRatioRaw_le_qGeom_sq hs
  have hterm := termF_nonneg s
  have h1 :
      exactRatioRaw s * termF wStep2 s ≤
        (qGeom * (Q'.ofNat (s + 1) * Q'.ofNat (s + 1))) * termF wStep2 s :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hrat hterm
  have h2 :
      (Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * termF wStep2 (s + 1) ≤
        (qGeom * (Q'.ofNat (s + 1) * Q'.ofNat (s + 1))) * termF wStep2 s :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlink) h1
  have hre :
      ((qGeom * (Q'.ofNat (s + 1) * Q'.ofNat (s + 1))) * termF wStep2 s).eqv
        ((Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * (termF wStep2 s * qGeom)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv qGeom (Q'.ofNat (s + 1) * Q'.ofNat (s + 1))
        (termF wStep2 s)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left qGeom _ _
        (Q'.mul_comm_eqv (Q'.ofNat (s + 1) * Q'.ofNat (s + 1))
          (termF wStep2 s))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv qGeom (termF wStep2 s)
        (Q'.ofNat (s + 1) * Q'.ofNat (s + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv qGeom (termF wStep2 s))) ?_
    exact Q'.mul_comm_eqv (termF wStep2 s * qGeom)
      (Q'.ofNat (s + 1) * Q'.ofNat (s + 1))
  have h3 :
      (Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * termF wStep2 (s + 1) ≤
        (Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * (termF wStep2 s * qGeom) :=
    Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hre)
  have hpos : (0 : Q') < Q'.ofNat (s + 1) * Q'.ofNat (s + 1) :=
    Q'.mul_pos (ofNat_pos (Nat.succ_pos _)) (ofNat_pos (Nat.succ_pos _))
  exact Q'.le_of_mul_le_mul_left h3 hpos

theorem geomSum_succ_split (k : Nat) :
    (geomSum qGeom k + qGeom ^ (k + 1)).eqv (1 + qGeom * geomSum qGeom k) := by
  induction k with
  | zero =>
    have e1 : geomSum qGeom 0 = (1 : Q') := rfl
    have ep : (qGeom ^ (0 + 1)).eqv qGeom := by
      refine eqv_of_eq' ?_
      rw [show (0 + 1 = Nat.succ 0) from rfl, Q'.pow_succ, Q'.pow_zero]
      -- qGeom * 1 = qGeom may need eqv; try decide/rfl on structure
      rfl
    refine add_eqv_congr_both (eqv_of_eq' e1) ?_
    refine Q'.eqv_trans _ _ _ ep ?_
    exact Q'.eqv_symm (Q'.mul_one_eqv qGeom)
  | succ k ih =>
    have e_succ : geomSum qGeom (k + 1) = 1 + qGeom * geomSum qGeom k := rfl
    have epow : (qGeom ^ (k + 1 + 1)).eqv (qGeom * qGeom ^ (k + 1)) := by
      exact eqv_of_eq' (by
        rw [show k + 1 + 1 = Nat.succ (k + 1) from rfl, Q'.pow_succ])
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_both (eqv_of_eq' e_succ) epow) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv 1 (qGeom * geomSum qGeom k)
        (qGeom * qGeom ^ (k + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ _
        (Q'.eqv_symm (Q'.mul_add_eqv qGeom (geomSum qGeom k)
          (qGeom ^ (k + 1))))) ?_
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.mul_eqv_congr_left qGeom _ _ ih)

theorem geomSum_le_cap (k : Nat) : geomSum qGeom k ≤ geomCap := by
  induction k with
  | zero => exact geomSum_zero_le_cap
  | succ k ih =>
    have h1 : qGeom * geomSum qGeom k ≤ qGeom * geomCap :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ ih qGeom_nonneg
    have h2 : (1 : Q') + qGeom * geomSum qGeom k ≤
        (1 : Q') + qGeom * geomCap :=
      Q'.add_le_add_left _ _ _ h1
    exact Q'.le_trans' _ _ _ h2 geomCap_closed.1

theorem termF_offset_le {s : Nat} (hs : 12 ≤ s) (k : Nat) :
    termF wStep2 (s + k) ≤ termF wStep2 s * qGeom ^ k := by
  induction k with
  | zero =>
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_one_eqv _)
    exact Q'.mul_eqv_congr_left _ _ _ (eqv_of_eq' (Q'.pow_zero qGeom))
  | succ k ih =>
    have hs' : 12 ≤ s + k := Nat.le_trans hs (Nat.le_add_right _ _)
    have hstep : termF wStep2 (s + k + 1) ≤ termF wStep2 (s + k) * qGeom :=
      termF_succ_ratio_le hs'
    have h2 : termF wStep2 (s + k) * qGeom ≤
        (termF wStep2 s * qGeom ^ k) * qGeom :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ ih qGeom_nonneg
    have h3 := Q'.le_trans' _ _ _ hstep h2
    have heqv : ((termF wStep2 s * qGeom ^ k) * qGeom).eqv
        (termF wStep2 s * qGeom ^ (k + 1)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (termF wStep2 s) (qGeom ^ k) qGeom) ?_
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (qGeom ^ k) qGeom) ?_
      exact eqv_of_eq' (Q'.pow_succ qGeom k).symm
    change termF wStep2 (s + (k + 1)) ≤ termF wStep2 s * qGeom ^ (k + 1)
    have eidx : s + (k + 1) = s + k + 1 := Nat.add_assoc s k 1
    rw [eidx]
    exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv heqv)

theorem tailFrom_le_geom (k : Nat) :
    tailFrom wStep2 12 k ≤ termF wStep2 12 * geomSum qGeom k := by
  induction k with
  | zero =>
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))
  | succ k ih =>
    have hterm : termF wStep2 (12 + (k + 1)) ≤
        termF wStep2 12 * qGeom ^ (k + 1) :=
      termF_offset_le (Nat.le_refl 12) (k + 1)
    have hadd := add_le_add ih hterm
    have hfac :
        (termF wStep2 12 * geomSum qGeom k +
            termF wStep2 12 * qGeom ^ (k + 1)).eqv
          (termF wStep2 12 * (geomSum qGeom k + qGeom ^ (k + 1))) :=
      Q'.eqv_symm (Q'.mul_add_eqv (termF wStep2 12) (geomSum qGeom k)
        (qGeom ^ (k + 1)))
    have hgeom := geomSum_succ_split k
    have hgoal :
        (termF wStep2 12 * (geomSum qGeom k + qGeom ^ (k + 1))).eqv
          (termF wStep2 12 * geomSum qGeom (k + 1)) := by
      have e : geomSum qGeom (k + 1) = 1 + qGeom * geomSum qGeom k := rfl
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      exact Q'.eqv_trans _ _ _ hgeom (eqv_of_eq' e.symm)
    refine Q'.le_trans' _ _ _ hadd ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) (Q'.le_of_eqv hgoal)

theorem tail_cert {M : Nat} (hM : 12 ≤ M) :
    tailPartial wStep2 12 M ≤ pad40 := by
  unfold tailPartial
  have hle : 12 ≤ M := hM
  simp only [hle, ↓reduceDIte]
  have h1 : tailFrom wStep2 12 (M - 12) ≤
      termF wStep2 12 * geomSum qGeom (M - 12) :=
    tailFrom_le_geom (M - 12)
  have h2 : termF wStep2 12 * geomSum qGeom (M - 12) ≤
      termF wStep2 12 * geomCap :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (geomSum_le_cap _) (termF_nonneg 12)
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ h1 h2) term12_geomCap_le_pad


/-! ## Local RC helpers -/

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_mul (A.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => q_add_zero_eqv (A.approx n)))

private theorem rc_mul_scale_right (scalar : Q') (left right : RC) :
    RCmul left (RCscale scalar right) = RCmul (RCscale scalar left) right := by
  refine Quotient.inductionOn₂ left right ?_
  intro L R
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => by
      change (L.approx n * (scalar * R.approx n)).eqv
        ((scalar * L.approx n) * R.approx n)
      -- L*(s*R) ≃ (L*s)*R ≃ (s*L)*R
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (L.approx n) scalar (R.approx n))) ?_
      exact Q'.mul_eqv_congr_right (L.approx n * scalar) (scalar * L.approx n)
        (R.approx n) (Q'.mul_comm_eqv (L.approx n) scalar)))

/-! ## L3 specialised form bound and CS -/

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "V" => Completion hw0 hw1 width

/-- L3 vac-kill with `ℓ := B(U,·)`. -/
theorem form_bound_vacuumComplement (ρ κ : Q')
    (H : ∀ z : V,
      RCle (B z (T 1 z))
        (RCadd (RCscale ρ (B z z))
          (RCscale κ (RCmul (B U z) (B U z))))) :
    ∀ y : VacuumComplement hw0 hw1 (width := width),
      RCle (B y.val (T 1 y.val)) (RCscale ρ (B y.val y.val)) := by
  intro y
  have h := H y.val
  have hvac : B U y.val = RCzero := y.property
  have hmul : RCmul (B U y.val) (B U y.val) = RCzero := by
    rw [hvac, rc_zero_mul]
  have hscale : RCscale κ (RCmul (B U y.val) (B U y.val)) = RCzero := by
    rw [hmul, RCscale_RCzero]
  have hadd :
      RCadd (RCscale ρ (B y.val y.val))
        (RCscale κ (RCmul (B U y.val) (B U y.val))) =
      RCscale ρ (B y.val y.val) := by
    rw [hscale, rc_add_zero]
  rw [hadd] at h
  exact h

/-- Intermediate square-form bound `‖T₁y‖² ≤ ρ · q(y)`. -/
private theorem square_form_of_form_bound (ρ : Q') (hρ0 : (0 : Q') ≤ ρ)
    (H : ∀ y : VacuumComplement hw0 hw1 (width := width),
      RCle (B y.val (T 1 y.val)) (RCscale ρ (B y.val y.val)))
    (y : VacuumComplement hw0 hw1 (width := width)) :
    RCle (B (T 1 y.val) (T 1 y.val))
      (RCscale ρ (B y.val (T 1 y.val))) := by
  let s : RC := B (T 1 y.val) (T 1 y.val)
  let qf : RC := B y.val (T 1 y.val)
  have hs_diag : s = B y.val (T 2 y.val) :=
    completedInner_time_sum hw0 hw1 1 1 y.val y.val
  have eT : T 1 (T 1 y.val) = T 2 y.val :=
    (completedTime_add hw0 hw1 1 1 y.val).symm
  have hcs : RCle (RCmul s s)
      (RCmul qf (B (T 1 y.val) (T 2 y.val))) := by
    have h := oneStep_cauchySchwarz hw0 hw1 width y.val (T 1 y.val)
    rw [eT, ← hs_diag] at h
    exact h
  have hyT : B U (T 1 y.val) = RCzero :=
    completedTime_preserves_vacuumComplement hw0 hw1 1 y.val y.property
  have hr : RCle (B (T 1 y.val) (T 2 y.val)) (RCscale ρ s) := by
    have h := H ⟨T 1 y.val, hyT⟩
    rw [← eT]; exact h
  have hqnn : RCnonneg qf := completedInner_oneStep_nonnegative hw0 hw1 y.val
  have hsnn : RCnonneg s := completedInner_nonnegative hw0 hw1 (T 1 y.val)
  have hproduct : RCle (RCmul qf (B (T 1 y.val) (T 2 y.val)))
      (RCmul qf (RCscale ρ s)) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap.CReal.RCmul_mono_nonnegative_left_local hqnn hr
  have hproduct' : RCle (RCmul qf (RCscale ρ s))
      (RCmul (RCscale ρ qf) s) := by
    rw [rc_mul_scale_right]; exact RCle_refl _
  have hscaled_nn : RCnonneg (RCscale ρ qf) := by
    have h := RCscale_mono hρ0 hqnn
    rwa [RCscale_RCzero] at h
  exact YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap.CReal.RCle_of_mul_self_le_mul_right_nonnegative hsnn hscaled_nn
    (RCle_trans hcs (RCle_trans hproduct hproduct'))

/-- CS + constructive RC cancel ⇒ `WilsonVacuumSqFactor (ρ*ρ)`. -/
theorem sqFactor_of_form_bound (ρ : Q') (hρ0 : (0 : Q') ≤ ρ)
    (H : ∀ y : VacuumComplement hw0 hw1 (width := width),
      RCle (B y.val (T 1 y.val)) (RCscale ρ (B y.val y.val))) :
    WilsonVacuumSqFactor hw0 hw1 width (ρ * ρ) := by
  intro y
  have hsq := square_form_of_form_bound hw0 hw1 ρ hρ0 H y
  have hq := H y
  have hscaled := RCscale_mono hρ0 hq
  have hchain := RCle_trans hsq hscaled
  rw [RCscale_RCscale] at hchain
  exact hchain

/-! ## Specialised Width2Model and fineAt assembly -/

/-- Authorised L3 specialisation: `ℓ := B(U,·)`, `κ := 1-ρ`, formBound as hyp. -/
structure Width2Model (ρ : Q') where
  formBound :
    ∀ z : Completion
        (robust3UndershootSchedule.nome_pos 3)
        (robust3UndershootSchedule.nome_lt_one 3) 2,
      RCle
        (completedInner
          (robust3UndershootSchedule.nome_pos 3)
          (robust3UndershootSchedule.nome_lt_one 3)
          z (completedTime
            (robust3UndershootSchedule.nome_pos 3)
            (robust3UndershootSchedule.nome_lt_one 3) 1 z))
        (RCadd
          (RCscale ρ
            (completedInner
              (robust3UndershootSchedule.nome_pos 3)
              (robust3UndershootSchedule.nome_lt_one 3) z z))
          (RCscale ((1 : Q') - ρ)
            (RCmul
              (completedInner
                (robust3UndershootSchedule.nome_pos 3)
                (robust3UndershootSchedule.nome_lt_one 3)
                (unitState
                  (robust3UndershootSchedule.nome_pos 3)
                  (robust3UndershootSchedule.nome_lt_one 3) 2) z)
              (completedInner
                (robust3UndershootSchedule.nome_pos 3)
                (robust3UndershootSchedule.nome_lt_one 3)
                (unitState
                  (robust3UndershootSchedule.nome_pos 3)
                  (robust3UndershootSchedule.nome_lt_one 3) 2) z))))

theorem rhoBound_nonneg : (0 : Q') ≤ rhoBound := by
  change (0 : Int) * 10000 ≤ (316 : Int) * 1; decide

theorem rhoBound_pow4_factor :
    rhoBound ^ 4 = (rhoBound * rhoBound) * (rhoBound * rhoBound) := by decide

theorem fineAt_width2_step2_of_model (ρ : Q') (hρ : ρ ≤ rhoBound)
    (hρ0 : (0 : Q') ≤ ρ) (M : Width2Model ρ) :
    fineAt (fun _ => 2) 2 (ρ * ρ * (ρ * ρ)) ∧
      SchurBudget (ρ * ρ * (ρ * ρ)) 0 (etaR3 2) := by
  let hw0 := robust3UndershootSchedule.nome_pos 3
  let hw1 := robust3UndershootSchedule.nome_lt_one 3
  have hvac := form_bound_vacuumComplement hw0 hw1 (width := 2) ρ ((1 : Q') - ρ)
    M.formBound
  have hsq := sqFactor_of_form_bound hw0 hw1 (width := 2) ρ hρ0 hvac
  have hcontr := wilsonVacuumSq_of_factor (r := ρ) (α := ρ * ρ)
    (Q'.le_refl' (ρ * ρ)) hsq
  have htwo := vacuumSq_implies_twoStepFactor ρ hcontr
  refine ⟨htwo, ?_⟩
  -- SchurBudget: ρ^4 ≤ 1/64 + (1-1/64)*0
  unfold SchurBudget
  rw [etaR3_two]
  have hz : (((1 : Q') - Q'.mkPos 1 64 (by decide)) * (0 : Q')).eqv (0 : Q') :=
    Q'.mul_zero_eqv _
  have hadd :
      (Q'.mkPos 1 64 (by decide) +
          ((1 : Q') - Q'.mkPos 1 64 (by decide)) * (0 : Q')).eqv
        (Q'.mkPos 1 64 (by decide)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hz) (q_add_zero_eqv _)
  -- ρ^4 ≤ rhoBound^4 ≤ 1/64
  have hb0 : (0 : Q') ≤ rhoBound := rhoBound_nonneg
  have h2 : ρ * ρ ≤ rhoBound * rhoBound :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right ρ rhoBound ρ hρ hρ0)
      (Q'.mul_le_mul_of_nonneg_left ρ rhoBound rhoBound hρ hb0)
  have hr2 : (0 : Q') ≤ ρ * ρ := Q'.mul_nonneg _ _ hρ0 hρ0
  have hb2 : (0 : Q') ≤ rhoBound * rhoBound := Q'.mul_nonneg _ _ hb0 hb0
  have h4 : (ρ * ρ) * (ρ * ρ) ≤ (rhoBound * rhoBound) * (rhoBound * rhoBound) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h2 hr2)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h2 hb2)
  have h4' : ρ * ρ * (ρ * ρ) ≤ rhoBound ^ 4 := by
    rw [rhoBound_pow4_factor]; exact h4
  have h4'' : ρ * ρ * (ρ * ρ) ≤ Q'.mkPos 1 64 (by decide) :=
    Q'.le_trans' _ _ _ h4' rho4_cert
  exact Q'.le_trans' _ _ _ h4'' (Q'.le_of_eqv (Q'.eqv_symm hadd))

end YMGap.RG.Robust3Width2Electric

/-! ## Axiom audit -/

#print axioms YMGap.RG.Robust3Width2Electric.etaR3_two
#print axioms YMGap.RG.Robust3Width2Electric.r3Nome_three
#print axioms YMGap.RG.Robust3Width2Electric.fOne_cert
#print axioms YMGap.RG.Robust3Width2Electric.tail_cert
#print axioms YMGap.RG.Robust3Width2Electric.rho_cert
#print axioms YMGap.RG.Robust3Width2Electric.rho4_cert
#print axioms YMGap.RG.Robust3Width2Electric.linear_anti
#print axioms YMGap.RG.Robust3Width2Electric.exactRatioRaw_anti
#print axioms YMGap.RG.Robust3Width2Electric.termF_succ_ratio_le
#print axioms YMGap.RG.Robust3Width2Electric.form_bound_vacuumComplement
#print axioms YMGap.RG.Robust3Width2Electric.sqFactor_of_form_bound
#print axioms YMGap.RG.Robust3Width2Electric.fineAt_width2_step2_of_model
