/-
# P5: an explicit Wilson cutoff schedule, the SU(2) one-loop constant, and the AF cross-check

**Label: Wilson lattice scaffolding; also true for U(1) (pure arithmetic); not gap evidence. No chart-closure claim.**
Additive. Constructive: every clause is a decidable rational or natural-number statement with explicit witnesses
and moduli. No `Real`, no Mathlib, no `Classical`; axioms within `propext`, `Quot.sound`.

1. **Schedule** (the arithmetic clauses of OpenAI's `WilsonTrajectory`, `YangMills/CutoffTrajectory.lean`):
   * `D N = 3^N`: `D 0 = 1`, `D N ∣ D (N+1)`, block `D (N+1) / D N = 3` (odd, `≥ 3`), strictly increasing;
   * `period p = 4(p+1)`: `4 ∣ period p`, strictly increasing;
   * gentle growth: for every additive logarithm `L` (with `L(ab) = L a + L b`), `L(D N) = N·L 3`. So
     `wilsonLogStep N = L(3)/L(D N) = 1/N`. The rational `1/N ≤ ε` holds for `N ≥ ε.den`, an explicit modulus.
   The `bare` clause (couplings tuned into `[c_N/2, 2c_N]`) is NOT ported: its existence is OpenAI's
   continuity/IVT tuning, class (b).
2. **Casimir** in OpenAI's trace-form normalisation (`wilsonOneLoop`, `YangMills/LatticeFields.lean`). On ℍ ≅ su(2),
   with `−Re tr(XY) = −2 Re(XY)` and the orthonormal basis `E = (I, J, K)` (`−Re tr(E_a E_b) = 2 δ_ab`):
   `Σ_{a,b} −Re tr([E_a,E_b]²) = 48` and `casimir = 48/(2·3) = 8` (decide).
   Hence `2·wilsonOneLoop = 11·8/(24π²) = 11/(3π²)`.
3. **π handling (constructive):** π is the repo's CReal `Pi.pi` with the explicit rational Machin enclosure
   `piLower 4 ≤ π_m ≤ piUpper 4` for every approximant `m ≥ 4`. ln 2 is `CRealLog.log2`, enclosed by
   `log2Lower 16 ≤ ln2_m ≤ log2Upper 16`. Every inequality below holds for all rationals in these enclosures.
4. **AF cross-check.** Wilson `β = 4/g²` with `β ≈ (11/(3π²))·log(1/a)` and `a_j = 2^{-j}` gives
   `g² = 12π²/(11 j ln2)`. The heat-kernel convention `g² = −8 log w` gives `1 − w_j ≈ g²/8 = A_pred/j` with
   `A_pred = 3π²/(22 ln 2) ≈ 1.94166`. We prove `|22·afA·ln2/(3π²) − 1| ≤ 1/2000` with `afA = 1942/1000`
   (`af_slope_crosscheck`); the actual relative gap is ≈ 1.75·10⁻⁴.
   Deviation: `work_plan.md` writes the ratio as `8·afA·ln2·3π²/(11·8)`. That expression is ≈ 3.62, not ≈ 1, so it
   is a typo; the ratio used here, `22·afA·ln2/(3π²)`, is the one the stated derivation gives.
   This is a one-loop calibration check only: no two-loop term or error bound is claimed.
-/

import YMGap.Constructive.Pi
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CRealLog
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
import YMGap.RepTheory.RationalQuaternionAlgebra

namespace YMGap.Continuum.WilsonTrajectorySchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afA)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The schedule -/

/-- Inverse lattice spacings `D_N = 3^N`. -/
def schedD (N : Nat) : Nat := 3 ^ N

/-- Periods `4(p+1)`. -/
def schedPeriod (p : Nat) : Nat := 4 * (p + 1)

/-- Block ratio `D_{N+1}/D_N`. -/
def schedBlock (N : Nat) : Nat := schedD (N + 1) / schedD N

theorem schedD_zero : schedD 0 = 1 := rfl

theorem schedD_succ (N : Nat) : schedD (N + 1) = schedD N * 3 := by
  show 3 ^ (N + 1) = 3 ^ N * 3
  exact Nat.pow_succ 3 N

theorem schedD_pos : ∀ N : Nat, 0 < schedD N
  | 0 => by decide
  | N + 1 => by rw [schedD_succ]; exact Nat.mul_pos (schedD_pos N) (by decide)

theorem schedD_dvd (N : Nat) : schedD N ∣ schedD (N + 1) := ⟨3, schedD_succ N⟩

theorem schedBlock_eq (N : Nat) : schedBlock N = 3 := by
  unfold schedBlock
  rw [schedD_succ, Nat.mul_comm]
  exact Nat.mul_div_cancel 3 (schedD_pos N)

/-- Odd block, explicit witness `3 = 2·1 + 1`. -/
theorem schedBlock_odd (N : Nat) : schedBlock N = 2 * 1 + 1 := schedBlock_eq N

theorem schedBlock_large (N : Nat) : 3 ≤ schedBlock N := Nat.le_of_eq (schedBlock_eq N).symm

theorem schedD_strict (N : Nat) : schedD N < schedD (N + 1) := by
  rw [schedD_succ, Nat.mul_succ]
  exact Nat.lt_add_of_pos_left (Nat.mul_pos (schedD_pos N) (by decide))

theorem schedPeriod_four (p : Nat) : 4 ∣ schedPeriod p := ⟨p + 1, rfl⟩

theorem schedPeriod_strict (p : Nat) : schedPeriod p < schedPeriod (p + 1) :=
  Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (by decide)

/-- Gentle growth, logarithm-free form: for every additive `L`, `L(D_N) = N·L(3)`. -/
theorem schedD_log (L : Nat → Q') (hL1 : L 1 ≈ 0) (hL : ∀ a b, L (a * b) ≈ L a + L b) :
    ∀ N : Nat, L (schedD N) ≈ Q'.ofNat N * L 3
  | 0 => Q'.eqv_trans _ _ _ hL1 (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | N + 1 => by
      rw [schedD_succ]
      refine Q'.eqv_trans _ _ _ (hL _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (schedD_log L hL1 hL N)) ?_)
      have e := YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.var 1)) (.mul (.add (.var 0) (.const 1)) (.var 1)) (by decide)
        (fun i => if i = 0 then Q'.ofNat N else L 3)
      refine Q'.eqv_trans _ _ _ e ?_
      exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv N 1))

/-- Rational log-step `1/N`. -/
def logStepRat (N : Nat) : Q' := Q'.mkPos 1 (N + 1) (Nat.succ_pos N)

/-- **Gentle (explicit modulus):** `1/(N+1) ≤ ε` for every `N + 1 ≥ ε.den`, `ε > 0`. -/
theorem logStep_gentle (ε : Q') (hε : (0 : Q') < ε) (N : Nat) (hN : ε.den ≤ N + 1) :
    logStepRat N ≤ ε := by
  have hn : (0 : Int) < ε.num := by
    have h0 : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    rw [Int.zero_mul] at h0
    exact Int.lt_of_lt_of_le h0 (Int.le_of_eq (Int.mul_one _))
  show ((1 : Nat) : Int) * (ε.den : Int) ≤ ε.num * (((N + 1 : Nat) : Int))
  rw [Int.ofNat_one, Int.one_mul]
  have h1 : (1 : Int) ≤ ε.num := hn
  have h2 := Int.mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg (N + 1))
  rw [Int.one_mul] at h2
  exact Int.le_trans (Int.ofNat_le.mpr hN) h2

/-! ## 2. Casimir in the trace-form normalisation -/

open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion (mul basisI basisJ basisK)

/-- The orthonormal basis `E_a` of su(2) ≅ Im ℍ. -/
def E : Nat → RationalQuaternion
  | 0 => basisI
  | 1 => basisJ
  | _ => basisK

/-- `−Re tr(XY) = −2 Re(XY)` on the 2×2 representation. -/
def traceForm (X Y : RationalQuaternion) : Q' := -((2 : Q') * (mul X Y).r)

/-- Commutator `XY − YX`. -/
def comm (X Y : RationalQuaternion) : RationalQuaternion :=
  let a := mul X Y; let b := mul Y X
  ⟨a.r + -b.r, a.i + -b.i, a.j + -b.j, a.k + -b.k⟩

/-- Orthonormality `−Re tr(E_a E_b) = 2 δ_ab` (decide). -/
theorem traceForm_basis :
    ∀ a, a < 3 → ∀ b, b < 3 → traceForm (E a) (E b) ≈ (if a = b then (2 : Q') else 0) := by decide

/-- `casimir = Σ_{a,b} −Re tr([E_a,E_b]²) / ((n+1)·m)` with `n + 1 = 2`, `m = 3`. -/
def casimirSU2 : Q' :=
  ((List.range 3).foldr (fun a s => (List.range 3).foldr
      (fun b t => traceForm (comm (E a) (E b)) (comm (E a) (E b)) + t) 0 + s) 0) *
    Q'.mkPos 1 6 (by decide)

/-- **`casimir = 8`** (decide); hence `2·wilsonOneLoop = 11·8/(24π²) = 11/(3π²)`. -/
theorem casimirSU2_eq : casimirSU2 ≈ 8 := by decide

/-- The one-loop slope coefficient: `2 b₁ · π² = 11·casimir/24 = 11/3`, i.e. `2 b₁ = 11/(3π²)`. -/
theorem slope_coeff : Q'.ofNat 11 * casimirSU2 * Q'.mkPos 1 24 (by decide) ≈ Q'.mkPos 11 3 (by decide) := by
  decide

/-! ## 3. π and ln 2 enclosures (constructive, explicit) -/

open YMGap.Constructive.Pi (pi piLower piUpper pi_approx_enclosure)
open YMGap.Constructive.CRealLog (log2 log2Lower log2Upper log2Lower_le_approx log2_approx_le_upper)

/-- Decidable rational brackets used below (`3.1415 ≤ π ≤ 3.1417`, `0.6931 ≤ ln 2 ≤ 0.69319`). -/
theorem enclosures :
    Q'.mkPos 31415 10000 (by decide) ≤ piLower 4 ∧ piUpper 4 ≤ Q'.mkPos 31417 10000 (by decide) ∧
    Q'.mkPos 6931 10000 (by decide) ≤ log2Lower 16 ∧ log2Upper 16 ≤ Q'.mkPos 69319 100000 (by decide) := by
  decide

/-! ## 4. AF cross-check -/

/-- **One-loop AF cross-check (rational, every point of the enclosures):** for every rational `p ∈ [3.1415, 3.1417]`
and `l ∈ [0.6931, 0.69319]`, `(1 − 1/2000)·3p² ≤ 22·afA·l ≤ (1 + 1/2000)·3p²`. -/
theorem af_slope_crosscheck_rat (p l : Q')
    (hp0 : Q'.mkPos 31415 10000 (by decide) ≤ p) (hp1 : p ≤ Q'.mkPos 31417 10000 (by decide))
    (hl0 : Q'.mkPos 6931 10000 (by decide) ≤ l) (hl1 : l ≤ Q'.mkPos 69319 100000 (by decide)) :
    Q'.mkPos 1999 2000 (by decide) * (3 * (p * p)) ≤ Q'.ofNat 22 * afA * l ∧
      Q'.ofNat 22 * afA * l ≤ Q'.mkPos 2001 2000 (by decide) * (3 * (p * p)) := by
  have hp0' : (0 : Q') ≤ p := Q'.le_trans' _ _ _ (by decide) hp0
  have sq_le : p * p ≤ Q'.mkPos 31417 10000 (by decide) * Q'.mkPos 31417 10000 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp1 hp0')
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hp1 (by decide))
  have sq_ge : Q'.mkPos 31415 10000 (by decide) * Q'.mkPos 31415 10000 (by decide) ≤ p * p :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp0 (by decide))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hp0 hp0')
  constructor
  · refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ sq_le (by decide)) (by decide)) ?_
    refine Q'.le_trans' _ _ _ ?_ (Q'.mul_le_mul_of_nonneg_left _ _ _ hl0 (by decide))
    decide
  · refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hl1 (by decide)) ?_
    refine Q'.le_trans' _ _ _ ?_
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ sq_ge (by decide)) (by decide))
    decide

/-- **AF cross-check at the actual CReal approximants** of π and ln 2 (every index `m ≥ 16`). -/
theorem af_slope_crosscheck (m : Nat) (hm : 16 ≤ m) :
    Q'.mkPos 1999 2000 (by decide) * (3 * (pi.approx m * pi.approx m)) ≤ Q'.ofNat 22 * afA * log2.approx m ∧
      Q'.ofNat 22 * afA * log2.approx m ≤ Q'.mkPos 2001 2000 (by decide) * (3 * (pi.approx m * pi.approx m)) := by
  have he := enclosures
  have hpi := pi_approx_enclosure 4 m (Nat.le_trans (by decide) hm)
  exact af_slope_crosscheck_rat _ _ (Q'.le_trans' _ _ _ he.1 hpi.1) (Q'.le_trans' _ _ _ hpi.2 he.2.1)
    (Q'.le_trans' _ _ _ he.2.2.1 (log2Lower_le_approx 16 m hm))
    (Q'.le_trans' _ _ _ (log2_approx_le_upper 16 m hm) he.2.2.2)

end YMGap.Continuum.WilsonTrajectorySchedule
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedPeriod
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedBlock
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD_zero
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD_pos
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD_succ
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD_dvd
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedBlock_eq
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedBlock_odd
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedBlock_large
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD_strict
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedPeriod_four
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedPeriod_strict
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.schedD_log
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.logStepRat
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.logStep_gentle
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.E
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.traceForm
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.comm
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.traceForm_basis
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.casimirSU2
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.casimirSU2_eq
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.slope_coeff
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.enclosures
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.af_slope_crosscheck_rat
#print axioms YMGap.Continuum.WilsonTrajectorySchedule.af_slope_crosscheck
