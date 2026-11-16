import YMGap.RG.Robust3MarginDischarge

/-!
# Robust3: `hspacing` stated on a heat-kernel string tension `a(w)` at the Lean nomes (window j6–7)

The existing `hspacing_OPEN` (`Robust3UndershootPhysicalUnits.lean:61`, `Robust3MarginDischarge.lean:118`) is a hypothesis
on an abstract sequence `a : Nat → Q'`, not tied to the nome schedule. Here `a := aHK ∘ r3Nome` for one function
`aHK : Q' → Q'` (OPEN physics object: the heat-kernel `a√σ` at nome `w`), with
* `hspacingHK_win aHK lo hi`: `2·aHK(w_{j+1}) ≤ ρ_j·aHK(w_j)` for `lo ≤ j ≤ hi` (the MC-supported window);
* `hspacingHK_off aHK lo hi`: the same for `j < lo ∨ hi < j` (OPEN: strong coupling / data / AF tail);
* `hposHK aHK`: `0 < aHK(w_j)` for all `j` (rules out the vacuous `a ≡ 0`).
The current window is `j6–7` (`hspacingHK_window := hspacingHK_win aHK 6 7`). **Extension point for j8**: once
Numerics reports w9, use `hspacingHK_win aHK 6 8` / `hspacingHK_off aHK 6 8`; every theorem below is generic in `lo, hi`.

Window support is Monte Carlo (task2k), NOT proof. Additive; no existing statement is changed.
Non-vacuity (`spacing_nonvacuous`) covers ONLY the spacing and positivity hypotheses (sequence `2^{-j}`).
-/

namespace YMGap.RG.Robust3SpacingHeatKernel

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.RG.DyadicCrossoverInstance (eDy)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule r3Nome)
open YMGap.RG.Robust2UndershootPhysicalUnits (r2Rho r2RhoTab r2RhoTail)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3Rho r3P robust3_spacing_bound)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3)
open YMGap.RG.Robust3MarginDischarge (robust3_physical_floor_noMargin)

/-- Spacing on `aHK` at the nomes, for `lo ≤ j ≤ hi`. -/
def hspacingHK_win (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → Q'.ofNat 2 * aHK (r3Nome (j+1)) ≤ r3Rho j * aHK (r3Nome j)

/-- Spacing on `aHK` off the window (`j < lo ∨ hi < j`); OPEN. -/
def hspacingHK_off (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, (j < lo ∨ hi < j) → Q'.ofNat 2 * aHK (r3Nome (j+1)) ≤ r3Rho j * aHK (r3Nome j)

/-- Positivity of `aHK` on the nomes. -/
def hposHK (aHK : Q' → Q') : Prop := ∀ j, (0 : Q') < aHK (r3Nome j)

/-- The current MC-supported window `j6–7` (extend to `6 8` once w9 is measured). -/
def hspacingHK_window (aHK : Q' → Q') : Prop := hspacingHK_win aHK 6 7

/-- Window + off-window give the existing `hspacing_OPEN` for `a := aHK ∘ r3Nome`. -/
theorem hspacing_of_HK (aHK : Q' → Q') (lo hi : Nat) (hw : hspacingHK_win aHK lo hi)
    (ho : hspacingHK_off aHK lo hi) :
    ∀ i, Q'.ofNat 2 * (fun j => aHK (r3Nome j)) (i+1) ≤ r3Rho i * (fun j => aHK (r3Nome j)) i := by
  intro i
  by_cases h1 : i < lo
  · exact ho i (Or.inl h1)
  · by_cases h2 : hi < i
    · exact ho i (Or.inr h2)
    · exact hw i (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)

theorem nonneg_of_pos (aHK : Q' → Q') (hp : hposHK aHK) : ∀ i, (0 : Q') ≤ aHK (r3Nome i) :=
  fun i => Q'.le_of_lt (hp i)

/-- **Physical-units spacing bound, heat-kernel form** (PROVED reduction; hypotheses OPEN):
`2ⁿ·aHK(w_n) ≤ P₃·aHK(w_0)`. -/
theorem robust3_spacing_bound_HK (aHK : Q' → Q') (lo hi : Nat) (hp : hposHK aHK)
    (hw : hspacingHK_win aHK lo hi) (ho : hspacingHK_off aHK lo hi) (n : Nat) :
    Q'.ofNat (2 ^ n) * aHK (r3Nome n) ≤ r3P * aHK (r3Nome 0) :=
  robust3_spacing_bound (fun j => aHK (r3Nome j)) (nonneg_of_pos aHK hp) (hspacing_of_HK aHK lo hi hw ho) n

/-- **Floor in physical units, heat-kernel form** (`robust3_physical_floor_noMargin` with `a := aHK ∘ r3Nome`).
OPEN: `hcross`, `hafδ`, `hupper`, `hschur` (unchanged) and the spacing hypotheses on `aHK`. -/
theorem robust3_physical_floor_noMargin_HK :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
      (_hafδ_OPEN : ∀ n, 6 ≤ n →
        delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) →
        VacuumComplement (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width := width (0+n)))
      (D : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) → RC)
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
      (_hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
        (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width (0+n+1)) (width (0+n))
        (delta n) (Phi n) (D n))
      (aHK : Q' → Q') (lo hi : Nat) (_hpos : hposHK aHK)
      (_hwin_MC : hspacingHK_win aHK lo hi) (_hoff_OPEN : hspacingHK_off aHK lo hi)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (r3P * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur aHK lo hi hp hw ho n =>
    robust3_physical_floor_noMargin width delta hd0 hd1 hcross hafδ Phi D hupper hschur
      (fun j => aHK (r3Nome j)) (nonneg_of_pos aHK hp) (hspacing_of_HK aHK lo hi hw ho) n

/-! ## Non-vacuity of the spacing + positivity part (sequence `a_j = 2^{-j}`) -/

theorem rho_ge_one (i : Nat) : (1 : Q') ≤ r3Rho i := by
  show (1 : Q') ≤ r2Rho i
  unfold r2Rho
  by_cases h : i < 11
  · rw [if_pos h]
    have hall : ∀ i, i < 11 → (1 : Q') ≤ r2RhoTab i := by decide
    exact hall i h
  · rw [if_neg h]
    generalize i - 11 = k
    unfold r2RhoTail
    show (1 : Int) * (((Q'.mkPos _ ((k+4) * (k+18)) _).den : Nat) : Int)
      ≤ (((k+17) * (k+5) : Nat) : Int) * ((1 : Nat) : Int)
    rw [Q'.mkPos_den]
    have key : 1 * ((k+4) * (k+17+1)) ≤ (k+17) * (k+4+1) * 1 := by
      rw [Nat.one_mul, Nat.mul_one, Nat.mul_add_one (k+4) (k+17), Nat.mul_add_one (k+17) (k+4),
        Nat.mul_comm (k+4) (k+17)]
      exact Nat.add_le_add_left (by simp +arith) _
    exact_mod_cast key

/-- The sequence `2^{-j}`. -/
def aSeq (j : Nat) : Q' := Q'.mkPos 1 (2 ^ j) (Nat.two_pow_pos _)

/-- **Non-vacuity (spacing + positivity only):** `a_j = 2^{-j}` is positive and satisfies
`2·a_{j+1} ≤ ρ_j·a_j` for EVERY `j` (window and off-window), since `ρ_j ≥ 1`. -/
theorem spacing_nonvacuous :
    (∀ j, (0 : Q') < aSeq j) ∧ ∀ j, Q'.ofNat 2 * aSeq (j+1) ≤ r3Rho j * aSeq j := by
  refine ⟨fun j => (show (0 : Int) * _ < 1 * _ from ?_), fun j => ?_⟩
  · show (0 : Int) * ((aSeq j).den : Int) < 1 * ((0 : Q').den : Int)
    rw [Int.zero_mul]
    exact (by decide : (0 : Int) < 1 * (((0 : Q').den : Nat) : Int))
  · have he : (Q'.ofNat 2 * aSeq (j+1)).eqv (aSeq j) := by
      unfold aSeq Q'.eqv
      show ((2 : Int) * 1) * (((Q'.mkPos 1 (2 ^ j) _).den : Nat) : Int)
        = 1 * ((Q'.ofNat 2 * Q'.mkPos 1 (2 ^ (j+1)) _).den : Int)
      rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den]
      show (2 * 1 : Int) * ((2 ^ j : Nat) : Int) = 1 * (((1 : Nat) : Int) * ((2 ^ (j+1) : Nat) : Int))
      rw [Nat.pow_succ]; push_cast; ac_rfl
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (rho_ge_one j)
          ((Q'.zero_le_iff_num_nonneg _).mpr (show (0 : Int) ≤ 1 by decide))))

/-- Any `aHK` agreeing with `2^{-j}` on the nomes satisfies all three `_HK` spacing/positivity hypotheses, for every
window `lo, hi`. (Existence of such an `aHK : Q' → Q'` needs `r3Nome` injective; not proved here.) -/
theorem HK_hyps_of_seq (aHK : Q' → Q') (h : ∀ j, aHK (r3Nome j) = aSeq j) (lo hi : Nat) :
    hposHK aHK ∧ hspacingHK_win aHK lo hi ∧ hspacingHK_off aHK lo hi := by
  refine ⟨fun j => ?_, fun j _ _ => ?_, fun j _ => ?_⟩
  · rw [h j]; exact spacing_nonvacuous.1 j
  · rw [h j, h (j+1)]; exact spacing_nonvacuous.2 j
  · rw [h j, h (j+1)]; exact spacing_nonvacuous.2 j

end YMGap.RG.Robust3SpacingHeatKernel
