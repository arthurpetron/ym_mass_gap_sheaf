/-
# Trace sandwich for the finite spectral model (proved finite lemmas)

ADDITIVE. On the existing `SpectralGap.SpectralModel` (finite `k`, `λ_i ≥ 0` as a
structure field `lam_nonneg`), `specMax` (`LocatedSpectralGap`) and `finSum`
(`RationalTail`):

* `excitedTrace S n = Σ_{i<k} λ_i^n`.
* `specMax_pow_le_excitedTrace` (`0 < n`): `specMax^n ≤ s_n`.
* `excitedTrace_double_le`: `s_{2n} ≤ specMax^n · s_n`.
* Root-free upper bound: `s_n ≤ U ≤ ρ^n`, `0 ≤ ρ`, `0 < n` ⇒ `specMax ≤ ρ`.
* Root-free lower bound: `A ≤ s_{2n}`, `s_n ≤ B`, `0 < B`, `ρ^n·B ≤ A`, `0 < n`
  ⇒ `ρ ≤ specMax`; ratio form `L·s_n ≤ s_{2n}`, `0 < s_n` ⇒ `L ≤ specMax^n`.
* `specMax_mem_of_trace_bounds`: both at once (certified rate interval).

Hypotheses used: `λ_i ≥ 0` (field of `SpectralModel`; needed for both directions),
`0 < n` (the `k = 0`, `n = 0` edge `1 ≤ 0` fails), `0 < B` resp. `0 < s_n` for the
lower bound. All rational (`Q'`), no `CReal`. Choice-free: the `Q'` order is decidable
on `Int` cross-products. Axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SpectralTraceSandwich

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SpectralGap (SpectralModel pow_le_pow_left finSum_mul_const_le)
open YMGap.Continuum (specMax specMaxAux specMaxAux_le_iff specMax_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Power trace of the finite spectral model: `s_n = Σ_{i<k} λ_i^n`. -/
def excitedTrace (S : SpectralModel) (n : Nat) : Q' :=
  finSum (fun i => S.lam i ^ n) S.k

theorem sts_finSum_nonneg (f : QSeq) (h : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ finSum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => Q'.zero_le_add _ _ (sts_finSum_nonneg f h n) (h n)

/-- Termwise comparison on the first `n` entries only. -/
theorem sts_finSum_le_of_lt (f g : QSeq) :
    ∀ n, (∀ i, i < n → f i ≤ g i) → finSum f n ≤ finSum g n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
    show finSum f n + f n ≤ finSum g n + g n
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (f n)
        (sts_finSum_le_of_lt f g n (fun i hi => h i (Nat.lt_succ_of_lt hi))))
      (Q'.add_le_add_left _ _ _ (h n (Nat.lt_succ_self n)))

theorem excitedTrace_nonneg (S : SpectralModel) (n : Nat) : (0 : Q') ≤ excitedTrace S n :=
  sts_finSum_nonneg _ (fun i => Q'.pow_nonneg (S.lam i) (S.lam_nonneg i) n) S.k

theorem sts_zero_pow_succ_le (p : Nat) : (0 : Q') ^ (p + 1) ≤ 0 := by
  show ((0 : Q') * (0 : Q') ^ p).num * ((0 : Q').den : Int) ≤
    (0 : Q').num * (((0 : Q') * (0 : Q') ^ p).den : Int)
  show ((0 : Int) * ((0 : Q') ^ p).num) * ((0 : Q').den : Int) ≤
    (0 : Int) * (((0 : Q') * (0 : Q') ^ p).den : Int)
  rw [Int.zero_mul, Int.zero_mul, Int.zero_mul]
  exact Int.le_refl 0

/-- Running max to a positive power is bounded by the power sum. -/
theorem specMaxAux_pow_le (lam : Nat → Q') (hlam : ∀ i, (0 : Q') ≤ lam i) (p : Nat) :
    ∀ n, specMaxAux lam n ^ (p + 1) ≤ finSum (fun i => lam i ^ (p + 1)) n
  | 0 => sts_zero_pow_succ_le p
  | n + 1 => by
    show (Q'.max' (specMaxAux lam n) (lam n)) ^ (p + 1) ≤
      finSum (fun i => lam i ^ (p + 1)) n + lam n ^ (p + 1)
    have hS : (0 : Q') ≤ finSum (fun i => lam i ^ (p + 1)) n :=
      sts_finSum_nonneg _ (fun i => Q'.pow_nonneg (lam i) (hlam i) (p + 1)) n
    unfold Q'.max'
    by_cases h : specMaxAux lam n ≤ lam n
    · rw [if_pos h]
      have h2 := Q'.add_le_add_right _ _ (lam n ^ (p + 1)) hS
      rw [Q'.zero_add'] at h2
      exact h2
    · rw [if_neg h]
      exact Q'.le_trans' _ _ _ (specMaxAux_pow_le lam hlam p n)
        (Q'.add_le_self_of_nonneg _ _ (Q'.pow_nonneg (lam n) (hlam n) (p + 1)))

/-- **PROVED.** `0 < n` ⇒ `specMax^n ≤ s_n`. -/
theorem specMax_pow_le_excitedTrace (S : SpectralModel) (n : Nat) (hn : 0 < n) :
    specMax S ^ n ≤ excitedTrace S n := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  exact specMaxAux_pow_le S.lam S.lam_nonneg p S.k

/-- Every mode is below `specMax`. -/
theorem lam_le_specMax (S : SpectralModel) (i : Nat) (hi : i < S.k) : S.lam i ≤ specMax S :=
  ((specMaxAux_le_iff S.lam (specMaxAux S.lam S.k) S.k).mp (Q'.le_refl' _)).2 i hi

theorem sts_pow_add (q : Q') (a : Nat) : ∀ b, q ^ (a + b) ≈ q ^ a * q ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (q ^ a))
  | b + 1 => by
    show q * q ^ (a + b) ≈ q ^ a * (q * q ^ b)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (sts_pow_add q a b))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => q | 1 => q ^ a | _ => q ^ b))

/-- **PROVED.** `s_{2n} ≤ specMax^n · s_n`. -/
theorem excitedTrace_double_le (S : SpectralModel) (n : Nat) :
    excitedTrace S (2 * n) ≤ specMax S ^ n * excitedTrace S n := by
  have hM : (0 : Q') ≤ specMax S ^ n := Q'.pow_nonneg _ (specMax_nonneg S) n
  have hterm : ∀ i, i < S.k →
      S.lam i ^ (2 * n) ≤ S.lam i ^ n * specMax S ^ n := by
    intro i hi
    rw [Nat.two_mul]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sts_pow_add (S.lam i) n n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (pow_le_pow_left (S.lam_nonneg i) (lam_le_specMax S i hi) n)
        (Q'.pow_nonneg _ (S.lam_nonneg i) n))
  have h1 := sts_finSum_le_of_lt (fun i => S.lam i ^ (2 * n))
    (fun i => S.lam i ^ n * specMax S ^ n) S.k hterm
  have h2 := finSum_mul_const_le (fun i => S.lam i ^ n) (specMax S ^ n) hM S.k
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 h2)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

theorem sts_pow_pos (a : Q') (ha : (0 : Q') < a) : ∀ n : Nat, (0 : Q') < a ^ n
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | n + 1 => Q'.mul_pos ha (sts_pow_pos a ha n)

/-- **Root-free cancellation.** `0 ≤ b`, `0 < n`, `a^n ≤ b^n` ⇒ `a ≤ b`
(decidable `Q'` order; choice-free). -/
theorem le_of_pow_le_pow (a b : Q') (hb : (0 : Q') ≤ b) (n : Nat) (hn : 0 < n)
    (h : a ^ n ≤ b ^ n) : a ≤ b := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  by_cases hab : a ≤ b
  · exact hab
  · have hlt : b < a := by
      show b.num * (a.den : Int) < a.num * (b.den : Int)
      have h' : ¬ (a.num * (b.den : Int) ≤ b.num * (a.den : Int)) := hab
      exact Int.not_le.mp h'
    have ha : (0 : Q') < a := Q'.lt_of_le_of_lt hb hlt
    have hp : (0 : Q') < a ^ p := sts_pow_pos a ha p
    have hbp : b ^ p ≤ a ^ p := pow_le_pow_left hb (Q'.le_of_lt hlt) p
    -- a·a^p ≤ b·b^p ≤ b·a^p
    have h1 : a * a ^ p ≤ b * a ^ p :=
      Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_left _ _ b hbp hb)
    have h2 : a ^ p * a ≤ a ^ p * b :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    exact Q'.le_of_mul_le_mul_left h2 hp

/-- **PROVED (upper, root-free).** `s_n ≤ U`, `U ≤ ρ^n`, `0 ≤ ρ`, `0 < n` ⇒ `specMax ≤ ρ`. -/
theorem specMax_le_of_trace_le (S : SpectralModel) (n : Nat) (hn : 0 < n) (U ρ : Q')
    (hρ : (0 : Q') ≤ ρ) (hU : excitedTrace S n ≤ U) (hUρ : U ≤ ρ ^ n) : specMax S ≤ ρ :=
  le_of_pow_le_pow _ _ hρ n hn
    (Q'.le_trans' _ _ _ (specMax_pow_le_excitedTrace S n hn) (Q'.le_trans' _ _ _ hU hUρ))

/-- **PROVED (lower, multiplicative).** `A ≤ s_{2n}`, `s_n ≤ B` ⇒ `A ≤ specMax^n · B`. -/
theorem specMax_pow_mul_ge (S : SpectralModel) (n : Nat) (A B : Q')
    (hA : A ≤ excitedTrace S (2 * n)) (hB : excitedTrace S n ≤ B) :
    A ≤ specMax S ^ n * B :=
  Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ (excitedTrace_double_le S n)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hB (Q'.pow_nonneg _ (specMax_nonneg S) n)))

/-- **PROVED (ratio form).** `0 < s_n`, `L·s_n ≤ s_{2n}` ⇒ `L ≤ specMax^n`. -/
theorem specMax_pow_ge_of_ratio (S : SpectralModel) (n : Nat) (L : Q')
    (hs : (0 : Q') < excitedTrace S n) (hL : L * excitedTrace S n ≤ excitedTrace S (2 * n)) :
    L ≤ specMax S ^ n := by
  have h := Q'.le_trans' _ _ _ hL (excitedTrace_double_le S n)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))) hs

/-- **PROVED (lower, root-free).** `A ≤ s_{2n}`, `s_n ≤ B`, `0 < B`, `ρ^n·B ≤ A`,
`0 < n` ⇒ `ρ ≤ specMax` (no sign condition on `ρ` needed). -/
theorem specMax_ge_of_trace_bounds (S : SpectralModel) (n : Nat) (hn : 0 < n) (ρ A B : Q')
    (hBpos : (0 : Q') < B) (hA : A ≤ excitedTrace S (2 * n)) (hB : excitedTrace S n ≤ B)
    (hρAB : ρ ^ n * B ≤ A) : ρ ≤ specMax S := by
  have h := Q'.le_trans' _ _ _ hρAB (specMax_pow_mul_ge S n A B hA hB)
  have h' : ρ ^ n ≤ specMax S ^ n :=
    Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))) hBpos
  exact le_of_pow_le_pow _ _ (specMax_nonneg S) n hn h'

/-- **PROVED (certified rate interval).** Rational trace bounds
`A ≤ s_{2n}`, `s_n ≤ B ≤ ρhi^n`, `ρlo^n·B ≤ A` (`0 < B`, `0 ≤ ρhi`, `0 < n`) locate
`ρlo ≤ specMax ≤ ρhi`. -/
theorem specMax_mem_of_trace_bounds (S : SpectralModel) (n : Nat) (hn : 0 < n)
    (ρlo ρhi A B : Q') (hBpos : (0 : Q') < B) (hρhi : (0 : Q') ≤ ρhi)
    (hA : A ≤ excitedTrace S (2 * n)) (hB : excitedTrace S n ≤ B)
    (hlo : ρlo ^ n * B ≤ A) (hhi : B ≤ ρhi ^ n) :
    ρlo ≤ specMax S ∧ specMax S ≤ ρhi :=
  ⟨specMax_ge_of_trace_bounds S n hn ρlo A B hBpos hA hB hlo,
    specMax_le_of_trace_le S n hn B ρhi hρhi hB hhi⟩

end YMGap.Continuum.SpectralTraceSandwich

#print axioms YMGap.Continuum.SpectralTraceSandwich.specMax_pow_le_excitedTrace
#print axioms YMGap.Continuum.SpectralTraceSandwich.excitedTrace_double_le
#print axioms YMGap.Continuum.SpectralTraceSandwich.le_of_pow_le_pow
#print axioms YMGap.Continuum.SpectralTraceSandwich.specMax_le_of_trace_le
#print axioms YMGap.Continuum.SpectralTraceSandwich.specMax_pow_mul_ge
#print axioms YMGap.Continuum.SpectralTraceSandwich.specMax_pow_ge_of_ratio
#print axioms YMGap.Continuum.SpectralTraceSandwich.specMax_ge_of_trace_bounds
#print axioms YMGap.Continuum.SpectralTraceSandwich.specMax_mem_of_trace_bounds
