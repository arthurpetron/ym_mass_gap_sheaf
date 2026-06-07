/-
The geometric-growth kernel `pow_dominates` for F.1 (clustering ⇒ gap).

Discharges the hypothesis of `SpectralGapConverse.gap_of_decay_of_growth`:

  pow_dominates : 0<μ → μ<λ → 0<w → 0≤C → ∃ n, C·μ^n < w·λ^n.

Strategy (division-free; `Q'` has no reciprocal; no Mathlib/`ring`):
reduce the `Q'` inequality through the `num/den` representation to a pure
`Nat` geometric-domination fact `nat_geom_dominates`, proved from a `Nat`
Bernoulli bound + elementary `Nat` arithmetic (where `omega` and core
`Nat` lemmas are available).

Built bottom-up; each lemma is axiom-clean (`#print axioms` = `[propext]`
or empty). See `docs/uniform-parametric-bound-plan.md` II.3.
-/

import YMGap.Continuum.SpectralGapConverse

namespace YMGap.Continuum.SpectralGap

open YMGap.Constructive

/-! ## Bite 1 — `Nat` Bernoulli

`p^(n+1) + (n+1)·p^n ≤ (p+1)^(n+1)`: the first two binomial terms of
`(p+1)^(n+1)`. Division-free, proved by induction. -/
theorem nat_bernoulli (p : Nat) (n : Nat) :
    p ^ (n + 1) + (n + 1) * p ^ n ≤ (p + 1) ^ (n + 1) := by
  induction n with
  | zero => simp [Nat.pow_succ]
  | succ n ih =>
      -- Abbreviations and the two power-recurrences.
      have hA : p ^ (n + 1) = p ^ n * p := Nat.pow_succ p n
      have hAA : p ^ (n + 1 + 1) = p ^ (n + 1) * p := Nat.pow_succ p (n + 1)
      -- Exact expansion of (p+1)·(pⁿ⁺¹ + (n+1)·pⁿ), keeping the (n+1+1) form.
      have expand : (p + 1) * (p ^ (n + 1) + (n + 1) * p ^ n)
          = p ^ (n + 1 + 1) + (n + 1 + 1) * p ^ (n + 1) + (n + 1) * p ^ n := by
        rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul,
            Nat.mul_comm p (p ^ (n + 1)), ← hAA,
            Nat.mul_left_comm p (n + 1) (p ^ n), Nat.mul_comm p (p ^ n), ← hA,
            Nat.succ_mul (n + 1) (p ^ (n + 1))]
        omega
      -- Bernoulli is monotone-multiplied by (p+1).
      have hmul : (p + 1) * (p ^ (n + 1) + (n + 1) * p ^ n)
                ≤ (p + 1) * (p + 1) ^ (n + 1) :=
        Nat.mul_le_mul_left (p + 1) ih
      have hpow : (p + 1) * (p + 1) ^ (n + 1) = (p + 1) ^ (n + 1 + 1) := by
        rw [Nat.pow_succ (p + 1) (n + 1), Nat.mul_comm (p + 1) ((p + 1) ^ (n + 1))]
      calc p ^ (n + 1 + 1) + (n + 1 + 1) * p ^ (n + 1)
          ≤ (p + 1) * (p ^ (n + 1) + (n + 1) * p ^ n) := by
            rw [expand]; exact Nat.le_add_right _ _
        _ ≤ (p + 1) * (p + 1) ^ (n + 1) := hmul
        _ = (p + 1) ^ (n + 1 + 1) := hpow

/-! ## Bite 2 — `Nat` geometric domination

`∃ n, a·pⁿ < b·qⁿ` for `0<b`, `0<p<q`: a faster geometric overtakes any
constant multiple of a slower one. Case `a ≤ b` is immediate at `n = 1`;
case `a > b` uses Bernoulli at `n = (a−b)·p + 1`. -/
theorem nat_geom_dominates (a b p q : Nat) (hb : 0 < b) (hp : 0 < p) (hpq : p < q) :
    ∃ n : Nat, a * p ^ n < b * q ^ n := by
  rcases Nat.lt_or_ge b a with hab | hab
  · -- b < a (i.e. a > b) : n = (a-b)*p + 1
    obtain ⟨m, hm⟩ : ∃ m, (a - b) * p = m := ⟨_, rfl⟩
    refine ⟨m + 1, ?_⟩
    have hpm : 0 < p ^ m := Nat.pow_pos hp
    have hbern : p ^ (m + 1) + (m + 1) * p ^ m ≤ q ^ (m + 1) :=
      Nat.le_trans (nat_bernoulli p m) (Nat.pow_le_pow_left hpq (m + 1))
    have hbq : b * (p ^ (m + 1) + (m + 1) * p ^ m) ≤ b * q ^ (m + 1) :=
      Nat.mul_le_mul_left b hbern
    -- factoring equalities
    have e1 : a * p ^ (m + 1) = a * p * p ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm (p ^ m) p, ← Nat.mul_assoc]
    have e2 : b * (p ^ (m + 1) + (m + 1) * p ^ m) = (b * p + b * (m + 1)) * p ^ m := by
      rw [Nat.add_mul (b * p) (b * (m + 1)) (p ^ m),
          Nat.mul_add b (p ^ (m + 1)) ((m + 1) * p ^ m),
          Nat.pow_succ p m, Nat.mul_comm (p ^ m) p,
          ← Nat.mul_assoc b p (p ^ m), ← Nat.mul_assoc b (m + 1) (p ^ m)]
    -- the reduced (factored-out) strict inequality
    have hkey0 : a * p < b * p + b * (m + 1) := by
      have hsplit : a * p = b * p + (a - b) * p := by
        rw [← Nat.add_mul]; congr 1; omega
      have hX : (a - b) * p ≤ b * ((a - b) * p) := Nat.le_mul_of_pos_left _ hb
      have hbm : b * (m + 1) = b * ((a - b) * p) + b := by
        rw [← hm, Nat.mul_add, Nat.mul_one]
      rw [hsplit, hbm]; omega
    have hkey : a * p ^ (m + 1) < b * (p ^ (m + 1) + (m + 1) * p ^ m) := by
      rw [e1, e2]
      exact Nat.mul_lt_mul_of_pos_right hkey0 hpm
    exact Nat.lt_of_lt_of_le hkey hbq
  · -- b ≥ a (i.e. a ≤ b) : n = 1
    have hab' : a ≤ b := hab
    refine ⟨1, ?_⟩
    rw [Nat.pow_one, Nat.pow_one]
    have h1 : a * p ≤ b * p := Nat.mul_le_mul_right p hab'
    have h2 : b * p < b * q := Nat.mul_lt_mul_of_pos_left hpq hb
    exact Nat.lt_of_le_of_lt h1 h2

/-! ## Bite 3 — `Nat` ⇒ `Int` ⇒ `Q'` bridge -/

/-- `Int` geometric domination: cast `nat_geom_dominates` up to `Int`. -/
theorem int_geom_dominates (A B P Q : Int)
    (hA : 0 ≤ A) (hB : 0 < B) (hP : 0 < P) (hPQ : P < Q) :
    ∃ n : Nat, A * P ^ n < B * Q ^ n := by
  obtain ⟨a, ha⟩ : ∃ a : Nat, A = (a : Int) := ⟨A.toNat, (Int.toNat_of_nonneg hA).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : Nat, B = (b : Int) := ⟨B.toNat, (Int.toNat_of_nonneg (Int.le_of_lt hB)).symm⟩
  obtain ⟨p, hp⟩ : ∃ p : Nat, P = (p : Int) := ⟨P.toNat, (Int.toNat_of_nonneg (Int.le_of_lt hP)).symm⟩
  obtain ⟨q, hq⟩ : ∃ q : Nat, Q = (q : Int) :=
    ⟨Q.toNat, (Int.toNat_of_nonneg (Int.le_of_lt (Int.lt_trans hP hPQ))).symm⟩
  have hb0 : 0 < b := by rw [hb] at hB; omega
  have hp0 : 0 < p := by rw [hp] at hP; omega
  have hpq0 : p < q := by rw [hp, hq] at hPQ; omega
  obtain ⟨n, hn⟩ := nat_geom_dominates a b p q hb0 hp0 hpq0
  refine ⟨n, ?_⟩
  rw [ha, hp, hb, hq,
      ← Int.natCast_pow, ← Int.natCast_pow, ← Int.natCast_mul, ← Int.natCast_mul]
  omega

/-- `(q^n).num = q.num^n`. -/
theorem num_pow (q : Q') (n : Nat) : (q ^ n).num = q.num ^ n := by
  induction n with
  | zero => rw [Int.pow_zero]; rfl
  | succ n ih =>
      show q.num * (q ^ n).num = q.num ^ (n + 1)
      rw [ih, Int.pow_succ, Int.mul_comm]

/-- `((q^n).den : Int) = (q.den : Int)^n`. -/
theorem den_cast_pow (q : Q') (n : Nat) : ((q ^ n).den : Int) = (q.den : Int) ^ n := by
  induction n with
  | zero => rw [Int.pow_zero]; rfl
  | succ n ih =>
      rw [show ((q ^ (n + 1)).den : Int) = (q.den : Int) * ((q ^ n).den : Int) from
            Q'.mul_den_cast q (q ^ n), ih, Int.pow_succ, Int.mul_comm]

/-- `(x·y)^n = x^n·y^n` over `Int`. -/
theorem int_mul_pow (x y : Int) (n : Nat) : (x * y) ^ n = x ^ n * y ^ n := by
  induction n with
  | zero => rw [Int.pow_zero, Int.pow_zero, Int.pow_zero, Int.one_mul]
  | succ n ih => rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]; ac_rfl

/-- `0 < a*b` and `0 < b` give `0 < a` (over `Int`). -/
theorem int_pos_left {a b : Int} (hab : 0 < a * b) (hb : 0 < b) : 0 < a := by
  rcases Int.lt_or_le 0 a with h | h
  · exact h
  · exfalso
    have hle : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hb)
    rw [Int.zero_mul] at hle
    exact absurd hab (Int.not_lt.mpr hle)

/-! ## Bite 4 — the kernel `pow_dominates` and the unconditional converse -/

/-- **The geometric-growth kernel.** A faster geometric overtakes any
constant multiple of a slower one: `∃ n, C·μ^n < w·λ^n`. -/
theorem pow_dominates {μ lam w C : Q'}
    (hμ : (0 : Q') < μ) (hlt : μ < lam) (hw : (0 : Q') < w) (hC : (0 : Q') ≤ C) :
    ∃ n : Nat, C * μ ^ n < w * lam ^ n := by
  -- component positivity
  have hμn : 0 < μ.num := (pos_iff_num_pos μ).mp hμ
  have hwn : 0 < w.num := (pos_iff_num_pos w).mp hw
  have hCn : 0 ≤ C.num := (Q'.zero_le_iff_num_nonneg C).mp hC
  have hμd : (0 : Int) < (μ.den : Int) := by have := Q'.den_pos μ; omega
  have hLd : (0 : Int) < (lam.den : Int) := by have := Q'.den_pos lam; omega
  have hwd : (0 : Int) < (w.den : Int) := by have := Q'.den_pos w; omega
  have hCd : (0 : Int) < (C.den : Int) := by have := Q'.den_pos C; omega
  -- μ<λ at the Int level is exactly P < Q
  have hPQ : μ.num * (lam.den : Int) < lam.num * (μ.den : Int) := hlt
  have hPpos : 0 < μ.num * (lam.den : Int) := Int.mul_pos hμn hLd
  have hLn : 0 < lam.num := int_pos_left (Int.lt_trans hPpos hPQ) hμd
  have hQpos : 0 < lam.num * (μ.den : Int) := Int.mul_pos hLn hμd
  have hApos : 0 ≤ C.num * (w.den : Int) := Int.mul_nonneg hCn (Int.le_of_lt hwd)
  have hBpos : 0 < w.num * (C.den : Int) := Int.mul_pos hwn hCd
  obtain ⟨n, hn⟩ := int_geom_dominates (C.num * (w.den : Int)) (w.num * (C.den : Int))
    (μ.num * (lam.den : Int)) (lam.num * (μ.den : Int)) hApos hBpos hPpos hPQ
  refine ⟨n, ?_⟩
  -- unfold the Q' strict inequality and reduce to hn
  show (C * μ ^ n).num * ((w * lam ^ n).den : Int)
      < (w * lam ^ n).num * ((C * μ ^ n).den : Int)
  rw [show (C * μ ^ n).num = C.num * (μ ^ n).num from rfl, num_pow,
      show (w * lam ^ n).num = w.num * (lam ^ n).num from rfl, num_pow,
      Q'.mul_den_cast w (lam ^ n), den_cast_pow,
      Q'.mul_den_cast C (μ ^ n), den_cast_pow]
  -- goal: (C.num*μ.num^n)*(w.den*lam.den^n) < (w.num*lam.num^n)*(C.den*μ.den^n)
  have hL : (C.num * μ.num ^ n) * ((w.den : Int) * (lam.den : Int) ^ n)
          = (C.num * (w.den : Int)) * (μ.num * (lam.den : Int)) ^ n := by
    rw [int_mul_pow]; ac_rfl
  have hR : (w.num * lam.num ^ n) * ((C.den : Int) * (μ.den : Int) ^ n)
          = (w.num * (C.den : Int)) * (lam.num * (μ.den : Int)) ^ n := by
    rw [int_mul_pow]; ac_rfl
  rw [hL, hR]; exact hn

/-- **Clustering ⇒ gap (finite volume), unconditional.** Measured
exponential clustering `corr S n ≤ C·μ^n` forces every populated mode
`λ_j ≤ μ`. This discharges `gap_of_decay_of_growth`'s kernel. -/
theorem gap_of_decay (S : SpectralModel) (C μ : Q')
    (hμ : (0 : Q') < μ) (hC : (0 : Q') ≤ C)
    (hdecay : DecaysAt S C μ) (j : Nat) (hj : j < S.k) (hwj : (0 : Q') < S.w j) :
    S.lam j ≤ μ :=
  gap_of_decay_of_growth S C μ
    (fun w lam hw hlt => pow_dominates hμ hlt hw hC) hdecay j hj hwj

end YMGap.Continuum.SpectralGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpectralGap.nat_bernoulli
#print axioms YMGap.Continuum.SpectralGap.nat_geom_dominates
#print axioms YMGap.Continuum.SpectralGap.int_geom_dominates
#print axioms YMGap.Continuum.SpectralGap.num_pow
#print axioms YMGap.Continuum.SpectralGap.den_cast_pow
#print axioms YMGap.Continuum.SpectralGap.int_mul_pow
#print axioms YMGap.Continuum.SpectralGap.pow_dominates
#print axioms YMGap.Continuum.SpectralGap.gap_of_decay
