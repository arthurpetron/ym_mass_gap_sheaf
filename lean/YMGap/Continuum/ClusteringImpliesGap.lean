/-
Clustering ⇒ spectral gap — the CONVERSE direction (the operator direction the
thermodynamic limit needs), at the finite `SpectralModel` level.

# Why this module exists

`Continuum/SpectralGap.lean` proves the FORWARD direction
(`decay_of_spectralGap_corr0`): a spectral gap (`λᵢ ≤ μ` for all modes) forces
the connected two-point function to decay geometrically,
`G(n) ≤ G(0)·μ^n`.  The physically load-bearing direction is the CONVERSE:
exponential CLUSTERING of the connected correlator forces a spectral gap.
This module discharges that converse over the finite positive Källén–Lehmann
model.

# The math (a clean moment / spectral-radius argument)

With `corr S n = Σ_{i<k} wᵢ·λᵢ^n`, `wᵢ, λᵢ ≥ 0`, suppose CLUSTERING:

    ∀ n, corr S n ≤ C·μ^n      (C > 0, 0 < μ).

Claim: every COUPLED eigenvalue is `≤ μ` — `∀ i, wᵢ > 0 → λᵢ ≤ μ`.

Proof (by contradiction, constructive).  Suppose `λⱼ > μ` with `wⱼ > 0`.
Write `λⱼ = μ + d`, `d := λⱼ − μ > 0`.  Since all terms are nonnegative,
`corr S n ≥ wⱼ·λⱼ^n` (single-term lower bound).  A division-free Bernoulli
bound gives `(μ+d)^(m+1) ≥ μ^(m+1) + (m+1)·d·μ^m ≥ (m+1)·d·μ^m`, so

    wⱼ·λⱼ^(m+1) ≥ wⱼ·(m+1)·d·μ^m.

By the Archimedean property pick `m` with `C·μ < wⱼ·(m+1)·d`; multiplying by
`μ^m > 0` gives `wⱼ·(m+1)·d·μ^m > C·μ·μ^m = C·μ^(m+1)`.  Hence
`corr S (m+1) > C·μ^(m+1)`, contradicting clustering.  The `μ^m` factor
CANCELS — no rational division is ever formed.

Everything is axiom-clean (`propext` / `Quot.sound` only), pure `Q'`/`Nat`,
reusing the `SpectralModel`/`corr` datum and the `LocatedSpectralGap` witness.

# Scope (no overstatement)

This is the ABSTRACT `SpectralModel` clustering⇒gap converse — the operator
direction at the spectral-datum level.  Connecting `corr` to a genuine Wilson
correlator is a separate obligation.  This is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` (and `Quot.sound` where `Nat`/`omega`
arithmetic enters) only.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.ClusterGapReduction
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CubeRoot
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.ClusteringImpliesGap

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap

/-! ## Small `Q'` strict-order / `eqv` / multiplicative helpers (self-contained) -/

/-- `a < b → b ≤ c → a < c` on `Q'` (mirror of `Q'.lt_of_le_of_lt`). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int))
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int))
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-- Strict `<` is irreflexive on `Q'`. -/
theorem lt_irrefl' (a : Q') (h : a < a) : False := by
  have : a.num * (a.den : Int) < a.num * (a.den : Int) := h
  exact (Int.lt_irrefl _) this

/-- Strict right multiplication by a positive factor: `0 < c → a < b → a*c < b*c`. -/
theorem mul_lt_mul_of_pos_right {a b c : Q'} (hc : (0 : Q') < c) (hab : a < b) :
    a * c < b * c :=
  lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv a c))
      (Q'.mul_lt_mul_of_pos_left hc hab))
    (Q'.le_of_eqv (Q'.mul_comm_eqv c b))

/-- `μ < λ → 0 < λ − μ` (positivity of the gap excess). -/
theorem sub_pos_of_lt {μ lam : Q'} (h : μ < lam) : (0 : Q') < lam - μ := by
  apply CReal.pos_of_num_pos
  -- (lam - μ).num = lam.num·μ.den + (-μ).num·lam.den = lam.num·μ.den − μ.num·lam.den
  have hμlt : μ.num * (lam.den : Int) < lam.num * (μ.den : Int) := h
  show (0 : Int) < (lam - μ).num
  show (0 : Int) < lam.num * (μ.den : Int) + (-μ).num * (lam.den : Int)
  have hneg : (-μ).num * (lam.den : Int) = -(μ.num * (lam.den : Int)) := by
    show (-μ.num) * (lam.den : Int) = -(μ.num * (lam.den : Int))
    rw [Int.neg_mul]
  rw [hneg]
  omega

/-- Combined additive congruence: `a ≃ b → c ≃ d → a+c ≃ b+d`. -/
theorem add_eqv_both {a b c d : Q'} (h1 : a.eqv b) (h2 : c.eqv d) :
    (a + c).eqv (b + d) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a b c h1)
    (Q'.add_eqv_congr_left b c d h2)

/-- `a·(b·c) ≃ b·(a·c)` (commute the outer-left factor inside). -/
theorem mul_comm_assoc (a b c : Q') : (a * (b * c)).eqv (b * (a * c)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (a * b) (b * a) c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-- `(1:Q')·a ≃ a` (alias of `one_mul_eqv`). -/
theorem one_mul' (a : Q') : ((1 : Q') * a).eqv a := Q'.one_mul_eqv a

/-- `μ^0 ≃ 1`. -/
theorem pow_zero_eqv (q : Q') : (q ^ 0).eqv (1 : Q') := by
  rw [Q'.pow_zero]; exact Q'.eqv_refl 1

/-- `q^1 ≃ q`. -/
theorem pow_one_eqv (q : Q') : (q ^ 1).eqv q :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left q (q ^ 0) 1 (pow_zero_eqv q)) (Q'.mul_one_eqv q)

/-- Powers respect `eqv`: `a ≃ b → a^n ≃ b^n`.  Induction on `n`. -/
theorem pow_eqv_congr (a b : Q') (h : a.eqv b) : ∀ n : Nat, (a ^ n).eqv (b ^ n)
  | 0 => Q'.eqv_trans _ _ _ (pow_zero_eqv a) (Q'.eqv_symm (pow_zero_eqv b))
  | n + 1 => by
      show (a * a ^ n).eqv (b * b ^ n)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b (a ^ n) h)
        (Q'.mul_eqv_congr_left b (a ^ n) (b ^ n) (pow_eqv_congr a b h n))

/-- `q^n > 0` when `q > 0`.  Induction on `n`. -/
theorem pow_pos {q : Q'} (h : (0 : Q') < q) : ∀ n : Nat, (0 : Q') < q ^ n
  | 0 => by
      show (0 : Q') < (1 : Q')
      exact CReal.pos_of_num_pos (by decide)
  | n + 1 => by
      show (0 : Q') < q * q ^ n
      exact Q'.mul_pos h (pow_pos h n)

/-! ## A positive Archimedean existence: `∃ m, A < (m+1)·B`

Given any `A` and a positive `B`, some integer multiple `(m+1)·B` exceeds `A`.
This is the rational Archimedean principle in the form the growth argument
needs (it provides the explicit large exponent).  The cross-product reduces to
`P < (m+1)·Q` for `P := A.num·B.den`, `Q := B.num·A.den > 0`; take `m :=
P.toNat`, using `Q ≥ 1` and `P ≤ ↑P.toNat`. -/
/-- Pure-`Int` core of the positive Archimedean step: for `1 ≤ Q`,
`P < (↑P.toNat + 1)·Q`.  Take the explicit witness `P.toNat`. -/
theorem int_succ_mul_gt (P Q : Int) (hQ1 : (1 : Int) ≤ Q) :
    P < ((P.toNat : Int) + 1) * Q := by
  have hPle : P ≤ (P.toNat : Int) := Int.self_le_toNat P
  have hm1 : (0 : Int) ≤ (P.toNat : Int) + 1 := by
    have : (0 : Int) ≤ (P.toNat : Int) := Int.natCast_nonneg _
    omega
  have hmul : ((P.toNat : Int) + 1) * (1 : Int)
      ≤ ((P.toNat : Int) + 1) * Q :=
    Int.mul_le_mul_of_nonneg_left hQ1 hm1
  rw [Int.mul_one] at hmul
  omega

theorem exists_succ_mul_gt (A B : Q') (hB : (0 : Q') < B) :
    ∃ m : Nat, A < (Q'.ofNat (m + 1)) * B := by
  have hBnum : (0 : Int) < B.num := Q'.num_pos_of_pos hB
  have hAden : (0 : Int) < (A.den : Int) := by exact_mod_cast A.den_pos
  have hQpos : (0 : Int) < B.num * (A.den : Int) := Int.mul_pos hBnum hAden
  have hQ1 : (1 : Int) ≤ B.num * (A.den : Int) := hQpos
  refine ⟨(A.num * (B.den : Int)).toNat, ?_⟩
  show A.num * ((Q'.ofNat ((A.num * (B.den : Int)).toNat + 1) * B).den : Int)
      < (Q'.ofNat ((A.num * (B.den : Int)).toNat + 1) * B).num * (A.den : Int)
  have hden :
      ((Q'.ofNat ((A.num * (B.den : Int)).toNat + 1) * B).den : Int) = (B.den : Int) := by
    rw [Q'.mul_den_cast]
    show ((Q'.ofNat ((A.num * (B.den : Int)).toNat + 1)).den : Int) * (B.den : Int)
        = (B.den : Int)
    have h1 : ((Q'.ofNat ((A.num * (B.den : Int)).toNat + 1)).den : Int) = (1 : Int) := by
      show (((0 : Nat) + 1 : Nat) : Int) = (1 : Int); decide
    rw [h1, Int.one_mul]
  have hnum : (Q'.ofNat ((A.num * (B.den : Int)).toNat + 1) * B).num
      = (((A.num * (B.den : Int)).toNat : Int) + 1) * B.num := by
    -- (ofNat k).num = Int.ofNat k definitionally, and Int.ofNat (j+1) = ↑j + 1.
    show (Int.ofNat ((A.num * (B.den : Int)).toNat + 1)) * B.num
        = (((A.num * (B.den : Int)).toNat : Int) + 1) * B.num
    congr 1
  rw [hden, hnum]
  -- Goal: A.num·B.den < (↑P.toNat + 1)·B.num · A.den, with P = A.num·B.den.
  -- Regroup the RHS to (↑P.toNat + 1)·(B.num·A.den) and apply the Int core.
  have hregroup :
      (((A.num * (B.den : Int)).toNat : Int) + 1) * B.num * (A.den : Int)
      = (((A.num * (B.den : Int)).toNat : Int) + 1) * (B.num * (A.den : Int)) := by
    rw [Int.mul_assoc]
  rw [hregroup]
  exact int_succ_mul_gt (A.num * (B.den : Int)) (B.num * (A.den : Int)) hQ1

/-! ## Division-free Bernoulli lower bound -/

/-- **Bernoulli (division-free, shifted).**  For `0 ≤ μ`, `0 ≤ d`:

    (μ + d)^(m+1)  ≥  μ^(m+1) + (m+1)·d·μ^m.

Proved by induction on `m`.  The inductive step expands `(μ+d)·(…)` only as far
as `μ·(…) + d·μ^(m+1)`, dropping the nonnegative cross term `d·((m+1)·d·μ^m)`
and matching the new linear coefficient by commutativity. -/
theorem bernoulli_lower (μ d : Q') (hμ : (0 : Q') ≤ μ) (hd : (0 : Q') ≤ d) :
    ∀ m : Nat,
      μ ^ (m + 1) + (Q'.ofNat (m + 1)) * (d * μ ^ m) ≤ (μ + d) ^ (m + 1)
  | 0 => by
      show μ ^ 1 + (Q'.ofNat 1) * (d * μ ^ 0) ≤ (μ + d) ^ 1
      have e1 : (μ ^ 1 + (Q'.ofNat 1) * (d * μ ^ 0)).eqv (μ + d) := by
        have hrt : ((Q'.ofNat 1) * (d * μ ^ 0)).eqv d := by
          refine Q'.eqv_trans _ _ _ (one_mul' (d * μ ^ 0)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left d (μ ^ 0) 1 (pow_zero_eqv μ)) ?_
          exact Q'.mul_one_eqv d
        exact add_eqv_both (pow_one_eqv μ) hrt
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.ge_of_eqv (pow_one_eqv (μ + d)))
  | m + 1 => by
      have ih := bernoulli_lower μ d hμ hd m
      have hμd : (0 : Q') ≤ μ + d := Q'.zero_le_add μ d hμ hd
      -- abbreviations (plain `let`; `set` is a Mathlib tactic, unavailable here)
      let A : Q' := μ ^ (m + 1)
      let T : Q' := (Q'.ofNat (m + 1)) * (d * μ ^ m)
      have hT_nn : (0 : Q') ≤ T :=
        Q'.mul_nonneg _ _
          (Q'.le_of_lt (Q'.ofNat_succ_pos m))
          (Q'.mul_nonneg d (μ ^ m) hd (Q'.pow_nonneg μ hμ m))
      -- Step 1: (μ+d)^(m+2) ≥ (μ+d)·(A + T)  [mul nonneg left on IH]
      have step1 : (μ + d) * (A + T) ≤ (μ + d) ^ (m + 2) :=
        Q'.mul_le_mul_of_nonneg_left _ _ (μ + d) ih hμd
      -- Step 2: (μ+d)·(A+T) ≥ μ·(A+T) + d·A   [drop d·T ≥ 0]
      have step2 : μ * (A + T) + d * A ≤ (μ + d) * (A + T) := by
        have hdist : ((μ + d) * (A + T)).eqv (μ * (A + T) + d * (A + T)) := by
          refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (μ + d) (A + T)) ?_
          refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (A + T) μ d) ?_
          exact add_eqv_both (Q'.mul_comm_eqv (A + T) μ) (Q'.mul_comm_eqv (A + T) d)
        have hdAT : d * A ≤ d * (A + T) :=
          Q'.mul_le_mul_of_nonneg_left A (A + T) d
            (Q'.add_le_self_of_nonneg A T hT_nn) hd
        have hge : μ * (A + T) + d * A ≤ μ * (A + T) + d * (A + T) :=
          Q'.add_le_add_left (μ * (A + T)) (d * A) (d * (A + T)) hdAT
        exact Q'.le_trans' _ _ _ hge (Q'.ge_of_eqv hdist)
      -- target LHS ≃ μ·A + μ·T + d·A
      have hμA : (μ * A).eqv (μ ^ (m + 2)) := Q'.eqv_refl _
      have hμT : (μ * T).eqv ((Q'.ofNat (m + 1)) * (d * μ ^ (m + 1))) := by
        -- μ·(N1·(d·μ^m)) ≃ N1·(μ·(d·μ^m)) ≃ N1·(d·(μ·μ^m)) = N1·(d·μ^(m+1))
        refine Q'.eqv_trans _ _ _
          (mul_comm_assoc μ (Q'.ofNat (m + 1)) (d * μ ^ m)) ?_
        refine Q'.mul_eqv_congr_left (Q'.ofNat (m + 1)) (μ * (d * μ ^ m))
          (d * μ ^ (m + 1)) ?_
        exact mul_comm_assoc μ d (μ ^ m)
      have hLHS :
          (μ ^ (m + 1 + 1) + (Q'.ofNat (m + 1 + 1)) * (d * μ ^ (m + 1))).eqv
            (μ * A + μ * T + d * A) := by
        have hdA : (d * A).eqv (d * μ ^ (m + 1)) := Q'.eqv_refl _
        have hsplit :
            ((Q'.ofNat (m + 1 + 1)) * (d * μ ^ (m + 1))).eqv
              ((Q'.ofNat (m + 1)) * (d * μ ^ (m + 1)) + d * μ ^ (m + 1)) := by
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (Q'.ofNat (m + 1 + 1))
              (Q'.ofNat (m + 1) + Q'.ofNat 1) (d * μ ^ (m + 1))
              (Q'.ofNat_add_eqv (m + 1) 1)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_comm_eqv (Q'.ofNat (m + 1) + Q'.ofNat 1) (d * μ ^ (m + 1))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_add_eqv (d * μ ^ (m + 1)) (Q'.ofNat (m + 1)) (Q'.ofNat 1)) ?_
          refine add_eqv_both (Q'.mul_comm_eqv (d * μ ^ (m + 1)) (Q'.ofNat (m + 1)))
            ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_comm_eqv (d * μ ^ (m + 1)) (Q'.ofNat 1)) ?_
          -- ofNat 1 ≃ 1, then 1·X ≃ X
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (Q'.ofNat 1) (1 : Q') (d * μ ^ (m + 1))
              (by decide)) ?_
          exact one_mul' (d * μ ^ (m + 1))
        refine Q'.eqv_trans _ _ _
          (add_eqv_both (Q'.eqv_refl (μ ^ (m + 1 + 1))) hsplit) ?_
        refine Q'.eqv_trans _ _ _
          (add_eqv_both (Q'.eqv_symm hμA)
            (add_eqv_both (Q'.eqv_symm hμT) (Q'.eqv_symm hdA))) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv (μ * A) (μ * T) (d * A))
      have hμAT : (μ * (A + T)).eqv (μ * A + μ * T) := Q'.mul_add_eqv μ A T
      have chain1 :
          (μ ^ (m + 1 + 1) + (Q'.ofNat (m + 1 + 1)) * (d * μ ^ (m + 1)))
            ≤ μ * (A + T) + d * A := by
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
        exact Q'.add_le_add_right (μ * A + μ * T) (μ * (A + T)) (d * A)
          (Q'.ge_of_eqv hμAT)
      show μ ^ (m + 1 + 1) + (Q'.ofNat (m + 1 + 1)) * (d * μ ^ (m + 1))
          ≤ (μ + d) ^ (m + 1 + 1)
      exact Q'.le_trans' _ _ _ chain1 (Q'.le_trans' _ _ _ step2 step1)

/-- **Bernoulli corollary (the growth lower bound used downstream).**  Dropping
the nonnegative `μ^(m+1)` term:

    (μ + d)^(m+1)  ≥  (m+1)·d·μ^m. -/
theorem pow_ge_linear (μ d : Q') (hμ : (0 : Q') ≤ μ) (hd : (0 : Q') ≤ d) (m : Nat) :
    (Q'.ofNat (m + 1)) * (d * μ ^ m) ≤ (μ + d) ^ (m + 1) := by
  refine Q'.le_trans' _ _ _ ?_ (bernoulli_lower μ d hμ hd m)
  have hμp : (0 : Q') ≤ μ ^ (m + 1) := Q'.pow_nonneg μ hμ (m + 1)
  -- N1·(d·μ^m) ≃ 0 + N1·(d·μ^m) ≤ μ^(m+1) + N1·(d·μ^m)
  have he : ((Q'.ofNat (m + 1)) * (d * μ ^ m)).eqv
      ((0 : Q') + (Q'.ofNat (m + 1)) * (d * μ ^ m)) :=
    Q'.eqv_of_eq (by rw [Q'.zero_add'])
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  exact Q'.add_le_add_right (0 : Q') (μ ^ (m + 1))
    ((Q'.ofNat (m + 1)) * (d * μ ^ m)) hμp

/-! ## Single-term lower bound on `corr` -/

/-- A single nonnegative term is `≤` the `finSum` of nonnegative terms. -/
theorem finSum_ge_single (f : QSeq) (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ k j, j < k → f j ≤ finSum f k
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, j, hj => by
      show f j ≤ finSum f k + f k
      rcases Nat.lt_or_ge j k with hjk | hjk
      · exact Q'.le_trans' _ _ _ (finSum_ge_single f hf k j hjk)
          (Q'.add_le_self_of_nonneg (finSum f k) (f k) (hf k))
      · have hjeq : j = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hjk
        subst hjeq
        have hfin_nn : (0 : Q') ≤ finSum f j := by
          clear hj hjk
          induction j with
          | zero => exact Q'.le_refl' 0
          | succ n ih =>
              show (0 : Q') ≤ finSum f n + f n
              exact Q'.zero_le_add _ _ ih (hf n)
        have he : (f j).eqv ((0 : Q') + f j) := Q'.eqv_of_eq (by rw [Q'.zero_add'])
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
        exact Q'.add_le_add_right (0 : Q') (finSum f j) (f j) hfin_nn

/-- **Single-term lower bound on the correlator.**  For any coupled mode
`j < k`, the connected correlator dominates that mode's contribution:
`wⱼ·λⱼ^n ≤ corr S n`. -/
theorem corr_ge_term (S : SpectralModel) (n : Nat) (j : Nat) (hj : j < S.k) :
    S.w j * (S.lam j) ^ n ≤ corr S n :=
  finSum_ge_single (fun i => S.w i * (S.lam i) ^ n)
    (fun i => Q'.mul_nonneg _ _ (S.w_nonneg i) (Q'.pow_nonneg (S.lam i) (S.lam_nonneg i) n))
    S.k j hj

/-! ## The geometric-growth contradiction -/

/-- **Geometric growth beats any geometric envelope.**  If `λ = μ + d` with
`μ > 0`, `d > 0`, and `w > 0`, `C > 0`, then for some `n` the single mode
`w·λ^n` strictly exceeds the envelope `C·μ^n`.  (This is the engine of the
converse: `corr ≥ w·λ^n > C·μ^n` contradicts clustering.) -/
theorem term_exceeds_envelope (w C μ d : Q')
    (hw : (0 : Q') < w) (_hC : (0 : Q') < C) (hμ : (0 : Q') < μ) (hd : (0 : Q') < d) :
    ∃ n : Nat, C * μ ^ n < w * (μ + d) ^ n := by
  have hwd : (0 : Q') < w * d := Q'.mul_pos hw hd
  obtain ⟨m, hm⟩ := exists_succ_mul_gt (C * μ) (w * d) hwd
  refine ⟨m + 1, ?_⟩
  have hμm : (0 : Q') < μ ^ m := pow_pos hμ m
  have hstrict :
      (C * μ) * μ ^ m < (Q'.ofNat (m + 1) * (w * d)) * μ ^ m :=
    mul_lt_mul_of_pos_right hμm hm
  have hLHS : ((C * μ) * μ ^ m).eqv (C * μ ^ (m + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv C μ (μ ^ m)) ?_
    exact Q'.eqv_refl (C * μ ^ (m + 1))
  have hRHS_eqv :
      ((Q'.ofNat (m + 1) * (w * d)) * μ ^ m).eqv
        (w * (Q'.ofNat (m + 1) * (d * μ ^ m))) := by
    -- (N1·(w·d))·μ^m ≃ N1·((w·d)·μ^m) ≃ N1·(w·(d·μ^m)) ≃ w·(N1·(d·μ^m))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (m + 1)) (w * d) (μ ^ m)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (m + 1)) ((w * d) * μ ^ m) (w * (d * μ ^ m))
        (Q'.mul_assoc_eqv w d (μ ^ m))) ?_
    exact mul_comm_assoc (Q'.ofNat (m + 1)) w (d * μ ^ m)
  have hbern : w * (Q'.ofNat (m + 1) * (d * μ ^ m)) ≤ w * (μ + d) ^ (m + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ w
      (pow_ge_linear μ d (Q'.le_of_lt hμ) (Q'.le_of_lt hd) m) (Q'.le_of_lt hw)
  have hRHS_le :
      (Q'.ofNat (m + 1) * (w * d)) * μ ^ m ≤ w * (μ + d) ^ (m + 1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hRHS_eqv) hbern
  exact lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.ge_of_eqv hLHS) hstrict)
    hRHS_le

/-! ## The converse: clustering ⇒ spectral gap bound -/

/-- **Clustering ⇒ coupled-mode bound (THE converse, honest per-mode form).**

Given clustering `∀ n, corr S n ≤ C·μ^n` with `C > 0`, `μ > 0`, every COUPLED
eigenvalue is `≤ μ`: for each mode `i < k` with positive weight `wᵢ > 0`,
`λᵢ ≤ μ`.  This is the fully honest content — modes with `wᵢ = 0` carry no
spectral content and are not (and cannot be) constrained by `corr`.

Proof: by contradiction via the single-term lower bound (`corr_ge_term`) and the
geometric-growth lemma (`term_exceeds_envelope`).  If some coupled `λⱼ > μ`,
write `λⱼ = μ + d` with `d > 0`; some `n` makes `wⱼ·λⱼ^n > C·μ^n`, but
`corr S n ≥ wⱼ·λⱼ^n` and clustering gives `corr S n ≤ C·μ^n` — contradiction. -/
theorem clustering_implies_coupled_le
    (S : SpectralModel) (C μ : Q') (hC : (0 : Q') < C) (hμ : (0 : Q') < μ)
    (hcluster : ∀ n, corr S n ≤ C * μ ^ n) :
    ∀ i, i < S.k → (0 : Q') < S.w i → S.lam i ≤ μ := by
  intro j hj hwj
  by_cases hle : S.lam j ≤ μ
  · exact hle
  · exfalso
    have hlt : μ < S.lam j := by
      show μ.num * ((S.lam j).den : Int) < (S.lam j).num * (μ.den : Int)
      have h' : ¬ ((S.lam j).num * (μ.den : Int) ≤ μ.num * ((S.lam j).den : Int)) := hle
      exact Int.not_le.mp h'
    -- d := λⱼ − μ = λⱼ + (−μ) (definitionally); 0 < d and μ + d ≃ λⱼ.
    let d : Q' := S.lam j - μ
    have hdpos : (0 : Q') < d := sub_pos_of_lt hlt
    -- add_sub_cancel_eqv : (S.lam j).eqv (μ + (S.lam j + −μ)); μ + d is defeq.
    have hsum : (μ + d).eqv (S.lam j) :=
      Q'.eqv_symm (Q'.add_sub_cancel_eqv (S.lam j) μ)
    obtain ⟨n, hn⟩ := term_exceeds_envelope (S.w j) C μ d hwj hC hμ hdpos
    have hpow_eqv : ((μ + d) ^ n).eqv ((S.lam j) ^ n) :=
      pow_eqv_congr (μ + d) (S.lam j) hsum n
    have hn' : C * μ ^ n < S.w j * (S.lam j) ^ n :=
      lt_of_lt_of_le hn
        (Q'.mul_le_mul_of_nonneg_left _ _ (S.w j)
          (Q'.le_of_eqv hpow_eqv) (Q'.le_of_lt hwj))
    have hge : S.w j * (S.lam j) ^ n ≤ corr S n := corr_ge_term S n j hj
    have hcontr : C * μ ^ n < C * μ ^ n :=
      lt_of_lt_of_le (lt_of_lt_of_le hn' hge) (hcluster n)
    exact lt_irrefl' _ hcontr

/-- **Clustering ⇒ `SpectralGapBound` (global form).**

To obtain the GLOBAL `SpectralGapBound S μ` (`∀ i, λᵢ ≤ μ`, quantified over ALL
indices) from clustering, two honest hypotheses are needed beyond clustering:

  * `hw` — per-mode coupling on the LIVE modes (`i < k ⇒ wᵢ > 0`): clustering
    constrains exactly the coupled live modes;
  * `hdead` — a bound on the UNUSED slots (`k ≤ i ⇒ λᵢ ≤ μ`): `corr` reads only
    `i < k`, so indices `i ≥ k` carry no spectral content and clustering says
    nothing about them.  This is the honest residual obligation for the
    convention that `lam : QSeq` is a total sequence whose tail past `k` is
    unused.  (At a concrete finite model the tail is set to `0 ≤ μ`, discharging
    `hdead` by `lam_nonneg`/`decide`.)

The live-mode content is `clustering_implies_coupled_le`; this packages it with
`hdead` into the global predicate. -/
theorem clustering_implies_gapBound
    (S : SpectralModel) (C μ : Q') (hC : (0 : Q') < C) (hμ : (0 : Q') < μ)
    (hcluster : ∀ n, corr S n ≤ C * μ ^ n)
    (hw : ∀ i, i < S.k → (0 : Q') < S.w i)
    (hdead : ∀ i, S.k ≤ i → S.lam i ≤ μ) :
    SpectralGapBound S μ := by
  intro i
  by_cases hik : i < S.k
  · exact clustering_implies_coupled_le S C μ hC hμ hcluster i hik (hw i hik)
  · exact hdead i (Nat.not_lt.mp hik)

/-! ## To the located gap (clustering ⇒ located gap at `sep = μ < 1`) -/

/-- **Clustering ⇒ located spectral gap (`sep = μ`).**

If additionally `μ < 1`, the derived `SpectralGapBound` packages as a genuine
`LocatedSpectralGap S` with `sep = μ` — the clustering ⇒ located-gap converse at
the compact (finite) transfer-operator level.  `sep_lt_one` is the clustering
rate `μ < 1`; `bound` is the derived gap.  Combined with
`LocatedSpectralGap.located`, the located top-of-spectrum `specMax S ≤ μ` is a
single decidable comparison.

Hypotheses are as in `clustering_implies_gapBound` (per-mode coupling `hw` on
live modes, the unused-slot bound `hdead`). -/
def clustering_implies_located
    (S : SpectralModel) (C μ : Q') (hC : (0 : Q') < C) (hμ : (0 : Q') < μ)
    (hμ1 : μ < (1 : Q'))
    (hcluster : ∀ n, corr S n ≤ C * μ ^ n)
    (hw : ∀ i, i < S.k → (0 : Q') < S.w i)
    (hdead : ∀ i, S.k ≤ i → S.lam i ≤ μ) :
    LocatedSpectralGap S where
  sep := μ
  sep_lt_one := hμ1
  bound := clustering_implies_gapBound S C μ hC hμ hcluster hw hdead

/-! ## Bridge to `ClusterGapReduction.UniformClusterBound`

`UniformClusterBound` (the single open input of the thermodynamic limit) carries
a `located : (Λ : Nat) → LocatedSpectralGap (gaps Λ)` field, which it currently
takes as SUPPLIED data.  The converse above lets that field be DERIVED from a
per-volume clustering hypothesis: given a family of finite spectral models
`gaps`, per-volume clustering rates `(C Λ, μ Λ)` with `μ Λ < 1`, and the coupling
/ unused-slot side conditions, the located gaps follow.

This `def` EXPOSES that bridge (it produces exactly the `located` field's type)
WITHOUT inhabiting `UniformClusterBound` — the remaining fields (`floorRate`,
the geometric single-step `incr_*`, the `modulus`) are separate volume-uniform
analytic content, not produced here. -/
def locatedFamily_of_clustering
    (gaps : Nat → SpectralModel)
    (C μ : Nat → Q')
    (hC : ∀ Λ, (0 : Q') < C Λ) (hμ : ∀ Λ, (0 : Q') < μ Λ)
    (hμ1 : ∀ Λ, μ Λ < (1 : Q'))
    (hcluster : ∀ Λ n, corr (gaps Λ) n ≤ C Λ * (μ Λ) ^ n)
    (hw : ∀ Λ i, i < (gaps Λ).k → (0 : Q') < (gaps Λ).w i)
    (hdead : ∀ Λ i, (gaps Λ).k ≤ i → (gaps Λ).lam i ≤ μ Λ) :
    (Λ : Nat) → LocatedSpectralGap (gaps Λ) :=
  fun Λ => clustering_implies_located (gaps Λ) (C Λ) (μ Λ)
    (hC Λ) (hμ Λ) (hμ1 Λ) (hcluster Λ) (hw Λ) (hdead Λ)

end YMGap.Continuum.ClusteringImpliesGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
#print axioms YMGap.Continuum.ClusteringImpliesGap.lt_irrefl'
#print axioms YMGap.Continuum.ClusteringImpliesGap.sub_pos_of_lt
#print axioms YMGap.Continuum.ClusteringImpliesGap.pow_eqv_congr
#print axioms YMGap.Continuum.ClusteringImpliesGap.pow_pos
#print axioms YMGap.Continuum.ClusteringImpliesGap.exists_succ_mul_gt
#print axioms YMGap.Continuum.ClusteringImpliesGap.bernoulli_lower
#print axioms YMGap.Continuum.ClusteringImpliesGap.pow_ge_linear
#print axioms YMGap.Continuum.ClusteringImpliesGap.finSum_ge_single
#print axioms YMGap.Continuum.ClusteringImpliesGap.corr_ge_term
#print axioms YMGap.Continuum.ClusteringImpliesGap.term_exceeds_envelope
#print axioms YMGap.Continuum.ClusteringImpliesGap.clustering_implies_coupled_le
#print axioms YMGap.Continuum.ClusteringImpliesGap.clustering_implies_gapBound
#print axioms YMGap.Continuum.ClusteringImpliesGap.clustering_implies_located
#print axioms YMGap.Continuum.ClusteringImpliesGap.locatedFamily_of_clustering
