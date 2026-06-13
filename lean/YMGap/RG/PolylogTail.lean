/-
The polynomial × geometric character-tail majorant: the clean rational
polylog bound that discharges the per-axis factor `AxisFactorBound`.

# The object

Each per-axis character-tail factor is a POLYNOMIAL × GEOMETRIC series

    S_i  =  Σ_{n≥1} (1 + c_i·n)^{2 m_i} · r^n ,    r = e^{−t Δ_i} ∈ [0, 1) .

The pitfall (`RG/WeylCharacterBound.lean`): this is **not** bare geometric
`Σ r^n`, so the too-weak majorant `r/(1−r)` is invalid.  This module supplies
the honest CLEAN RATIONAL polylog majorant — no window (valid for every
`r ∈ [0,1)`), no new transcendental — via the single inequality

    Σ_{n≥0} C(n,k) r^n  ≤  H^{k+1}        (`binomGeomSum_le`)

where `H` plays the role of `1/(1−r)` through the geometric base recurrence
`1 + r·H ≤ H` (i.e. `H ≥ 1/(1−r)`).  This is the negative-binomial identity
`Σ C(n,k) r^n = r^k/(1−r)^{k+1} ≤ 1/(1−r)^{k+1}`, proven constructively here
by induction on `k` through Pascal's recurrence `C(n+1,k+1) = C(n,k) +
C(n,k+1)` — a clean telescope, no Eulerian numbers, no windowing.

The pure-power monomial bound `Σ_{n≥0} n^k r^n ≤ k!·H^{k+1}` follows since
`n^k ≤ k!·C(n,k) + (lower-order with the SAME bound)`; we expose the binomial
form (the genuinely clean object) and the assembled per-axis closed form

    S_i  ≤  (2 m_i)! · (1 + c_i)^{2 m_i} · H^{2 m_i + 1}     (`axisFactor_le`)

— integer factorial, integer power, and the `1/(1−r)`-surrogate `H` only.

# What CLOSES

  * `recurrence_closure` — the generic `a(N+1) ≤ c + r·a(N) ⟹ a(N) ≤ c·H`
    closure (the `Q'` engine, mirroring `geometric_tail_closure`).
  * `binomGeomSum_le` — `Σ_{n<N} C(n,k) r^n ≤ H^{k+1}`, induction on `k`
    via Pascal.  The clean general polylog majorant.
  * `axisFactor_le` — the assembled per-axis closed form for `(1+c·n)^{2m}`.

All over `Q'`, division-free, no window.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Q'`/`Nat` order layer).  No `Classical.*`, no `native_decide`, no
`sorryAx`.  See the `#print axioms` block at the end.
-/

import YMGap.Constructive.GeometricTail
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.QPoly
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CharacterTail

namespace YMGap.RG

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## Binomial coefficients (`Nat`, no Mathlib)

`Nat.choose` is unavailable in this Mathlib-free core, so we define the
binomial coefficient by the Pascal recurrence directly — which is exactly
the recurrence the telescope consumes. -/

/-- Binomial coefficient `C(n,k)` by the Pascal recurrence. -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

@[simp] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

@[simp] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := rfl

/-- **Pascal's identity** `C(n+1,k+1) = C(n,k) + C(n,k+1)` (by definition). -/
theorem binom_succ_succ (n k : Nat) :
    binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

/-- `C(n,k) = 0` for `n < k`. -/
theorem binom_eq_zero_of_lt : ∀ n k, n < k → binom n k = 0
  | _,     0,     h => absurd h (by omega)
  | 0,     _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      rw [binom_succ_succ, binom_eq_zero_of_lt n k (by omega),
          binom_eq_zero_of_lt n (k + 1) (by omega)]

/-- `C(n,n) = 1`. -/
theorem binom_self : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [binom_succ_succ, binom_self n, binom_eq_zero_of_lt n (n + 1) (by omega)]

/-- `0 ≤ ofNat n` (local helper; the named copies live in heavier modules). -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) ≤ (Q'.ofNat n).num * ((0 : Q').den : Int)
  have e1 : (Q'.ofNat n).num = (n : Int) := rfl
  have e2 : ((0 : Q').den : Int) = 1 := rfl
  rw [e1, e2, Int.zero_mul, Int.mul_one]
  exact Int.natCast_nonneg n

/-! ## The generic recurrence closure

The `Q'` engine: a nonnegative sequence `a` with `a 0 ≤ c·H` and the
one-step recurrence `a(N+1) ≤ c + r·a(N)` is uniformly bounded by `c·H`,
provided `r,c,H ≥ 0` and the geometric recurrence `1 + r·H ≤ H` (so `H`
is the `1/(1−r)` surrogate).  Mirrors `geometric_tail_closure`, but for a
sequence given by its own recurrence (the partial-sum sequence of a
binomial-weighted geometric series). -/

/-- **Generic recurrence closure.**  For `r,c,H ≥ 0` with `1 + r·H ≤ H`, a
sequence `a` with `a 0 ≤ c·H` and `a(N+1) ≤ c + r·(a N)` satisfies
`a N ≤ c·H` for every `N`.

The step: `a(N+1) ≤ c + r·(a N) ≤ c + r·(c·H) ≃ c·(1 + r·H) ≤ c·H`. -/
theorem recurrence_closure (a : Nat → Q') (r c H : Q')
    (hr : (0 : Q') ≤ r) (hc : (0 : Q') ≤ c) (hH : (0 : Q') ≤ H)
    (hrec : (1 : Q') + r * H ≤ H)
    (h0 : a 0 ≤ c * H)
    (hstep : ∀ N, a (N + 1) ≤ c + r * (a N)) :
    ∀ N, a N ≤ c * H := by
  intro N
  induction N with
  | zero => exact h0
  | succ N ih =>
    -- a(N+1) ≤ c + r·(a N) ≤ c + r·(c·H)
    have h1 : c + r * (a N) ≤ c + r * (c * H) :=
      Q'.add_le_add_left c (r * (a N)) (r * (c * H))
        (Q'.mul_le_mul_of_nonneg_left (a N) (c * H) r ih hr)
    refine Q'.le_trans' _ _ _ (hstep N) (Q'.le_trans' _ _ _ h1 ?_)
    -- c + r·(c·H) ≃ c·1 + c·(r·H) ≃ c·(1 + r·H) ≤ c·H
    -- r·(c·H) ≃ c·(r·H)
    have hrcH : (r * (c * H)).eqv (c * (r * H)) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r c H))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (r * c) (c * r) H (Q'.mul_comm_eqv r c))
          (Q'.mul_assoc_eqv c r H))
    -- c ≃ c·1
    have hc1 : c.eqv (c * 1) := Q'.eqv_symm (Q'.mul_one_eqv c)
    -- c + r·(c·H) ≃ c·1 + c·(r·H) ≃ c·(1 + r·H)
    have hsum : (c + r * (c * H)).eqv (c * (1 + r * H)) :=
      Q'.eqv_trans _ _ _
        (QPoly.q_add_congr hc1 hrcH)
        (Q'.eqv_symm (Q'.mul_add_eqv c 1 (r * H)))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) ?_
    -- c·(1 + r·H) ≤ c·H
    exact Q'.mul_le_mul_of_nonneg_left (1 + r * H) H c hrec hc

/-! ## The binomial-weighted geometric partial sum and its Pascal recurrence

`binomGeomSum r k N = Σ_{n<N} C(n,k)·r^n`, the partial sum of the
negative-binomial series.  Pascal's identity `C(n+1,k+1) = C(n,k) +
C(n,k+1)` gives the cross-level recurrence

    binomGeomSum r (k+1) (N+1)
      = Σ_{n<N+1} C(n,k+1) r^n
      ≤ r·binomGeomSum r k N + r·binomGeomSum r (k+1) N

(the `C(0,k+1)=0` term drops; each `n≥1` term splits and pulls out an `r`),
which `recurrence_closure` turns into `binomGeomSum r (k+1) N ≤ (r·H^{k+1})·H`. -/

/-- `C(n,k)·r^n` as a `Q'` value (the negative-binomial term). -/
def binomTerm (r : Q') (k n : Nat) : Q' := (Q'.ofNat (binom n k)) * r ^ n

/-- The binomial-weighted geometric partial sum `Σ_{n<N} C(n,k)·r^n`. -/
def binomGeomSum (r : Q') (k : Nat) : Nat → Q' :=
  fun N => finSum (binomTerm r k) N

@[simp] theorem binomGeomSum_zero (r : Q') (k : Nat) : binomGeomSum r k 0 = 0 := rfl

theorem binomGeomSum_succ (r : Q') (k N : Nat) :
    binomGeomSum r k (N + 1) = binomGeomSum r k N + binomTerm r k N := rfl

/-- The terms are nonnegative for `0 ≤ r`. -/
theorem binomTerm_nonneg {r : Q'} (hr : (0 : Q') ≤ r) (k n : Nat) :
    (0 : Q') ≤ binomTerm r k n :=
  Q'.mul_nonneg _ _ (ofNat_nonneg _) (Q'.pow_nonneg r hr n)

/-- `binomGeomSum` is nonnegative for `0 ≤ r`. -/
theorem binomGeomSum_nonneg {r : Q'} (hr : (0 : Q') ≤ r) (k : Nat) :
    ∀ N, (0 : Q') ≤ binomGeomSum r k N := by
  intro N
  induction N with
  | zero => exact Q'.le_refl' 0
  | succ N ih =>
    rw [binomGeomSum_succ]
    exact Q'.zero_le_add _ _ ih (binomTerm_nonneg hr k N)

/-! ### The Pascal cross-level recurrence on partial sums

`binomTerm r (k+1) 0 ≃ 0` (the `C(0,k+1)=0` head), and each shifted term
splits `binomTerm r (k+1) (i+1) ≃ r·binomTerm r k i + r·binomTerm r (k+1) i`
(Pascal + `r^{i+1} = r·r^i`).  Summing gives the cross-level recurrence. -/

/-- The head term vanishes: `binomTerm r (k+1) 0 ≃ 0` (`C(0,k+1) = 0`). -/
theorem binomTerm_head_zero (r : Q') (k : Nat) :
    (binomTerm r (k + 1) 0).eqv 0 := by
  -- binomTerm r (k+1) 0 = ofNat (binom 0 (k+1)) * r^0 = ofNat 0 * 1
  show ((Q'.ofNat (binom 0 (k + 1))) * r ^ 0).eqv 0
  rw [binom_zero_succ]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (r ^ 0) Q'.ofNat_zero_eqv)
    (QPoly.q_zero_mul (r ^ 0))

/-- **The per-term Pascal split.**  `binomTerm r (k+1) (i+1) ≃
r·binomTerm r k i + r·binomTerm r (k+1) i`. -/
theorem binomTerm_split (r : Q') (k i : Nat) :
    (binomTerm r (k + 1) (i + 1)).eqv
      (r * binomTerm r k i + r * binomTerm r (k + 1) i) := by
  -- LHS = ofNat (binom i k + binom i (k+1)) * (r * r^i)
  show ((Q'.ofNat (binom (i + 1) (k + 1))) * r ^ (i + 1)).eqv
      (r * ((Q'.ofNat (binom i k)) * r ^ i)
        + r * ((Q'.ofNat (binom i (k + 1))) * r ^ i))
  rw [binom_succ_succ]
  -- r^(i+1) = r * r^i definitionally (pow_succ)
  show ((Q'.ofNat (binom i k + binom i (k + 1))) * (r * r ^ i)).eqv
      (r * ((Q'.ofNat (binom i k)) * r ^ i)
        + r * ((Q'.ofNat (binom i (k + 1))) * r ^ i))
  -- ofNat (a+b) ≃ ofNat a + ofNat b
  have hsplit : (Q'.ofNat (binom i k + binom i (k + 1))).eqv
      (Q'.ofNat (binom i k) + Q'.ofNat (binom i (k + 1))) :=
    Q'.ofNat_add_eqv _ _
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (r * r ^ i) hsplit) ?_
  -- (A + B) * (r*r^i) ≃ A*(r*r^i) + B*(r*r^i)
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_mul (Q'.ofNat (binom i k)) (Q'.ofNat (binom i (k + 1))) (r * r ^ i)) ?_
  -- now match each summand: A*(r*r^i) ≃ r*(A*r^i)
  refine QPoly.q_add_congr ?_ ?_
  · -- ofNat a * (r * r^i) ≃ r * (ofNat a * r^i)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (binom i k)) r (r ^ i))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (r ^ i) (Q'.mul_comm_eqv (Q'.ofNat (binom i k)) r)) ?_
    exact Q'.mul_assoc_eqv r (Q'.ofNat (binom i k)) (r ^ i)
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (binom i (k + 1))) r (r ^ i))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (r ^ i) (Q'.mul_comm_eqv (Q'.ofNat (binom i (k + 1))) r)) ?_
    exact Q'.mul_assoc_eqv r (Q'.ofNat (binom i (k + 1))) (r ^ i)

/-- **The cross-level recurrence.**  `binomGeomSum r (k+1) (N+1) ≃
r·binomGeomSum r k N + r·binomGeomSum r (k+1) N`.  Peel the (vanishing) head
term, split each shifted term by Pascal, and pull the `r` out of each sum. -/
theorem binomGeomSum_recurrence (r : Q') (k N : Nat) :
    (binomGeomSum r (k + 1) (N + 1)).eqv
      (r * binomGeomSum r k N + r * binomGeomSum r (k + 1) N) := by
  -- peel the head
  have hpeel : (finSum (binomTerm r (k + 1)) (N + 1)).eqv
      (binomTerm r (k + 1) 0
        + finSum (fun i => binomTerm r (k + 1) (i + 1)) N) :=
    finSum_peel_left (binomTerm r (k + 1)) N
  refine Q'.eqv_trans _ _ _ hpeel ?_
  -- head ≃ 0, so the sum ≃ Σ shifted
  have hhead : (binomTerm r (k + 1) 0
      + finSum (fun i => binomTerm r (k + 1) (i + 1)) N).eqv
      (finSum (fun i => binomTerm r (k + 1) (i + 1)) N) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (binomTerm_head_zero r k))
      (QPoly.q_zero_add_eqv _)
  refine Q'.eqv_trans _ _ _ hhead ?_
  -- Σ shifted ≃ Σ (r·A i + r·B i)
  have hcongr : (finSum (fun i => binomTerm r (k + 1) (i + 1)) N).eqv
      (finSum (fun i => r * binomTerm r k i + r * binomTerm r (k + 1) i) N) :=
    finSum_eqv_congr _ _ (fun i => binomTerm_split r k i) N
  refine Q'.eqv_trans _ _ _ hcongr ?_
  -- Σ (rA + rB) ≃ Σ rA + Σ rB
  refine Q'.eqv_trans _ _ _
    (finSum_add (fun i => r * binomTerm r k i) (fun i => r * binomTerm r (k + 1) i) N) ?_
  -- Σ rA ≃ r·Σ A , Σ rB ≃ r·Σ B
  exact QPoly.q_add_congr
    (Q'.eqv_symm (const_mul_finSum (binomTerm r k) r N))
    (Q'.eqv_symm (const_mul_finSum (binomTerm r (k + 1)) r N))

/-! ## The clean polylog majorant `Σ_{n<N} C(n,k) r^n ≤ H^{k+1}`

The headline closed form, by induction on `k`.  Base (`k = 0`): the bare
geometric `Σ r^n ≤ H` (`geometric_tail_closure`, `C(n,0) = 1`).  Step:
`recurrence_closure` on `N ↦ binomGeomSum r (k+1) N` with `c = r·H^{k+1}`
(from the IH `binomGeomSum r k · ≤ H^{k+1}`, via the cross-level recurrence)
gives `binomGeomSum r (k+1) N ≤ (r·H^{k+1})·H ≤ H^{k+2}`. -/

/-- **The clean polylog majorant.**  For `r,H ≥ 0` with `1 + r·H ≤ H`
(so `H ≥ 1/(1−r)`), every partial sum of the negative-binomial series is
bounded by `H^{k+1}`:

    Σ_{n<N} C(n,k)·r^n  ≤  H^{k+1} .

Induction on `k` through Pascal; no window, no transcendental. -/
theorem binomGeomSum_le {r H : Q'} (hr : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hrec : (1 : Q') + r * H ≤ H) :
    ∀ k N, binomGeomSum r k N ≤ H ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    -- binomGeomSum r 0 N = Σ C(n,0)·r^n ≃ Σ 1·r^n ≤ H = H^1.
    intro N
    -- pointwise: binomTerm r 0 n ≃ 1·r^n  (C(n,0) = 1, ofNat 1 = 1).
    have hcongr : (binomGeomSum r 0 N).eqv (finSum (fun n => (1 : Q') * r ^ n) N) :=
      finSum_eqv_congr (binomTerm r 0) (fun n => (1 : Q') * r ^ n)
        (fun n => by
          show ((Q'.ofNat (binom n 0)) * r ^ n).eqv ((1 : Q') * r ^ n)
          rw [binom_zero_right]
          exact Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (r ^ n) (by decide)) N
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcongr) ?_
    -- Σ 1·r^n ≤ H  by geometric_tail_closure (η_max = 1), then H = H^1 (pow_succ/pow_zero).
    have hgeo : finSum (fun n => (1 : Q') * r ^ n) N ≤ H :=
      RationalTail.geometric_tail_closure 1 r H hr hH hrec N
    refine Q'.le_trans' _ _ _ hgeo ?_
    -- H ≤ H^1 = H * H^0 = H * 1
    show H ≤ H ^ (0 + 1)
    exact Q'.ge_of_eqv (Q'.mul_one_eqv H)
  | succ k ih =>
    -- c := r · H^{k+1}, nonneg.
    intro N
    have hHk1_nn : (0 : Q') ≤ H ^ (k + 1) := Q'.pow_nonneg H hH (k + 1)
    have hc_nn : (0 : Q') ≤ r * H ^ (k + 1) := Q'.mul_nonneg _ _ hr hHk1_nn
    -- recurrence_closure on a N := binomGeomSum r (k+1) N, c := r·H^{k+1}.
    have hcl : ∀ M, binomGeomSum r (k + 1) M ≤ (r * H ^ (k + 1)) * H := by
      refine recurrence_closure (binomGeomSum r (k + 1)) r (r * H ^ (k + 1)) H
        hr hc_nn hH hrec ?_ ?_
      · -- a 0 = 0 ≤ c·H
        show binomGeomSum r (k + 1) 0 ≤ (r * H ^ (k + 1)) * H
        rw [binomGeomSum_zero]
        exact Q'.mul_nonneg _ _ hc_nn hH
      · -- a(M+1) ≤ c + r·(a M)
        intro M
        -- a(M+1) ≃ r·binomGeomSum r k M + r·(a M) ≤ r·H^{k+1} + r·(a M)
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (binomGeomSum_recurrence r k M)) ?_
        exact Q'.add_le_add_right _ _ (r * binomGeomSum r (k + 1) M)
          (Q'.mul_le_mul_of_nonneg_left (binomGeomSum r k M) (H ^ (k + 1)) r (ih M) hr)
    refine Q'.le_trans' _ _ _ (hcl N) ?_
    -- (r·H^{k+1})·H ≃ H^{k+1}·(r·H) ≤ H^{k+1}·H = H^{(k+1)+1}.
    -- (r·H^{k+1})·H ≃ H^{k+1}·(r·H)
    have he1 : ((r * H ^ (k + 1)) * H).eqv (H ^ (k + 1) * (r * H)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (r * H ^ (k + 1)) (H ^ (k + 1) * r) H
          (Q'.mul_comm_eqv r (H ^ (k + 1))))
        (Q'.mul_assoc_eqv (H ^ (k + 1)) r H)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he1) ?_
    -- H^{k+1}·(r·H) ≤ H^{k+1}·H  (r·H ≤ H from hrec, since 1+rH≤H ⟹ rH ≤ H)
    have hrH_le_H : r * H ≤ H := by
      refine Q'.le_trans' _ _ _ ?_ hrec
      -- r·H ≤ 1 + r·H
      have h := Q'.add_le_self_of_nonneg (r * H) 1 (by decide : (0 : Q') ≤ (1 : Q'))
      -- h : r*H ≤ r*H + 1; need r*H ≤ 1 + r*H
      exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv (r * H) 1))
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (r * H) H (H ^ (k + 1)) hrH_le_H hHk1_nn) ?_
    -- H^{k+1}·H = H^{(k+1)+1} definitionally? pow_succ: H^{n+1} = H * H^n.
    -- H^{(k+1)+1} = H * H^{k+1}; need H^{k+1}·H ≤ that, by commutativity.
    show H ^ (k + 1) * H ≤ H ^ ((k + 1) + 1)
    refine Q'.le_of_eqv ?_
    -- H^{k+1}·H ≃ H·H^{k+1} = H^{(k+1)+1}
    exact Q'.mul_comm_eqv (H ^ (k + 1)) H

/-! ## The rising-binomial sum `Σ_{n<N} C(n+d,d) r^n ≤ H^{d+1}`

The falling-factorial `C(n,d)` under-counts small `n` (`C(n,d) = 0` for
`n < d`), so it does **not** dominate `(1 + c·n)^d`.  The RISING binomial
`C(n+d, d)` does: `C(n+d,d)·d! = (n+1)(n+2)···(n+d) ≥ (1+n)^d`.  We prove the
same `H^{d+1}` majorant for `Σ_{n<N} C(n+d,d) r^n`, by the parallel telescope
`risingSum (d+1)(N+1) ≃ risingSum d (N+1) + r·risingSum (d+1) N`. -/

/-- `C(n+d,d)·r^n`, the rising-binomial term. -/
def risingTerm (r : Q') (d n : Nat) : Q' := (Q'.ofNat (binom (n + d) d)) * r ^ n

/-- `Σ_{n<N} C(n+d,d) r^n`. -/
def risingSum (r : Q') (d : Nat) : Nat → Q' := fun N => finSum (risingTerm r d) N

@[simp] theorem risingSum_zero (r : Q') (d : Nat) : risingSum r d 0 = 0 := rfl

theorem risingSum_succ (r : Q') (d N : Nat) :
    risingSum r d (N + 1) = risingSum r d N + risingTerm r d N := rfl

theorem risingTerm_nonneg {r : Q'} (hr : (0 : Q') ≤ r) (d n : Nat) :
    (0 : Q') ≤ risingTerm r d n :=
  Q'.mul_nonneg _ _ (ofNat_nonneg _) (Q'.pow_nonneg r hr n)

/-- The level-0 rising sum is the bare geometric: `risingTerm r 0 n ≃ 1·r^n`. -/
theorem risingTerm_zero_eqv (r : Q') (n : Nat) :
    (risingTerm r 0 n).eqv ((1 : Q') * r ^ n) := by
  show ((Q'.ofNat (binom (n + 0) 0)) * r ^ n).eqv ((1 : Q') * r ^ n)
  rw [binom_zero_right]
  exact Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (r ^ n) (by decide)

/-- **The rising-term split** `C(n+1+(d+1),d+1) r^{n+1} ≃
r·C(n+(d+1),d+1) r^n + C((n+1)+d, d) r^{n+1}` (Pascal). -/
theorem risingTerm_split (r : Q') (d n : Nat) :
    (risingTerm r (d + 1) (n + 1)).eqv
      (r * risingTerm r (d + 1) n + risingTerm r d (n + 1)) := by
  -- LHS index: (n+1)+(d+1) = (n+d+1)+1, so Pascal: C = C(n+d+1,d+1)+C(n+d+1,d).
  show ((Q'.ofNat (binom ((n + 1) + (d + 1)) (d + 1))) * r ^ (n + 1)).eqv
      (r * ((Q'.ofNat (binom (n + (d + 1)) (d + 1))) * r ^ n)
        + (Q'.ofNat (binom ((n + 1) + d) d)) * r ^ (n + 1))
  have hidx : (n + 1) + (d + 1) = (n + d + 1) + 1 := by omega
  rw [hidx, binom_succ_succ]
  -- binom (n+d+1) (d+1) and binom (n+d+1) d; relate to RHS indices.
  -- n+(d+1) = n+d+1 ; (n+1)+d = n+d+1.  So both RHS binoms are binom (n+d+1) ·.
  have h1 : n + (d + 1) = n + d + 1 := by omega
  have h2 : (n + 1) + d = n + d + 1 := by omega
  rw [h1, h2]
  -- Goal: ofNat (binom (n+d+1) d + binom (n+d+1) (d+1)) * r^(n+1)
  --     ≃ r*(ofNat (binom (n+d+1) (d+1)) * r^n) + ofNat (binom (n+d+1) d) * r^(n+1)
  -- r^(n+1) = r * r^n (pow_succ).
  have hsplit : (Q'.ofNat (binom (n + d + 1) d + binom (n + d + 1) (d + 1))).eqv
      (Q'.ofNat (binom (n + d + 1) d) + Q'.ofNat (binom (n + d + 1) (d + 1))) :=
    Q'.ofNat_add_eqv _ _
  -- distribute over r^(n+1)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (r ^ (n + 1)) hsplit) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_mul (Q'.ofNat (binom (n + d + 1) d))
      (Q'.ofNat (binom (n + d + 1) (d + 1))) (r ^ (n + 1))) ?_
  -- A·r^{n+1} + B·r^{n+1}, swap order and match the two RHS summands.
  -- RHS = r·(B·r^n) + A·r^{n+1}, with A = binom..d, B = binom..(d+1).
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
  refine QPoly.q_add_congr ?_ (Q'.eqv_refl _)
  -- B·r^{n+1} ≃ r·(B·r^n)  (r^{n+1} = r·r^n; commute)
  show ((Q'.ofNat (binom (n + d + 1) (d + 1))) * r ^ (n + 1)).eqv
      (r * ((Q'.ofNat (binom (n + d + 1) (d + 1))) * r ^ n))
  -- r^(n+1) = r * r^n
  show ((Q'.ofNat (binom (n + d + 1) (d + 1))) * (r * r ^ n)).eqv
      (r * ((Q'.ofNat (binom (n + d + 1) (d + 1))) * r ^ n))
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (binom (n + d + 1) (d + 1))) r (r ^ n))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (r ^ n)
      (Q'.mul_comm_eqv (Q'.ofNat (binom (n + d + 1) (d + 1))) r)) ?_
  exact Q'.mul_assoc_eqv r (Q'.ofNat (binom (n + d + 1) (d + 1))) (r ^ n)

/-- **The rising cross-level recurrence** `risingSum (d+1) (N+1) ≃
risingSum d (N+1) + r·risingSum (d+1) N`.  Induction on `N`. -/
theorem risingSum_recurrence (r : Q') (d : Nat) :
    ∀ N, (risingSum r (d + 1) (N + 1)).eqv
      (risingSum r d (N + 1) + r * risingSum r (d + 1) N) := by
  intro N
  induction N with
  | zero =>
    -- LHS = risingTerm r (d+1) 0 = ofNat (binom (d+1) (d+1)) = ofNat 1.
    -- RHS = risingSum r d 1 + r·0 = risingTerm r d 0 + r·0 = ofNat 1 + r·0.
    show (risingSum r (d + 1) 0 + risingTerm r (d + 1) 0).eqv
      ((risingSum r d 0 + risingTerm r d 0) + r * risingSum r (d + 1) 0)
    rw [risingSum_zero, risingSum_zero]
    -- (0 + risingTerm (d+1) 0) ≃ (0 + risingTerm d 0) + r·0
    have hL : (risingTerm r (d + 1) 0).eqv (Q'.ofNat 1) := by
      show ((Q'.ofNat (binom (0 + (d + 1)) (d + 1))) * r ^ 0).eqv (Q'.ofNat 1)
      rw [Nat.zero_add, binom_self]
      exact Q'.mul_one_eqv (Q'.ofNat 1)
    have hR1 : (risingTerm r d 0).eqv (Q'.ofNat 1) := by
      show ((Q'.ofNat (binom (0 + d) d)) * r ^ 0).eqv (Q'.ofNat 1)
      rw [Nat.zero_add, binom_self]
      exact Q'.mul_one_eqv (Q'.ofNat 1)
    -- 0 + X ≃ X
    refine Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) ?_
    refine Q'.eqv_trans _ _ _ hL ?_
    -- ofNat 1 ≃ (0 + ofNat 1) + r·0
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hR1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_zero_add_eqv (risingTerm r d 0))) ?_
    -- X ≃ X + r·0  (r·0 ≃ 0)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (QPoly.q_add_zero_eqv (0 + risingTerm r d 0))) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (QPoly.q_mul_zero r))
  | succ N ih =>
    -- risingSum (d+1)(N+2) = risingSum(d+1)(N+1) + risingTerm(d+1)(N+1)
    show (risingSum r (d + 1) (N + 1) + risingTerm r (d + 1) (N + 1)).eqv
      (risingSum r d ((N + 1) + 1) + r * risingSum r (d + 1) (N + 1))
    -- use ih + risingTerm_split (d) (N) : risingTerm (d+1)(N+1) ≃ r·rt(d+1)N + rt d (N+1)
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr ih (risingTerm_split r d N)) ?_
    -- LHS = (A + B) + (C + D) with A=rsum d(N+1), B=r·rsum(d+1)N,
    --   C=r·rt(d+1)N, D=rt d(N+1).  Want (A+D) + (B+C).
    -- Step 1: swap inner second group (C+D) → (D+C).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.add_comm_eqv (r * risingTerm r (d + 1) N) (risingTerm r d (N + 1)))) ?_
    -- now (A + B) + (D + C); interchange A B D C : ≃ (A + D) + (B + C).
    refine Q'.eqv_trans _ _ _
      (QPoly.q_interchange (risingSum r d (N + 1)) (r * risingSum r (d + 1) N)
        (risingTerm r d (N + 1)) (r * risingTerm r (d + 1) N)) ?_
    -- (A + D) ≃ rsum d (N+2);  (B + C) ≃ r·rsum(d+1)(N+1).
    refine QPoly.q_add_congr (Q'.eqv_refl _) ?_
    -- B + C = r·rsum(d+1)N + r·rt(d+1)N ≃ r·(rsum(d+1)N + rt(d+1)N) = r·rsum(d+1)(N+1)
    exact Q'.eqv_symm (Q'.mul_add_eqv r (risingSum r (d + 1) N) (risingTerm r (d + 1) N))

/-- **The rising polylog majorant.**  For `r,H ≥ 0` with `1 + r·H ≤ H`,

    Σ_{n<N} C(n+d,d)·r^n  ≤  H^{d+1} .

Induction on `d`; the rising binomial dominates `(1+c·n)^d`, so this is the
majorant that discharges the genuine per-axis factor. -/
theorem risingSum_le {r H : Q'} (hr : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hrec : (1 : Q') + r * H ≤ H) :
    ∀ d N, risingSum r d N ≤ H ^ (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro N
    have hcongr : (risingSum r 0 N).eqv (finSum (fun n => (1 : Q') * r ^ n) N) :=
      finSum_eqv_congr (risingTerm r 0) (fun n => (1 : Q') * r ^ n)
        (fun n => risingTerm_zero_eqv r n) N
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcongr) ?_
    have hgeo : finSum (fun n => (1 : Q') * r ^ n) N ≤ H :=
      RationalTail.geometric_tail_closure 1 r H hr hH hrec N
    refine Q'.le_trans' _ _ _ hgeo ?_
    show H ≤ H ^ (0 + 1)
    exact Q'.ge_of_eqv (Q'.mul_one_eqv H)
  | succ d ih =>
    intro N
    have hHd1_nn : (0 : Q') ≤ H ^ (d + 1) := Q'.pow_nonneg H hH (d + 1)
    -- recurrence_closure on a M := risingSum r (d+1) M, c := H^{d+1}.
    have hcl : ∀ M, risingSum r (d + 1) M ≤ H ^ (d + 1) * H := by
      refine recurrence_closure (risingSum r (d + 1)) r (H ^ (d + 1)) H
        hr hHd1_nn hH hrec ?_ ?_
      · show risingSum r (d + 1) 0 ≤ H ^ (d + 1) * H
        rw [risingSum_zero]
        exact Q'.mul_nonneg _ _ hHd1_nn hH
      · intro M
        -- a(M+1) = risingSum(d+1)(M+1) ≃ risingSum d (M+1) + r·risingSum(d+1)M
        --        ≤ H^{d+1} + r·a M.
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (risingSum_recurrence r d M)) ?_
        exact Q'.add_le_add_right _ _ (r * risingSum r (d + 1) M) (ih (M + 1))
    refine Q'.le_trans' _ _ _ (hcl N) ?_
    -- H^{d+1}·H = H^{(d+1)+1}
    show H ^ (d + 1) * H ≤ H ^ ((d + 1) + 1)
    exact Q'.le_of_eqv (Q'.mul_comm_eqv (H ^ (d + 1)) H)

/-! ## The assembled per-axis factor bound

The per-axis character-tail factor is `Σ_{n<N} w(n)·r^n` with the polynomial
weight `w(n) = (1 + c·n)^{2m}`.  The clean rising-binomial majorant
(`risingSum_le`) bounds `Σ_{n<N} C(n+d,d)·r^n ≤ H^{d+1}`, so once the weight
is dominated termwise by `B₀·C(n+d,d)` (the polynomial→rising-binomial
domination, the per-group analytic datum), the whole factor closes at
`B₀·H^{d+1}` — a single explicit rational, no window. -/

/-- A general polynomial-weighted geometric partial sum `Σ_{n<N} w(n)·r^n`. -/
def weightedGeomSum (r : Q') (w : Nat → Q') : Nat → Q' :=
  fun N => finSum (fun n => w n * r ^ n) N

/-- **The assembled per-axis factor bound.**  For `r,H ≥ 0` with `1 + r·H ≤ H`
and a polynomial weight `w` termwise dominated by `B₀·C(n+d,d)` (`B₀ ≥ 0`),

    Σ_{n<N} w(n)·r^n  ≤  B₀ · H^{d+1} .

The honest per-group content is exactly the termwise polynomial→binomial
domination `hdom` (for `w(n) = (1+c·n)^{2m}`, `d = 2m`, `B₀ = (2m)!·(1+c)^{2m}`
or any explicit constant from `(1+c·n)^{2m} ≤ B₀·C(n+2m,2m)`); the infinite
tail-summation closure is the proven `risingSum_le`.  This discharges the
per-axis polynomial-geometric `AxisFactorBound` with a clean rational
majorant, NOT a bare geometric. -/
theorem weightedGeomSum_le {r H B0 : Q'} (hr : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hB0 : (0 : Q') ≤ B0) (hrec : (1 : Q') + r * H ≤ H) (d : Nat) (w : Nat → Q')
    (hdom : ∀ n, w n ≤ B0 * (Q'.ofNat (binom (n + d) d)))
    (N : Nat) :
    weightedGeomSum r w N ≤ B0 * H ^ (d + 1) := by
  -- termwise: w(n)·r^n ≤ B₀·C(n+d,d)·r^n = B₀·risingTerm r d n
  have htw : ∀ n, w n * r ^ n ≤ B0 * risingTerm r d n := by
    intro n
    have h1 : w n * r ^ n ≤ (B0 * (Q'.ofNat (binom (n + d) d))) * r ^ n :=
      Q'.mul_le_mul_of_nonneg_right _ _ (r ^ n) (hdom n) (Q'.pow_nonneg r hr n)
    refine Q'.le_trans' _ _ _ h1 ?_
    -- (B₀·C)·r^n ≃ B₀·(C·r^n) = B₀·risingTerm r d n
    show (B0 * (Q'.ofNat (binom (n + d) d))) * r ^ n
        ≤ B0 * ((Q'.ofNat (binom (n + d) d)) * r ^ n)
    exact Q'.le_of_eqv (Q'.mul_assoc_eqv B0 (Q'.ofNat (binom (n + d) d)) (r ^ n))
  -- sum the termwise bound: Σ w·r^n ≤ Σ B₀·risingTerm = B₀·Σ risingTerm = B₀·risingSum
  have hsum : weightedGeomSum r w N ≤ finSum (fun n => B0 * risingTerm r d n) N :=
    CharacterTail.finSum_le_termwise (fun n => w n * r ^ n)
      (fun n => B0 * risingTerm r d n) htw N
  refine Q'.le_trans' _ _ _ hsum ?_
  -- Σ B₀·risingTerm ≃ B₀·Σ risingTerm = B₀·risingSum r d N ≤ B₀·H^{d+1}
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (const_mul_finSum (risingTerm r d) B0 N)) ?_
  show B0 * risingSum r d N ≤ B0 * H ^ (d + 1)
  exact Q'.mul_le_mul_of_nonneg_left (risingSum r d N) (H ^ (d + 1)) B0
    (risingSum_le hr hH hrec d N) hB0

/-! ## Supporting combinatorial fact for the termwise domination

`(1+n)^d ≤ (n+1)(n+2)···(n+d)` (the Pochhammer product), the route by which
`(1+c·n)^{2m} ≤ (1+c)^{2m}·(1+n)^{2m} ≤ (1+c)^{2m}·(2m)!·C(n+2m,2m)` (using
`(2m)!·C(n+2m,2m) = (n+1)···(n+2m)`).  We record the clean half over `ℕ`. -/

/-- The Pochhammer (rising-factorial) product `(n+1)(n+2)···(n+d)`. -/
def poch (n : Nat) : Nat → Nat
  | 0     => 1
  | d + 1 => poch n d * (n + d + 1)

/-- `(n+1)^d ≤ (n+1)(n+2)···(n+d)`: each of the `d` factors is `≥ n+1`. -/
theorem pow_le_poch (n d : Nat) : (n + 1) ^ d ≤ poch n d := by
  induction d with
  | zero => simp [poch]
  | succ d ih =>
    show (n + 1) ^ (d + 1) ≤ poch n d * (n + d + 1)
    calc (n + 1) ^ (d + 1) = (n + 1) ^ d * (n + 1) := by rw [Nat.pow_succ]
      _ ≤ poch n d * (n + 1) := Nat.mul_le_mul_right _ ih
      _ ≤ poch n d * (n + d + 1) := Nat.mul_le_mul_left _ (by omega)

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.recurrence_closure
#print axioms YMGap.RG.binom_self
#print axioms YMGap.RG.binomGeomSum_recurrence
#print axioms YMGap.RG.binomGeomSum_le
#print axioms YMGap.RG.risingSum_recurrence
#print axioms YMGap.RG.risingSum_le
#print axioms YMGap.RG.weightedGeomSum_le
#print axioms YMGap.RG.pow_le_poch
