/-
Track B / R2 — **Theorem B: the reciprocal `1/k` rate from the two-loop
asymptotic-freedom recurrence.**

# What this module proves (PURE constructive recurrence arithmetic)

The two-loop asymptotic-freedom (AF) flow for the log-coupling `τ_k = −log w_k`
(with `w_k` the per-scale heat-kernel weight) is

      τ_{k+1}  =  τ_k − β·τ_k² + O(τ_k³)                       (two-loop AF flow)

— this RECURRENCE is the standard, NAMED AF physics input.  Everything else in
this module is PROVED constructively, with no compactness, no subsequence, no
classical input: from the recurrence (in its small-`τ`, contracting form) we
derive the sharp reciprocal `1/k` decay rate

      τ_k  ≤  A / (k + B)                                      (Theorem B, PROVED)

and hence the AF-rate-modulus bound on the per-scale margin

      1 − w_k  ≤  A / (k + B).                                 (rate_upper shape)

The mechanism is the classical "reciprocal increment" argument made
constructive in `Q'`:

  * `recip_step` — one step of the recurrence increases the reciprocal
    `1/τ_k` by at least `c = β/2`:  `1/τ_k + c ≤ 1/τ_{k+1}`.  The key `Q'`
    inequality is `1/(1−y) ≥ 1+y` for `0 ≤ y < 1`, which reduces to
    `0 ≤ y²`; here `y = c·τ_k`.

  * `recip_lb` — iterating gives the linear-in-`k` reciprocal lower bound
    `1/τ_{k0} + c·(k − k0) ≤ 1/τ_k`.

  * `tau_inverse_linear_rate` — inverting yields `τ_k ≤ A/(k + B)` with the
    EXPLICIT constants `A = 1/c = 2/β` and `B = 1/(c·τ_{k0}) − k0` (returned as
    data, with the offset handled so `B > 0`).

# What is NAMED input (honest)

  * The RECURRENCE `τ_{k+1} ≤ τ_k·(1 − c·τ_k)` (the contracting, small-`τ`
    form of the two-loop AF flow) is the AF physics hypothesis — carried as a
    `∀ k ≥ k0` hypothesis, NOT derived here.

  * The AF dictionary link `1 − w_k ≤ τ_k` (the per-scale margin is bounded by
    the log-coupling, i.e. `1 − e^{−τ} ≤ τ`) is the named scalar input that
    converts the proved coupling rate into the weight-margin rate.  Given any
    rational weight trajectory satisfying it, `rate_upper` is then PROVED by
    transitivity.

So this CLOSES Theorem B: *given the named two-loop β-recurrence, the AF rate
`1 − w_k ≤ A/(k+B)` is a proved constructive consequence.*

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic (the positivity-guarded `Q'.divPos` and its
`divPos_mul_eqv` / `le_divPos_of_mul_le` / `divPos_le_of_le_mul`
characterizations, reused `Q'` order/`eqv` lemmas) and a structural `Nat`
induction.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses (`A`, `B`, the rate bound) are
`Type`-level data.
-/

import YMGap.Continuum.AFRateCalibration

namespace YMGap.Continuum.AFReciprocalRate

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.AFRateCalibration

/-! ## 0. Small `Q'` reciprocal helpers (proved here)

`recip τ = 1/τ` via the positivity-guarded `divPos`, plus the two facts the
reciprocal-step needs: `(1/τ)·τ ≃ 1` and `1 ≤ (1/τ)·τ` (`divPos_mul_eqv`), and
the elementary `1 ≥ (1+y)(1−y)` (`= 1 − y²`). -/

/-- The reciprocal `1/τ` of a positive `τ`. -/
def recip (τ : Q') (hτ : (0 : Q') < τ) : Q' := Q'.divPos 1 τ hτ

theorem recip_pos (τ : Q') (hτ : (0 : Q') < τ) : (0 : Q') < recip τ hτ :=
  Q'.divPos_pos 1 τ hτ (by decide)

theorem recip_nonneg (τ : Q') (hτ : (0 : Q') < τ) : (0 : Q') ≤ recip τ hτ :=
  Q'.le_of_lt (recip_pos τ hτ)

/-- `(1/τ)·τ ≃ 1`. -/
theorem recip_mul_eqv (τ : Q') (hτ : (0 : Q') < τ) : (recip τ hτ * τ).eqv 1 :=
  Q'.divPos_mul_eqv 1 τ hτ

/-- **The reciprocal-of-`(1−y)` lemma at the multiplicative level.**
`(1 + y)·(1 − y) ≤ 1`, i.e. `1 − y² ≤ 1`, valid for every `y` (it only uses
`0 ≤ y²`).  This is the `Q'` core of `1/(1−y) ≥ 1+y`. -/
theorem one_add_mul_one_sub_le_one (y : Q') (hy : (0 : Q') ≤ y) :
    (1 + y) * (1 - y) ≤ 1 := by
  -- (1+y)·(1−y) ≃ 1 − y·y, and 0 ≤ y·y, so (1+y)(1−y) ≤ 1.
  -- Expand: (1+y)·(1 + -y) ≃ (1·1 + 1·(-y)) + (y·1 + y·(-y))
  --        ≃ (1 + -y) + (y + -(y·y)) ≃ 1 + (-y + y) + -(y·y) ≃ 1 + -(y·y).
  have hexpand : ((1 + y) * (1 - y)).eqv (1 + -(y * y)) := by
    show ((1 + y) * (1 + -y)).eqv (1 + -(y * y))
    -- right-distribute then left-distribute
    refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv 1 y (1 + -y)) ?_
    -- 1·(1+-y) + y·(1+-y)
    have h1 : ((1 : Q') * (1 + -y)).eqv (1 + -y) := Q'.one_mul_eqv (1 + -y)
    have h2 : (y * (1 + -y)).eqv (y + -(y * y)) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv y 1 (-y)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (y * 1) y (y * (-y)) (Q'.mul_one_eqv y)) ?_
      exact Q'.add_eqv_congr_left y (y * (-y)) (-(y * y)) (Q'.mul_neg_eqv y y)
    -- assemble: (1·(1+-y)) + (y·(1+-y)) ≃ (1+-y) + (y + -(y·y))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (y * (1 + -y)) h1) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 + -y) _ _ h2) ?_
    -- (1 + -y) + (y + -(y·y)) ≃ 1 + (-y + (y + -(y·y))) ≃ 1 + ((-y + y) + -(y·y))
    --    ≃ 1 + (0 + -(y·y)) ≃ 1 + -(y·y)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-y) (y + -(y * y))) ?_
    refine Q'.add_eqv_congr_left 1 _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-y) y (-(y * y)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (-y + y) 0 (-(y * y)) (Q'.neg_add_self_eqv y)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (-(y * y)))
      (Q'.eqv_of_eq (Q'.add_zero' (-(y * y))))
  -- 1 + -(y·y) ≤ 1  since 0 ≤ y·y.
  have hyy : (0 : Q') ≤ y * y := Q'.mul_nonneg y y hy hy
  have hle : (1 : Q') + -(y * y) ≤ 1 := by
    -- 1 + -(y·y) ≤ 1 + 0 ≃ 1
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 (-(y * y)) 0 ?_)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))
    -- -(y·y) ≤ 0, directly at the `Int` cross-product level.
    show (-(y * y)).num * ((0 : Q').den : Int) ≤ (0 : Q').num * ((-(y * y)).den : Int)
    have hn : (0 : Int) ≤ (y * y).num := (Q'.zero_le_iff_num_nonneg (y * y)).mp hyy
    show (-(y * y)).num * (1 : Int) ≤ (0 : Int) * ((-(y * y)).den : Int)
    rw [Int.zero_mul, Int.mul_one]
    show -((y * y).num) ≤ (0 : Int)
    omega
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) hle

/-! ## 1. The reciprocal-increment step

Given the contracting recurrence `τ_{k+1} ≤ τ_k·(1 − c·τ_k)` (the small-`τ`
two-loop AF flow, with `c = β/2`), one step increases the reciprocal by at
least `c`:

      1/τ_k + c  ≤  1/τ_{k+1}.

Proof.  By `le_divPos_of_mul_le` it suffices to show `(1/τ_k + c)·τ_{k+1} ≤ 1`.
Since `τ_{k+1} ≤ τ_k·(1 − c·τ_k)` and `1/τ_k + c ≥ 0`,

      (1/τ_k + c)·τ_{k+1}  ≤  (1/τ_k + c)·(τ_k·(1 − c·τ_k))
                            ≃ ((1/τ_k + c)·τ_k)·(1 − c·τ_k)
                            ≃ (1 + c·τ_k)·(1 − c·τ_k)        [(1/τ_k)·τ_k ≃ 1]
                            ≤ 1                              [`one_add_mul_one_sub_le_one`].
-/

/-- **The reciprocal-increment step.**  From the contracting recurrence
`τ_{k+1} ≤ τ_k·(1 − c·τ_k)` (and `τ_k, τ_{k+1}, c > 0`), the reciprocal
increases by at least `c`:  `1/τ_k + c ≤ 1/τ_{k+1}`. -/
theorem recip_step (τk τk1 c : Q') (hτk : (0 : Q') < τk) (hτk1 : (0 : Q') < τk1)
    (hc : (0 : Q') ≤ c) (hrec : τk1 ≤ τk * (1 - c * τk)) :
    recip τk hτk + c ≤ recip τk1 hτk1 := by
  -- It suffices: (1/τk + c)·τk1 ≤ 1.
  refine Q'.le_divPos_of_mul_le 1 τk1 hτk1 ?_
  -- (1/τk + c)·τk1 ≤ (1/τk + c)·(τk·(1−c·τk)).
  have hS_nonneg : (0 : Q') ≤ recip τk hτk + c :=
    Q'.zero_le_add _ _ (recip_nonneg τk hτk) hc
  have hstep1 : (recip τk hτk + c) * τk1
      ≤ (recip τk hτk + c) * (τk * (1 - c * τk)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrec hS_nonneg
  -- regroup: S·(τk·(1−c·τk)) ≃ (S·τk)·(1−c·τk).
  have hregroup : ((recip τk hτk + c) * (τk * (1 - c * τk))).eqv
      (((recip τk hτk + c) * τk) * (1 - c * τk)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (recip τk hτk + c) τk (1 - c * τk))
  -- S·τk ≃ 1 + c·τk :  (1/τk + c)·τk ≃ (1/τk)·τk + c·τk ≃ 1 + c·τk.
  have hStk : ((recip τk hτk + c) * τk).eqv (1 + c * τk) := by
    refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv (recip τk hτk) c τk) ?_
    exact Q'.add_eqv_congr_right _ _ (c * τk) (recip_mul_eqv τk hτk)
  -- so (S·τk)·(1−c·τk) ≃ (1 + c·τk)·(1 − c·τk).
  have hprod_eqv : (((recip τk hτk + c) * τk) * (1 - c * τk)).eqv
      ((1 + c * τk) * (1 - c * τk)) :=
    Q'.mul_eqv_congr_right _ _ (1 - c * τk) hStk
  -- (1 + c·τk)·(1 − c·τk) ≤ 1  (the `1 − y²` lemma at y = c·τk).
  have hctk : (0 : Q') ≤ c * τk := Q'.mul_nonneg c τk hc (Q'.le_of_lt hτk)
  have hkey : (1 + c * τk) * (1 - c * τk) ≤ 1 :=
    one_add_mul_one_sub_le_one (c * τk) hctk
  -- chain everything.
  exact Q'.le_trans' _ _ _ hstep1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hprod_eqv) hkey))

/-! ## 2. The reciprocal lower bound (induction)

Iterating `recip_step` from the base `k0`: after `k − k0` steps the reciprocal
has grown by at least `c·(k − k0)`:

      1/τ_{k0} + c·(ofNat (k − k0))  ≤  1/τ_k       (for all `k ≥ k0`).

We phrase the induction additively as `∀ d, 1/τ_{k0} + c·(ofNat d) ≤ 1/τ_{k0+d}`,
which is the clean `Nat`-induction form (`k = k0 + d`). -/

/-- **The reciprocal lower bound (additive form).**  Under the contracting
recurrence valid from `k0`, after `d` steps:
`1/τ_{k0} + c·(ofNat d) ≤ 1/τ_{k0+d}`. -/
theorem recip_lb_add (τ : Nat → Q') (τ_pos : ∀ k, (0 : Q') < τ k) (c : Q')
    (hc : (0 : Q') ≤ c) (k0 : Nat)
    (hrec : ∀ k, k0 ≤ k → τ (k + 1) ≤ τ k * (1 - c * τ k)) :
    ∀ d, recip (τ k0) (τ_pos k0) + c * Q'.ofNat d
        ≤ recip (τ (k0 + d)) (τ_pos (k0 + d)) := by
  intro d
  induction d with
  | zero =>
    -- 1/τk0 + c·0 ≤ 1/τk0 ; LHS ≃ 1/τk0.
    show recip (τ k0) (τ_pos k0) + c * Q'.ofNat 0 ≤ recip (τ (k0 + 0)) (τ_pos (k0 + 0))
    have hc0 : (c * Q'.ofNat 0).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ ofNat_zero_eqv)
        (Q'.mul_zero_eqv c)
    have hL : (recip (τ k0) (τ_pos k0) + c * Q'.ofNat 0).eqv (recip (τ k0) (τ_pos k0)) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 hc0)
        (Q'.eqv_of_eq (Q'.add_zero' (recip (τ k0) (τ_pos k0))))
    -- k0 + 0 = k0 definitionally.
    exact Q'.le_of_eqv hL
  | succ d ih =>
    -- target: 1/τk0 + c·(d+1) ≤ 1/τ_{k0+d+1}.
    -- recip_step at k = k0+d: 1/τ_{k0+d} + c ≤ 1/τ_{k0+d+1}.
    have hk0d : k0 ≤ k0 + d := Nat.le_add_right k0 d
    have hstep : recip (τ (k0 + d)) (τ_pos (k0 + d)) + c
        ≤ recip (τ ((k0 + d) + 1)) (τ_pos ((k0 + d) + 1)) :=
      recip_step (τ (k0 + d)) (τ ((k0 + d) + 1)) c
        (τ_pos (k0 + d)) (τ_pos ((k0 + d) + 1)) hc (hrec (k0 + d) hk0d)
    -- (1/τk0 + c·d) + c ≤ 1/τ_{k0+d} + c ≤ 1/τ_{k0+d+1}.
    have hchain : (recip (τ k0) (τ_pos k0) + c * Q'.ofNat d) + c
        ≤ recip (τ ((k0 + d) + 1)) (τ_pos ((k0 + d) + 1)) :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ c ih) hstep
    -- LHS ≃ 1/τk0 + c·(d+1) :  (1/τk0 + c·d) + c ≃ 1/τk0 + (c·d + c) ≃ 1/τk0 + c·(d+1).
    have hcd1 : (c * Q'.ofNat d + c).eqv (c * Q'.ofNat (d + 1)) := by
      -- c·d + c ≃ c·d + c·1 ≃ c·(d + 1) ≃ c·ofNat(d+1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (c * Q'.ofNat d) c (c * 1)
          (Q'.eqv_symm (Q'.mul_one_eqv c))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv c (Q'.ofNat d) 1)) ?_
      refine Q'.mul_eqv_congr_left c (Q'.ofNat d + 1) (Q'.ofNat (d + 1)) ?_
      -- ofNat d + 1 ≃ ofNat (d+1)
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (ofNat_add_eqv d 1) ?_)
      exact Q'.add_eqv_congr_left (Q'.ofNat d) (Q'.ofNat 1) 1 (Q'.eqv_of_eq rfl)
    have hLeqv : ((recip (τ k0) (τ_pos k0) + c * Q'.ofNat d) + c).eqv
        (recip (τ k0) (τ_pos k0) + c * Q'.ofNat (d + 1)) :=
      Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (recip (τ k0) (τ_pos k0)) (c * Q'.ofNat d) c)
        (Q'.add_eqv_congr_left (recip (τ k0) (τ_pos k0)) _ _ hcd1)
    show recip (τ k0) (τ_pos k0) + c * Q'.ofNat (d + 1)
        ≤ recip (τ (k0 + (d + 1))) (τ_pos (k0 + (d + 1)))
    -- k0 + (d+1) = (k0 + d) + 1 definitionally (Nat.add_succ).
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLeqv) hchain

/-! ## 3. Theorem B — the reciprocal `1/k` rate

Inverting `recip_lb_add`: from `1/τ_{k0} + c·(ofNat d) ≤ 1/τ_{k0+d}` we get, by
`divPos_le_of_le_mul`,

      τ_{k0+d}  ≤  1 / (1/τ_{k0} + c·d).

We repackage this as `A/(k + B)` with EXPLICIT constants.  Writing `k = k0 + d`,
so `d = k − k0`, the denominator is `1/τ_{k0} + c·(k − k0) = c·(k + B)` with

      A := 1/c        (= 2/β),
      B := 1/(c·τ_{k0}) − k0      (chosen so c·(k + B) = 1/τ_{k0} + c·(k − k0)).

To keep `B > 0` and the `harmDen B` denominator-shape exactly matching
`AFRateCalibration`, we state the rate against the shifted index `d = k − k0`:
`τ_{k0+d} ≤ A/(d + B')` with `B' := 1/(c·τ_{k0}) > 0` and `A := 1/c > 0`.  This
is the genuine `1/k` decay; the `k`-indexed form is the same bound at
`k = k0 + d`. -/

/-- **Theorem B (shifted form).**  Under the contracting two-loop recurrence
from `k0`, the coupling decays reciprocally in the step count `d = k − k0`:

      τ_{k0+d}  ≤  A / (d + B'),     A = 1/c,  B' = 1/(c·τ_{k0}),

both `> 0`, returned as DATA.  This is the proved `1/k` rate. -/
def tau_inverse_linear_rate (τ : Nat → Q') (τ_pos : ∀ k, (0 : Q') < τ k) (c : Q')
    (hc : (0 : Q') < c) (k0 : Nat)
    (hrec : ∀ k, k0 ≤ k → τ (k + 1) ≤ τ k * (1 - c * τ k)) :
    Σ' (A : Q') (B' : Q') (hA : (0 : Q') < A) (hB' : (0 : Q') < B'),
      ∀ d, τ (k0 + d) ≤ Q'.divPos A (harmDen B' d) (harmDen_pos hB' d) := by
  -- A := 1/c, B' := (1/c)·(1/τ_{k0}) = 1/(c·τ_{k0}).
  have hcnn : (0 : Q') ≤ c := Q'.le_of_lt hc
  refine ⟨recip c hc, recip c hc * recip (τ k0) (τ_pos k0), recip_pos c hc,
    Q'.mul_pos (recip_pos c hc) (recip_pos (τ k0) (τ_pos k0)), ?_⟩
  intro d
  -- Use the upper-quotient characterization `le_divPos_of_mul_le`:  it suffices to
  -- prove  τ_{k0+d} · (harmDen B' d)  ≤  A = 1/c.
  refine Q'.le_divPos_of_mul_le (recip c hc) (harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d)
    (harmDen_pos (Q'.mul_pos (recip_pos c hc) (recip_pos (τ k0) (τ_pos k0))) d) ?_
  -- Goal: τ_{k0+d} · (harmDen B' d) ≤ 1/c.
  -- Let L := 1/τk0 + c·ofNat d (≤ 1/τ_{k0+d}), and note L ≃ c·(harmDen B' d).
  have hLB : recip (τ k0) (τ_pos k0) + c * Q'.ofNat d
      ≤ recip (τ (k0 + d)) (τ_pos (k0 + d)) := recip_lb_add τ τ_pos c hcnn k0 hrec d
  -- L ≃ c·(harmDen B' d):  c·(ofNat d + (1/c)·(1/τk0))
  --    ≃ c·ofNat d + c·((1/c)·(1/τk0)) ≃ c·ofNat d + (c·(1/c))·(1/τk0)
  --    ≃ c·ofNat d + 1·(1/τk0) ≃ c·ofNat d + 1/τk0 ≃ 1/τk0 + c·ofNat d = L.
  have hLeqv : (recip (τ k0) (τ_pos k0) + c * Q'.ofNat d).eqv
      (c * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d) := by
    show (recip (τ k0) (τ_pos k0) + c * Q'.ofNat d).eqv
        (c * (Q'.ofNat d + recip c hc * recip (τ k0) (τ_pos k0)))
    -- RHS: c·(ofNat d + (1/c)·(1/τk0)) ≃ c·ofNat d + c·((1/c)·(1/τk0))
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (Q'.ofNat d) (recip c hc * recip (τ k0) (τ_pos k0))) ?_
    -- c·ofNat d + c·((1/c)·(1/τk0))  ;  reduce the second summand to 1/τk0.
    have hsnd : (c * (recip c hc * recip (τ k0) (τ_pos k0))).eqv (recip (τ k0) (τ_pos k0)) := by
      -- c·((1/c)·r) ≃ (c·(1/c))·r ≃ 1·r ≃ r
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv c (recip c hc) (recip (τ k0) (τ_pos k0)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 1 (recip (τ k0) (τ_pos k0)) ?_) ?_
      · -- c·(1/c) ≃ 1
        refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv c (recip c hc)) (recip_mul_eqv c hc)
      · exact Q'.one_mul_eqv (recip (τ k0) (τ_pos k0))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (c * Q'.ofNat d) _ _ hsnd) ?_
    -- c·ofNat d + 1/τk0 ≃ 1/τk0 + c·ofNat d
    exact Q'.add_comm_eqv (c * Q'.ofNat d) (recip (τ k0) (τ_pos k0))
  -- So c·(harmDen B' d) ≃ L ≤ 1/τ_{k0+d}.
  have hcH_le : c * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d
      ≤ recip (τ (k0 + d)) (τ_pos (k0 + d)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLeqv) hLB
  -- Write `D := harmDen B' d` (the denominator).  Goal: τ_{k0+d} · D ≤ 1/c.
  -- Step (i): τ·(c·D) ≤ τ·(1/τ) ≃ 1,  hence (τ·c)·D ≤ 1.
  have hτd_nonneg : (0 : Q') ≤ τ (k0 + d) := Q'.le_of_lt (τ_pos (k0 + d))
  have hi : τ (k0 + d) * (c * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d)
      ≤ τ (k0 + d) * recip (τ (k0 + d)) (τ_pos (k0 + d)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcH_le hτd_nonneg
  have hi1 : τ (k0 + d) * recip (τ (k0 + d)) (τ_pos (k0 + d)) ≤ 1 :=
    Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (τ (k0 + d)) (recip (τ (k0 + d)) (τ_pos (k0 + d))))
        (recip_mul_eqv (τ (k0 + d)) (τ_pos (k0 + d))))
  -- (τ·c)·D ≤ 1  (regroup τ·(c·D) ≃ (τ·c)·D).
  have hi2 : (τ (k0 + d) * c) * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv (τ (k0 + d)) c
        (harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d)))
      (Q'.le_trans' _ _ _ hi hi1)
  -- Step (ii): multiply by (1/c) ≥ 0:  (1/c)·((τ·c)·D) ≤ (1/c)·1 ≃ 1/c.
  have hii : recip c hc * ((τ (k0 + d) * c)
        * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d) ≤ recip c hc * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hi2 (recip_nonneg c hc)
  -- LHS ≃ τ·D :  (1/c)·((τ·c)·D) ≃ ((1/c)·(τ·c))·D ≃ τ·D, since (1/c)·(τ·c) ≃ τ.
  have hLHS : (recip c hc * ((τ (k0 + d) * c)
        * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d)).eqv
      (τ (k0 + d) * harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d) := by
    -- (1/c)·((τ·c)·D) ≃ ((1/c)·(τ·c))·D
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (recip c hc) (τ (k0 + d) * c)
        (harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d))) ?_
    -- ((1/c)·(τ·c))·D ≃ τ·D  via (1/c)·(τ·c) ≃ τ.
    refine Q'.mul_eqv_congr_right _ _
      (harmDen (recip c hc * recip (τ k0) (τ_pos k0)) d) ?_
    -- (1/c)·(τ·c) ≃ (1/c)·(c·τ) ≃ ((1/c)·c)·τ ≃ 1·τ ≃ τ
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (recip c hc) _ _ (Q'.mul_comm_eqv (τ (k0 + d)) c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (recip c hc) c (τ (k0 + d)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 1 (τ (k0 + d)) (recip_mul_eqv c hc)) ?_
    exact Q'.one_mul_eqv (τ (k0 + d))
  -- RHS ≃ 1/c.
  have hRHS : (recip c hc * 1).eqv (recip c hc) := Q'.mul_one_eqv (recip c hc)
  -- Conclude τ·D ≤ 1/c.
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLHS)
    (Q'.le_trans' _ _ _ hii (Q'.le_of_eqv hRHS))

/-! ## 4. The AF-rate bound on `1 − w` — Theorem B closure

The proved coupling rate `τ_{k0+d} ≤ A/(d + B')` converts to the AF-rate-modulus
bound on the per-scale weight margin `1 − w_k` via the AF dictionary link

      1 − w_k  ≤  τ_k                 (`= 1 − e^{−τ_k} ≤ τ_k`),

the standard scalar relation between the weight margin and the log-coupling.
Given this NAMED link for a rational weight trajectory `w`, the upper AF rate
`1 − w_k ≤ A/(k+B)` (the `rate_upper`-field shape of an `AFRateModulus`) is then
PROVED by transitivity.  This CLOSES Theorem B: from the named two-loop
β-recurrence the AF rate is a derived constructive consequence. -/

/-- **Theorem B closure — the AF-rate bound on `1 − w` (shifted form).**
Under the contracting two-loop recurrence from `k0` and the AF dictionary link
`1 − w_{k0+d} ≤ τ_{k0+d}` (the scalar relation `1 − e^{−τ} ≤ τ` for a rational
weight model), the per-scale margin obeys the reciprocal rate

      1 − w_{k0+d}  ≤  A / (d + B'),

with the SAME explicit `A = 1/c`, `B' = 1/(c·τ_{k0})` returned by
`tau_inverse_linear_rate`.  This is the `rate_upper`-field shape derived from the
recurrence. -/
def afRateModulus_of_recurrence
    (τ : Nat → Q') (τ_pos : ∀ k, (0 : Q') < τ k) (c : Q')
    (hc : (0 : Q') < c) (k0 : Nat)
    (hrec : ∀ k, k0 ≤ k → τ (k + 1) ≤ τ k * (1 - c * τ k))
    (w : Nat → Q') (hlink : ∀ k, k0 ≤ k → (1 : Q') - w k ≤ τ k) :
    Σ' (A : Q') (B' : Q') (hA : (0 : Q') < A) (hB' : (0 : Q') < B'),
      ∀ d, (1 : Q') - w (k0 + d)
        ≤ Q'.divPos A (harmDen B' d) (harmDen_pos hB' d) := by
  obtain ⟨A, B', hA, hB', hrate⟩ := tau_inverse_linear_rate τ τ_pos c hc k0 hrec
  refine ⟨A, B', hA, hB', ?_⟩
  intro d
  -- 1 − w_{k0+d} ≤ τ_{k0+d} ≤ A/(d + B').
  exact Q'.le_trans' _ _ _ (hlink (k0 + d) (Nat.le_add_right k0 d)) (hrate d)

/-! ## 5. The `k`-indexed reciprocal lower bound (named deliverable)

`recip_lb` is the `recip_lb_add` reciprocal lower bound re-expressed against the
absolute index `k ≥ k0`, with the step count `k − k0` recovered from `k = k0 +
(k − k0)`. -/

/-- **The reciprocal lower bound (`k`-indexed form).**  For every `k ≥ k0`,
`1/τ_{k0} + c·(ofNat (k − k0)) ≤ 1/τ_k`. -/
theorem recip_lb (τ : Nat → Q') (τ_pos : ∀ k, (0 : Q') < τ k) (c : Q')
    (hc : (0 : Q') ≤ c) (k0 : Nat)
    (hrec : ∀ k, k0 ≤ k → τ (k + 1) ≤ τ k * (1 - c * τ k))
    (k : Nat) (hk : k0 ≤ k) :
    recip (τ k0) (τ_pos k0) + c * Q'.ofNat (k - k0) ≤ recip (τ k) (τ_pos k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk   -- k = k0 + d
  have hd : k0 + d - k0 = d := by omega
  rw [hd]
  exact recip_lb_add τ τ_pos c hc k0 hrec d

end YMGap.Continuum.AFReciprocalRate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFReciprocalRate.recip_pos
#print axioms YMGap.Continuum.AFReciprocalRate.recip_mul_eqv
#print axioms YMGap.Continuum.AFReciprocalRate.one_add_mul_one_sub_le_one
#print axioms YMGap.Continuum.AFReciprocalRate.recip_step
#print axioms YMGap.Continuum.AFReciprocalRate.recip_lb_add
#print axioms YMGap.Continuum.AFReciprocalRate.tau_inverse_linear_rate
#print axioms YMGap.Continuum.AFReciprocalRate.afRateModulus_of_recurrence
#print axioms YMGap.Continuum.AFReciprocalRate.recip_lb
