/-
Track B / R2 — THE BULK-MODE CRUX: the SHARP order of the heat-kernel-SCALED
bulk contribution of the 4D Migdal–Kadanoff bond-moving defect.  VERDICT:
**OBSTRUCTION** (case b).  Per-`s` heat-kernel reweighting does NOT cure the bulk.

# The question

The full-mode bond-moving quadratic defect is summed over the SU(2) spin tower
weighted by the renormalized heat-kernel density `μ(s) ∝ (s+1)²·w^{C₄(s)}`.  The
crux is the BULK window `s ∼ 1/√(1−w)`, where the Casimir-margin product
`C₄(s)·(1−w)` is `Θ(1)`.  There the heat-kernel weight `w^{C₄(s)} ≈ e^{−1}` is
NOT suppressed, so reweighting alone may fail.  We determine the order of the
per-mode RENORMALIZED defect on that window — and prove it does NOT vanish.

# The per-mode renormalized defect (the object)

`deltaRen w s = C₄(s)·(1−w) − (1 − w^{C₄(s)})` is the OVERSHOOT of the matched
linear (`s = 1` marginal) model over the true first-excited deviation — exactly
the renormalized transverse residual whose `s = 1` value `BondMovingQuadratic`
proves quadratic.  Per `secondOrder_qpow` it has the QUADRATIC UPPER bound
`deltaRen w s ≤ C₄(s)²·(1−w)²`.  This module proves the matching LOWER bound and
reads off the bulk order.

# What is PROVED here (genuine `Q'`/`Nat`, axiom-clean)

  * `triSum` / `triSum_closed` — the triangular number `∑_{i<n} i`, with the exact
    quadratic identity `2·triSum n + n = n²` (no subtraction; clean induction).
  * `qpow_ge_bernoulli` — Bernoulli `w^n ≥ 1 − n·(1−w)` on `[0,1]` (local copy).
  * `subA` / `lowDeficit` / **`overshoot_lower`** — the genuine QUADRATIC-FROM-BELOW
    engine: `(1−w)²·w^n·triSum n ≤ deficit`, hence
        `deltaRen w s  ≥  (1−w)²·w^{C₄(s)}·triSum(C₄(s))`.
    Together with `secondOrder_qpow` (the upper bound) this is the TWO-SIDED
    per-mode characterization `deltaRen ≍ (1−w)²·C₄(s)²` on active modes.
  * **`overshoot_floor`** (THE SHARP NEGATIVE RESULT).  On the bulk window
    `1/2 ≤ C₄(s)·(1−w) ≤ 3/4` (with `1−w ≤ 1/4`, the near-continuum regime),
        `deltaRen w s  ≥  1/128`   —  a POSITIVE CONSTANT independent of `w`.
    So the renormalized per-mode defect is `Θ(1)` = `O((1−w)⁰)` on the bulk: it
    does NOT vanish as `w → 1`.  (Order: `bulkSum`'s per-mode factor is `O(1)`.)
  * `bulkSum` / `bulkMassNorm` / **`bulkSum_ge`** — the scaled bulk-window sums and
    the termwise reduction `bulkSum w ≥ (1/128)·(∑_{bulk} μ)`.  Hence the scaled
    bulk contribution is `≥ (1/128)·(normalized bulk mass)`.
  * **`BulkObstruction` / `bulkObstruction_floor`** — the packaged verdict: given a
    populated bulk window and the (named) `O(1)` bulk-mass fraction `∑_{bulk} μ ≥
    c_mass`, the SCALED bulk contribution is `≥ (1/128)·c_mass`, a POSITIVE
    CONSTANT.  The heat-kernel-scaled reweighting leaves a NON-VANISHING bulk.

# The order verdict — and the diagnosis for the next loop

ORDER:  `bulkSum w ≥ (1/128)·(∑_{bulk} μ)` and the per-mode defect is `O(1)`; the
normalized bulk mass `∑_{bulk} μ` is `O(1)` (a constant FRACTION of the mass lives
at `s ∼ 1/√(1−w)`, since `Z ∼ (1−w)^{−3/2}` and the bulk window carries the same
order).  ⇒ `bulkSum w = O((1−w)⁰)`: NOT summably small.  This is CASE (b), the
SHARP OBSTRUCTION: per-`s` heat-kernel weighting is INSUFFICIENT.

WHY:  `deltaRen w s ≍ C₄(s)²·(1−w)²` (two-sided), and at `s ∼ 1/√(1−w)` we have
`C₄(s) ∼ 1/(1−w)`, so the per-mode defect is `Θ(1)`.  The `μ`-weight normalizes
MASS to one but does NOT down-weight the DEFECT where the mass concentrates.

FIX (next loop):  a `C₄(s)`-graded (Sobolev `H^{−2}`-type) norm: measure the
per-mode residual RELATIVE to `C₄(s)²` (equivalently weight mode `s` by
`1/(1+τ·C₄(s))²` with the residual divided by the SAME factor), so the GRADED
per-mode defect `deltaRen/C₄(s)² ≤ (1−w)²` is UNIFORMLY quadratic; then the graded
bulk sum is `≤ (1−w)²·(∑_{bulk} μ) = O((1−w)²)` — controlled.  A `(1+τ·C₄(s))^q`
test factor ALONE (which MULTIPLIES, as in `qfac`) does NOT suffice: at `τ·C₄(s) ∼
1` it is itself `Θ(1)`.  The grading must DIVIDE the defect by the full Casimir
square, i.e. a genuine mode-graded (inverse-Casimir) retuning, not the `s = 1`-only
marginal retuning.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Q'` numeric facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only `decide`
on decidable facts), no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.AFRateCalibration

namespace YMGap.Continuum.BulkModeCrux

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingQuadratic

/-! ## 0. Small generic `Q'` helpers -/

/-- Two-sided additive monotonicity `a ≤ b → c ≤ d → a + c ≤ b + d`. -/
theorem qadd_le_add {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-- `(A + b) + -b ≃ A`. -/
theorem add_sub_cancel (A b : Q') : ((A + b) + -b).eqv A := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A b (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left A _ 0 (Q'.add_neg_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' A)

/-! ## 1. The triangular number `triSum n = ∑_{i<n} i` and its exact quadratic
identity `2·triSum n + n ≃ n²`. -/

/-- `triSum n = ∑_{i<n} (i : Q')` (lowest term first). -/
def triSum : Nat → Q'
  | 0 => 0
  | n + 1 => triSum n + Q'.ofNat n

theorem triSum_nonneg : ∀ n, (0 : Q') ≤ triSum n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ triSum n + Q'.ofNat n
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' 0 (triSum n) _ (triSum_nonneg n)
          (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (triSum n))))))
        (Q'.add_le_add_left (triSum n) 0 (Q'.ofNat n) (zero_le_ofNat n))

/-- `ofNat 2 · m ≃ m + m`. -/
theorem two_mul_ofNat (n : Nat) :
    (Q'.ofNat 2 * Q'.ofNat n).eqv (Q'.ofNat n + Q'.ofNat n) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ofNat_mul_eqv 2 n)) ?_
  have h : 2 * n = n + n := by omega
  rw [h]
  exact Q'.ofNat_add_eqv n n

/-- `ofNat (n+1) ≃ ofNat n + 1`. -/
theorem ofNat_succ_eqv (n : Nat) : (Q'.ofNat (n + 1)).eqv (Q'.ofNat n + 1) :=
  Q'.ofNat_add_eqv n 1

/-- The core one-variable ring identity `(m+1)·(m+1) ≃ m·m + (m + (m+1))`. -/
theorem sq_succ (m : Q') :
    ((m + 1) * (m + 1)).eqv (m * m + (m + (m + 1))) := by
  -- (m+1)(m+1) ≃ m(m+1) + 1(m+1) ≃ (m·m + m) + (m+1) ≃ m·m + (m + (m+1))
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv m 1 (m + 1)) ?_
  have h1 : (m * (m + 1)).eqv (m * m + m) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv m m 1) ?_
    exact Q'.add_eqv_congr_left (m * m) _ _ (Q'.mul_one_eqv m)
  have h2 : ((1 : Q') * (m + 1)).eqv (m + 1) := Q'.one_mul_eqv (m + 1)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h1 h2) ?_
  exact Q'.add_assoc_eqv (m * m) m (m + 1)

/-- **The exact quadratic identity** `2·triSum n + n ≃ n·n`. -/
theorem triSum_closed : ∀ n,
    (Q'.ofNat 2 * triSum n + Q'.ofNat n).eqv (Q'.ofNat n * Q'.ofNat n)
  | 0 => by decide
  | n + 1 => by
      -- LHS = 2·(triSum n + n) + (n+1)
      show (Q'.ofNat 2 * (triSum n + Q'.ofNat n) + Q'.ofNat (n + 1)).eqv
          (Q'.ofNat (n + 1) * Q'.ofNat (n + 1))
      have IH : (Q'.ofNat 2 * triSum n + Q'.ofNat n).eqv (Q'.ofNat n * Q'.ofNat n) :=
        triSum_closed n
      have hsucc : (Q'.ofNat (n + 1)).eqv (Q'.ofNat n + 1) := ofNat_succ_eqv n
      -- expand 2·(triSum n + n) ≃ 2·triSum n + (n + n)
      have hexp : (Q'.ofNat 2 * (triSum n + Q'.ofNat n)).eqv
          (Q'.ofNat 2 * triSum n + (Q'.ofNat n + Q'.ofNat n)) := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 2) (triSum n) (Q'.ofNat n)) ?_
        exact Q'.add_eqv_congr_left _ _ _ (two_mul_ofNat n)
      -- LHS ≃ (2·triSum n + (n+n)) + ofNat(n+1)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (Q'.ofNat (n + 1)) hexp) ?_
      -- regroup ((2T + (n+n)) + (n+1)) ≃ (2T + n) + (n + (n+1))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (Q'.ofNat (n + 1))
          (Q'.add_eqv_congr_left (Q'.ofNat 2 * triSum n) _ _
            (Q'.eqv_refl (Q'.ofNat n + Q'.ofNat n)))) ?_
      -- ((2T) + (n+n)) + (n+1) ≃ (2T) + ((n+n) + (n+1))  [assoc]
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (Q'.ofNat 2 * triSum n) (Q'.ofNat n + Q'.ofNat n) (Q'.ofNat (n + 1))) ?_
      -- rewrite ofNat(n+1) ≃ n+1 inside, and (n+n)+(n+1) regroup to n + (n+(n+1))? We instead
      -- build the target (m·m + (m + (m+1))) with m = ofNat n.
      -- First push the inner sum: (n+n) + ofNat(n+1) ≃ n + (n + (n+1))  with ofNat(n+1)≃n+1.
      have hinner : ((Q'.ofNat n + Q'.ofNat n) + Q'.ofNat (n + 1)).eqv
          (Q'.ofNat n + (Q'.ofNat n + (Q'.ofNat n + 1))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ hsucc) ?_
        exact Q'.add_assoc_eqv (Q'.ofNat n) (Q'.ofNat n) (Q'.ofNat n + 1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (Q'.ofNat 2 * triSum n) _ _ hinner) ?_
      -- (2T) + (n + (n + (n+1))) ≃ ((2T) + n) + (n + (n+1))  [assoc symm]
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.add_assoc_eqv (Q'.ofNat 2 * triSum n) (Q'.ofNat n)
            (Q'.ofNat n + (Q'.ofNat n + 1)))) ?_
      -- replace (2T + n) by n·n (IH)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (Q'.ofNat n + (Q'.ofNat n + 1)) IH) ?_
      -- now goal: n·n + (n + (n + 1)) ≃ ofNat(n+1)·ofNat(n+1)
      -- RHS ≃ (n+1)·(n+1) by congr (hsucc both factors); then sq_succ.
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (n + 1)) hsucc) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat n + 1) _ _ hsucc) ?_
      exact sq_succ (Q'.ofNat n)

/-! ## 2. Bernoulli `w^n ≥ 1 − n·(1−w)` on `[0,1]` (local copy). -/

theorem qpow_ge_bernoulli {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (n : Nat) : (1 : Q') - Q'.ofNat n * ((1 : Q') - w) ≤ qpow w n := by
  have hfac : ((1 : Q') - qpow w n).eqv (((1 : Q') - w) * geomSum w n) :=
    oneSub_pow_factor w n
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hgs : geomSum w n ≤ Q'.ofNat n := geomSum_le hw0 hw1 n
  have hstep : ((1 : Q') - w) * geomSum w n ≤ ((1 : Q') - w) * Q'.ofNat n :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgs hnn
  have hle1 : (1 : Q') - qpow w n ≤ Q'.ofNat n * ((1 : Q') - w) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac)
      (Q'.le_trans' _ _ _ hstep
        (Q'.le_of_eqv (Q'.mul_comm_eqv ((1 : Q') - w) (Q'.ofNat n))))
  have h2 : (1 : Q') ≤ Q'.ofNat n * ((1 : Q') - w) + qpow w n := by
    have hadd : ((1 : Q') - qpow w n) + qpow w n
        ≤ Q'.ofNat n * ((1 : Q') - w) + qpow w n :=
      Q'.add_le_add_right _ _ (qpow w n) hle1
    have ecollapse : (((1 : Q') - qpow w n) + qpow w n).eqv (1 : Q') := by
      show (((1 : Q') + -(qpow w n)) + qpow w n).eqv (1 : Q')
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (1 : Q') (-(qpow w n)) (qpow w n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (1 : Q') _ 0 (Q'.neg_add_self_eqv (qpow w n))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv ecollapse) hadd
  exact Q'.sub_le_of_le_add h2

/-! ## 3. The QUADRATIC-FROM-BELOW engine -/

/-- **Sub-lemma A.**  `(1−w)·(i·w^i) ≤ 1 − w^i` on `[0,1]`: from `1 − w^i =
(1−w)·geomSum w i` and `i·w^i ≤ i·w^{i−1} ≤ geomSum w i`. -/
theorem subA {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (i : Nat) :
    ((1 : Q') - w) * (Q'.ofNat i * qpow w i) ≤ (1 : Q') - qpow w i := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hanti : qpow w i ≤ qpow w (i - 1) :=
    qpow_antitone hw0 hw1 (i - 1) i (Nat.sub_le i 1)
  have hpoly : Q'.ofNat i * qpow w i ≤ Q'.ofNat i * qpow w (i - 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hanti (zero_le_ofNat i)
  have hgepow : Q'.ofNat i * qpow w (i - 1) ≤ geomSum w i := geomSum_ge_pow hw0 hw1 i
  have h1 : Q'.ofNat i * qpow w i ≤ geomSum w i := Q'.le_trans' _ _ _ hpoly hgepow
  have h2 : ((1 : Q') - w) * (Q'.ofNat i * qpow w i) ≤ ((1 : Q') - w) * geomSum w i :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h1 hnn
  have h3 : (((1 : Q') - w) * geomSum w i).eqv ((1 : Q') - qpow w i) :=
    Q'.eqv_symm (oneSub_pow_factor w i)
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv h3)

/-- **The deficit lower bound** `(1−w)·(w^n·triSum n) ≤ n − geomSum w n` on
`[0,1]`, by induction on `n`. -/
theorem lowDeficit {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : ∀ n,
    ((1 : Q') - w) * (qpow w n * triSum n) ≤ Q'.ofNat n - geomSum w n
  | 0 => by
      -- both sides ≃ 0
      have hinner : (qpow w 0 * triSum 0).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (qpow w 0) (triSum 0)) (Q'.zero_mul_eqv (qpow w 0))
      have hL : (((1 : Q') - w) * (qpow w 0 * triSum 0)).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ hinner)
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv ((1 : Q') - w) 0) (Q'.zero_mul_eqv ((1 : Q') - w)))
      have hR : (Q'.ofNat 0 - geomSum w 0).eqv 0 := by rw [geomSum_zero]; decide
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR))
  | n + 1 => by
      have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
      have IH : ((1 : Q') - w) * (qpow w n * triSum n) ≤ Q'.ofNat n - geomSum w n :=
        lowDeficit hw0 hw1 n
      -- RHS(n+1) ≃ (ofNat n − geomSum w n) + (1 − qpow w n)
      have hRHS : (Q'.ofNat (n + 1) - geomSum w (n + 1)).eqv
          ((Q'.ofNat n - geomSum w n) + ((1 : Q') - qpow w n)) := by
        show (Q'.ofNat (n + 1) + -(geomSum w n + qpow w n)).eqv
            ((Q'.ofNat n + -(geomSum w n)) + ((1 : Q') + -(qpow w n)))
        -- ofNat(n+1) ≃ ofNat n + 1
        have hsucc : (Q'.ofNat (n + 1)).eqv (Q'.ofNat n + 1) := ofNat_succ_eqv n
        -- -(g + q) ≃ -g + -q
        have hneg : (-(geomSum w n + qpow w n)).eqv (-(geomSum w n) + -(qpow w n)) :=
          Q'.neg_add_eqv (geomSum w n) (qpow w n)
        -- 1 + (-g + -q) ≃ -g + (1 + -q)
        have hmid : ((1 : Q') + (-(geomSum w n) + -(qpow w n))).eqv
            (-(geomSum w n) + ((1 : Q') + -(qpow w n))) := by
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(geomSum w n)) (-(qpow w n)))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ (-(qpow w n)) (Q'.add_comm_eqv (1 : Q') (-(geomSum w n)))) ?_
          exact Q'.add_assoc_eqv (-(geomSum w n)) (1 : Q') (-(qpow w n))
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hsucc hneg) ?_
        -- (ofNat n + 1) + (-g + -q) ≃ ofNat n + (1 + (-g+-q)) ≃ ofNat n + (-g + (1+-q))
        --   ≃ (ofNat n + -g) + (1 + -q)
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (Q'.ofNat n) 1 (-(geomSum w n) + -(qpow w n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Q'.ofNat n) _ _ hmid) ?_
        exact Q'.eqv_symm
          (Q'.add_assoc_eqv (Q'.ofNat n) (-(geomSum w n)) ((1 : Q') + -(qpow w n)))
      -- swap LHS to (ofNat n + -g) + (1 + -q) form is done; now bound the two terms.
      -- LHS(n+1) ≃ term1 + term2
      have hLHS : (((1 : Q') - w) * (qpow w (n + 1) * triSum (n + 1))).eqv
          ((((1 : Q') - w) * ((qpow w n * w) * triSum n))
            + (((1 : Q') - w) * ((qpow w n * w) * Q'.ofNat n))) := by
        show (((1 : Q') - w) * ((qpow w n * w) * (triSum n + Q'.ofNat n))).eqv _
        have hin : (((qpow w n * w) * (triSum n + Q'.ofNat n))).eqv
            (((qpow w n * w) * triSum n) + ((qpow w n * w) * Q'.ofNat n)) :=
          Q'.mul_add_eqv (qpow w n * w) (triSum n) (Q'.ofNat n)
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ hin) ?_
        exact Q'.mul_add_eqv ((1 : Q') - w) ((qpow w n * w) * triSum n)
          ((qpow w n * w) * Q'.ofNat n)
      -- term1 ≤ ofNat n − geomSum w n
      have hqle : qpow w n * w ≤ qpow w n := by
        have := qpow_succ_le hw0 hw1 n
        -- qpow w (n+1) = qpow w n * w
        exact this
      have ht1 : ((1 : Q') - w) * ((qpow w n * w) * triSum n)
          ≤ Q'.ofNat n - geomSum w n := by
        have hstep : (qpow w n * w) * triSum n ≤ qpow w n * triSum n :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hqle (triSum_nonneg n)
        have hstep2 : ((1 : Q') - w) * ((qpow w n * w) * triSum n)
            ≤ ((1 : Q') - w) * (qpow w n * triSum n) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hstep hnn
        exact Q'.le_trans' _ _ _ hstep2 IH
      -- term2 ≤ 1 − qpow w n
      have ht2 : ((1 : Q') - w) * ((qpow w n * w) * Q'.ofNat n)
          ≤ (1 : Q') - qpow w n := by
        -- (qpow w n*w)*ofNat n ≤ qpow w n*ofNat n ≃ ofNat n*qpow w n
        have hstep : (qpow w n * w) * Q'.ofNat n ≤ qpow w n * Q'.ofNat n :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hqle (zero_le_ofNat n)
        have hcomm : (qpow w n * Q'.ofNat n).eqv (Q'.ofNat n * qpow w n) :=
          Q'.mul_comm_eqv (qpow w n) (Q'.ofNat n)
        have hle : (qpow w n * w) * Q'.ofNat n ≤ Q'.ofNat n * qpow w n :=
          Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcomm)
        have hstep2 : ((1 : Q') - w) * ((qpow w n * w) * Q'.ofNat n)
            ≤ ((1 : Q') - w) * (Q'.ofNat n * qpow w n) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hle hnn
        exact Q'.le_trans' _ _ _ hstep2 (subA hw0 hw1 n)
      -- assemble
      have hsum : (((1 : Q') - w) * ((qpow w n * w) * triSum n))
            + (((1 : Q') - w) * ((qpow w n * w) * Q'.ofNat n))
          ≤ (Q'.ofNat n - geomSum w n) + ((1 : Q') - qpow w n) :=
        qadd_le_add ht1 ht2
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hRHS))

/-- **The per-mode renormalized bond-moving defect** (the OVERSHOOT of the matched
`s = 1` marginal-flow model over the true first-excited deviation at mode `s`):

    deltaRen w s  =  C₄(s)·(1 − w)  −  (1 − w^{C₄(s)}). -/
def deltaRen (w : Q') (s : Nat) : Q' :=
  Q'.ofNat (c4 s) * ((1 : Q') - w) - ((1 : Q') - qpow w (c4 s))

/-- **THE QUADRATIC-FROM-BELOW BOUND** (the engine, at general exponent `n`):

    (1 − w)²·(w^n · triSum n)  ≤  n·(1 − w) − (1 − w^n). -/
theorem overshoot_lower {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat) :
    (((1 : Q') - w) * ((1 : Q') - w)) * (qpow w n * triSum n)
      ≤ Q'.ofNat n * ((1 : Q') - w) - ((1 : Q') - qpow w n) := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hdef : ((1 : Q') - w) * (qpow w n * triSum n) ≤ Q'.ofNat n - geomSum w n :=
    lowDeficit hw0 hw1 n
  -- multiply by (1−w) ≥ 0 on the left
  have hmul : ((1 : Q') - w) * (((1 : Q') - w) * (qpow w n * triSum n))
      ≤ ((1 : Q') - w) * (Q'.ofNat n - geomSum w n) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdef hnn
  -- LHS reassoc: (1−w)·((1−w)·X) ≃ ((1−w)·(1−w))·X
  have hLeq : (((1 : Q') - w) * (((1 : Q') - w) * (qpow w n * triSum n))).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * (qpow w n * triSum n)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv ((1 : Q') - w) ((1 : Q') - w) (qpow w n * triSum n))
  -- RHS: (1−w)·(n − geomSum) ≃ overshoot  (linOvershoot_eq, symm)
  have hReq : (((1 : Q') - w) * (Q'.ofNat n - geomSum w n)).eqv
      (Q'.ofNat n * ((1 : Q') - w) - ((1 : Q') - qpow w n)) :=
    Q'.eqv_symm (linOvershoot_eq w n)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLeq) (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hReq))

/-- The two-sided per-mode characterization (LOWER side), specialized to `n = C₄(s)`:

    (1 − w)²·(w^{C₄(s)}·triSum(C₄(s)))  ≤  deltaRen w s. -/
theorem deltaRen_lower {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    (((1 : Q') - w) * ((1 : Q') - w)) * (qpow w (c4 s) * triSum (c4 s))
      ≤ deltaRen w s :=
  overshoot_lower hw0 hw1 (c4 s)

/-- The two-sided per-mode characterization (UPPER side), from `secondOrder_qpow`:

    deltaRen w s  ≤  C₄(s)²·(1 − w)². -/
theorem deltaRen_upper {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    deltaRen w s
      ≤ (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
  secondOrder_qpow hw0 hw1 (c4 s)

/-! ## 4. THE SHARP NEGATIVE RESULT — the bulk per-mode floor

On the BULK window `1/2 ≤ n·(1−w) ≤ 3/4` with `(1−w) ≤ 1/4`, the overshoot is
`≥ 1/128`: a positive constant independent of `w`. -/

/-- `1/2`. -/ def q12 : Q' := Q'.mkPos 1 2 (by decide)
/-- `3/4`. -/ def q34 : Q' := Q'.mkPos 3 4 (by decide)
/-- `1/4`. -/ def q14 : Q' := Q'.mkPos 1 4 (by decide)
/-- `3/16`. -/ def q316 : Q' := Q'.mkPos 3 16 (by decide)
/-- `1/16`. -/ def q116 : Q' := Q'.mkPos 1 16 (by decide)
/-- `1/32`. -/ def q132 : Q' := Q'.mkPos 1 32 (by decide)
/-- `1/128`. -/ def q1128 : Q' := Q'.mkPos 1 128 (by decide)

/-! **THE BULK PER-MODE FLOOR.**  For `0 ≤ w ≤ 1` with `1 − w ≤ 1/4`, and any `n`
on the bulk window `1/2 ≤ n·(1 − w) ≤ 3/4`, the renormalized overshoot is bounded
below by the absolute constant `1/128`:  `n·(1 − w) − (1 − w^n) ≥ 1/128`.  So the
renormalized per-mode defect is `Θ(1) = O((1 − w)⁰)` on the bulk window — it does
NOT vanish as `w → 1`.  PROOF: `overshoot ≥ (1−w)²·w^n·triSum n`; Bernoulli gives
`w^n ≥ 1/4`; the exact identity `2·(1−w)²·triSum n + (1−w)·t ≃ t²` (`t = n·(1−w)`)
plus `t² ≥ 1/4`, `(1−w)·t ≤ 3/16` give `(1−w)²·triSum n ≥ 1/32`, hence `≥ 1/128`. -/

/-- **The abstract quadratic identity** `2·((e·e)·T) + e·(m·e) ≃ (m·e)·(m·e)`, given
the triangular-closed form `2·T + m ≃ m·m`.  (Pure `Q'` ring rearrangement; this is
the `triSum_closed` content lifted onto the margin-scaled bulk quantities, with
`e = 1 − w`, `m = C₄(s)`, `T = triSum(C₄(s))`.) -/
theorem sq_identity (e m T : Q') (hcl : (Q'.ofNat 2 * T + m).eqv (m * m)) :
    (Q'.ofNat 2 * ((e * e) * T) + e * (m * e)).eqv ((m * e) * (m * e)) := by
  have hA : ((e * e) * (Q'.ofNat 2 * T + m)).eqv ((e * e) * (m * m)) :=
    Q'.mul_eqv_congr_left (e * e) _ _ hcl
  have hB : ((e * e) * (Q'.ofNat 2 * T + m)).eqv
      ((e * e) * (Q'.ofNat 2 * T) + (e * e) * m) :=
    Q'.mul_add_eqv (e * e) (Q'.ofNat 2 * T) m
  have hC : ((e * e) * (Q'.ofNat 2 * T)).eqv (Q'.ofNat 2 * ((e * e) * T)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (e * e) (Q'.ofNat 2) T)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ T (Q'.mul_comm_eqv (e * e) (Q'.ofNat 2))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofNat 2) (e * e) T
  have hD : ((e * e) * m).eqv (e * (m * e)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv e e m) ?_
    exact Q'.mul_eqv_congr_left e _ _ (Q'.mul_comm_eqv e m)
  have hE : ((e * e) * (m * m)).eqv ((m * e) * (m * e)) := by
    refine Q'.eqv_trans _ _ _ (mul_four_swap e e m m) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (e * m) (Q'.mul_comm_eqv e m)) ?_
    exact Q'.mul_eqv_congr_left (m * e) _ _ (Q'.mul_comm_eqv e m)
  have hLHS' : (Q'.ofNat 2 * ((e * e) * T) + e * (m * e)).eqv
      ((e * e) * (Q'.ofNat 2 * T + m)) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ hB ?_
    exact Q'.add_eqv_congr' hC hD
  exact Q'.eqv_trans _ _ _ hLHS' (Q'.eqv_trans _ _ _ hA hE)

/-- **The abstract numeric floor.**  With `e ≤ 1/4`, `1/2 ≤ t ≤ 3/4`, and the
identity `2·((e·e)·T) + e·t ≃ t·t`, the scaled core is `≥ 1/128`:

    1/128  ≤  (e·e)·(1/4 · T).

(`t·t ≥ 1/4`, `e·t ≤ 3/16` ⇒ `(e·e)·T ≥ 1/32` ⇒ `(1/4)·(e·e)·T ≥ 1/128`.) -/
theorem floor_numeric (e T t : Q')
    (he_le : e ≤ q14) (ht_lo : q12 ≤ t) (ht_hi : t ≤ q34)
    (hid : (Q'.ofNat 2 * ((e * e) * T) + e * t).eqv (t * t)) :
    q1128 ≤ (e * e) * (q14 * T) := by
  have hPlow_eq : ((e * e) * (q14 * T)).eqv (q14 * ((e * e) * T)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (e * e) q14 T)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ T (Q'.mul_comm_eqv (e * e) q14)) ?_
    exact Q'.mul_assoc_eqv q14 (e * e) T
  have ht_nn : (0 : Q') ≤ t := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ q12) ht_lo
  have ht_sq : q14 ≤ t * t := by
    have hsq : q12 * q12 ≤ t * t := sq_le_sq (by decide : (0 : Q') ≤ q12) ht_lo
    exact Q'.le_trans' _ _ _ (by decide : q14 ≤ q12 * q12) hsq
  have heps_t : e * t ≤ q316 := by
    have s1 : e * t ≤ q14 * t := Q'.mul_le_mul_of_nonneg_right _ _ _ he_le ht_nn
    have s2 : q14 * t ≤ q14 * q34 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ ht_hi (by decide : (0 : Q') ≤ q14)
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ s1 s2) (by decide : q14 * q34 ≤ q316)
  have h2P : q116 ≤ Q'.ofNat 2 * ((e * e) * T) := by
    have h2Peq : (Q'.ofNat 2 * ((e * e) * T)).eqv (t * t + -(e * t)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (add_sub_cancel (Q'.ofNat 2 * ((e * e) * T)) (e * t))) ?_
      exact Q'.add_eqv_congr_right _ _ (-(e * t)) hid
    have hbound : q116 ≤ t * t + -(e * t) := by
      have hnegle : -q316 ≤ -(e * t) := Q'.neg_le_neg heps_t
      have hsum : q14 + -q316 ≤ t * t + -(e * t) := qadd_le_add ht_sq hnegle
      exact Q'.le_trans' _ _ _ (by decide : q116 ≤ q14 + -q316) hsum
    exact Q'.le_trans' _ _ _ hbound (Q'.ge_of_eqv h2Peq)
  have hP : q132 ≤ (e * e) * T := by
    have hmul : q12 * q116 ≤ q12 * (Q'.ofNat 2 * ((e * e) * T)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ h2P (by decide : (0 : Q') ≤ q12)
    have hcollapse : (q12 * (Q'.ofNat 2 * ((e * e) * T))).eqv ((e * e) * T) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q12 (Q'.ofNat 2) ((e * e) * T))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((e * e) * T) (by decide : (q12 * Q'.ofNat 2).eqv 1)) ?_
      exact Q'.one_mul_eqv ((e * e) * T)
    exact Q'.le_trans' _ _ _ (by decide : q132 ≤ q12 * q116)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcollapse))
  have hfin : q1128 ≤ q14 * ((e * e) * T) := by
    have hmul : q14 * q132 ≤ q14 * ((e * e) * T) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hP (by decide : (0 : Q') ≤ q14)
    exact Q'.le_trans' _ _ _ (by decide : q1128 ≤ q14 * q132) hmul
  exact Q'.le_trans' _ _ _ hfin (Q'.ge_of_eqv hPlow_eq)

theorem overshoot_floor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat)
    (hε : (1 : Q') - w ≤ q14)
    (hlo : q12 ≤ Q'.ofNat n * ((1 : Q') - w))
    (hhi : Q'.ofNat n * ((1 : Q') - w) ≤ q34) :
    q1128 ≤ Q'.ofNat n * ((1 : Q') - w) - ((1 : Q') - qpow w n) := by
  have hεnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hBnn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) := Q'.mul_nonneg _ _ hεnn hεnn
  -- (1) engine
  have hEng : (((1 : Q') - w) * ((1 : Q') - w)) * (qpow w n * triSum n)
      ≤ Q'.ofNat n * ((1 : Q') - w) - ((1 : Q') - qpow w n) := overshoot_lower hw0 hw1 n
  -- (2) Bernoulli: q14 ≤ w^n
  have hq14 : q14 ≤ qpow w n := by
    have hbern : (1 : Q') - Q'.ofNat n * ((1 : Q') - w) ≤ qpow w n := qpow_ge_bernoulli hw0 hw1 n
    have h_onesub : q14 ≤ (1 : Q') - Q'.ofNat n * ((1 : Q') - w) := by
      have hneg : -q34 ≤ -(Q'.ofNat n * ((1 : Q') - w)) := Q'.neg_le_neg hhi
      have hstep : (1 : Q') + -q34 ≤ (1 : Q') + -(Q'.ofNat n * ((1 : Q') - w)) :=
        Q'.add_le_add_left (1 : Q') _ _ hneg
      exact Q'.le_trans' _ _ _ (by decide : q14 ≤ (1 : Q') + -q34) hstep
    exact Q'.le_trans' _ _ _ h_onesub hbern
  -- (3) push q14 through the engine
  have hXlb : q14 * triSum n ≤ qpow w n * triSum n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hq14 (triSum_nonneg n)
  have hStep1 : (((1 : Q') - w) * ((1 : Q') - w)) * (q14 * triSum n)
      ≤ (((1 : Q') - w) * ((1 : Q') - w)) * (qpow w n * triSum n) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hXlb hBnn
  have hPlow_le : (((1 : Q') - w) * ((1 : Q') - w)) * (q14 * triSum n)
      ≤ Q'.ofNat n * ((1 : Q') - w) - ((1 : Q') - qpow w n) :=
    Q'.le_trans' _ _ _ hStep1 hEng
  -- (4) the abstract floor on the scaled core
  have hid : (Q'.ofNat 2 * ((((1 : Q') - w) * ((1 : Q') - w)) * triSum n)
        + ((1 : Q') - w) * (Q'.ofNat n * ((1 : Q') - w))).eqv
      ((Q'.ofNat n * ((1 : Q') - w)) * (Q'.ofNat n * ((1 : Q') - w))) :=
    sq_identity ((1 : Q') - w) (Q'.ofNat n) (triSum n) (triSum_closed n)
  have hfloor : q1128 ≤ (((1 : Q') - w) * ((1 : Q') - w)) * (q14 * triSum n) :=
    floor_numeric ((1 : Q') - w) (triSum n) (Q'.ofNat n * ((1 : Q') - w)) hε hlo hhi hid
  exact Q'.le_trans' _ _ _ hfloor hPlow_le

/-- **The per-mode bulk floor on `deltaRen`.**  On the bulk window
`1/2 ≤ C₄(s)·(1−w) ≤ 3/4` with `1−w ≤ 1/4`, `deltaRen w s ≥ 1/128`. -/
theorem deltaRen_floor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat)
    (hε : (1 : Q') - w ≤ q14)
    (hlo : q12 ≤ Q'.ofNat (c4 s) * ((1 : Q') - w))
    (hhi : Q'.ofNat (c4 s) * ((1 : Q') - w) ≤ q34) :
    q1128 ≤ deltaRen w s :=
  overshoot_floor hw0 hw1 (c4 s) hε hlo hhi

/-! ## 5. The scaled bulk-window sums and the termwise reduction -/

/-- A windowed termwise `≤` for `finSum`: only the in-range terms `k < n` need to
be compared. -/
theorem finSum_le_win (f g : Nat → Q') :
    ∀ n, (∀ k, k < n → f k ≤ g k) → RationalTail.finSum f n ≤ RationalTail.finSum g n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      show RationalTail.finSum f n + f n ≤ RationalTail.finSum g n + g n
      have hrec : RationalTail.finSum f n ≤ RationalTail.finSum g n :=
        finSum_le_win f g n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hk : f n ≤ g n := h n (Nat.lt_succ_self n)
      exact qadd_le_add hrec hk

/-- Pulling a constant out of a `finSum`: `c · (∑ g) ≃ ∑ (c · g)`. -/
theorem finSum_const_mul (c : Q') (g : Nat → Q') :
    ∀ n, (c * RationalTail.finSum g n).eqv (RationalTail.finSum (fun k => c * g k) n)
  | 0 => by
      show (c * (0 : Q')).eqv (0 : Q')
      exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv c 0) (Q'.zero_mul_eqv c)
  | n + 1 => by
      show (c * (RationalTail.finSum g n + g n)).eqv
          (RationalTail.finSum (fun k => c * g k) n + c * g n)
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (RationalTail.finSum g n) (g n)) ?_
      exact Q'.add_eqv_congr_right _ _ (c * g n) (finSum_const_mul c g n)

/-- The total normalized bulk mass `∑_{k<L} μ(a+k)` (the scaled mass on the bulk
window `[a, a+L)`). -/
def bulkMassNorm (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (a L : Nat) : Q' :=
  RationalTail.finSum (fun k => μ w N hZ (a + k)) L

/-- The SCALED bulk contribution `∑_{k<L} μ(a+k)·deltaRen(a+k)` (the scaled-norm
bulk-window sum of the renormalized per-mode defect). -/
def bulkSum (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (a L : Nat) : Q' :=
  RationalTail.finSum (fun k => μ w N hZ (a + k) * deltaRen w (a + k)) L

/-- **The bulk reduction.**  If every window mode has `deltaRen ≥ 1/128` (the bulk
floor), then `bulkSum w ≥ (1/128)·bulkMassNorm w`. -/
theorem bulkSum_ge {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (a L : Nat) (hfloor : ∀ k, k < L → q1128 ≤ deltaRen w (a + k)) :
    q1128 * bulkMassNorm w N hZ a L ≤ bulkSum w N hZ a L := by
  -- termwise: q1128·μ(a+k) ≤ μ(a+k)·deltaRen(a+k)
  have hterm : ∀ k, k < L →
      q1128 * μ w N hZ (a + k) ≤ μ w N hZ (a + k) * deltaRen w (a + k) := by
    intro k hk
    have hμnn : (0 : Q') ≤ μ w N hZ (a + k) := μ_nonneg hw0 N hZ (a + k)
    have hcomm : (q1128 * μ w N hZ (a + k)).eqv (μ w N hZ (a + k) * q1128) :=
      Q'.mul_comm_eqv q1128 (μ w N hZ (a + k))
    have hmono : μ w N hZ (a + k) * q1128 ≤ μ w N hZ (a + k) * deltaRen w (a + k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (hfloor k hk) hμnn
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) hmono
  have hsumle : RationalTail.finSum (fun k => q1128 * μ w N hZ (a + k)) L
      ≤ bulkSum w N hZ a L :=
    finSum_le_win _ _ L hterm
  have hfactor : (q1128 * bulkMassNorm w N hZ a L).eqv
      (RationalTail.finSum (fun k => q1128 * μ w N hZ (a + k)) L) :=
    finSum_const_mul q1128 (fun k => μ w N hZ (a + k)) L
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hsumle

/-! ## 6. THE PACKAGED VERDICT — `BulkObstruction` -/

/-- **The bulk obstruction certificate.**  A `Type`-level package: a populated bulk
window `[a, a+L)` (every mode satisfies the Casimir-margin window), the near-
continuum regime `1 − w ≤ 1/4`, and the ONE genuinely-open GLOBAL analytic input —
the `O(1)` normalized bulk-mass fraction `bulkMassNorm ≥ c_mass > 0`.  (That
`c_mass = O(1)` is the constant-fraction-of-mass statement: `Z ∼ (1−w)^{−3/2}` and
the bulk window at `s ∼ 1/√(1−w)` carries the same order; it is the residual
`Z`-comparison, named here as data, not faked.) -/
structure BulkObstruction (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (a L : Nat) : Type where
  /-- Near-continuum regime. -/
  hε : (1 : Q') - w ≤ q14
  /-- The bulk window is genuinely populated by the modes `a, …, a+L−1`. -/
  hwindow : ∀ k, k < L →
    q12 ≤ Q'.ofNat (c4 (a + k)) * ((1 : Q') - w)
      ∧ Q'.ofNat (c4 (a + k)) * ((1 : Q') - w) ≤ q34
  /-- The `O(1)` normalized bulk-mass fraction (the named global input). -/
  cmass : Q'
  /-- Its positivity. -/
  hcmass_pos : (0 : Q') < cmass
  /-- The mass lower bound. -/
  hmass : cmass ≤ bulkMassNorm w N hZ a L

/-- **THE OBSTRUCTION.**  From a `BulkObstruction`, the SCALED bulk contribution is
bounded below by the POSITIVE CONSTANT `(1/128)·c_mass`, independent of `w`:

    bulkSum w  ≥  (1/128)·c_mass  >  0.

So the heat-kernel-SCALED reweighting leaves a NON-VANISHING bulk: `bulkSum w` does
NOT tend to `0` as `w → 1`.  This is the SHARP order verdict (b): per-`s`
heat-kernel weighting is INSUFFICIENT. -/
theorem bulkObstruction_floor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (a L : Nat)
    (ob : BulkObstruction w N hZ a L) :
    q1128 * ob.cmass ≤ bulkSum w N hZ a L := by
  -- per-mode floor on the window
  have hfloor : ∀ k, k < L → q1128 ≤ deltaRen w (a + k) := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := ob.hwindow k hk
    exact deltaRen_floor hw0 hw1 (a + k) ob.hε hlo hhi
  -- bulkSum ≥ (1/128)·bulkMassNorm ≥ (1/128)·cmass
  have h1 : q1128 * bulkMassNorm w N hZ a L ≤ bulkSum w N hZ a L :=
    bulkSum_ge hw0 N hZ a L hfloor
  have h2 : q1128 * ob.cmass ≤ q1128 * bulkMassNorm w N hZ a L :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ ob.hmass (by decide : (0 : Q') ≤ q1128)
  exact Q'.le_trans' _ _ _ h2 h1

/-! ## 7. Demo — the bulk floor FIRES at a concrete near-continuum weight

At `w = 29/32` (`1 − w = 3/32 ≤ 1/4`), the mode `s = 2` has `C₄(2) = 8` and
`8·(3/32) = 3/4`, on the bulk window `[1/2, 3/4]`.  The floor gives
`deltaRen (29/32) 2 ≥ 1/128`: a concrete non-vanishing renormalized defect at a
genuine bulk mode (the per-mode obstruction is REAL, not posited). -/

/-- The demo weight `w = 29/32`. -/
def demoW : Q' := Q'.mkPos 29 32 (by decide)

theorem demoW_pos : (0 : Q') ≤ demoW := by decide
theorem demoW_le_one : demoW ≤ (1 : Q') := by decide

/-- **The bulk floor fires at `w = 29/32`, `s = 2`.**  `deltaRen (29/32) 2 ≥ 1/128`
— the renormalized per-mode defect on a genuine bulk mode is a positive constant. -/
theorem demo_floor : q1128 ≤ deltaRen demoW 2 :=
  deltaRen_floor demoW_pos demoW_le_one 2
    (by decide) (by decide) (by decide)

end YMGap.Continuum.BulkModeCrux

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BulkModeCrux.triSum_closed
#print axioms YMGap.Continuum.BulkModeCrux.qpow_ge_bernoulli
#print axioms YMGap.Continuum.BulkModeCrux.subA
#print axioms YMGap.Continuum.BulkModeCrux.lowDeficit
#print axioms YMGap.Continuum.BulkModeCrux.overshoot_lower
#print axioms YMGap.Continuum.BulkModeCrux.deltaRen_lower
#print axioms YMGap.Continuum.BulkModeCrux.deltaRen_upper
#print axioms YMGap.Continuum.BulkModeCrux.overshoot_floor
#print axioms YMGap.Continuum.BulkModeCrux.deltaRen_floor
#print axioms YMGap.Continuum.BulkModeCrux.finSum_le_win
#print axioms YMGap.Continuum.BulkModeCrux.finSum_const_mul
#print axioms YMGap.Continuum.BulkModeCrux.bulkSum_ge
#print axioms YMGap.Continuum.BulkModeCrux.bulkObstruction_floor
#print axioms YMGap.Continuum.BulkModeCrux.demo_floor
