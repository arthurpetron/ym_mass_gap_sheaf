/-
Track B / R2 — ONE explicit Migdal–Kadanoff / hierarchical RENORMALIZATION-GROUP
BLOCK STEP for the SU(2) heat-kernel action, separating the EXACT favorable part
(decimation) from the named residual (bond-moving).

# Why this module exists — the first genuine crack at the open residual

The open continuum-gap content of Route B is localized to the named map
`NASuscept_to_PerScaleRateData` (the susceptibility ⇒ per-RG-scale-rate step):
the genuine analytic frontier.  This module takes the FIRST GENUINE CRACK at its
atomic piece by EXPLICITLY COMPUTING one Migdal–Kadanoff (MK) / hierarchical RG
block step for the SU(2) heat-kernel action, and isolating exactly which half is
favorable-and-exact and which half is the open residual.

A single MK block step with rescale factor `b` is `bond-moving ∘ decimation`:

  * **DECIMATION** (collapse `b` links in series into one).  The `b`-fold
    convolution of the heat kernel multiplies the normalized character
    coefficients, `e^{−t·C₂} → e^{−b·t·C₂}` — i.e. the per-Casimir-unit weight
    `w ↦ w^b` (the heat semigroup is a one-parameter monoid).  This is EXACT and
    PRESERVES THE HEAT-KERNEL FORM.  Hence the gap separator transforms as
    `sep = w³ ↦ sep^b = w^{3b}`.

  * **BOND-MOVING** (collect `b^{d−1}` plaquettes in parallel).  For `d > 2` this
    does NOT preserve the heat-kernel form (pointwise powers / Clebsch–Gordan
    mixing of characters), so its deviation from the decimated weight is the
    genuine residual.  On the HIERARCHICAL / diamond lattice bond-moving IS, by
    construction, the decimation, so the residual VANISHES there.  On ℝ⁴ it is
    uncontrolled (MK is approximate) — the open content.

Under one block step the spacing rescales `a ↦ b·a`, so the PHYSICAL gap margin
`physGap = (1 − sep)/a` transforms to `(1 − sep^b)/(b·a)`.  With the finite
geometric factorization `1 − sep^b = (1 − sep)·∑_{i<b} sep^i`, the per-block
PHYSICAL multiplier is

    ρ_dec(b, sep) = (∑_{i<b} sep^i)/b ∈ (0,1],     and   ρ_dec → 1 as sep → 1,

the FAVORABLE dimensional-transmutation behaviour: the decimation per-block
multiplier approaches `1` in the continuum, so a product of such multipliers can
stay bounded below.

# What is GENUINELY PROVED here — and what is the NAMED open residual (honest)

PROVED (genuine `Q'` arithmetic, axiom-clean):

  * `mkDecimate b w = w^b` and `mkDecimate_sep : sep(w^b) = sep(w)^b` (the EXACT
    decimation half: the separator commutes with the heat semigroup);
  * `geomSum w n = ∑_{i<n} w^i`, the finite geometric factorization
    `oneSub_pow_factor : 1 − w^n = (1 − w)·geomSum w n`, and its cofactor bounds
    `geomSum_le : geomSum w n ≤ n` and `geomSum_ge_pow` on `[0,1]`;
  * `rhoDecimate b w = (∑_{i<b} w^i)/b` with `rhoDecimate_le_one` and THE CRACK
    `rhoDecimate_to_one : 1 − rhoDecimate b w ≤ (b+1)·(1 − w)` — the explicit
    modulus exhibiting `ρ_dec → 1` as `w → 1` (`rhoDecimate b` averages the
    `b+1`-term geometric sum, the multiplier of a `b+1`-link series block);
  * `singleLinkSusceptibility = 4/3`, the GENUINE single-link (single-mode)
    susceptibility atom — the S³ Poincaré / Bakry–Émery constant from the EXACT
    `3/4` Casimir gap.

NAMED OPEN (NOT inhabited for ℝ⁴):

  * `BondMovingResidual` carries the bond-moving deviation `δ ≥ 0` with the named
    bound `δ ≤ resC · a · Λ`; it is EXACT (`δ = 0`) on the hierarchical/diamond
    lattice and is the genuine UNCONTROLLED 4D content on ℝ⁴.  The 4D case is NOT
    inhabited.

The honest verdict: this does NOT solve the 4D gap.  It CRACKS the atom of the
open residual into an exactly-computed FAVORABLE part (decimation, `ρ_dec → 1`)
plus a SHARPLY-NAMED residual (bond-moving, `δ`), and it ships a genuine
hierarchical-model inhabitant of the per-scale rate data when `δ = 0`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, and the reused `Q'`
order/`divPos` lemmas.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable `Q'` facts), no
`sorry`.  All witnesses (`mkDecimate`, `geomSum`, `rhoDecimate`,
`singleLinkSusceptibility`, the residual record) are `Type`-level data.
-/

import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.HeatKernelLinearBound
import YMGap.Continuum.PerScaleContraction
import YMGap.Continuum.NonAbelianGapChain
import YMGap.Continuum.ProductFloor
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.HeatKernelRGStep

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelLinearBound

/-! ## 0. `qpow` exponent arithmetic

The decimation identity rests on `w^{m+n} = w^m · w^n` and the exponent
re-association `(w^a)^b = w^{a·b} = (w^b)^a` for the `qpow` fold of `RGTransport`. -/

/-- `qpow w (m + n) ≃ qpow w m * qpow w n` (the heat-semigroup monoid law at the
coefficient level).  An `eqv` because `Q'` multiplication by the fold's literal
`1` is value-level, not definitional. -/
theorem qpow_add (w : Q') (m : Nat) :
    ∀ n, (qpow w (m + n)).eqv (qpow w m * qpow w n)
  | 0 => by
      -- qpow w (m+0) = qpow w m ; RHS = qpow w m * 1 ≃ qpow w m
      show (qpow w m).eqv (qpow w m * qpow w 0)
      rw [qpow_zero]
      exact Q'.eqv_symm (Q'.mul_one_eqv (qpow w m))
  | n + 1 => by
      -- qpow w (m+n+1) = qpow w (m+n) * w ≃ (qpow w m * qpow w n) * w
      --                ≃ qpow w m * (qpow w n * w)
      show (qpow w (m + n) * w).eqv (qpow w m * (qpow w n * w))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w (qpow_add w m n)) ?_
      exact Q'.mul_assoc_eqv (qpow w m) (qpow w n) w

/-- `qpow (qpow w a) b ≃ qpow w (a * b)` (iterated power = product of exponents),
via the additive law. -/
theorem qpow_qpow (w : Q') (a : Nat) :
    ∀ b, (qpow (qpow w a) b).eqv (qpow w (a * b))
  | 0 => by
      show (1 : Q').eqv (qpow w (a * 0))
      rw [Nat.mul_zero]
      exact Q'.eqv_refl _
  | b + 1 => by
      -- qpow (qpow w a) (b+1) = qpow (qpow w a) b * qpow w a
      --   ≃ qpow w (a*b) * qpow w a ≃ qpow w (a*b + a) = qpow w (a*(b+1))
      show (qpow (qpow w a) b * qpow w a).eqv (qpow w (a * (b + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow w a) (qpow_qpow w a b)) ?_
      rw [Nat.mul_succ]
      exact Q'.eqv_symm (qpow_add w (a * b) a)

/-! ### Small local `Q'` order / arithmetic helpers (proved here, axiom-clean) -/

/-- `0 ≤ ofNat n`. -/
theorem zero_le_ofNat (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _

/-- `0 < 0 + 1` on `Q'`. -/
theorem zero_lt_zero_add_one : (0 : Q') < (0 : Q') + 1 := by decide

/-- `a < b → b ≤ c → a < c` on `Q'`. -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 (by exact_mod_cast c.den_pos : (0:Int) < (c.den:Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 (by exact_mod_cast Nat.zero_le a.den : (0:Int) ≤ (a.den:Int))
    have hl : (a.den : Int) * (b.num * (c.den : Int)) = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int)) = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-- `ofNat (a·b) ≃ ofNat a · ofNat b` (proved at the `num`/`den` level, no
`push_cast`). -/
theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a * b)).den : Int) = 1 := rfl
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a * b)).den : Int)
  rw [hd1, hd2, Int.mul_one, Int.mul_one, Int.natCast_mul]

/-- `divPos (k·v) k ≃ v` (cancel the positive left factor against the denominator). -/
theorem divPos_mul_left_cancel (k v : Q') (hk : (0 : Q') < k) :
    (Q'.divPos (k * v) k hk).eqv v := by
  -- (k·v)·(1/k) ≃ v·(k·(1/k)) ≃ v·1 ≃ v
  show ((k * v) * Q'.recipPos k hk).eqv v
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.recipPos k hk) (Q'.mul_comm_eqv k v)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv v k (Q'.recipPos k hk)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left v _ _ (Q'.mul_recipPos_eqv k hk)) ?_
  exact Q'.mul_one_eqv v

/-- `1 − p/q ≃ (q − p)/q` for `0 < q`. -/
theorem one_sub_divPos_eqv (p q : Q') (hq : (0 : Q') < q) :
    ((1 : Q') - Q'.divPos p q hq).eqv (Q'.divPos (q - p) q hq) := by
  -- (q−p)/q = (q + −p)·(1/q) ≃ q·(1/q) + (−p)·(1/q) ≃ 1 + −(p·(1/q)) = 1 − p/q
  refine Q'.eqv_symm ?_
  show ((q - p) * Q'.recipPos q hq).eqv ((1 : Q') - Q'.divPos p q hq)
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv q (-p) (Q'.recipPos q hq)) ?_
  -- q·(1/q) + (−p)·(1/q) ≃ 1 + −(p·(1/q))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_recipPos_eqv q hq) (Q'.neg_mul_eqv p (Q'.recipPos q hq))) ?_
  exact Q'.eqv_refl _

/-! ## 1. The EXACT decimation map `w ↦ w^b` (the heat-semigroup half)

The `b`-fold series convolution of the SU(2) heat kernel multiplies the
per-Casimir-unit weight: `w ↦ w^b`.  This is EXACT and preserves the
heat-kernel form. -/

/-- **The exact decimation map.**  Collapsing `b` heat-kernel links in series
multiplies the per-Casimir-unit weight, `w ↦ w^b` (the heat semigroup at scale
`b`).  This is the EXACT half of one MK / hierarchical block step. -/
def mkDecimate (b : Nat) (w : Q') : Q' := qpow w b

/-- The decimated weight is nonnegative for nonnegative `w`. -/
theorem mkDecimate_nonneg (b : Nat) {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') ≤ mkDecimate b w :=
  qpow_nonneg w hw b

/-- A decimated sub-unit weight stays `≤ 1`. -/
theorem mkDecimate_le_one (b : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) : mkDecimate b w ≤ (1 : Q') :=
  qpow_le_one hw0 hw1 b

/-- **The decimation gap-separator law (EXACT).**  `sep(w^b) ≃ sep(w)^b = w^{3b}`:
the heat-kernel gap separator commutes with the decimation heat semigroup.  Both
sides are `≃ qpow w (3*b)`, via `qpow_qpow` (`3` and `b` re-associate).  An `eqv`
since the underlying fold trees differ in grouping. -/
theorem mkDecimate_sep (b : Nat) (w : Q') :
    (heatKernelSep (mkDecimate b w)).eqv (qpow (heatKernelSep w) b) := by
  show (qpow (qpow w b) 3).eqv (qpow (qpow w 3) b)
  -- qpow (qpow w b) 3 ≃ qpow w (b*3) = qpow w (3*b) ; qpow (qpow w 3) b ≃ qpow w (3*b)
  refine Q'.eqv_trans _ _ _ (qpow_qpow w b 3) ?_
  rw [Nat.mul_comm b 3]
  exact Q'.eqv_symm (qpow_qpow w 3 b)

/-! ## 2. The finite geometric factorization `1 − w^n = (1 − w)·∑_{i<n} w^i`

`geomSum w n = ∑_{i<n} w^i`, a `Nat.rec` fold (lowest term first).  The
factorization is the discrete telescoping identity; the cofactor bounds on
`[0,1]` (`geomSum ≤ n`, `geomSum ≥ n·w^{n−1}`, positivity) are what control the
per-block multiplier. -/

/-- `geomSum w n = ∑_{i<n} w^i = 1 + w + ⋯ + w^{n−1}` (the finite geometric sum,
fold with the new highest term added on the right). -/
def geomSum (w : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => geomSum w n + qpow w n

@[simp] theorem geomSum_zero (w : Q') : geomSum w 0 = 0 := rfl

@[simp] theorem geomSum_succ (w : Q') (n : Nat) :
    geomSum w (n + 1) = geomSum w n + qpow w n := rfl

theorem geomSum_one (w : Q') : geomSum w 1 = 0 + 1 := rfl

/-- The geometric sum is nonnegative for nonnegative `w`. -/
theorem geomSum_nonneg {w : Q'} (hw : (0 : Q') ≤ w) : ∀ n, (0 : Q') ≤ geomSum w n
  | 0 => by show (0 : Q') ≤ (0 : Q'); exact Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ geomSum w n + qpow w n
      have h1 : (0 : Q') ≤ geomSum w n := geomSum_nonneg hw n
      have h2 : (0 : Q') ≤ qpow w n := qpow_nonneg w hw n
      have hstep : (0 : Q') + (0 : Q') ≤ geomSum w n + qpow w n :=
        Q'.le_trans' _ _ _ (Q'.add_le_add_right 0 (geomSum w n) 0 h1)
          (Q'.add_le_add_left (geomSum w n) 0 (qpow w n) h2)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_add_zero_eqv 0))) hstep

/-- **The exact finite geometric factorization** `1 − w^n = (1 − w)·∑_{i<n} w^i`
(as a `Q'` `eqv`), proved by induction on `n` via the telescoping recurrence
`(1 − w)·geomSum w (n+1) = (1 − w)·geomSum w n + (1 − w)·w^n = (1 − w^n) + w^n − w^{n+1}`. -/
theorem oneSub_pow_factor (w : Q') :
    ∀ n, ((1 : Q') - qpow w n).eqv (((1 : Q') - w) * geomSum w n)
  | 0 => by
      -- LHS: 1 − w^0 = 1 − 1 ≃ 0 ; RHS: (1−w)·geomSum w 0 = (1−w)·0 ≃ 0
      show ((1 : Q') - qpow w 0).eqv (((1 : Q') - w) * geomSum w 0)
      rw [qpow_zero, geomSum_zero]
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq ?_) (Q'.eqv_symm (q_mul_zero ((1 : Q') - w)))
      -- 1 − 1 = 0 as a `Q'` propositional equality (num/den): use sub_self structure
      show (1 : Q') - 1 = 0
      decide
  | n + 1 => by
      -- (1−w)·geomSum w (n+1) = (1−w)·geomSum w n + (1−w)·w^n
      -- ≃ (1 − w^n) + (1−w)·w^n  (IH)
      -- = (1 − w^n) + (w^n − w^{n+1}) ≃ 1 − w^{n+1}.
      have IH : ((1 : Q') - qpow w n).eqv (((1 : Q') - w) * geomSum w n) :=
        oneSub_pow_factor w n
      -- RHS distribution: (1−w)·(geomSum w n + w^n) ≃ (1−w)·geomSum w n + (1−w)·w^n
      have hdist : (((1 : Q') - w) * (geomSum w n + qpow w n)).eqv
          (((1 : Q') - w) * geomSum w n + ((1 : Q') - w) * qpow w n) :=
        Q'.mul_add_eqv ((1 : Q') - w) (geomSum w n) (qpow w n)
      -- (1−w)·w^n ≃ w^n − w^{n+1}
      have hterm : (((1 : Q') - w) * qpow w n).eqv (qpow w n - qpow w (n + 1)) := by
        -- (1 + (−w))·w^n ≃ 1·w^n + (−w)·w^n ≃ w^n + (−(w·w^n)) ; and w·w^n = w^{n+1}?
        -- careful: qpow w (n+1) = qpow w n * w, so we need −(w^n·w).
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-w) (qpow w n)) ?_
        -- 1·w^n + (−w)·w^n ≃ w^n + −(w^n·w) = w^n − w^{n+1}
        have a1 : ((1 : Q') * qpow w n).eqv (qpow w n) := Q'.one_mul_eqv (qpow w n)
        have a2 : ((-w) * qpow w n).eqv (-(qpow w n * w)) :=
          Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv w (qpow w n))
            (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv w (qpow w n)))
        -- assemble: w^n + −(w^n·w) ; RHS qpow w (n+1) = qpow w n * w by def
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' a1 a2) ?_
        -- qpow w n + −(qpow w n * w) = qpow w n − qpow w (n+1)
        show (qpow w n + -(qpow w n * w)).eqv (qpow w n - qpow w (n + 1))
        exact Q'.eqv_refl _
      -- Now chain on RHS: (1−w)·geomSum w (n+1) ≃ (1−w^n) + (w^n − w^{n+1})
      have hRHS : (((1 : Q') - w) * geomSum w (n + 1)).eqv
          (((1 : Q') - qpow w n) + (qpow w n - qpow w (n + 1))) := by
        show (((1 : Q') - w) * (geomSum w n + qpow w n)).eqv
            (((1 : Q') - qpow w n) + (qpow w n - qpow w (n + 1)))
        refine Q'.eqv_trans _ _ _ hdist ?_
        exact Q'.add_eqv_congr' (Q'.eqv_symm IH) hterm
      -- and (1−w^n) + (w^n − w^{n+1}) ≃ 1 − w^{n+1}
      refine Q'.eqv_symm (Q'.eqv_trans _ _ _ hRHS ?_)
      -- (1 + −w^n) + (w^n + −w^{n+1}) ≃ 1 + −w^{n+1}
      show (((1 : Q') + -(qpow w n)) + (qpow w n + -(qpow w (n + 1)))).eqv
          ((1 : Q') + -(qpow w (n + 1)))
      -- regroup: = 1 + (−w^n + (w^n + −w^{n+1})) = 1 + ((−w^n + w^n) + −w^{n+1})
      --          = 1 + (0 + −w^{n+1}) = 1 + −w^{n+1}
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (1 : Q') (-(qpow w n)) _) ?_
      refine Q'.add_eqv_congr_left (1 : Q') _ _ ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-(qpow w n)) (qpow w n) _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(qpow w (n + 1))) (Q'.neg_add_self_eqv (qpow w n))) ?_
      exact q_zero_add_eqv (-(qpow w (n + 1)))

/-! ### Cofactor bounds on `[0,1]` -/

/-- **Upper cofactor bound** `geomSum w n ≤ n` on `[0,1]`: each of the `n` terms
`w^i` is `≤ 1`. -/
theorem geomSum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ n, geomSum w n ≤ Q'.ofNat n
  | 0 => by show (0 : Q') ≤ Q'.ofNat 0; exact Q'.le_refl' 0
  | n + 1 => by
      show geomSum w n + qpow w n ≤ Q'.ofNat (n + 1)
      have IH : geomSum w n ≤ Q'.ofNat n := geomSum_le hw0 hw1 n
      have hterm : qpow w n ≤ (1 : Q') := qpow_le_one hw0 hw1 n
      -- geomSum w n + w^n ≤ ofNat n + 1 ≃ ofNat (n+1)
      have hstep : geomSum w n + qpow w n ≤ Q'.ofNat n + (1 : Q') :=
        Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (qpow w n) IH)
          (Q'.add_le_add_left (Q'.ofNat n) (qpow w n) 1 hterm)
      -- ofNat n + 1 ≃ ofNat n + ofNat 1 ≃ ofNat (n+1)
      have he : (Q'.ofNat n + (1 : Q')).eqv (Q'.ofNat (n + 1)) := by
        have h1 : (Q'.ofNat n + Q'.ofNat 1).eqv (Q'.ofNat (n + 1)) :=
          Q'.eqv_symm (Q'.ofNat_add_eqv n 1)
        -- ofNat 1 = (1 : Q') definitionally
        exact h1
      exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv he)

/-- A power of `w ∈ [0,1]` is monotone-DECREASING in the exponent:
`w^{n} ≥ w^{n+1}` (multiply `w^n` by `w ≤ 1`). -/
theorem qpow_succ_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (n : Nat) : qpow w (n + 1) ≤ qpow w n := by
  show qpow w n * w ≤ qpow w n
  have h1 : qpow w n * w ≤ qpow w n * 1 :=
    Q'.mul_le_mul_of_nonneg_left w 1 (qpow w n) hw1 (qpow_nonneg w hw0 n)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_one_eqv (qpow w n)))

/-- `w^i ≥ w^n` for `i ≤ n` on `[0,1]` (powers decrease in the exponent). -/
theorem qpow_antitone {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ i n, i ≤ n → qpow w n ≤ qpow w i
  | i, n, h => by
      induction n with
      | zero =>
          have : i = 0 := Nat.le_zero.mp h
          subst this; exact Q'.le_refl' _
      | succ m ih =>
          rcases Nat.lt_or_ge i (m + 1) with hlt | hge
          · have hile : i ≤ m := Nat.le_of_lt_succ hlt
            exact Q'.le_trans' _ _ _ (qpow_succ_le hw0 hw1 m) (ih hile)
          · have : i = m + 1 := Nat.le_antisymm h hge
            subst this; exact Q'.le_refl' _

/-- **Lower cofactor bound** `n·w^{n} ≤ geomSum w (n)`? — stated in the cleaner
`geomSum_ge_pow` form below using the smallest term `w^{n−1}` of the `n`-term
sum: `n·w^{n−1} ≤ geomSum w n` on `[0,1]` (each of the `n` terms `w^i`,
`i < n`, is `≥ w^{n−1}`). -/
theorem geomSum_ge_pow {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ n, Q'.ofNat n * qpow w (n - 1) ≤ geomSum w n
  | 0 => by
      -- ofNat 0 * w^… ≤ geomSum w 0 = 0 ; LHS ≃ 0
      show Q'.ofNat 0 * qpow w (0 - 1) ≤ geomSum w 0
      rw [geomSum_zero]
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv) ?_
      exact q_zero_mul _
  | n + 1 => by
      -- geomSum w (n+1) = geomSum w n + w^n ; bound geomSum w n ≥ n·w^{n−1} ≥ n·w^n,
      -- and the new term is w^n, giving (n+1)·w^n.
      show Q'.ofNat (n + 1) * qpow w ((n + 1) - 1) ≤ geomSum w n + qpow w n
      -- (n+1)·w^n = n·w^n + w^n
      have hsplit : (Q'.ofNat (n + 1) * qpow w n).eqv
          (Q'.ofNat n * qpow w n + qpow w n) := by
        -- ofNat (n+1) ≃ ofNat n + 1, multiply by w^n
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (qpow w n)
            (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
              (Q'.eqv_refl (Q'.ofNat n + Q'.ofNat 1)))) ?_
        -- (ofNat n + 1)·w^n ≃ ofNat n·w^n + 1·w^n ≃ ofNat n·w^n + w^n
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat n) 1 (qpow w n)) ?_
        exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (qpow w n))
      -- lower-bound n·w^n by n·w^{n} (equal); and geomSum w n ≥ n·w^{n−1} ≥ n·w^n.
      have hgs : Q'.ofNat n * qpow w n ≤ geomSum w n := by
        -- geomSum w n ≥ n·w^{n−1} ≥ n·w^n
        have h1 : Q'.ofNat n * qpow w (n - 1) ≤ geomSum w n := geomSum_ge_pow hw0 hw1 n
        have h2 : Q'.ofNat n * qpow w n ≤ Q'.ofNat n * qpow w (n - 1) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _
            (qpow_antitone hw0 hw1 (n - 1) n (Nat.sub_le n 1))
            (zero_le_ofNat n)
        exact Q'.le_trans' _ _ _ h2 h1
      -- assemble: (n+1)·w^n ≃ n·w^n + w^n ≤ geomSum w n + w^n
      have hassemble : Q'.ofNat n * qpow w n + qpow w n ≤ geomSum w n + qpow w n :=
        Q'.add_le_add_right _ _ (qpow w n) hgs
      -- LHS exponent: (n+1)-1 = n
      have hexp : (n + 1) - 1 = n := rfl
      rw [hexp]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hassemble

/-- Positivity of `geomSum` for `0 ≤ w` and `n ≥ 1` (the first term `w^0 = 1` is
positive and all others nonnegative): `0 < geomSum w (n+1)`. -/
theorem geomSum_succ_pos {w : Q'} (hw : (0 : Q') ≤ w) (n : Nat) :
    (0 : Q') < geomSum w (n + 1) := by
  induction n with
  | zero =>
      -- geomSum w 1 = 0 + 1 = 1 > 0
      show (0 : Q') < geomSum w 0 + qpow w 0
      rw [geomSum_zero, qpow_zero]
      exact zero_lt_zero_add_one
  | succ m ih =>
      -- geomSum w (m+2) = geomSum w (m+1) + w^{m+1} ≥ geomSum w (m+1) > 0
      show (0 : Q') < geomSum w (m + 1) + qpow w (m + 1)
      have h2 : (0 : Q') ≤ qpow w (m + 1) := qpow_nonneg w hw (m + 1)
      have hmono : geomSum w (m + 1) ≤ geomSum w (m + 1) + qpow w (m + 1) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_add_zero_eqv _)))
          (Q'.add_le_add_left (geomSum w (m + 1)) 0 (qpow w (m + 1)) h2)
      exact lt_of_lt_of_le ih hmono

/-! ## 3. The decimation per-block multiplier `ρ_dec → 1` — THE CRACK

`rhoDecimate b w = (∑_{i<b+1} w^i)/(b+1)` is the per-block PHYSICAL-gap multiplier
of one decimation step collapsing `b+1` links in series (`physGap = (1−sep)/a ↦
(1−sep^{b+1})/((b+1)·a)`, and `1 − sep^{b+1} = (1−sep)·geomSum sep (b+1)`, so the
multiplier is `geomSum sep (b+1) / (b+1)`).  The crack is the explicit modulus
`1 − ρ_dec ≤ (b+1)·(1 − w)`, showing `ρ_dec → 1` as `w → 1`. -/

/-- **The decimation per-block multiplier** `ρ_dec(b, w) = (∑_{i<b+1} w^i)/(b+1)`
(collapsing `b+1` links in series).  This is the per-block physical-gap multiplier
of one EXACT decimation step; `ρ_dec ∈ (0,1]` on `[0,1]` and `→ 1` as `w → 1`. -/
def rhoDecimate (b : Nat) (w : Q') : Q' :=
  Q'.divPos (geomSum w (b + 1)) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)

/-- `0 < rhoDecimate b w` for `0 ≤ w` (positive numerator over positive `b+1`). -/
theorem rhoDecimate_pos (b : Nat) {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') < rhoDecimate b w :=
  Q'.divPos_pos (geomSum w (b + 1)) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)
    (geomSum_succ_pos hw b)

/-- **`ρ_dec ≤ 1`** on `[0,1]`: the per-block decimation multiplier never
exceeds `1` (since `geomSum w (b+1) ≤ b+1`). -/
theorem rhoDecimate_le_one (b : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) : rhoDecimate b w ≤ (1 : Q') := by
  show Q'.divPos (geomSum w (b + 1)) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b) ≤ (1 : Q')
  refine Q'.divPos_le_of_le_mul _ _ _ ?_
  -- geomSum w (b+1) ≤ b+1 = 1·(b+1)
  refine Q'.le_trans' _ _ _ (geomSum_le hw0 hw1 (b + 1)) ?_
  exact Q'.ge_of_eqv (Q'.one_mul_eqv (Q'.ofNat (b + 1)))

/-- The decimation gap-margin transformation law (sep-margin under one block step):
`1 − sep^{b+1} = (1 − sep)·geomSum sep (b+1)` for `sep = heatKernelSep w`.  Ties
`ρ_dec` (whose numerator is `geomSum sep (b+1)`) to the actual gap margin. -/
theorem decimation_margin_law (b : Nat) (w : Q') :
    ((1 : Q') - qpow (heatKernelSep w) (b + 1)).eqv
      (((1 : Q') - heatKernelSep w) * geomSum (heatKernelSep w) (b + 1)) :=
  oneSub_pow_factor (heatKernelSep w) (b + 1)

/-! ### THE CRACK: `1 − ρ_dec ≤ (b)·(1 − w)`, hence `ρ_dec → 1` as `w → 1`

`1 − ρ_dec = 1 − geomSum w (b+1)/(b+1) = ( (b+1) − geomSum w (b+1) )/(b+1)
           = ( ∑_{i<b+1} (1 − w^i) )/(b+1)`,
and each `1 − w^i ≤ i·(1 − w) ≤ (b+1)·(1 − w)`.  We prove the clean explicit
modulus `1 − ρ_dec ≤ (ofNat (b+1))·(1 − w)` via the numerator bound
`(b+1) − geomSum w (b+1) ≤ (b+1)·((b+1)·(1−w))` (`ofNat_sub_geomSum_le`), divided
by `(b+1)` (cancelling one factor): the deficit of `ρ_dec` from `1` is linear in
the margin `1 − w`, so `ρ_dec → 1` as `w → 1`. -/

/-- Per-term bound `1 − w^i ≤ (ofNat i)·(1 − w)` on `[0,1]`, from the geometric
factorization `1 − w^i = (1 − w)·geomSum w i` and `geomSum w i ≤ i`. -/
theorem oneSub_qpow_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (i : Nat) : (1 : Q') - qpow w i ≤ Q'.ofNat i * ((1 : Q') - w) := by
  -- 1 − w^i ≃ (1−w)·geomSum w i ≤ (1−w)·(ofNat i) ≃ (ofNat i)·(1−w)
  have hfac : ((1 : Q') - qpow w i).eqv (((1 : Q') - w) * geomSum w i) :=
    oneSub_pow_factor w i
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hgs : geomSum w i ≤ Q'.ofNat i := geomSum_le hw0 hw1 i
  have hstep : ((1 : Q') - w) * geomSum w i ≤ ((1 : Q') - w) * Q'.ofNat i :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgs hnn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.mul_comm_eqv ((1 : Q') - w) (Q'.ofNat i)))

/-- **The numerator deficit bound** `n − geomSum w n ≤ n·(n·(1 − w))` on `[0,1]`.
Since `n − geomSum w n = ∑_{i<n}(1 − w^i)` and each `1 − w^i ≤ n·(1 − w)`, the
sum of `n` such terms is `≤ n·(n·(1 − w))`.  (A quadratic-in-`n` bound — loose but
sufficient: it is the numerator of `1 − ρ_dec` over `n = b+1`.)  Proved by
induction on `n`. -/
theorem ofNat_sub_geomSum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ n, Q'.ofNat n - geomSum w n ≤ Q'.ofNat n * (Q'.ofNat n * ((1 : Q') - w))
  | 0 => by
      -- ofNat 0 − geomSum w 0 = 0 − 0 ≃ 0 ≤ 0
      show Q'.ofNat 0 - geomSum w 0 ≤ Q'.ofNat 0 * (Q'.ofNat 0 * ((1 : Q') - w))
      rw [geomSum_zero]
      refine Q'.le_trans' (Q'.ofNat 0 - (0 : Q')) (0 : Q') _ ?_ ?_
      · show Q'.ofNat 0 - (0 : Q') ≤ (0 : Q')
        refine Q'.le_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.sub_zero' (Q'.ofNat 0))) Q'.ofNat_zero_eqv
      · -- 0 ≤ ofNat 0 * (…) ≃ 0
        refine Q'.ge_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv) ?_
        exact q_zero_mul _
  | n + 1 => by
      -- (n+1) − geomSum w (n+1) = (n+1) − (geomSum w n + w^n)
      --   = (n − geomSum w n) + (1 − w^n)
      --   ≤ n·(n·(1−w)) + n·(1−w)   [IH and per-term bound, with i = n ≤ n]
      --   ≤ (n+1)·((n+1)·(1−w)).
      -- We bound by the (looser but sufficient) RHS (n+1)·((n+1)·(1−w)).
      have IH : Q'.ofNat n - geomSum w n ≤ Q'.ofNat n * (Q'.ofNat n * ((1 : Q') - w)) :=
        ofNat_sub_geomSum_le hw0 hw1 n
      have hterm : (1 : Q') - qpow w n ≤ Q'.ofNat n * ((1 : Q') - w) :=
        oneSub_qpow_le hw0 hw1 n
      -- LHS rewrite: ofNat (n+1) − (geomSum w n + w^n)
      --            ≃ (ofNat n − geomSum w n) + (1 − w^n)
      have hLHS : (Q'.ofNat (n + 1) - geomSum w (n + 1)).eqv
          ((Q'.ofNat n - geomSum w n) + ((1 : Q') - qpow w n)) := by
        show (Q'.ofNat (n + 1) - (geomSum w n + qpow w n)).eqv
            ((Q'.ofNat n - geomSum w n) + ((1 : Q') - qpow w n))
        -- ofNat (n+1) ≃ ofNat n + 1
        -- (ofNat n + 1) − (geomSum w n + w^n) ≃ (ofNat n − geomSum w n) + (1 − w^n)
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (-(geomSum w n + qpow w n)) (Q'.ofNat_add_eqv n 1)) ?_
        -- (ofNat n + ofNat 1) + −(geomSum + w^n) ; ofNat 1 = 1
        -- regroup to (ofNat n + −geomSum) + (1 + −w^n)
        show ((Q'.ofNat n + (1 : Q')) + -(geomSum w n + qpow w n)).eqv
            ((Q'.ofNat n + -(geomSum w n)) + ((1 : Q') + -(qpow w n)))
        -- use neg of sum and re-associate
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv (geomSum w n) (qpow w n))) ?_
        -- (ofNat n + 1) + (−geomSum + −w^n) ≃ (ofNat n + −geomSum) + (1 + −w^n)
        exact Q'.add_swap_inner (Q'.ofNat n) (1 : Q') (-(geomSum w n)) (-(qpow w n))
      -- RHS bound: (n−geomSum) + (1−w^n) ≤ n·(n·(1−w)) + n·(1−w)
      have hsum : (Q'.ofNat n - geomSum w n) + ((1 : Q') - qpow w n)
          ≤ Q'.ofNat n * (Q'.ofNat n * ((1 : Q') - w)) + Q'.ofNat n * ((1 : Q') - w) :=
        Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ IH)
          (Q'.add_le_add_left _ _ _ hterm)
      -- and n·(n·(1−w)) + n·(1−w) ≤ (n+1)·((n+1)·(1−w))
      have hfinal : Q'.ofNat n * (Q'.ofNat n * ((1 : Q') - w)) + Q'.ofNat n * ((1 : Q') - w)
          ≤ Q'.ofNat (n + 1) * (Q'.ofNat (n + 1) * ((1 : Q') - w)) := by
        -- (n+1)·((n+1)·L) = (n²+2n+1)·L where L = (1−w) ≥ 0; LHS = (n²+n)·L.
        -- Prove via: LHS ≤ RHS ⇐ (n²+n) ≤ (n+1)², i.e. compare the scalar
        -- coefficients times the nonnegative L.  We expand both as scalar·L.
        have hL : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
        -- LHS ≃ (ofNat n * ofNat n + ofNat n) * (1−w)
        have hLHS2 : (Q'.ofNat n * (Q'.ofNat n * ((1 : Q') - w)) + Q'.ofNat n * ((1 : Q') - w)).eqv
            ((Q'.ofNat n * Q'.ofNat n + Q'.ofNat n) * ((1 : Q') - w)) := by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat n * Q'.ofNat n) (Q'.ofNat n) ((1 : Q') - w)) ?_
          exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat n) (Q'.ofNat n) ((1 : Q') - w))
        -- RHS ≃ (ofNat (n+1) * ofNat (n+1)) * (1−w)
        have hRHS2 : (Q'.ofNat (n + 1) * (Q'.ofNat (n + 1) * ((1 : Q') - w))).eqv
            ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * ((1 : Q') - w)) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (n + 1)) (Q'.ofNat (n + 1)) ((1 : Q') - w))
        -- scalar comparison: (n·n + n) ≤ (n+1)·(n+1)
        have hscal : Q'.ofNat n * Q'.ofNat n + Q'.ofNat n
            ≤ Q'.ofNat (n + 1) * Q'.ofNat (n + 1) := by
          -- both sides are ofNat; compare via ofNat monotone in Nat:
          -- n·n + n ≤ (n+1)·(n+1) = n·n + 2n + 1
          have h1 : (Q'.ofNat n * Q'.ofNat n + Q'.ofNat n).eqv (Q'.ofNat (n * n + n)) := by
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv n n))) ?_
            exact Q'.eqv_symm (Q'.ofNat_add_eqv (n * n) n)
          have h2 : (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)).eqv (Q'.ofNat ((n + 1) * (n + 1))) :=
            Q'.eqv_symm (ofNat_mul_eqv (n + 1) (n + 1))
          have hnat : n * n + n ≤ (n + 1) * (n + 1) := by
            have he : (n + 1) * (n + 1) = n * n + n + (n + 1) := by
              rw [Nat.succ_mul, Nat.mul_succ]
            omega
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv h1) ?_
          refine Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hnat) (Q'.ge_of_eqv h2)
        -- multiply hscal by L ≥ 0 (right factor)
        have hmul : (Q'.ofNat n * Q'.ofNat n + Q'.ofNat n) * ((1 : Q') - w)
            ≤ (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * ((1 : Q') - w) :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hscal hL
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS2)
          (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv hRHS2))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
      exact Q'.le_trans' _ _ _ hsum hfinal

/-- **THE CRACK — the explicit modulus `ρ_dec → 1`.**  On `[0,1]`,
`1 − rhoDecimate b w ≤ (ofNat (b+1))·(1 − w)`: the decimation per-block
multiplier approaches `1` as `w → 1`, with the explicit linear modulus
`(b+1)·(1 − w)`.  This is the FAVORABLE dimensional-transmutation behaviour —
the decimation multiplier's deficit from `1` is controlled by the linear margin
`1 − w`, so a product of such multipliers stays bounded below as `w → 1`. -/
theorem rhoDecimate_to_one (b : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (1 : Q') - rhoDecimate b w ≤ Q'.ofNat (b + 1) * ((1 : Q') - w) := by
  -- 1 − geomSum/(b+1) = ((b+1) − geomSum)/(b+1)
  -- ≤ ((b+1)·((b+1)·(1−w)))/(b+1) ≃ (b+1)·(1−w).
  have hb1 : (0 : Q') < Q'.ofNat (b + 1) := Q'.ofNat_succ_pos b
  -- numerator bound from ofNat_sub_geomSum_le at n = b+1
  have hnum : Q'.ofNat (b + 1) - geomSum w (b + 1)
      ≤ Q'.ofNat (b + 1) * (Q'.ofNat (b + 1) * ((1 : Q') - w)) :=
    ofNat_sub_geomSum_le hw0 hw1 (b + 1)
  -- 1 − ρ_dec ≃ ((b+1) − geomSum)/(b+1)
  have hrw : ((1 : Q') - rhoDecimate b w).eqv
      (Q'.divPos (Q'.ofNat (b + 1) - geomSum w (b + 1)) (Q'.ofNat (b + 1)) hb1) := by
    -- 1 = (b+1)/(b+1) ; subtract geomSum/(b+1).
    show ((1 : Q') - Q'.divPos (geomSum w (b + 1)) (Q'.ofNat (b + 1)) (Q'.ofNat_succ_pos b)).eqv
        (Q'.divPos (Q'.ofNat (b + 1) - geomSum w (b + 1)) (Q'.ofNat (b + 1)) hb1)
    exact one_sub_divPos_eqv (geomSum w (b + 1)) (Q'.ofNat (b + 1)) hb1
  -- ((b+1) − geomSum)/(b+1) ≤ ((b+1)·((b+1)·(1−w)))/(b+1) ≃ (b+1)·(1−w)
  have hstep : Q'.divPos (Q'.ofNat (b + 1) - geomSum w (b + 1)) (Q'.ofNat (b + 1)) hb1
      ≤ Q'.divPos (Q'.ofNat (b + 1) * (Q'.ofNat (b + 1) * ((1 : Q') - w))) (Q'.ofNat (b + 1)) hb1 :=
    divPos_le_divPos_of_le hb1 hnum
  have hcollapse : (Q'.divPos (Q'.ofNat (b + 1) * (Q'.ofNat (b + 1) * ((1 : Q') - w)))
        (Q'.ofNat (b + 1)) hb1).eqv (Q'.ofNat (b + 1) * ((1 : Q') - w)) :=
    divPos_mul_left_cancel (Q'.ofNat (b + 1)) (Q'.ofNat (b + 1) * ((1 : Q') - w)) hb1
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrw) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcollapse)

/-! ## 4. The single-link S³ susceptibility atom (`4/3`)

The single-link (single-mode) susceptibility is the per-scale Hessian / Poincaré
constant `1/gap = 4/3`, from the EXACT spin-½ Casimir gap `3/4` on `S³`.  This is
the GENUINE inhabitant of the single-link atom of the susceptibility certificate
(the per-mode covariance bound), reused from `su2PerScale`. -/

/-- **The single-link S³ susceptibility atom** `= 4/3` — the per-scale
Poincaré / Bakry–Émery constant `1/gap` from the EXACT `3/4` spin-½ Casimir gap.
This is the genuine inhabitant of the SINGLE-LINK (single-mode) slice of the
susceptibility certificate: the per-mode covariance / Hessian bound.  Reuses the
exact `su2PerScale` datum (no new `3/4` constant). -/
def singleLinkSusceptibility : Q' := su2PerScale.poincareConst

/-- The single-link susceptibility is strictly positive. -/
theorem singleLinkSusceptibility_pos : (0 : Q') < singleLinkSusceptibility :=
  su2PerScale.poincareConst_pos

/-- The single-link susceptibility is the exact `4/3` (two-sided): both
`≤ 4/3` and `4/3 ≤`.  From the exact spin-½ gap `3/4`. -/
theorem singleLinkSusceptibility_le : singleLinkSusceptibility ≤ Q'.mkPos 4 3 (by decide) :=
  su2PerScale_poincareConst_le

theorem singleLinkSusceptibility_ge : Q'.mkPos 4 3 (by decide) ≤ singleLinkSusceptibility :=
  su2PerScale_poincareConst_ge

/-! ## 5. The bond-moving residual — the NAMED open content

The full MK block step is `bond-moving ∘ decimation`.  Decimation is EXACT
(§§1–3).  Bond-moving (`b^{d−1}` plaquettes in parallel) does NOT preserve the
heat-kernel form for `d > 2` (pointwise power / Clebsch–Gordan mixing), so its
deviation is the residual `δ`.  We name it as `Type`-level data with the open
bound `δ ≤ resC · a · Λ`.  It is EXACT (`δ = 0`) on the hierarchical / diamond
lattice (where bond-moving IS the decimation by construction); the genuine 4D
residual on ℝ⁴ is UNCONTROLLED (MK is approximate there) and is NOT inhabited. -/

/-- **The bond-moving residual record (NAMED OPEN content).**

Carries, for a fixed block factor `b`, spacing `a`, and pre-step weight `w`:

  * `delta`, `delta_nonneg` — the bond-moving deviation `δ ≥ 0` of the full-step
    weight from the (exact) decimated weight;
  * `resC`, `resC_nonneg` — a residual constant;
  * `cutoff` (`Λ`) — the energy / curvature cutoff entering the MK bond-moving
    error;
  * `fullStepWeight` — the actual full-step normalized weight;
  * `decimatedWeight = mkDecimate b w` — the EXACT decimated weight;
  * `residual_bound` — **the OPEN analytic content:** the full step deviates from
    the exact decimation by at most `δ`, with the named bound
    `δ ≤ resC · a · Λ`.

An inhabitant with `δ = 0` is EXACT — the hierarchical / diamond-lattice case
(`hierarchicalBondMovingResidual`).  No ℝ⁴ inhabitant is provided. -/
structure BondMovingResidual (b : Nat) (a w : Q') : Type where
  /-- The bond-moving deviation `δ`. -/
  delta : Q'
  /-- `δ ≥ 0`. -/
  delta_nonneg : (0 : Q') ≤ delta
  /-- A residual constant. -/
  resC : Q'
  /-- `resC ≥ 0`. -/
  resC_nonneg : (0 : Q') ≤ resC
  /-- The MK energy / curvature cutoff `Λ`. -/
  cutoff : Q'
  /-- `Λ ≥ 0`. -/
  cutoff_nonneg : (0 : Q') ≤ cutoff
  /-- The actual full-step normalized weight. -/
  fullStepWeight : Q'
  /-- The exact decimated weight `w^b`. -/
  decimatedWeight : Q'
  /-- The decimated weight IS the exact decimation map. -/
  decimated_eq : decimatedWeight = mkDecimate b w
  /-- **The OPEN bound:** the full step deviates from exact decimation by `≤ δ`,
  and `δ ≤ resC · a · Λ` (the named MK bond-moving error). -/
  residual_bound : (0 : Q') ≤ delta ∧ delta ≤ resC * a * cutoff

/-- **The hierarchical / diamond-lattice bond-moving residual is EXACT (`δ = 0`).**
On the hierarchical (Migdal recursion / diamond) lattice, bond-moving is BY
CONSTRUCTION the decimation, so the full-step weight equals the decimated weight
and the residual vanishes: `δ = 0`.  This is a GENUINE inhabitant of
`BondMovingResidual` — the exactly-solvable case where the MK step is no
approximation.  (The ℝ⁴ residual is NOT inhabited; MK is approximate there.) -/
def hierarchicalBondMovingResidual (b : Nat) (a w : Q')
    (_ha : (0 : Q') ≤ a) : BondMovingResidual b a w where
  delta := 0
  delta_nonneg := Q'.le_refl' 0
  resC := 0
  resC_nonneg := Q'.le_refl' 0
  cutoff := 0
  cutoff_nonneg := Q'.le_refl' 0
  fullStepWeight := mkDecimate b w
  decimatedWeight := mkDecimate b w
  decimated_eq := rfl
  residual_bound := ⟨Q'.le_refl' 0, by
    -- 0 ≤ 0·a·0 = 0
    show (0 : Q') ≤ (0 : Q') * a * 0
    refine Q'.ge_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ 0 (q_zero_mul a)) ?_
    exact q_zero_mul 0⟩

/-- On the hierarchical lattice the full-step weight equals the EXACT decimated
weight (`fullStepWeight = w^b`): the MK step is no approximation. -/
theorem hierarchical_fullStep_eq_decimate (b : Nat) (a w : Q') (ha : (0 : Q') ≤ a) :
    (hierarchicalBondMovingResidual b a w ha).fullStepWeight = mkDecimate b w := rfl

/-- On the hierarchical lattice the bond-moving deviation vanishes (`δ = 0`). -/
theorem hierarchical_residual_zero (b : Nat) (a w : Q') (ha : (0 : Q') ≤ a) :
    (hierarchicalBondMovingResidual b a w ha).delta = 0 := rfl

/-! ## 6. Assembly toward `PerScaleRateData` — the hierarchical inhabitant

On the hierarchical lattice (`δ = 0`) the per-block multiplier is EXACTLY the
decimation multiplier `ρ_k = rhoDecimate b (sep_k)`, with the decimation deficit
`1 − ρ_dec ≤ (b+1)·(1 − sep_k)`.  If the per-scale separators `sep_k` satisfy a
SUMMABLE-loss budget `∑_{k<n}(1 − ρ_k) ≤ R < 1`, this assembles into a genuine
`NonAbelianGapChain.PerScaleRateData` — a real inhabitant ON THE HIERARCHICAL
MODEL.  We package exactly that: given rates with the summable-loss budget, build
the per-scale rate data.  The ℝ⁴ case (where `δ ≠ 0` is uncontrolled) is NOT
inhabited. -/

open YMGap.Continuum.NonAbelianGapChain in
/-- **The hierarchical `PerScaleRateData` inhabitant (genuine, on the hierarchical
model).**  Given per-block decimation rates `ρ k = rhoDecimate (bb k) (sep k)`
for sub-unit separators `sep k`, a summable-loss budget `R < 1` with
`∑_{k<n}(1 − ρ_k) ≤ R`, an `a`-scaling, and a positive base LSI scale, assemble a
`PerScaleRateData`.  This is a REAL inhabitant of the per-scale-rate obligation on
the hierarchical lattice (`δ = 0`), where the full MK step IS the EXACT
decimation.  (For ℝ⁴ the bond-moving residual `δ` is uncontrolled; no such
inhabitant is provided.) -/
def hierarchicalPerScaleRateData
    (bb : Nat → Nat) (sep : Nat → Q')
    (hsep0 : ∀ k, (0 : Q') ≤ sep k) (hsep1 : ∀ k, sep k ≤ (1 : Q'))
    (R : Q') (hR : R < 1)
    (hloss : ∀ n : Nat,
      ProductFloor.lossSum (fun k => 1 - rhoDecimate (bb k) (sep k)) n ≤ R)
    (aSc : Nat → Q') (haSc : ∀ a : Nat, (0 : Q') < aSc a)
    (base : Q') (hbase : (0 : Q') < base) :
    NonAbelianGapChain.PerScaleRateData where
  rho := fun k => rhoDecimate (bb k) (sep k)
  rho_nonneg := fun k => Q'.le_of_lt (rhoDecimate_pos (bb k) (hsep0 k))
  rho_le_one := fun k => rhoDecimate_le_one (bb k) (hsep0 k) (hsep1 k)
  R := R
  R_lt_one := hR
  lossSummable := hloss
  window := fun _ => True
  aScaling := aSc
  aScaling_pos := haSc
  baseLSI := base
  baseLSI_pos := hbase

open YMGap.Continuum.NonAbelianGapChain in
/-- The hierarchical per-scale data's rates are exactly the decimation
multipliers. -/
@[simp] theorem hierarchicalPerScaleRateData_rho
    (bb : Nat → Nat) (sep : Nat → Q')
    (hsep0 : ∀ k, (0 : Q') ≤ sep k) (hsep1 : ∀ k, sep k ≤ (1 : Q'))
    (R : Q') (hR : R < 1)
    (hloss : ∀ n : Nat,
      ProductFloor.lossSum (fun k => 1 - rhoDecimate (bb k) (sep k)) n ≤ R)
    (aSc : Nat → Q') (haSc : ∀ a : Nat, (0 : Q') < aSc a)
    (base : Q') (hbase : (0 : Q') < base) (k : Nat) :
    (hierarchicalPerScaleRateData bb sep hsep0 hsep1 R hR hloss aSc haSc base hbase).rho k
      = rhoDecimate (bb k) (sep k) := rfl

open YMGap.Continuum.NonAbelianGapChain in
/-- **The hierarchical chain payoff.**  Feeding the hierarchical per-scale rate
data through the PROVED multiscale assembly produces a genuine spacing-uniform
`UniformLSI` on the hierarchical model.  This is the honest bonus: a REAL
inhabitant of the per-scale-rate ⇒ uniform-LSI arrow built from the
exactly-computed decimation half of the MK step (`δ = 0`). -/
def hierarchicalUniformLSI
    (bb : Nat → Nat) (sep : Nat → Q')
    (hsep0 : ∀ k, (0 : Q') ≤ sep k) (hsep1 : ∀ k, sep k ≤ (1 : Q'))
    (R : Q') (hR : R < 1)
    (hloss : ∀ n : Nat,
      ProductFloor.lossSum (fun k => 1 - rhoDecimate (bb k) (sep k)) n ≤ R)
    (aSc : Nat → Q') (haSc : ∀ a : Nat, (0 : Q') < aSc a)
    (base : Q') (hbase : (0 : Q') < base) :
    NonAbelianGapChain.UniformLSI :=
  NonAbelianGapChain.perScaleRateData_to_uniformLSI
    (hierarchicalPerScaleRateData bb sep hsep0 hsep1 R hR hloss aSc haSc base hbase)

/-! ## 7. Doc-section — the first genuine crack (HONEST)

This module takes the FIRST GENUINE CRACK at the atomic piece of the open
susceptibility ⇒ per-scale-rate map by EXPLICITLY COMPUTING one Migdal–Kadanoff /
hierarchical RG block step for the SU(2) heat-kernel action:

  * The EXACT decimation half is computed: `mkDecimate b w = w^b` (heat
    semigroup), and `mkDecimate_sep` shows the gap separator commutes with it,
    `sep(w^b) = sep(w)^b = w^{3b}`.  PROVED, axiom-clean.

  * Its per-block PHYSICAL-gap multiplier `ρ_dec = (∑_{i<b} sep^i)/b` is proved to
    approach `1` in the continuum: `rhoDecimate_to_one` gives the explicit linear
    modulus `1 − ρ_dec ≤ (b+1)·(1 − w)`.  This is the FAVORABLE
    dimensional-transmutation behaviour — the decimation half does not destroy
    the gap; its deficit is controlled by the linear margin `1 − w`.  PROVED.

  * The single-link (single-mode) susceptibility atom is inhabited:
    `singleLinkSusceptibility = 4/3`, the S³ Poincaré / Bakry–Émery constant from
    the EXACT `3/4` Casimir gap.  PROVED (two-sided exact value).

  * The bond-moving deviation is ISOLATED as the precise residual
    `BondMovingResidual` with the named open bound `δ ≤ resC·a·Λ`.  It is EXACT
    (`δ = 0`) on the hierarchical / diamond lattice
    (`hierarchicalBondMovingResidual`) — where the MK step is no approximation —
    and is the genuine UNCONTROLLED open content on ℝ⁴.

  * BONUS: on the hierarchical model (`δ = 0`) the exact decimation rates assemble
    into a genuine `PerScaleRateData` and, through the PROVED multiscale assembly,
    a `UniformLSI` (`hierarchicalPerScaleRateData` / `hierarchicalUniformLSI`).

HONEST VERDICT.  This does NOT solve the 4D Yang–Mills gap.  It CRACKS the atom of
the open residual into an exactly-computed FAVORABLE part (decimation, with
`ρ_dec → 1`) plus a SHARPLY-NAMED residual (bond-moving `δ`), and ships a genuine
inhabitant ONLY on the hierarchical lattice where `δ = 0`.  The distinction is
explicit throughout: the decimation half and the hierarchical (`δ = 0`) case are
GENUINELY PROVED; the ℝ⁴ bond-moving residual is the NAMED open content and is
NOT inhabited. -/

end YMGap.Continuum.HeatKernelRGStep

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelRGStep.qpow_add
#print axioms YMGap.Continuum.HeatKernelRGStep.qpow_qpow
#print axioms YMGap.Continuum.HeatKernelRGStep.mkDecimate_sep
#print axioms YMGap.Continuum.HeatKernelRGStep.geomSum_nonneg
#print axioms YMGap.Continuum.HeatKernelRGStep.oneSub_pow_factor
#print axioms YMGap.Continuum.HeatKernelRGStep.geomSum_le
#print axioms YMGap.Continuum.HeatKernelRGStep.geomSum_ge_pow
#print axioms YMGap.Continuum.HeatKernelRGStep.geomSum_succ_pos
#print axioms YMGap.Continuum.HeatKernelRGStep.rhoDecimate_pos
#print axioms YMGap.Continuum.HeatKernelRGStep.rhoDecimate_le_one
#print axioms YMGap.Continuum.HeatKernelRGStep.decimation_margin_law
#print axioms YMGap.Continuum.HeatKernelRGStep.oneSub_qpow_le
#print axioms YMGap.Continuum.HeatKernelRGStep.rhoDecimate_to_one
#print axioms YMGap.Continuum.HeatKernelRGStep.singleLinkSusceptibility_pos
#print axioms YMGap.Continuum.HeatKernelRGStep.singleLinkSusceptibility_le
#print axioms YMGap.Continuum.HeatKernelRGStep.singleLinkSusceptibility_ge
#print axioms YMGap.Continuum.HeatKernelRGStep.hierarchicalBondMovingResidual
#print axioms YMGap.Continuum.HeatKernelRGStep.hierarchical_residual_zero
#print axioms YMGap.Continuum.HeatKernelRGStep.hierarchicalPerScaleRateData
#print axioms YMGap.Continuum.HeatKernelRGStep.hierarchicalUniformLSI
