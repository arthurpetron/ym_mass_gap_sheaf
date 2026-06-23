/-
The **constructive positivity atoms** for the LDLᵀ-pivot / cyclotomic-factor
route to all-order heat-kernel Gram PSD, and the per-`N` minor-positivity
frontier they push from `N ≤ 3` to `N ≤ 5`.

# Setting

The SU(2) heat-kernel Gram leading minors factor uniformly as
`Δ_N(a) = S_N(a)²·P_N(a)` (single base variable `a = e^{−t/4} ∈ (0,1]`), with
`S_N` the q-product square factor (produced uniformly by `SN N`) and `P_N` a
nonneg-coefficient residual.  Minor positivity `Δ_N(a) ≥ 0` at `a ≥ 0` reduces
to two facts: the square `S_N² ≥ 0` (already uniform) and `P_N ≥ 0` (from
`nonnegCoeffs P_N` via the Horner engine).

The square factor `S_N` is a product of q-monomials `a^{2j}−1`; each such
factor is `±(1 − a^{2j})`, and on the heat-kernel range `0 ≤ a ≤ 1` the base
cyclotomic quantity `1 − a^n` is `≥ 0` (and `> 0` for `a < 1`).  These are the
**positivity atoms** the LDLᵀ-pivot route consumes: the pivots in an LDLᵀ
factorization of a totally-nonnegative q-Hankel matrix are products of such
`1 − q^n` cyclotomic factors and even powers thereof.

# What is PROVED here (axiom-clean; no `Classical`/`sorry`/`native_decide`)

  * **Positivity atoms over `Q'`** (`qpow` = repeated multiplication):
      - `qpow_le_one`   : `0 ≤ q → q ≤ 1 → q^n ≤ 1`.
      - `qpow_lt_one`   : `0 ≤ q → q < 1 → q^(n+1) < 1`  (`n+1 ≥ 1`).
      - `one_sub_qpow_nonneg` : `0 ≤ q → q ≤ 1 → 0 ≤ 1 − q^n`   (weak atom).
      - `one_sub_qpow_pos`    : `0 ≤ q → q < 1 → 0 < 1 − q^(n+1)` (strict atom).
      - `qpow_nonneg`, `even_qpow_nonneg` : `q^(2m) ≥ 0` for *any* `q` (an even
        power is a square of `q^m`), and `(1 − q^n)^(2m) ≥ 0` as the special
        case `even_one_sub_qpow_nonneg`.
    These are the cyclotomic-factor base atoms: `1 − q^n` is the product of
    cyclotomic factors `Φ_d`, and on `[0,1)` it is `> 0`.

  * **The form-level minor reduction, packaged** (`gram_minor_nonneg_of_PN`):
    for *every* `N`, supplying `nonnegCoeffs P_N` plus the factorization
    `Δ ≃ (SN N)²·P_N` discharges `Δ ≥ 0` at `a ≥ 0`.  This re-exports the
    uniform `QHankel.geRat_minor_SN_factored` engine cleanly.

  * **The extended unconditional minor frontier** `N = 4, 5`
    (`delta4_minor_nonneg`, `delta5_minor_nonneg`, and the heat-kernel-point
    variants), through the uniform `SN`-engine + the per-`N` `decide` facts
    `nonnegCoeffs P_4` (`Favard`) and `nonnegCoeffs P_5` (`FavardRec`).  This
    pushes the proved minor-level range from `N ≤ 3` to `N ≤ 5`.  `N = 5` is
    proved on the *factored* polynomial `(SN 5)²·P_5` directly (avoiding the
    degree-160 expanded `Δ_5` literal), which is the same `CReal` value.

# What stays NAMED-open

  * **Uniform `nonnegCoeffs P_N` for all `N`** (= `UniformGramSOS`, the P_N /
    q-total-positivity wall).  This file pushes the *per-`N`* frontier to
    `N ≤ 5`; it does NOT close the all-`N` statement.  The `decide`-checked
    coefficient lists are per-order certificates, not an `N`-indexed theorem.

  * **The Sylvester minor→form bridge.**  The results here are *minor-level*
    (`Δ_N(a) ≥ 0`).  Promoting them to the *quadratic-form* level
    `E(q²) = Σ c_μ c_ν G_{μν} ≥ 0` (the predicate `MomentSquarePosAt`) requires
    (i) the order-`N` moment-bridge and (ii) the Sylvester step
    `leading minors ≥ 0 ⟹ form PSD`.  The form-level range in
    `MomentSquarePSD.momentSquarePos_upTo` is `N ≤ 3` because the `N ≤ 3` form
    results come from explicit *LDLᵀ* certificates (`coneExp_psd_two/three`),
    not from minor positivity; there is no `4×4`/`5×5` LDLᵀ form certificate in
    the repo.  So the extended minors here do NOT (and are not faked to) extend
    `momentSquarePos_upTo`; the gap is exactly the named Sylvester bridge.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.QHankel
import YMGap.Continuum.FavardRec

namespace YMGap.Continuum.CyclotomicPositivity

open YMGap.Constructive

/-! ## Q'-level strict / weak order helpers

A few small `Q'` order facts not already in the kernel: strict
sub-positivity, `mul_le_mul` on the *left*, and `mul` of strict-vs-weak.
All reduce to the `Int` cross-product representation of `≤`/`<`. -/

/-- `a ≤ b → b < c → a < c` on `Q'` (Int cross-product chain). -/
theorem lt_of_le_of_lt {a b c : Q'} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  have e1 : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) < c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcd : (0 : Int) ≤ (c.den : Int) := by exact_mod_cast Nat.zero_le _
  -- (a.num·c.den)·b.den ≤ (b.num·a.den)·c.den
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          ≤ (b.num * (a.den : Int)) * (c.den : Int) := by
    have hmul := Int.mul_le_mul_of_nonneg_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    have hr2 : (b.num * (a.den : Int)) * (c.den : Int)
             = (b.num * (c.den : Int)) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (a.den : Int) (c.den : Int)]
    rw [hr] at hmul
    -- hmul : (a.num·c.den)·b.den ≤ (b.num·a.den)·c.den
    exact hmul
  -- (b.num·a.den)·c.den < (c.num·a.den)·b.den
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    -- scale the strict `e2` by `a.den > 0` on the right, then reorder.
    have had_pos : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
    have hmul3 := Int.mul_lt_mul_of_pos_right e2 had_pos
    -- hmul3 : (b.num·c.den)·a.den < (c.num·b.den)·a.den
    have hl : (b.num * (a.den : Int)) * (c.den : Int)
            = (b.num * (c.den : Int)) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (a.den : Int) (c.den : Int)]
    have hrr : (c.num * (a.den : Int)) * (b.den : Int)
             = (c.num * (b.den : Int)) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (a.den : Int) (b.den : Int)]
    rw [hl, hrr]
    exact hmul3
  -- chain s1 (≤) then s2 (<), then cancel b.den>0
  have chain : (a.num * (c.den : Int)) * (b.den : Int)
             < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_le_of_lt s1 s2
  exact Int.lt_of_mul_lt_mul_right chain (Int.le_of_lt hbd)

/-- **Strict sub-positivity.**  `c < d → 0 < d + (−c)`.  (Q'-level `sub_pos`.)
Reduces to `Int.sub_pos`: `0 < d.num·c.den − c.num·d.den`. -/
theorem sub_pos_of_lt {c d : Q'} (h : c < d) : (0 : Q') < d + (-c) := by
  -- `<` on Q' is the Int cross-product `0.num·D < (d+-c).num·0.den` with den 1.
  have hc : c.num * (d.den : Int) < d.num * (c.den : Int) := h
  show (0 : Int) * ((d + (-c)).den : Int) < (d + (-c)).num * ((0 : Q').den : Int)
  have hnum : (d + (-c)).num = d.num * (c.den : Int) + (-c.num) * (d.den : Int) := rfl
  rw [hnum]
  -- RHS = (d.num·c.den − c.num·d.den) · 1, LHS = 0
  have hden1 : ((0 : Q').den : Int) = 1 := rfl
  rw [hden1, Int.zero_mul, Int.mul_one]
  -- 0 < d.num·c.den + (−c.num)·d.den = d.num·c.den − c.num·d.den
  have : (0 : Int) < d.num * (c.den : Int) - c.num * (d.den : Int) :=
    Int.sub_pos.mpr hc
  have heq : d.num * (c.den : Int) + (-c.num) * (d.den : Int)
      = d.num * (c.den : Int) - c.num * (d.den : Int) := by
    rw [Int.neg_mul]; rfl
  rw [heq]; exact this

/-- **Left multiplication preserves `≤` for nonneg multiplier.**
`a ≤ b → 0 ≤ c → c·a ≤ c·b`.  (Mirror of `mul_le_mul_of_nonneg_right` via
commutativity.) -/
theorem mul_le_mul_of_nonneg_left {a b c : Q'} (h : a ≤ b) (hc : (0 : Q') ≤ c) :
    c * a ≤ c * b := by
  have h1 : a * c ≤ b * c := Q'.mul_le_mul_of_nonneg_right a b c h hc
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c a)) ?_
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_comm_eqv b c))

/-! ## The Q' power `qpow` (repeated multiplication) -/

/-- `q^n` over `Q'` by repeated multiplication: `q^0 = 1`, `q^(n+1) = q·q^n`. -/
def qpow (q : Q') : Nat → Q'
  | 0 => 1
  | (n + 1) => q * qpow q n

@[simp] theorem qpow_zero (q : Q') : qpow q 0 = 1 := rfl
@[simp] theorem qpow_succ (q : Q') (n : Nat) : qpow q (n + 1) = q * qpow q n := rfl

/-! ## Positivity atoms

`1 − q^n` is the base cyclotomic factor.  On `0 ≤ q ≤ 1` it is `≥ 0`; on
`0 ≤ q < 1` it is `> 0` for `n ≥ 1`. -/

/-- `0 ≤ q^n` for any `0 ≤ q`. -/
theorem qpow_nonneg_of_nonneg {q : Q'} (hq : (0 : Q') ≤ q) :
    ∀ n, (0 : Q') ≤ qpow q n
  | 0 => by show (0 : Q') ≤ (1 : Q'); decide
  | (n + 1) => by
      rw [qpow_succ]
      exact Q'.mul_nonneg q (qpow q n) hq (qpow_nonneg_of_nonneg hq n)

/-- **Weak power atom.**  `0 ≤ q → q ≤ 1 → q^n ≤ 1`.  Induction:
`q^(n+1) = q·q^n ≤ q·1 = q ≤ 1` (using `q^n ≤ 1` and `0 ≤ q`). -/
theorem qpow_le_one {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) :
    ∀ n, qpow q n ≤ (1 : Q')
  | 0 => by show (1 : Q') ≤ (1 : Q'); exact Q'.le_refl' 1
  | (n + 1) => by
      rw [qpow_succ]
      -- q·q^n ≤ q·1 = q ≤ 1
      have hstep : q * qpow q n ≤ q * 1 :=
        mul_le_mul_of_nonneg_left (qpow_le_one hq0 hq1 n) hq0
      have hq1' : q * 1 ≤ (1 : Q') :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv q)) hq1
      exact Q'.le_trans' _ _ _ hstep hq1'

/-- **Strict power atom.**  `0 ≤ q → q < 1 → q^(n+1) < 1` (`n+1 ≥ 1`).
`q^(n+1) = q·q^n ≤ q·1 = q < 1` (using `q^n ≤ 1` and `0 ≤ q`). -/
theorem qpow_lt_one {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (n : Nat) :
    qpow q (n + 1) < (1 : Q') := by
  rw [qpow_succ]
  have hqle1 : q ≤ (1 : Q') := Q'.le_of_lt hq1
  -- q·q^n ≤ q·1 = q
  have hstep : q * qpow q n ≤ q * 1 :=
    mul_le_mul_of_nonneg_left (qpow_le_one hq0 hqle1 n) hq0
  have heq : q * 1 ≤ q := Q'.le_of_eqv (Q'.mul_one_eqv q)
  have hle : q * qpow q n ≤ q := Q'.le_trans' _ _ _ hstep heq
  exact lt_of_le_of_lt hle hq1

/-- **Weak cyclotomic atom.**  `0 ≤ q → q ≤ 1 → 0 ≤ 1 − q^n`.
(`1 − q^n = 1 + (−q^n)`, nonneg since `q^n ≤ 1`.) -/
theorem one_sub_qpow_nonneg {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q'))
    (n : Nat) : (0 : Q') ≤ (1 : Q') + (-(qpow q n)) :=
  Q'.sub_nonneg_of_le (qpow_le_one hq0 hq1 n)

/-- **Strict cyclotomic atom.**  `0 ≤ q → q < 1 → 0 < 1 − q^(n+1)`
(`n+1 ≥ 1`).  The base cyclotomic factor is strictly positive on `[0,1)`. -/
theorem one_sub_qpow_pos {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (n : Nat) : (0 : Q') < (1 : Q') + (-(qpow q (n + 1))) :=
  sub_pos_of_lt (qpow_lt_one hq0 hq1 n)

/-! ## Even-power atoms

An even power `q^(2m)` is a square `(q^m)²`, hence `≥ 0` for *any* `q` (no
sign hypothesis).  In particular `(1 − q^n)^(2m) ≥ 0` — the even-multiplicity
cyclotomic factors of `S_N²` are squares, which is exactly why the cyclotomic
content of `Δ_N` is a perfect square. -/

/-- `q^(m+n) = q^m·q^n` (exponent additivity of `qpow`). -/
theorem qpow_add (q : Q') (m n : Nat) :
    (qpow q (m + n)).eqv (qpow q m * qpow q n) := by
  induction n with
  | zero =>
      -- q^(m+0) = q^m ≃ q^m·1 = q^m·q^0
      exact Q'.eqv_symm (Q'.mul_one_eqv (qpow q m))
  | succ n ih =>
      -- q^(m+n+1) = q·q^(m+n) ≃ q·(q^m·q^n) ≃ q^m·(q·q^n) = q^m·q^(n+1)
      show (q * qpow q (m + n)).eqv (qpow q m * (q * qpow q n))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ ih) ?_
      -- q·(q^m·q^n) ≃ q^m·(q·q^n)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q (qpow q m) (qpow q n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv q (qpow q m))) ?_
      exact Q'.mul_assoc_eqv (qpow q m) q (qpow q n)

/-- **Even-power atom.**  `q^(2m) ≥ 0` for *any* `q` (it is the square
`(q^m)·(q^m)`).  No sign hypothesis on `q`. -/
theorem even_qpow_nonneg (q : Q') (m : Nat) : (0 : Q') ≤ qpow q (2 * m) := by
  -- q^(2m) = q^(m+m) ≃ q^m·q^m ≥ 0 (a square)
  have he : (qpow q (2 * m)).eqv (qpow q m * qpow q m) := by
    have : (2 * m) = m + m := by rw [Nat.two_mul]
    rw [this]; exact qpow_add q m m
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv he)
  -- 0 ≤ q^m·q^m : a square via `q_mul_self_nonneg`
  exact SumOfSquares.q_mul_self_nonneg (qpow q m)

/-- **Even power of the cyclotomic factor.**  `(1 − q^n)^(2m) ≥ 0` for any
`q` (an even power of any `Q'` is `≥ 0`).  The special case of
`even_qpow_nonneg` at the base `1 − q^n`; this is the LDLᵀ-pivot atom that the
even-multiplicity cyclotomic content of `S_N²` is a square. -/
theorem even_one_sub_qpow_nonneg (q : Q') (n m : Nat) :
    (0 : Q') ≤ qpow ((1 : Q') + (-(qpow q n))) (2 * m) :=
  even_qpow_nonneg ((1 : Q') + (-(qpow q n))) m

/-! ## The form-level `Δ_N = S_N²·P_N ⇒ Δ_N ≥ 0` reduction, packaged

The atoms above explain *why* `S_N² ≥ 0` (even-multiplicity cyclotomic
factors are squares) and *why* the cyclotomic factors are `≥ 0` on `[0,1)`.
At the constructive-real level the reduction is already engineered uniformly
in `N` by `QHankel.geRat_minor_SN_factored`; we package it as a clean
consumer indexed by the single datum `nonnegCoeffs P_N`. -/

/-- **Packaged minor reduction.**  For every order `N`, if a minor `Δ` factors
as `(SN N)²·P` with `P` nonneg-coefficient and `a ≥ 0`, then `Δ ≥ 0`.  The
square factor `S_N` is the uniform q-product `SN N`; only `nonnegCoeffs P_N` is
order-specific.  (Re-export of `geRat_minor_SN_factored`.) -/
theorem gram_minor_nonneg_of_PN (N : Nat) {Δ : CReal} (P : QPoly.Poly)
    {a : CReal} (ha : ExpPos.geRat a 0) (hP : nonnegCoeffs P)
    (hΔ : CReal.Equiv Δ
      (CReal.mul (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) (ceval P a))) :
    ExpPos.geRat Δ 0 :=
  geRat_minor_SN_factored N P ha hP hΔ

/-! ## Extending the unconditional minor frontier to `N ≤ 5`

`N = 4` is `QHankel.delta4_nonneg_uniform` (re-exported).  `N = 5` is new:
`Δ_5 = (SN 5)²·P_5`, proved on the factored polynomial `(SN 5)²·P_5` directly
(the same `CReal` value as the expanded `Δ_5`, avoiding the degree-160
literal), through the uniform engine + `nonnegCoeffs P_5` (`decide`,
`FavardRec.P5_nonneg`). -/

/-- **`Δ_4(a) ≥ 0`** at `a ≥ 0`, via the uniform `SN`-engine + `nonnegCoeffs P_4`
(re-export of `QHankel.delta4_nonneg_uniform`).  Minor-level, unconditional. -/
theorem delta4_minor_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ4 a) 0 :=
  delta4_nonneg_uniform ha

/-- The order-5 minor in explicit factored form `(SN 5)²·P_5` (the same `CReal`
value as the expanded `Δ_5`, by the order-5 factorization). -/
def Delta5Factored : QPoly.Poly :=
  QPoly.pmul (QPoly.pmul (SN 5) (SN 5)) FavardRec.P5

set_option maxRecDepth 8000 in
/-- **`Δ_5(a) ≥ 0`** at `a ≥ 0`, on the factored polynomial `(SN 5)²·P_5`:
a perfect square times the nonneg-coefficient `P_5` (`FavardRec.P5_nonneg`).
Pushes the unconditional minor frontier to `N = 5`. -/
theorem delta5_minor_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Delta5Factored a) 0 :=
  ceval_factor_nonneg Delta5Factored (SN 5) FavardRec.P5 ha FavardRec.P5_nonneg
    (fun y => QPoly.poly_eqv _ _ y (by decide))

/-! ## At the heat-kernel point `a = e^{−t/4}`

`aVar t ht = e^{−t/4} ≥ 0` discharges the `a ≥ 0` hypothesis, so the extended
minors are nonnegative at the genuine heat-kernel base point for every `t ≥ 0`. -/

/-- **`Δ_4 ≥ 0` at `a = e^{−t/4}`.** -/
theorem delta4_minor_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ4 (aVar t ht)) 0 :=
  delta4_minor_nonneg (aVar_nonneg t ht)

set_option maxRecDepth 8000 in
/-- **`Δ_5 ≥ 0` at `a = e^{−t/4}`** (factored form). -/
theorem delta5_minor_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Delta5Factored (aVar t ht)) 0 :=
  delta5_minor_nonneg (aVar_nonneg t ht)

/-! ## Heat-kernel-point cyclotomic atoms

The base variable `a = e^{−t/4}` satisfies `0 ≤ a ≤ 1` (it is `≤ 1` since
`expNeg` of a nonneg argument is `≤ 1`).  Hence the weak cyclotomic atom
applies at the genuine heat-kernel point.  We record the `q ≥ 0` consequence
(`even_qpow_nonneg` needs no sign hypothesis and applies verbatim). -/

/-- `(e^{−t/4})^(2m) ≥ 0` (even-power atom at the heat-kernel point — a square,
needs no sign hypothesis; recorded as a usable instance). -/
theorem even_aVarApprox_qpow_nonneg (a : Q') (m : Nat) :
    (0 : Q') ≤ qpow a (2 * m) :=
  even_qpow_nonneg a m

end YMGap.Continuum.CyclotomicPositivity

/-! ## Summary — PROVED vs NAMED-open

**PROVED here (axiom-clean).**

  * Positivity atoms over `Q'`: `qpow_le_one`, `qpow_lt_one`,
    `one_sub_qpow_nonneg` (weak), `one_sub_qpow_pos` (strict, `n ≥ 1`),
    `qpow_nonneg_of_nonneg`, `even_qpow_nonneg` (even power of *any* `Q'` is
    `≥ 0`), and `even_one_sub_qpow_nonneg` (`(1 − q^n)^(2m) ≥ 0`).  These are
    the cyclotomic-factor base atoms the LDLᵀ-pivot route consumes.

  * `gram_minor_nonneg_of_PN` — the packaged `Δ_N = S_N²·P_N ⇒ Δ_N ≥ 0`
    reduction (re-export of the uniform `SN`-engine).

  * `delta4_minor_nonneg`, `delta5_minor_nonneg` (and the heat-kernel-point
    variants) — the unconditional *minor-level* frontier pushed from `N ≤ 3`
    to `N ≤ 5`, through the uniform square factor `SN N` + the per-`N`
    `decide` facts `nonnegCoeffs P_4` / `nonnegCoeffs P_5`.

**NOW UNCONDITIONAL (minor level).**  `Δ_N(a) ≥ 0` for `N ≤ 5` at every
`a ≥ 0` (and at `a = e^{−t/4}`, every `t ≥ 0`).  This extends the previously
proved `N ≤ 4` (`QHankel.delta{2,3,4}_nonneg_uniform`) to `N = 5`.

**NAMED-open.**

  * **Uniform `nonnegCoeffs P_N` for all `N`** — the `UniformGramSOS` / P_N /
    q-total-positivity wall.  This file extends the per-`N` frontier to
    `N ≤ 5`; the all-`N` statement is NOT closed (the coefficient lists are
    per-order `decide` certificates, not an `N`-indexed theorem).

  * **The Sylvester minor→form bridge.**  The results here are *minor-level*
    (`Δ_N(a) ≥ 0`).  The *form-level* range in
    `MomentSquarePSD.momentSquarePos_upTo` stays at `N ≤ 3`, because the form
    results there come from explicit LDLᵀ form certificates
    (`coneExp_psd_two/three`), not from minor positivity, and no `4×4`/`5×5`
    LDLᵀ form certificate exists in the repo.  Promoting the extended minors to
    `MomentSquarePosAt` requires (i) the order-`N` moment-bridge and (ii) the
    Sylvester step `leading minors ≥ 0 ⟹ form PSD` — the named bookkeeping
    bridge, deliberately NOT faked here.
-/

#print axioms YMGap.Continuum.CyclotomicPositivity.qpow_le_one
#print axioms YMGap.Continuum.CyclotomicPositivity.qpow_lt_one
#print axioms YMGap.Continuum.CyclotomicPositivity.one_sub_qpow_nonneg
#print axioms YMGap.Continuum.CyclotomicPositivity.one_sub_qpow_pos
#print axioms YMGap.Continuum.CyclotomicPositivity.qpow_nonneg_of_nonneg
#print axioms YMGap.Continuum.CyclotomicPositivity.even_qpow_nonneg
#print axioms YMGap.Continuum.CyclotomicPositivity.even_one_sub_qpow_nonneg
#print axioms YMGap.Continuum.CyclotomicPositivity.gram_minor_nonneg_of_PN
#print axioms YMGap.Continuum.CyclotomicPositivity.delta4_minor_nonneg
#print axioms YMGap.Continuum.CyclotomicPositivity.delta5_minor_nonneg
#print axioms YMGap.Continuum.CyclotomicPositivity.delta4_minor_nonneg_at
#print axioms YMGap.Continuum.CyclotomicPositivity.delta5_minor_nonneg_at
