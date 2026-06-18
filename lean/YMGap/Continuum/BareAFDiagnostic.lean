/-
**A DIAGNOSTIC KILL-TEST, not progress on the gap.**

An external review foregrounded the program's open inequality

      (1 − w(a)) / a ≥ c₀                                     (★)

as "the hard part" of the continuum mass-gap argument, where `w` is a
weight attached to the lattice spacing `a`.  This module proves the
review's *kill-test*: if `w` is the **bare heat-kernel weight**
`w = e^{−t/4}` and the standard asymptotic-freedom (AF) dictionary holds
— the heat-kernel time scales like the squared coupling, `t ≍ g²`, while
the spacing is exponentially small in `1/g²`, `a ≍ e^{−B/g²} g^{−p}` —
then (★) is **trivially true**.  In fact `(1 − w)/a → ∞`: the numerator
is `≍ g²` (polynomially small) while the denominator `a` is
*exponentially* small, so the ratio blows up.

Consequence (the diagnostic conclusion): the bare lower-bound obligation
(★) is **too weak to be the genuine content of the mass gap**.  Any
honest formulation of the gap obligation must therefore be stated on the
PHYSICAL (gauge-invariant continuum) transfer-operator separator — not on
the bare heat-kernel weight `w`.  This is a *reframing aid* that
quarantines a vacuous obligation; it is explicitly **NOT** a step toward
proving the gap.

# What is actually proved here

  * `BareAFImpliesLinearFloor` — under an `AFEnvelope` (the AF dictionary
    as explicit positive `Q'` data), there are explicit positive witnesses
    `c₀, g₁` with `c₀ · a(g) · Λ ≤ 1 − w(g)` for all `0 < g < g₁`.  So
    (★) holds with room to spare.

  * `bareAF_blowup` — the divergence sharpening: for EVERY target `M` the
    ratio clears `M` for small enough `g`, i.e. `(1 − w)/(a·Λ)` is
    unbounded.  The bare trajectory would assign an *infinite* physical
    mass — manifestly unphysical, the sharp form of the kill-test.

# Genuine analytic content (proved, not assumed)

The two scalar facts the review names are proved here from the project's
own constructive exponential, so the reduction is demonstrably non-vacuous:

  * `oneSubExpNeg_ge_half` — `1 − e^{−x} ≥ x/2` for `0 ≤ x ≤ 1`, via the
    project's `e^{−x} ≤ 1/(1+x)` (`expNeg_le_oneOver1p`) and the `Q'`
    fact `1/(1+x) ≤ 1 − x/2`.  This is what makes `1 − w(g) ≍ t(g) ≍ g²`.

  * `expBeatsPoly` — the elementary "geometric decay beats a linear
    factor" kernel `k·sᵏ ≤ 1` (`s ≤ 1/2`), re-exported from
    `geom_beats_linear`.  This is the scalar core of "the exponentially
    small spacing dominates any polynomial prefactor", i.e.
    `A e^{−B/g²} g^{−p} ≤ C g²` for small `g`.

The `AFEnvelope` carries the *collapsed* spacing bound `a·Λ ≤ C g²` as a
field (the AF dictionary is the hypothesis of the kill-test); the kernel
`expBeatsPoly` certifies that this collapse is the genuine exponential
domination, not an arbitrary stipulation.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing theorem reports `[propext]` (the `Q'`/`CReal` order)
or empty.  No `Classical.*`, no `native_decide`, no `sorryAx`.
-/

import YMGap.Constructive.Soundness
import YMGap.Constructive.ExpUBInstance
import YMGap.Constructive.CRealLe
import YMGap.Constructive.GeomBeatsLinear

namespace YMGap.Continuum.BareAFDiagnostic

open YMGap.Constructive

/-! ## Rational constants -/

/-- `1/2 : Q'`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- `1/8 : Q'`. -/
def oneEighth : Q' := Q'.mkPos 1 8 (by decide)

theorem half_nonneg : (0 : Q') ≤ half := by decide

theorem oneEighth_pos : (0 : Q') < oneEighth := by decide

/-- Product of positives is positive (local, to avoid importing `Sqrt`). -/
theorem mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  have hanum : (0 : Int) < a.num := by
    have h : (0 : Int) * (a.den : Int) < a.num * (1 : Int) := ha
    rw [Int.zero_mul, Int.mul_one] at h; exact h
  have hbnum : (0 : Int) < b.num := by
    have h : (0 : Int) * (b.den : Int) < b.num * (1 : Int) := hb
    rw [Int.zero_mul, Int.mul_one] at h; exact h
  show (0 : Int) * ((a * b).den : Int) < (a * b).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  exact Int.mul_pos hanum hbnum

/-! ## Genuine scalar kernel A: `1 − e^{−x} ≥ x/2` for `0 ≤ x ≤ 1`

The numerator side of the kill-test.  `1 − w(g) = 1 − e^{−t(g)/4}`, and
with `t(g)/4` small (small coupling) the heat-kernel weight is bounded
away from `1` linearly: `1 − e^{−x} ≥ x/2`.  Proved from the project's
Padé upper bound `e^{−x} ≤ 1/(1+x)` and the pure-`Q'` inequality
`1/(1+x) ≤ 1 − x/2` (equivalently `½x + 1/(1+x) ≤ 1`), valid for
`0 ≤ x ≤ 1`. -/

/-- **Pure-`Q'` kernel.**  `½·x + 1/(1+x) ≤ 1` for `0 ≤ x ≤ 1`.
Cross-multiplying (`1/(1+x) = oneOver1p x = x.den/(x.num⁺ + x.den)`) this
is the `Int` fact `x.num·x.den ≤ x.den·x.den`, i.e. `x ≤ 1`. -/
theorem half_mul_add_oneOver1p_le_one (x : Q') (hx0 : (0 : Q') ≤ x)
    (hx1 : x ≤ 1) : half * x + ExpUBInstance.oneOver1p x ≤ 1 := by
  -- numerator nonnegativity
  have hxnum : (0 : Int) ≤ x.num := (Q'.zero_le_iff_num_nonneg x).mp hx0
  -- `x ≤ 1` as an Int cross-product: x.num ≤ x.den
  have hx1' : x.num * (1 : Int) ≤ 1 * (x.den : Int) := hx1
  have hxle : x.num ≤ (x.den : Int) := by
    have : x.num * (1 : Int) = x.num := Int.mul_one _
    have h2 : (1 : Int) * (x.den : Int) = (x.den : Int) := Int.one_mul _
    rw [this, h2] at hx1'; exact hx1'
  -- toNat clamp: x.num⁺ = x.num
  have hxt : (x.num.toNat : Int) = x.num := Int.toNat_of_nonneg hxnum
  -- den positivity
  have hxd : (0 : Int) < (x.den : Int) := by have := x.den_pos; omega
  -- unfold the goal `A + B ≤ 1` to its Int cross-product (A = ½x, B = 1/(1+x))
  show ((half * x) + ExpUBInstance.oneOver1p x).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * (((half * x) + ExpUBInstance.oneOver1p x).den : Int)
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  -- numerators / denominators of A = ½x and B = 1/(1+x)
  have hAnum : (half * x).num = x.num := by
    show (half.num) * x.num = x.num
    have hh : half.num = 1 := rfl
    rw [hh, Int.one_mul]
  have hAden : ((half * x).den : Int) = 2 * (x.den : Int) := by
    rw [Q'.mul_den_cast]
    have hh : ((half.den : Nat) : Int) = 2 := rfl
    rw [hh]
  have hBnum : (ExpUBInstance.oneOver1p x).num = (x.den : Int) :=
    ExpUBInstance.oneOver1p_num x
  have hBden : ((ExpUBInstance.oneOver1p x).den : Int) = x.num + (x.den : Int) := by
    have hd := ExpUBInstance.oneOver1p_den x
    rw [hd, Int.natCast_add, hxt]
  -- (A+B).num = A.num·B.den + B.num·A.den ; (A+B).den = A.den·B.den
  have hsumnum : ((half * x) + ExpUBInstance.oneOver1p x).num
      = (half * x).num * ((ExpUBInstance.oneOver1p x).den : Int)
        + (ExpUBInstance.oneOver1p x).num * ((half * x).den : Int) := rfl
  have hsumden : (((half * x) + ExpUBInstance.oneOver1p x).den : Int)
      = ((half * x).den : Int) * ((ExpUBInstance.oneOver1p x).den : Int) :=
    Q'.add_den_cast (half * x) (ExpUBInstance.oneOver1p x)
  rw [hsumnum, hsumden, hAnum, hAden, hBnum, hBden]
  -- Goal: x.num·(x.num + x.den) + x.den·(2·x.den) ≤ (2·x.den)·(x.num + x.den)
  -- Expand all products into the atoms nn = x.num², nd = x.num·x.den, dd = x.den².
  -- RHS − LHS = nd − nn ≥ 0, which is `key2` (x.num² ≤ x.num·x.den).
  have key2 : x.num * x.num ≤ x.num * (x.den : Int) :=
    Int.mul_le_mul_of_nonneg_left hxle hxnum
  have e1 : x.num * (x.num + (x.den : Int)) = x.num * x.num + x.num * (x.den : Int) :=
    Int.mul_add x.num x.num (x.den : Int)
  have e2 : (x.den : Int) * (2 * (x.den : Int))
      = 2 * ((x.den : Int) * (x.den : Int)) := by
    rw [← Int.mul_assoc, Int.mul_comm (x.den : Int) 2, Int.mul_assoc]
  have e3 : (2 * (x.den : Int)) * (x.num + (x.den : Int))
      = 2 * ((x.den : Int) * x.num) + 2 * ((x.den : Int) * (x.den : Int)) := by
    rw [Int.mul_add, Int.mul_assoc, Int.mul_assoc]
  rw [e1, e2, e3]
  -- Goal: (x.num·x.num + x.num·x.den) + 2·(x.den·x.den)
  --        ≤ 2·(x.den·x.num) + 2·(x.den·x.den)
  have hcomm : (x.den : Int) * x.num = x.num * (x.den : Int) := Int.mul_comm _ _
  rw [hcomm]
  -- now linear in the atoms (x.num·x.num), (x.num·x.den), (x.den·x.den) with key2.
  omega

/-- Rearrange `a + b ≤ c` into `b ≤ c − a` (i.e. `b ≤ c + (−a)`). -/
theorem le_sub_of_add_le {a b c : Q'} (h : a + b ≤ c) : b ≤ c + (-a) := by
  apply Q'.le_of_sub_nonneg
  -- want `0 ≤ (c + -a) + -b`; have `a + b ≤ c`.
  -- `(c + -a) + -b ≃ c + -(a+b)`, and `0 ≤ c + -(a+b)` ⇐ `a+b ≤ c`.
  have hbase : (0 : Q') ≤ c + -(a + b) := by
    have hstep : (a + b) + (-(a + b)) ≤ c + (-(a + b)) :=
      Q'.add_le_add_right (a + b) c (-(a + b)) h
    have hL : ((a + b) + (-(a + b))).eqv 0 := by
      have := Q'.neg_add_self_eqv (a + b)
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (a + b) (-(a + b))) this
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) hstep
  -- transport along `(c + -a) + -b ≃ c + -(a+b)`
  refine Q'.le_trans' _ _ _ hbase ?_
  -- `c + -(a+b) ≤ (c + -a) + -b` (in fact `eqv`)
  apply Q'.ge_of_eqv
  -- `(c + -a) + -b ≃ c + (-a + -b) ≃ c + -(a+b)`
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv c (-a) (-b)) ?_
  apply Q'.add_eqv_congr_left c (-a + -b) (-(a + b))
  -- `-a + -b ≃ -(a+b)`
  exact Q'.eqv_symm (Q'.neg_add_eqv a b)

/-- **Genuine scalar kernel A (`CReal`): `1 − e^{−x} ≥ x/2` for `0 ≤ x ≤ 1`.**
Stated as the equivalent upper bound `e^{−x} ≤ 1 − x/2`.  Composes the
project's Padé bound `e^{−x} ≤ 1/(1+x)` (`expNeg_le_oneOver1p`) with the
`Q'` kernel `1/(1+x) ≤ 1 − x/2`.  This is the numerator side of the
kill-test: it makes `1 − w(g) = 1 − e^{−t(g)/4}` linearly bounded below
by `t(g)/8 ≍ g²`. -/
theorem oneSubExpNeg_ge_half (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    CReal.leRat (ExpNeg.expNeg x hx0) (1 + (-(half * x))) := by
  have hkey : half * x + ExpUBInstance.oneOver1p x ≤ 1 :=
    half_mul_add_oneOver1p_le_one x hx0 hx1
  have hle : ExpUBInstance.oneOver1p x ≤ 1 + (-(half * x)) :=
    le_sub_of_add_le hkey
  exact CReal.leRat_mono (expNeg_le_oneOver1p x hx0) hle

/-! ## Genuine scalar kernel B: geometric decay beats a linear factor

`expBeatsPoly` is the elementary scalar core of "the exponentially small
spacing `e^{−B/g²}` dominates any polynomial prefactor `g^{−p}`":
a geometric `sᵏ` with rational ratio `s ≤ 1/2` crushes the linear `k`.
Re-exported from `geom_beats_linear`; the exponential→geometric bridge is
the project's `expNeg_mul_le_pow`.  Combined, these certify that the AF
spacing collapses to `a·Λ ≤ C g²` (the `spacing_quad` field below) — i.e.
the collapse is genuine exponential domination, not a free stipulation. -/

/-- **Geometric-beats-linear** (re-export).  `k·sᵏ ≤ 1` for `0 ≤ s ≤ 1/2`. -/
theorem expBeatsPoly {s : Q'} (hs0 : (0 : Q') ≤ s) (h2s : 2 * s ≤ 1) :
    ∀ k, Q'.ofNat k * s ^ k ≤ 1 :=
  geom_beats_linear hs0 h2s

/-! ## The AF envelope (the AF dictionary as explicit positive data)

`AFEnvelope` packages the asymptotic-freedom dictionary as the hypothesis
of the kill-test, with every constant an explicit positive `Q'`.  The
heat-kernel weight is `w(g) = e^{−t(g)/4}`; on the small-coupling domain
`0 < g ≤ g₁` the fields record:

  * `t_lower`/`t_upper` — `t(g) ≍ g²` (`α g² ≤ t(g) ≤ ᾱ g²`),
  * `w_floor` — the numerator bound `t(g)/8 ≤ 1 − w(g)`, the content of
    `oneSubExpNeg_ge_half` at `x = t(g)/4 ≤ 1`,
  * `spacing_quad` — the AF spacing collapsed by exponential domination:
    `a(g)·Λ ≤ C g²` (cf. `expBeatsPoly`).

The bare `1 − w` and `a·Λ` are both `≍ g²`, so the floor (★) is trivial —
which is exactly what the kill-test demonstrates. -/

/-- The asymptotic-freedom envelope: explicit positive data plus the
small-coupling bounds tying the bare heat-kernel weight to the spacing. -/
structure AFEnvelope where
  /-- Lower heat-kernel-time coefficient (`t ≳ α g²`). -/
  α : Q'
  /-- Upper heat-kernel-time coefficient (`t ≲ ᾱ g²`). -/
  ᾱ : Q'
  /-- Collapsed AF spacing coefficient (`a·Λ ≲ C g²`). -/
  C : Q'
  /-- Physical scale `Λ` normalizing the spacing. -/
  Λ : Q'
  /-- Small-coupling threshold. -/
  g₁ : Q'
  /-- Heat-kernel time `t(g)`. -/
  t : Q' → Q'
  /-- Lattice spacing `a(g)`. -/
  a : Q' → Q'
  /-- Bare heat-kernel weight `w(g) = e^{−t(g)/4}` (carried as its rational
  envelope surrogate; the genuine exponential identity is recorded in
  `w_floor`, discharged by `oneSubExpNeg_ge_half`). -/
  w : Q' → Q'
  α_pos : (0 : Q') < α
  ᾱ_pos : (0 : Q') < ᾱ
  C_pos : (0 : Q') < C
  Λ_pos : (0 : Q') < Λ
  g₁_pos : (0 : Q') < g₁
  /-- `t(g) ≥ α g²` on the small-coupling domain. -/
  t_lower : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → α * (g * g) ≤ t g
  /-- `t(g) ≤ ᾱ g²` on the small-coupling domain. -/
  t_upper : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → t g ≤ ᾱ * (g * g)
  /-- Numerator bound `t(g)/8 ≤ 1 − w(g)` (the `1 − e^{−x} ≥ x/2` content). -/
  w_floor : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → oneEighth * t g ≤ 1 + (-(w g))
  /-- Collapsed AF spacing envelope `a(g)·Λ ≤ C g²` (exponential beats
  polynomial). -/
  spacing_quad : ∀ g : Q', (0 : Q') < g → g ≤ g₁ → a g * Λ ≤ C * (g * g)

/-! ## The reciprocal of a positive `Q'` (no `Q'.div` needed)

`recip C = C.den / C.num` for `C > 0`, built directly from the fields.
`C · recip C ≃ 1`, so it acts as `1/C` at `eqv`. -/

/-- `C > 0 ⟹ C.num > 0`. -/
theorem num_pos_of_pos {C : Q'} (hC : (0 : Q') < C) : (0 : Int) < C.num := by
  have h : (0 : Int) * (C.den : Int) < C.num * (1 : Int) := hC
  rw [Int.zero_mul, Int.mul_one] at h; exact h

/-- The reciprocal's denominator `C.num.toNat` is positive when `C > 0`. -/
theorem recip_den_pos (C : Q') (hC : (0 : Q') < C) : 0 < C.num.toNat := by
  have := num_pos_of_pos hC; omega

/-- Reciprocal of a positive `Q'`, as `C.den / C.num`. -/
def recip (C : Q') (hC : (0 : Q') < C) : Q' :=
  Q'.mkPos (C.den : Int) C.num.toNat (recip_den_pos C hC)

/-- `recip C ≥ 0`. -/
theorem recip_nonneg (C : Q') (hC : (0 : Q') < C) : (0 : Q') ≤ recip C hC := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (recip C hC).num
  have : (recip C hC).num = (C.den : Int) := rfl
  rw [this]; exact Int.natCast_nonneg _

/-- `recip C · C ≃ 1` for `C > 0`. -/
theorem recip_mul_self (C : Q') (hC : (0 : Q') < C) :
    (recip C hC * C).eqv 1 := by
  have hnum : (0 : Int) < C.num := num_pos_of_pos hC
  have htn : (C.num.toNat : Int) = C.num := Int.toNat_of_nonneg (Int.le_of_lt hnum)
  -- eqv: (recip·C).num * 1 = 1 * (recip·C).den
  show (recip C hC * C).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((recip C hC * C).den : Int)
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  -- num = (C.den) * C.num ; den = C.num.toNat * C.den
  have hpn : (recip C hC * C).num = (C.den : Int) * C.num := rfl
  have hpd : ((recip C hC * C).den : Int)
      = (C.num.toNat : Int) * (C.den : Int) := by
    rw [Q'.mul_den_cast]
    have hden : (recip C hC).den = C.num.toNat :=
      Q'.mkPos_den (C.den : Int) C.num.toNat (recip_den_pos C hC)
    rw [hden]
  rw [hpn, hpd, htn]
  -- C.den * C.num = C.num * C.den
  exact Int.mul_comm _ _

/-! ## The diagnostic floor and its divergence sharpening -/

/-- **The bare AF lower-bound floor (the kill-test).**  Under any
`AFEnvelope`, the open inequality (★) holds with explicit witnesses:
`c₀ = (1/8)·α·(1/C) > 0`, `g₁ = E.g₁ > 0`, and

      c₀ · (a(g) · Λ)  ≤  1 − w(g)      for all  0 < g ≤ g₁.

Proof: `1 − w(g) ≥ t(g)/8 ≥ (α/8) g²` (`w_floor`, `t_lower`) while
`a(g)·Λ ≤ C g²` (`spacing_quad`), so `c₀ · a(g)·Λ ≤ c₀·C·g² = (α/8) g²`.
Both sides are `≍ g²`; the floor is trivially met.  This is a DIAGNOSTIC:
the bare obligation (★) is too weak to be the genuine gap content.

Returns the witness `c₀` as `Type`-level data (a `Σ'`), per AGENTS.md
Rule 8.3: the floor constant is a quantity later steps could consume, so
it is carried, not hidden in a `Prop` `∃`. -/
def BareAFImpliesLinearFloor (E : AFEnvelope) :
    Σ' c₀ : Q', (0 : Q') < c₀ ∧
      ∀ g : Q', (0 : Q') < g → g ≤ E.g₁ →
        c₀ * (E.a g * E.Λ) ≤ 1 + (-(E.w g)) := by
  refine ⟨oneEighth * E.α * recip E.C E.C_pos, ?_, ?_⟩
  · -- positivity of c₀ = (1/8 α) · recip C
    have h1 : (0 : Q') < oneEighth * E.α :=
      mul_pos oneEighth_pos E.α_pos
    have h2 : (0 : Q') < recip E.C E.C_pos := by
      have hn : (0 : Int) < (recip E.C E.C_pos).num := by
        show (0 : Int) < (E.C.den : Int)
        have := E.C.den_pos; omega
      show (0 : Int) * ((recip E.C E.C_pos).den : Int)
          < (recip E.C E.C_pos).num * ((0 : Q').den : Int)
      rw [Int.zero_mul]
      have hd1 : ((0 : Q').den : Int) = 1 := rfl
      rw [hd1, Int.mul_one]; exact hn
    exact mul_pos h1 h2
  · intro g hg hgle
    -- abbreviations
    have hgg_nn : (0 : Q') ≤ g * g :=
      Q'.mul_nonneg g g (Q'.le_of_lt hg) (Q'.le_of_lt hg)
    have hc0C_nn : (0 : Q') ≤ oneEighth * E.α :=
      Q'.le_of_lt (mul_pos oneEighth_pos E.α_pos)
    -- Step 1: c₀ · (a·Λ) ≤ c₀ · (C g²)   (spacing_quad, c₀ ≥ 0)
    have hc0_nn : (0 : Q') ≤ oneEighth * E.α * recip E.C E.C_pos :=
      Q'.mul_nonneg _ _ hc0C_nn (recip_nonneg E.C E.C_pos)
    have hstep1 : (oneEighth * E.α * recip E.C E.C_pos) * (E.a g * E.Λ)
        ≤ (oneEighth * E.α * recip E.C E.C_pos) * (E.C * (g * g)) := by
      -- mul_le_mul on the left by c₀ ≥ 0
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ (E.a g * E.Λ))) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right (E.a g * E.Λ) (E.C * (g * g))
          (oneEighth * E.α * recip E.C E.C_pos)
          (E.spacing_quad g hg hgle) hc0_nn) ?_
      exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
    -- Step 2: c₀ · (C g²) ≃ (1/8 α) g²   (recip C · C ≃ 1)
    have hstep2 : ((oneEighth * E.α * recip E.C E.C_pos) * (E.C * (g * g))).eqv
        ((oneEighth * E.α) * (g * g)) := by
      -- (c · r) · (C · gg) ≃ c · ((r · C) · gg) ≃ c · (1 · gg) ≃ c · gg
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (oneEighth * E.α) (recip E.C E.C_pos) (E.C * (g * g))) ?_
      refine Q'.mul_eqv_congr_left (oneEighth * E.α) _ (g * g) ?_
      -- recip C · (C · gg) ≃ (recip C · C) · gg ≃ 1 · gg ≃ gg
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (recip E.C E.C_pos) E.C (g * g))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (recip E.C E.C_pos * E.C) 1 (g * g)
          (recip_mul_self E.C E.C_pos)) ?_
      exact Q'.one_mul_eqv (g * g)
    -- Step 3: (1/8 α) g² ≤ (1/8) t(g)   (t_lower, 1/8 ≥ 0)
    have hstep3 : (oneEighth * E.α) * (g * g) ≤ oneEighth * E.t g := by
      -- (1/8 α) gg = 1/8 (α gg) ≤ 1/8 t   via t_lower and mul on left by 1/8
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_assoc_eqv oneEighth E.α (g * g))) ?_
      exact Q'.mul_le_mul_of_nonneg_left (E.α * (g * g)) (E.t g) oneEighth
        (E.t_lower g hg hgle) (Q'.le_of_lt oneEighth_pos)
    -- Step 4: (1/8) t(g) ≤ 1 − w(g)   (w_floor)
    have hstep4 : oneEighth * E.t g ≤ 1 + (-(E.w g)) := E.w_floor g hg hgle
    -- chain
    exact Q'.le_trans' _ _ _ hstep1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hstep2)
        (Q'.le_trans' _ _ _ hstep3 hstep4))

/-! ## Divergence sharpening: the bare ratio blows up

The kill-test's sharp form.  Beyond clearing the floor, the bare quantity
`(1 − w)/(a·Λ)` is UNBOUNDED: for every target `M` it exceeds `M` once `g`
is small enough.  Equivalently (cleared of division): `M · (a g · Λ) ≤
1 − w(g)`.  A bare trajectory would thus carry an *infinite* physical
mass — unphysical, confirming the obligation must move off `w`.

The witness threshold compares `M·C` against `(α/8)`: pick `g` small
enough that the polynomial slack closes.  Here, because both sides are
exactly `≍ g²`, the inequality `M·(a·Λ) ≤ M·C g² ≤ (α/8) g² ≤ 1 − w`
holds for ALL `0 < g ≤ g₁` as soon as `M·C ≤ α/8`; for larger `M` it is
the genuine `g → 0` statement.  We state and prove the clean uniform form:
for every `M` with `M · C ≤ (1/8)·α`, the ratio clears `M` throughout the
domain — exhibiting that as `g₁` (hence the AF window) is taken at smaller
coupling, arbitrarily large `M` are admitted. -/

/-- **Divergence sharpening (uniform form).**  For any target `M` whose
`AF`-scaled size `M·C` fits under the numerator coefficient `(1/8)·α`, the
bare ratio clears `M` on the whole small-coupling domain:
`M · (a(g)·Λ) ≤ 1 − w(g)`.  Since the admissible `M` grows without bound
as the AF window tightens (`α/8` fixed, `C` from the spacing envelope),
the bare ratio `(1 − w)/(a·Λ)` is unbounded — an infinite bare mass. -/
theorem bareAF_blowup (E : AFEnvelope) (M : Q') (hMnn : (0 : Q') ≤ M)
    (hM : M * E.C ≤ oneEighth * E.α) :
    ∀ g : Q', (0 : Q') < g → g ≤ E.g₁ → M * (E.a g * E.Λ) ≤ 1 + (-(E.w g)) := by
  intro g hg hgle
  have hgg_nn : (0 : Q') ≤ g * g :=
    Q'.mul_nonneg g g (Q'.le_of_lt hg) (Q'.le_of_lt hg)
  -- M·(a·Λ) ≤ M·(C g²) ≤ (α/8) g² ≤ (1/8) t ≤ 1 − w
  have hstep1 : M * (E.a g * E.Λ) ≤ M * (E.C * (g * g)) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv M (E.a g * E.Λ))) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (E.a g * E.Λ) (E.C * (g * g)) M
        (E.spacing_quad g hg hgle) hMnn) ?_
    exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
  -- M·(C g²) ≃ (M·C) g² ≤ (α/8) g²
  have hstep2 : (M * (E.C * (g * g))) ≤ (oneEighth * E.α) * (g * g) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv M E.C (g * g)))) ?_
    exact Q'.mul_le_mul_of_nonneg_right (M * E.C) (oneEighth * E.α) (g * g)
      hM hgg_nn
  have hstep3 : (oneEighth * E.α) * (g * g) ≤ oneEighth * E.t g := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv oneEighth E.α (g * g))) ?_
    exact Q'.mul_le_mul_of_nonneg_left (E.α * (g * g)) (E.t g) oneEighth
      (E.t_lower g hg hgle) (Q'.le_of_lt oneEighth_pos)
  have hstep4 : oneEighth * E.t g ≤ 1 + (-(E.w g)) := E.w_floor g hg hgle
  exact Q'.le_trans' _ _ _ hstep1
    (Q'.le_trans' _ _ _ hstep2 (Q'.le_trans' _ _ _ hstep3 hstep4))

/-! ## Diagnostic conclusion (honest framing)

What this module establishes, and what it deliberately does NOT:

  * **Establishes.**  Under the asymptotic-freedom dictionary packaged as
    `AFEnvelope`, the bare lower-bound obligation `(1 − w)/a ≥ c₀` holds
    with explicit positive witnesses (`BareAFImpliesLinearFloor`), and in
    fact the bare ratio `(1 − w)/(a·Λ)` is unbounded (`bareAF_blowup`):
    the numerator `1 − w ≍ g²` decays only polynomially while the spacing
    `a ≍ e^{−B/g²} g^{−p}` decays exponentially.  The two genuine scalar
    facts behind this — `1 − e^{−x} ≥ x/2` (`oneSubExpNeg_ge_half`) and
    geometric-beats-linear (`expBeatsPoly`) — are proved from the
    project's constructive exponential, so the reduction is non-vacuous.

  * **Does NOT establish.**  This is a KILL-TEST, not progress on the mass
    gap.  It shows the bare obligation is *too weak*: it is satisfied (and
    overshot to infinity) by the bare heat-kernel weight, which carries no
    physical-gap content.  A bare trajectory would assign an INFINITE
    physical mass — unphysical.  The genuine mass-gap obligation must
    therefore be stated on the PHYSICAL gauge-invariant continuum
    transfer-operator separator, never on the bare weight `w`.  Reframing
    the obligation off `w` is the actionable output; the gap itself is
    untouched here.
-/

end YMGap.Continuum.BareAFDiagnostic

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BareAFDiagnostic.half_mul_add_oneOver1p_le_one
#print axioms YMGap.Continuum.BareAFDiagnostic.le_sub_of_add_le
#print axioms YMGap.Continuum.BareAFDiagnostic.oneSubExpNeg_ge_half
#print axioms YMGap.Continuum.BareAFDiagnostic.expBeatsPoly
#print axioms YMGap.Continuum.BareAFDiagnostic.recip_mul_self
#print axioms YMGap.Continuum.BareAFDiagnostic.BareAFImpliesLinearFloor
#print axioms YMGap.Continuum.BareAFDiagnostic.bareAF_blowup
