/-
The **exponential product floor** — an all-`R` lower bound for the
one-minus-loss product, upgrading the Weierstrass floor (valid only for
`R < 1`) to the exponential form valid for every finite total defect.

# What this module delivers

Writing `δ_k` for the per-block *loss* and `∏_{k<n}(1 − δ_k)` for the running
one-minus-loss product, this module proves — entirely constructively,
axiom-clean — the exponential floor

    ∏_{k<n} (1 − δ_k)  ≥  e^{−2·∑_{k<n} δ_k}  ≥  e^{−2R}

valid for `0 ≤ δ_k ≤ 1/2` and any uniform partial-sum bound `∑ δ_k ≤ R`.  The
constant `e^{−2R}` is strictly positive for ALL finite `R ≥ 0`, in contrast to
the Weierstrass floor `1 − R`, which is positive only when `R < 1`.  Since the
summable per-block defect of the RG persistence trajectory can have `R ≥ 1`,
this all-`R` floor is the form the persistence bridge actually needs.

# The sound rational-bound formulation

The product `∏_{k<n}(1 − δ_k)` is a pure rational `Q'` value (its factors are
rationals).  The exponential `e^{−y}` is a constructive real built from the
rational partial sums of its series.  The relation we prove is therefore the
SOUND rational upper bound on the exponential, `CReal.leRat (e^{−y}) b`: the
limit of `e^{−y}` is `≤ b` for the rational `b = ∏(1 − δ_k)`.  This is the
regularity-free bound the exponential-soundness layer already uses
(it composes through rationals, unlike the non-transitive one-slack `≤`), and
it carries no classical content.

# The crux elementary inequality

The mathematical heart is `expNegTwoX_leRat_oneSub`: for `x ∈ [0, 1/2]`,

    e^{−2x}  ≤  1 − x .

Proof route, fully constructive:
`e^{−2x} = e^{−x}·e^{−x}` (the exponential addition law), each factor
`e^{−x} ≤ 1/(1+x)` (the recorded U.5 soundness bound), so by the product upper
bound `e^{−2x} ≤ (1/(1+x))²`; and `(1/(1+x))² ≤ 1 − x` is the pure-`Q'`
polynomial inequality `1 ≤ (1−x)(1+x)²` on `[0,1/2]`, which factors as
`0 ≤ x·(d² − x.num·d − x.num²)` and holds because `2·x.num ≤ x.den` there.

# The positivity of the floor constant

`e^{−2R} > 0`.  Strict positivity for arbitrary `R` is a reciprocal-of-an-
upper-bound fact: from `e^{2R}·e^{−2R} ≥ 1` and a rational upper bound
`e^{2R} ≤ E` we get `e^{−2R} ≥ 1/(E+1) > 0`.  The rational upper bound `E` on the
positive series `e^{2R}` is the dual of the negative-series certificate
(`expPos_leRat` below), and the reciprocal lower bound is `expNeg_geRat_recipPos`.
The witness is `geRat (e^{−2R}) (1/(E+1))` with `1/(E+1) > 0`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom; the
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  Every constant is `Type`-level data.
-/

import YMGap.Constructive.Soundness
import YMGap.Constructive.CRealMulLe
import YMGap.Constructive.ExpNegCongr
import YMGap.Constructive.ProductLaw
import YMGap.Constructive.Sqrt
import YMGap.Continuum.ProductFloor

namespace YMGap.Continuum.ExpProductFloor

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat
open YMGap.Continuum.ProductFloor

/-! ## 1. The crux: `e^{−2x} ≤ 1 − x` on `[0, 1/2]`

We work with `2x` rendered as `x + x` so the exponential addition law
`e^{−x}·e^{−x} ≃ e^{−(x+x)}` applies verbatim.  The factor bound
`e^{−x} ≤ 1/(1+x) = ExpUBInstance.oneOver1p x` and the product upper bound
`leRat_mul` give `e^{−(x+x)} ≤ (oneOver1p x)²`, and the remaining work is the
pure-`Q'` polynomial inequality `(oneOver1p x)² ≤ 1 − x`. -/

/-- The integer polynomial core of the crux.  With `d = n + m` (so `m = d − n`),
`0 ≤ n`, and `n ≤ m` (the cross form of `x = n/d ≤ 1/2`, i.e. `2n ≤ d`):

    (n + m)·(n + m)·(n + m)  ≤  m·((2n + m)·(2n + m)) .

This is `d³ ≤ (d−n)·(n+d)²` rewritten with `d = n + m`, `n + d = 2n + m`.  The
difference `RHS − LHS = n·(m² + m·n − n²) ≥ 0`, established here additively (no
subtraction) via the identity `RHS + n·n·n = LHS + (n·(m·m) + n·(m·n))` plus the
bound `n·(n·n) ≤ n·(m·m)`. -/
theorem crux_int (n m : Int) (hn : (0 : Int) ≤ n) (hnm : n ≤ m) :
    (n + m) * (n + m) * (n + m) ≤ m * ((2 * n + m) * (2 * n + m)) := by
  -- additive identity: RHS + n·(n·n) = LHS + (n·(m·m) + n·(m·n)).
  have hid : m * ((2 * n + m) * (2 * n + m)) + n * (n * n)
      = (n + m) * (n + m) * (n + m) + (n * (m * m) + n * (m * n)) := by
    have h2n : (2 : Int) * n = n + n := by
      rw [show (2 : Int) = 1 + 1 from by decide, Int.add_mul, Int.one_mul]
    rw [h2n]
    simp only [Int.add_mul, Int.mul_add]
    ac_rfl
  -- n·(n·n) ≤ n·(m·m) since n ≤ m (so n·n ≤ m·m) and n ≥ 0.
  have hmm : n * n ≤ m * m :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right hnm hn)
      (Int.mul_le_mul_of_nonneg_left hnm (Int.le_trans hn hnm))
  have h1 : n * (n * n) ≤ n * (m * m) := Int.mul_le_mul_of_nonneg_left hmm hn
  -- 0 ≤ n·(m·n).
  have h2 : (0 : Int) ≤ n * (m * n) :=
    Int.mul_nonneg hn (Int.mul_nonneg (Int.le_trans hn hnm) hn)
  omega

/-- The `Q'` crux at the level of `oneOver1p`.  For `0 ≤ x ≤ 1/2`,

    oneOver1p x · oneOver1p x  ≤  1 − x .

Reduced to `crux_int` via the cross-product; the `Int.toNat` clamp in
`oneOver1p`'s denominator collapses to `x.num` because `x ≥ 0`. -/
theorem oneOver1p_sq_le_oneSub (x : Q') (hx0 : (0 : Q') ≤ x)
    (hx1 : x ≤ half) :
    ExpUBInstance.oneOver1p x * ExpUBInstance.oneOver1p x ≤ 1 - x := by
  -- num/den facts.
  have hnum_nn : (0 : Int) ≤ x.num := (Q'.zero_le_iff_num_nonneg x).mp hx0
  have hden1 : (1 : Int) ≤ (x.den : Int) := by have := x.den_pos; omega
  -- x ≤ 1/2 cross form: x.num · 2 ≤ 1 · x.den, i.e. 2·x.num ≤ x.den.
  have h2 : 2 * x.num ≤ (x.den : Int) := by
    have h : x.num * ((half).den : Int) ≤ (half).num * (x.den : Int) := hx1
    -- half.num = 1, half.den = 2.
    have hhn : (half).num = 1 := rfl
    have hhd : ((half).den : Int) = 2 := rfl
    rw [hhn, hhd, Int.one_mul] at h
    omega
  -- toNat clamp.
  have htoNat : (x.num.toNat : Int) = x.num := Int.toNat_of_nonneg hnum_nn
  -- Unfold the goal at the Int cross-product level.
  show (ExpUBInstance.oneOver1p x * ExpUBInstance.oneOver1p x).num
        * ((1 - x).den : Int)
      ≤ (1 - x).num
        * ((ExpUBInstance.oneOver1p x * ExpUBInstance.oneOver1p x).den : Int)
  -- LHS num = (x.den)·(x.den) ; LHS den = (oneOver1p x).den².
  rw [Q'.mul_num_cast]
  rw [ExpUBInstance.oneOver1p_num]
  -- (1 - x).num and .den.
  have h1x_num : (1 - x).num = (x.den : Int) - x.num := by
    show (1 : Q').num * ((-x).den : Int) + (-x).num * ((1 : Q').den : Int)
        = (x.den : Int) - x.num
    have e1 : ((-x).den : Int) = (x.den : Int) := rfl
    have e2 : (-x).num = -x.num := rfl
    have hn : (1 : Q').num = 1 := rfl
    have hd : ((1 : Q').den : Int) = 1 := rfl
    rw [e1, e2, hn, hd, Int.one_mul, Int.mul_one]
    omega
  have h1x_den : ((1 - x).den : Int) = (x.den : Int) := by
    show (((1 : Q').den * (-x).den : Nat) : Int) = (x.den : Int)
    have : ((1 : Q').den * (-x).den : Nat) = x.den := by
      show (1 * x.den : Nat) = x.den; omega
    rw [this]
  rw [h1x_num, h1x_den]
  -- LHS den (oneOver1p x).den as Int = (x.num.toNat + x.den)·(x.num.toNat + x.den).
  rw [Q'.mul_den_cast]
  rw [ExpUBInstance.oneOver1p_den]
  -- Now the goal is purely Int; rewrite the toNat clamp and apply crux_int.
  -- ((x.num.toNat + x.den : Nat) : Int) = x.num + x.den.
  have hcast : ((x.num.toNat + x.den : Nat) : Int) = x.num + (x.den : Int) := by
    rw [Int.natCast_add, htoNat]
  show (x.den : Int) * (x.den : Int) * (x.den : Int)
      ≤ ((x.den : Int) - x.num)
        * (((x.num.toNat + x.den : Nat) : Int) * ((x.num.toNat + x.den : Nat) : Int))
  rw [hcast]
  -- Apply crux_int with n = x.num, m = x.den − x.num; rewrite back to goal shape.
  have hm := crux_int x.num ((x.den : Int) - x.num) hnum_nn (by omega)
  have e1 : x.num + ((x.den : Int) - x.num) = (x.den : Int) := by omega
  have e2 : 2 * x.num + ((x.den : Int) - x.num) = x.num + (x.den : Int) := by omega
  rw [e1, e2] at hm
  exact hm

/-- **The crux elementary inequality.**  For `0 ≤ x ≤ 1/2`,

    e^{−2x}  ≤  1 − x    (as the sound rational bound `leRat`),

with `2x` written `x + x`.  Chain:
`e^{−(x+x)} ≃ e^{−x}·e^{−x} ≤ (oneOver1p x)² ≤ 1 − x`. -/
theorem expNegTwoX_leRat_oneSub (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ half) :
    CReal.leRat (ExpNeg.expNeg (x + x) (Q'.zero_le_add x x hx0 hx0)) (1 - x) := by
  -- e^{−x}·e^{−x} ≤ (oneOver1p x)·(oneOver1p x).
  have hmul : CReal.leRat
      (CReal.mul (ExpNeg.expNeg x hx0) (ExpNeg.expNeg x hx0))
      (ExpUBInstance.oneOver1p x * ExpUBInstance.oneOver1p x) :=
    CReal.leRat_mul (expNeg_le_oneOver1p x hx0) (expNeg_le_oneOver1p x hx0)
      (expNeg_geRat_zero x hx0) (expNeg_geRat_zero x hx0)
      (ExpUBInstance.oneOver1p_nonneg x) (ExpUBInstance.oneOver1p_nonneg x)
  -- transfer the bound to e^{−(x+x)} via the addition law.
  have htrans : CReal.leRat (ExpNeg.expNeg (x + x) (Q'.zero_le_add x x hx0 hx0))
      (ExpUBInstance.oneOver1p x * ExpUBInstance.oneOver1p x) :=
    CReal.leRat_of_equiv
      (CReal.Equiv.symm (expNeg_add_equiv x x hx0 hx0)) hmul
  -- weaken the rational bound to 1 − x.
  exact CReal.leRat_mono htrans (oneOver1p_sq_le_oneSub x hx0 hx1)

/-! ## 2. The finite exponential product floor

`prodOneSub δ n = ∏_{k<n}(1 − δ_k)` and `lossSum δ n = ∑_{k<n} δ_k` are the pure
`Q'` recursions from the companion product-floor module.  The exponent `2·∑δ` is
carried as `lossSum δ n + lossSum δ n` so the exponential addition law applies
verbatim.  The floor

    e^{−(∑δ + ∑δ)}  ≤  ∏_{k<n}(1 − δ_k)

is proved by induction: the step splits the exponential along the addition law
into `e^{−(L+L)}·e^{−(δ+δ)}`, bounds the first factor by the IH and the second
by the crux, and multiplies (the per-block factor `1 − δ_n ≥ 0`). -/

/-- `e^{−0} ≤ 1` (the base case): `e^{−(0+0)} ≤ oneOver1p 0 = 1`. -/
theorem expNeg_zero_leRat_one :
    CReal.leRat (ExpNeg.expNeg ((0 : Q') + 0) (Q'.zero_le_add 0 0 (by decide) (by decide)))
      (1 : Q') := by
  have h := expNeg_le_oneOver1p ((0 : Q') + 0) (Q'.zero_le_add 0 0 (by decide) (by decide))
  -- oneOver1p (0+0) ≤ 1 (antitone in 0 ≤ 0+0, oneOver1p 0 = 1) — use the bound ≤ 1 directly.
  refine CReal.leRat_mono h ?_
  -- oneOver1p (0+0) ≤ 1 : its num = (0+0).den, den = ... ; decide.
  decide

/-- Every per-block loss `δ_k ≤ 1/2` (`< 1`), so `0 ≤ 1 − δ_k`; the running
product `prodOneSub` stays nonnegative. -/
theorem prodOneSub_nonneg (δ : Nat → Q')
    (hδ : ∀ k, (0 : Q') ≤ δ k ∧ δ k ≤ half) :
    ∀ n, (0 : Q') ≤ prodOneSub δ n
  | 0 => by show (0 : Q') ≤ (1 : Q'); decide
  | n + 1 => by
    show (0 : Q') ≤ prodOneSub δ n * (1 - δ n)
    have hfac : (0 : Q') ≤ 1 - δ n := by
      show (0 : Q') ≤ 1 + (-δ n)
      have h : δ n ≤ 1 :=
        Q'.le_trans' (δ n) half 1 (hδ n).2 (by decide)
      have hstep := Q'.add_le_add_right (δ n) 1 (-δ n) h
      refine Q'.le_trans' _ _ _ ?_ hstep
      exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (δ n))
    exact Q'.mul_nonneg _ _ (prodOneSub_nonneg δ hδ n) hfac

/-- **The finite exponential product floor.**  For per-block losses
`0 ≤ δ_k ≤ 1/2`,

    e^{−(∑_{k<n}δ + ∑_{k<n}δ)}  ≤  ∏_{k<n}(1 − δ_k)    (sound `leRat`). -/
theorem prod_floor_exp_finite (δ : Nat → Q')
    (hδ : ∀ k, (0 : Q') ≤ δ k ∧ δ k ≤ half) :
    ∀ n, CReal.leRat
      (ExpNeg.expNeg (lossSum δ n + lossSum δ n)
        (Q'.zero_le_add _ _ (lossSum_nonneg δ (fun k => (hδ k).1) n)
          (lossSum_nonneg δ (fun k => (hδ k).1) n)))
      (prodOneSub δ n)
  | 0 => by
    -- lossSum δ 0 = 0, so the exponent is 0 + 0; prodOneSub δ 0 = 1.
    exact expNeg_zero_leRat_one
  | n + 1 => by
    have ih := prod_floor_exp_finite δ hδ n
    -- abbreviations.
    have hLnn : (0 : Q') ≤ lossSum δ n := lossSum_nonneg δ (fun k => (hδ k).1) n
    have hδnnn : (0 : Q') ≤ δ n := (hδ n).1
    -- nonnegativity of the relevant sums.
    have hLL : (0 : Q') ≤ lossSum δ n + lossSum δ n := Q'.zero_le_add _ _ hLnn hLnn
    have hdd : (0 : Q') ≤ δ n + δ n := Q'.zero_le_add _ _ hδnnn hδnnn
    -- e^{−(L+L)}·e^{−(δ+δ)} ≃ e^{−((L+L)+(δ+δ))}.
    have hadd := expNeg_add_equiv (lossSum δ n + lossSum δ n) (δ n + δ n) hLL hdd
    -- the next exponent (L+δ)+(L+δ) ≃ (L+L)+(δ+δ).
    have hLnext : (0 : Q') ≤ lossSum δ (n + 1) :=
      lossSum_nonneg δ (fun k => (hδ k).1) (n + 1)
    have hexp_eqv : ((lossSum δ (n + 1) + lossSum δ (n + 1))).eqv
        ((lossSum δ n + lossSum δ n) + (δ n + δ n)) := by
      -- lossSum δ (n+1) = lossSum δ n + δ n definitionally.
      show (((lossSum δ n + δ n) + (lossSum δ n + δ n))).eqv
          ((lossSum δ n + lossSum δ n) + (δ n + δ n))
      -- pure additive rearrangement (a+b)+(a+b) ≃ (a+a)+(b+b).
      show (((lossSum δ n + δ n) + (lossSum δ n + δ n)).num
          * (((lossSum δ n + lossSum δ n) + (δ n + δ n)).den : Int))
        = (((lossSum δ n + lossSum δ n) + (δ n + δ n)).num
          * (((lossSum δ n + δ n) + (lossSum δ n + δ n)).den : Int))
      simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul]
      ac_rfl
    -- e^{−(L+δ + L+δ)} ≃ e^{−((L+L)+(δ+δ))} ≃ e^{−(L+L)}·e^{−(δ+δ)}.
    have hcongr := expNeg_eqv_congr
      (Q'.zero_le_add _ _ hLnext hLnext)
      (Q'.zero_le_add _ _ hLL hdd) hexp_eqv
    -- the product bound: e^{−(L+L)}·e^{−(δ+δ)} ≤ prodOneSub δ n · (1 − δ n).
    have hfac_le : CReal.leRat
        (ExpNeg.expNeg (δ n + δ n) hdd) (1 - δ n) :=
      expNegTwoX_leRat_oneSub (δ n) hδnnn (hδ n).2
    have hprodOne_nn : (0 : Q') ≤ prodOneSub δ n := prodOneSub_nonneg δ hδ n
    have h1δ_nn : (0 : Q') ≤ 1 - δ n := by
      show (0 : Q') ≤ 1 + (-δ n)
      have h : δ n ≤ 1 := Q'.le_trans' (δ n) half 1 (hδ n).2 (by decide)
      refine Q'.le_trans' _ _ _ ?_ (Q'.add_le_add_right (δ n) 1 (-δ n) h)
      exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (δ n))
    have hmul : CReal.leRat
        (CReal.mul (ExpNeg.expNeg (lossSum δ n + lossSum δ n) hLL)
          (ExpNeg.expNeg (δ n + δ n) hdd))
        (prodOneSub δ n * (1 - δ n)) :=
      CReal.leRat_mul ih hfac_le
        (expNeg_geRat_zero _ hLL) (expNeg_geRat_zero _ hdd)
        hprodOne_nn h1δ_nn
    -- transfer through the two Equivs to the (n+1) exponent.
    have hstep : CReal.leRat
        (ExpNeg.expNeg (lossSum δ (n + 1) + lossSum δ (n + 1))
          (Q'.zero_le_add _ _ hLnext hLnext))
        (prodOneSub δ n * (1 - δ n)) :=
      CReal.leRat_of_equiv
        (CReal.Equiv.trans hcongr (CReal.Equiv.symm hadd)) hmul
    -- prodOneSub δ (n+1) = prodOneSub δ n * (1 − δ n) definitionally.
    exact hstep

/-! ## 3. The floor from a uniform summability bound (all `R`)

From a uniform partial-sum bound `∑_{k<n} δ ≤ R` the finite floor strengthens to
the single constant `e^{−(R+R)}`, positive for ALL finite `R ≥ 0`.  We split the
exponent `R = ∑δ + (R − ∑δ)` (with `R − ∑δ ≥ 0`) and bound the surplus factor
`e^{−((R−L)+(R−L))} ≤ 1`. -/

/-- `e^{−y} ≤ 1` for `y ≥ 0`: `e^{−y} ≤ oneOver1p y ≤ oneOver1p 0 = 1`. -/
theorem expNeg_leRat_one (y : Q') (hy : (0 : Q') ≤ y) :
    CReal.leRat (ExpNeg.expNeg y hy) (1 : Q') := by
  refine CReal.leRat_mono (expNeg_le_oneOver1p y hy) ?_
  -- oneOver1p y ≤ oneOver1p 0 = 1.
  refine Q'.le_trans' _ _ _ (ExpUBInstance.oneOver1p_antitone 0 y hy) ?_
  rw [ExpUBInstance.oneOver1p_zero]
  exact Q'.le_refl' 1

/-- **The exponential product floor from summability.**  If every loss partial
sum is `≤ R`, then `e^{−(R+R)} ≤ ∏_{k<n}(1 − δ_k)` for every prefix length `n`. -/
theorem prod_floor_exp_of_sum_le (δ : Nat → Q')
    (hδ : ∀ k, (0 : Q') ≤ δ k ∧ δ k ≤ half)
    (R : Q') (hR : ∀ n, lossSum δ n ≤ R) :
    ∀ n, CReal.leRat
      (ExpNeg.expNeg (R + R) (Q'.zero_le_add R R
        (Q'.le_trans' 0 (lossSum δ 0) R (lossSum_nonneg δ (fun k => (hδ k).1) 0) (hR 0))
        (Q'.le_trans' 0 (lossSum δ 0) R (lossSum_nonneg δ (fun k => (hδ k).1) 0) (hR 0))))
      (prodOneSub δ n) := by
  intro n
  -- abbreviations.
  have hRnn : (0 : Q') ≤ R :=
    Q'.le_trans' 0 (lossSum δ 0) R (lossSum_nonneg δ (fun k => (hδ k).1) 0) (hR 0)
  have hLnn : (0 : Q') ≤ lossSum δ n := lossSum_nonneg δ (fun k => (hδ k).1) n
  -- surplus s := R − lossSum δ n ≥ 0.
  have hsnn : (0 : Q') ≤ R + (-(lossSum δ n)) := by
    have hstep := Q'.add_le_add_right (lossSum δ n) R (-(lossSum δ n)) (hR n)
    refine Q'.le_trans' _ _ _ ?_ hstep
    exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (lossSum δ n))
  have hLL : (0 : Q') ≤ lossSum δ n + lossSum δ n := Q'.zero_le_add _ _ hLnn hLnn
  have hss : (0 : Q') ≤ (R + (-(lossSum δ n))) + (R + (-(lossSum δ n))) :=
    Q'.zero_le_add _ _ hsnn hsnn
  -- (R+R) ≃ (L+L) + (s+s) where s = R − L = R + (-L).  Proved by pure additive
  -- `Q'.eqv` rearrangement: (L+L)+(s+s) ≃ (L+s)+(L+s) and L+s ≃ R.
  have hLs : ((lossSum δ n) + (R + (-(lossSum δ n)))).eqv R := by
    -- L + (R + -L) ≃ L + (-L + R) ≃ (L + -L) + R ≃ 0 + R ≃ R.
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (lossSum δ n) _ _
        (Q'.add_comm_eqv R (-(lossSum δ n)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (lossSum δ n) (-(lossSum δ n)) R)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ 0 R (Q'.add_neg_self_eqv (lossSum δ n))) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' R)
  have hexp_eqv : ((R + R)).eqv
      ((lossSum δ n + lossSum δ n)
        + ((R + (-(lossSum δ n))) + (R + (-(lossSum δ n))))) := by
    refine Q'.eqv_symm ?_
    -- (L+L)+(s+s) ≃ (L+s)+(L+s) ≃ R+R.
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner (lossSum δ n) (lossSum δ n)
        (R + (-(lossSum δ n))) (R + (-(lossSum δ n)))) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ R _ hLs)
      (Q'.add_eqv_congr_left R _ R hLs)
  -- e^{−(L+L)}·e^{−(s+s)} ≃ e^{−((L+L)+(s+s))} ≃ e^{−(R+R)}.
  have hadd := expNeg_add_equiv (lossSum δ n + lossSum δ n)
    ((R + (-(lossSum δ n))) + (R + (-(lossSum δ n)))) hLL hss
  have hcongr := expNeg_eqv_congr
    (Q'.zero_le_add R R hRnn hRnn)
    (Q'.zero_le_add _ _ hLL hss) hexp_eqv
  -- finite floor at n bounds the first factor; surplus factor ≤ 1.
  have hfin := prod_floor_exp_finite δ hδ n
  have hsurplus : CReal.leRat
      (ExpNeg.expNeg ((R + (-(lossSum δ n))) + (R + (-(lossSum δ n)))) hss) (1 : Q') :=
    expNeg_leRat_one _ hss
  have hprodOne_nn : (0 : Q') ≤ prodOneSub δ n := prodOneSub_nonneg δ hδ n
  -- product bound: ≤ prodOneSub δ n · 1.
  have hmul : CReal.leRat
      (CReal.mul (ExpNeg.expNeg (lossSum δ n + lossSum δ n) hLL)
        (ExpNeg.expNeg ((R + (-(lossSum δ n))) + (R + (-(lossSum δ n)))) hss))
      (prodOneSub δ n * 1) :=
    CReal.leRat_mul hfin hsurplus
      (expNeg_geRat_zero _ hLL) (expNeg_geRat_zero _ hss)
      hprodOne_nn (by decide)
  -- prodOneSub δ n · 1 ≤ prodOneSub δ n.
  have hmul' : CReal.leRat
      (CReal.mul (ExpNeg.expNeg (lossSum δ n + lossSum δ n) hLL)
        (ExpNeg.expNeg ((R + (-(lossSum δ n))) + (R + (-(lossSum δ n)))) hss))
      (prodOneSub δ n) :=
    CReal.leRat_mono hmul (Q'.le_of_eqv (Q'.mul_one_eqv (prodOneSub δ n)))
  -- transfer to e^{−(R+R)}.
  exact CReal.leRat_of_equiv
    (CReal.Equiv.trans hcongr (CReal.Equiv.symm hadd)) hmul'

/-! ## 4. Strict positivity of the floor constant `e^{−(R+R)} > 0`

Strict positivity for arbitrary `R` is the reciprocal of an upper bound on the
positive series.  `expPos_leRat` is the rational upper bound `e^y ≤ E` (the dual
of the negative-series certificate `ExpNeg.expNeg_leRat`, via the magnitude block
bounds); `expNeg_geRat_recipPos` then extracts `e^{−y} ≥ 1/E > 0` from
`e^y·e^{−y} ≥ 1` (`expProd_geRat`).  The positivity witness for the floor is
therefore `geRat (e^{−(R+R)}) (1/E) ` with `1/E > 0`. -/

/-- **Sound rational upper bound on `e^{+y}`.**  `e^y ≤ᵣ b`, certified by a single
`Q'` inequality `partialSumAbs y K + (termAbs y K + termAbs y K) ≤ b` at a cutoff
index `K` past `halfRatioCutoff y` (the dual of `ExpNeg.expNeg_leRat`). -/
theorem expPos_leRat (y : Q') (hy : (0 : Q') ≤ y) (b : Q') (K : Nat)
    (hcut : halfRatioCutoff y ≤ K)
    (hcert : ExpNeg.partialSumAbs y K
        + (ExpNeg.termAbs y K + ExpNeg.termAbs y K) ≤ b) :
    CReal.leRat (ExpPos.expPos y hy) b := by
  apply CReal.leRat_of_eventually
  refine ⟨K, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show ExpNeg.partialSumAbs y (K + d) ≤ b
  have hc : (0 : Q') ≤ ExpNeg.termAbs y K := ExpNeg.termAbs_nonneg y hy K
  have hH : (0 : Q') ≤ ExpNeg.termAbs y K + ExpNeg.termAbs y K := Q'.zero_le_add _ _ hc hc
  have hhalfcc : (half * (ExpNeg.termAbs y K + ExpNeg.termAbs y K)).eqv
      (ExpNeg.termAbs y K) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv half (ExpNeg.termAbs y K) (ExpNeg.termAbs y K))
      (ExpNeg.two_halves (ExpNeg.termAbs y K))
  have hrec : ExpNeg.termAbs y K + half * (ExpNeg.termAbs y K + ExpNeg.termAbs y K)
      ≤ ExpNeg.termAbs y K + ExpNeg.termAbs y K :=
    ExpNeg.expNeg_recurrence y K (ExpNeg.termAbs y K + ExpNeg.termAbs y K)
      (Q'.ge_of_eqv hhalfcc)
  have htail : ExpNeg.blockAbs y K d ≤ ExpNeg.termAbs y K + ExpNeg.termAbs y K :=
    ExpNeg.blockAbs_le y half (ExpNeg.termAbs y K + ExpNeg.termAbs y K) hy K
      HalfPow.half_nonneg hH (ExpNeg.x_invSucc_le_half y hy K hcut) hrec d
  exact Q'.le_trans' _ _ _ (ExpPos.partialSumAbs_le_add_blockAbs y K d)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left (ExpNeg.partialSumAbs y K) (ExpNeg.blockAbs y K d)
        (ExpNeg.termAbs y K + ExpNeg.termAbs y K) htail)
      hcert)

/-- A concrete rational upper bound on `e^y` (`y ≥ 0`): take the cutoff
`K = halfRatioCutoff y` and `E := partialSumAbs y K + 2·termAbs y K`.  It is
`≥ partialSumAbs y K ≥ 1 > 0`. -/
def expPosBound (y : Q') : Q' :=
  ExpNeg.partialSumAbs y (halfRatioCutoff y)
    + (ExpNeg.termAbs y (halfRatioCutoff y)
        + ExpNeg.termAbs y (halfRatioCutoff y))

/-- `e^y ≤ expPosBound y`. -/
theorem expPos_le_expPosBound (y : Q') (hy : (0 : Q') ≤ y) :
    CReal.leRat (ExpPos.expPos y hy) (expPosBound y) :=
  expPos_leRat y hy (expPosBound y) (halfRatioCutoff y) (Nat.le_refl _)
    (Q'.le_refl' _)

/-- `0 < expPosBound y`: it dominates `partialSumAbs y K ≥ partialSumAbs y 1 = 1`. -/
theorem expPosBound_pos (y : Q') (hy : (0 : Q') ≤ y) : (0 : Q') < expPosBound y := by
  -- partialSumAbs y K ≥ 1 (K ≥ 1? no — K = halfRatioCutoff, may be 0).  Use that
  -- expPosBound = P_K + 2·t_K with P_K ≥ 0, t_K ≥ 0, and t_K = y^K/K! includes
  -- t_0 = 1 contribution when K = 0 (P_0 = 0, t_0 = 1, so bound = 0 + (1+1) = 2).
  -- General: P_K + t_K ≥ partialSumAbs y (K+1) ≥ partialSumAbs y 1 = 1 > 0, and the
  -- extra t_K ≥ 0 keeps it positive.  We show 1 ≤ expPosBound y.
  have h1 : (1 : Q') ≤ expPosBound y := by
    -- P_K + t_K = partialSumAbs y (K+1) ≥ partialSumAbs y 1 = 1.
    have hPt : ExpNeg.partialSumAbs y (halfRatioCutoff y)
        + ExpNeg.termAbs y (halfRatioCutoff y)
        = ExpNeg.partialSumAbs y (halfRatioCutoff y + 1) := rfl
    have hmono : ExpNeg.partialSumAbs y 1
        ≤ ExpNeg.partialSumAbs y (1 + halfRatioCutoff y) :=
      ExpPos.partialSumAbs_mono y hy 1 (halfRatioCutoff y)
    have heq1 : ExpNeg.partialSumAbs y 1 = 1 := by
      show ExpNeg.partialSumAbs y 0 + ExpNeg.termAbs y 0 = 1
      show (0 : Q') + 1 = 1
      exact Q'.zero_add' 1
    have hidx : (1 + halfRatioCutoff y) = (halfRatioCutoff y + 1) :=
      Nat.add_comm 1 _
    rw [hidx, heq1] at hmono
    -- 1 ≤ partialSumAbs y (K+1) = P_K + t_K ≤ P_K + (t_K + t_K) = expPosBound y.
    have htnn : (0 : Q') ≤ ExpNeg.termAbs y (halfRatioCutoff y) :=
      ExpNeg.termAbs_nonneg y hy _
    have hstep : ExpNeg.partialSumAbs y (halfRatioCutoff y + 1) ≤ expPosBound y := by
      rw [← hPt]
      show ExpNeg.partialSumAbs y (halfRatioCutoff y)
            + ExpNeg.termAbs y (halfRatioCutoff y)
          ≤ ExpNeg.partialSumAbs y (halfRatioCutoff y)
            + (ExpNeg.termAbs y (halfRatioCutoff y)
                + ExpNeg.termAbs y (halfRatioCutoff y))
      exact Q'.add_le_add_left _ _ _
        (Q'.add_le_self_of_nonneg _ _ htnn)
    exact Q'.le_trans' _ _ _ hmono hstep
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) h1

/-- The positive floor denominator `E + 1` for `e^{−y}`, with `E = expPosBound y`
the rational upper bound on `e^y`.  Using `E + 1` (rather than `E`) absorbs the
`leRat` slack into a fixed bound. -/
def expPosBound1 (y : Q') : Q' := expPosBound y + 1

theorem expPosBound1_pos (y : Q') (hy : (0 : Q') ≤ y) : (0 : Q') < expPosBound1 y := by
  have h := expPosBound_pos y hy
  show (0 : Q') < expPosBound y + 1
  exact Q'.pos_of_lt_of_le h
    (Q'.add_le_self_of_nonneg (expPosBound y) 1 (by decide))

/-- **Reciprocal positive lower bound on `e^{−y}`.**  For `y ≥ 0`,

    e^{−y}  ≥ᵣ  1/(E+1)  >  0 ,    E = expPosBound y .

From `e^y·e^{−y} ≥ 1` (`expProd_geRat`), `e^y ≤ E` (`expPos_le_expPosBound`), and
`partialSumAbs y n ≥ 1` for `n ≥ 1`: at each large `n`, `P_n·Q_n ≥ 1 − ε` forces
`Q_n ≥ 0` (else the product is `≤ 0`), and then `(E+1)·Q_n ≥ P_n·Q_n ≥ 1 − ε`,
i.e. `Q_n ≥ (1−ε)/(E+1)`. -/
theorem expNeg_geRat_recipPos (y : Q') (hy : (0 : Q') ≤ y) :
    ExpPos.geRat (ExpNeg.expNeg y hy)
      (Q'.recipPos (expPosBound1 y) (expPosBound1_pos y hy)) := by
  intro δ hδ
  have hE1pos : (0 : Q') < expPosBound1 y := expPosBound1_pos y hy
  have hcpos : (0 : Q') < Q'.recipPos (expPosBound1 y) hE1pos :=
    Q'.recipPos_pos (expPosBound1 y) hE1pos
  have hcnn : (0 : Q') ≤ Q'.recipPos (expPosBound1 y) hE1pos := Q'.le_of_lt hcpos
  -- choose ε ≤ 1/2 with c·ε ≤ δ.
  obtain ⟨ε0, hε0pos, hε0⟩ := CReal.exists_mul_le hcnn hδ
  -- ε := min'(ε0, 1/2): ε ≤ 1/2, ε ≤ ε0, 0 < ε.
  have hεle : Q'.min' ε0 half ≤ half := Q'.min_le_right' ε0 half
  have hεleε0 : Q'.min' ε0 half ≤ ε0 := Q'.min_le_left' ε0 half
  have hεpos : (0 : Q') < Q'.min' ε0 half := by
    unfold Q'.min'
    by_cases h : ε0 ≤ half
    · rw [if_pos h]; exact hε0pos
    · rw [if_neg h]; decide
  have hεnn : (0 : Q') ≤ Q'.min' ε0 half := Q'.le_of_lt hεpos
  -- bounds from the product law and the upper bound, at tolerance ε.
  obtain ⟨N1, hN1⟩ := expProd_geRat y hy (Q'.min' ε0 half) hεpos
  obtain ⟨N2, hN2⟩ := expPos_le_expPosBound y hy (Q'.min' ε0 half) hεpos
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have ln1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have ln2 : N2 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have ln3 : 1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- abbreviations.
  -- P_n = partialSumAbs y n, Q_n = partialSum y n.
  have hprodlb : (1 : Q') ≤ ExpNeg.partialSumAbs y n * ExpNeg.partialSum y n
      + Q'.min' ε0 half := hN1 n ln1
  have hPub : ExpNeg.partialSumAbs y n ≤ expPosBound y + Q'.min' ε0 half := hN2 n ln2
  -- P_n ≥ 1 (n ≥ 1).
  have hPlb : (1 : Q') ≤ ExpNeg.partialSumAbs y n := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ln3
    have hmono : ExpNeg.partialSumAbs y 1 ≤ ExpNeg.partialSumAbs y (1 + d) :=
      ExpPos.partialSumAbs_mono y hy 1 d
    have heq1 : ExpNeg.partialSumAbs y 1 = 1 := by
      show ExpNeg.partialSumAbs y 0 + ExpNeg.termAbs y 0 = 1
      show (0 : Q') + 1 = 1; exact Q'.zero_add' 1
    rw [heq1] at hmono; exact hmono
  have hPnn : (0 : Q') ≤ ExpNeg.partialSumAbs y n :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hPlb
  -- P_n ≤ E + 1 = expPosBound1 y (since ε ≤ 1/2 ≤ 1).
  have hPub1 : ExpNeg.partialSumAbs y n ≤ expPosBound1 y := by
    refine Q'.le_trans' _ _ _ hPub ?_
    show expPosBound y + Q'.min' ε0 half ≤ expPosBound y + 1
    exact Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hεle (by decide : half ≤ 1))
  -- Q_n ≥ 0 : otherwise P_n·Q_n ≤ 0 ⇒ 1 − ε ≤ 0, impossible for ε ≤ 1/2.
  have hQnn : (0 : Q') ≤ ExpNeg.partialSum y n := by
    by_cases hQ : (0 : Q') ≤ ExpNeg.partialSum y n
    · exact hQ
    · exfalso
      have hQle : ExpNeg.partialSum y n ≤ 0 := by
        show (ExpNeg.partialSum y n).num * ((0 : Q').den : Int)
            ≤ (0 : Q').num * ((ExpNeg.partialSum y n).den : Int)
        have h' : ¬ ((0 : Q').num * ((ExpNeg.partialSum y n).den : Int)
            ≤ (ExpNeg.partialSum y n).num * ((0 : Q').den : Int)) := hQ
        exact Int.le_of_lt (Int.not_le.mp h')
      -- P_n·Q_n ≤ P_n·0 ≃ 0.
      have hprodle0 : ExpNeg.partialSumAbs y n * ExpNeg.partialSum y n ≤ 0 := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left (ExpNeg.partialSum y n) 0
            (ExpNeg.partialSumAbs y n) hQle hPnn) ?_
        exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv (ExpNeg.partialSumAbs y n) 0)
          (Q'.zero_mul_eqv (ExpNeg.partialSumAbs y n)))
      -- then 1 ≤ 0 + ε = ε ≤ 1/2, contradiction.
      have h1ε : (1 : Q') ≤ Q'.min' ε0 half := by
        refine Q'.le_trans' _ _ _ hprodlb ?_
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hprodle0) ?_
        exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _))
      have h12 : (1 : Q') ≤ half := Q'.le_trans' _ _ _ h1ε hεle
      exact absurd h12 (by decide)
  -- (E+1)·Q_n ≥ P_n·Q_n ≥ 1 − ε.
  have hEQ : ExpNeg.partialSumAbs y n * ExpNeg.partialSum y n
      ≤ expPosBound1 y * ExpNeg.partialSum y n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hPub1 hQnn
  have hbig : (1 : Q') ≤ expPosBound1 y * ExpNeg.partialSum y n + Q'.min' ε0 half :=
    Q'.le_trans' _ _ _ hprodlb (Q'.add_le_add_right _ _ _ hEQ)
  -- multiply by c = 1/(E+1) ≥ 0 and collapse c·(E+1) ≃ 1.
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.recipPos (expPosBound1 y) hE1pos) hbig hcnn
  -- hmul : c·1 ≤ c·((E+1)·Q_n + ε)
  -- LHS ≃ c ; RHS ≃ c·(E+1)·Q_n + c·ε ≃ Q_n + c·ε.
  have hL : (Q'.recipPos (expPosBound1 y) hE1pos * 1).eqv
      (Q'.recipPos (expPosBound1 y) hE1pos) := Q'.mul_one_eqv _
  have hcE1 : (Q'.recipPos (expPosBound1 y) hE1pos * expPosBound1 y).eqv 1 := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
    exact Q'.mul_recipPos_eqv (expPosBound1 y) hE1pos
  -- expand RHS.
  have hR : (Q'.recipPos (expPosBound1 y) hE1pos
        * (expPosBound1 y * ExpNeg.partialSum y n + Q'.min' ε0 half)).eqv
      (ExpNeg.partialSum y n
        + Q'.recipPos (expPosBound1 y) hE1pos * Q'.min' ε0 half) := by
    -- c·((E+1)·Q + ε) ≃ c·((E+1)·Q) + c·ε ≃ (c·(E+1))·Q + c·ε ≃ 1·Q + c·ε ≃ Q + c·ε.
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.recipPos (expPosBound1 y) hE1pos)
        (expPosBound1 y * ExpNeg.partialSum y n) (Q'.min' ε0 half)) ?_
    refine Q'.add_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.recipPos (expPosBound1 y) hE1pos)
        (expPosBound1 y) (ExpNeg.partialSum y n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 1 (ExpNeg.partialSum y n) hcE1) ?_
    exact Q'.one_mul_eqv (ExpNeg.partialSum y n)
  -- assemble: c ≤ Q_n + c·ε ≤ Q_n + δ.
  have hstep : Q'.recipPos (expPosBound1 y) hE1pos
      ≤ ExpNeg.partialSum y n
        + Q'.recipPos (expPosBound1 y) hE1pos * Q'.min' ε0 half :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hR))
  refine Q'.le_trans' _ _ _ hstep ?_
  refine Q'.add_le_add_left _ _ _ ?_
  -- c·ε ≤ c·ε0 ≤ δ.
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (Q'.min' ε0 half) ε0
      (Q'.recipPos (expPosBound1 y) hE1pos) hεleε0 hcnn) hε0

/-- **Strict positivity of `e^{−(R+R)}`** (the floor constant), packaged as a
positive rational lower bound `geRat`.  `c := 1/(expPosBound1 (R+R)) > 0`, and
`geRat (e^{−(R+R)}) c` holds by `expNeg_geRat_recipPos`. -/
def expNegTwoR_isPositive (R : Q') (hR : (0 : Q') ≤ R) :
    Σ' c : Q', (0 : Q') < c
      ∧ ExpPos.geRat (ExpNeg.expNeg (R + R) (Q'.zero_le_add R R hR hR)) c :=
  ⟨Q'.recipPos (expPosBound1 (R + R)) (expPosBound1_pos (R + R) (Q'.zero_le_add R R hR hR)),
   Q'.recipPos_pos _ _,
   expNeg_geRat_recipPos (R + R) (Q'.zero_le_add R R hR hR)⟩

/-! ## 5. The persistence bridge

With `δ_k := 1 − ρ_k` (the per-block *loss*), `prodOneSub δ` is exactly the
prefix product `RGGapPersistence.prodPrefix ρ` (`ProductFloor.prodOneSub_loss_eqv`),
so the summability floor becomes the product-floor datum the per-block persistence
form requires — now with a constant positive for ALL `R ≥ 0`, the all-`R`
replacement for the Weierstrass bridge `sum_block_loss_to_productFloor`. -/

/-- **The exponential persistence bridge.**  From per-block multipliers
`0 ≤ ρ_k ≤ 1` whose losses `δ_k = 1 − ρ_k` satisfy `1 − ρ_k ≤ 1/2` and have all
partial sums `≤ R`, CONSTRUCT the strictly-positive constructive-real constant
`c = e^{−(R+R)}` (a sound positive `Q'` lower bound `ε` is supplied as data) with
`c ≤ ∏_{k<n} ρ_k` (the sound rational bound `leRat`) for every prefix length `n`
— in the exact `RGGapPersistence.prodPrefix ρ` shape.

This is the all-`R` floor: valid for any finite total defect `R ≥ 0`, unlike the
Weierstrass bridge which needs `R < 1`. -/
def sum_loss_to_productFloor_exp (ρ : Nat → Q')
    (hρ0 : ∀ k, (0 : Q') ≤ ρ k) (hρ1 : ∀ k, ρ k ≤ 1)
    (hρhalf : ∀ k, (1 - ρ k) ≤ half)
    (R : Q') (hR : ∀ n, lossSum (fun k => 1 - ρ k) n ≤ R) :
    Σ' (c : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat c ε
      ∧ ∀ n, CReal.leRat c (RGGapPersistence.prodPrefix ρ n) := by
  -- the per-block losses δ_k = 1 − ρ_k satisfy 0 ≤ δ_k ≤ 1/2.
  have hδ : ∀ k, (0 : Q') ≤ (1 - ρ k) ∧ (1 - ρ k) ≤ half := by
    intro k
    refine ⟨?_, hρhalf k⟩
    show (0 : Q') ≤ 1 + (-ρ k)
    have hstep := Q'.add_le_add_right (ρ k) 1 (-ρ k) (hρ1 k)
    refine Q'.le_trans' _ _ _ ?_ hstep
    exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (ρ k))
  have hRnn : (0 : Q') ≤ R :=
    Q'.le_trans' 0 (lossSum (fun k => 1 - ρ k) 0) R
      (lossSum_nonneg (fun k => 1 - ρ k) (fun k => (hδ k).1) 0) (hR 0)
  -- the exponential summability floor against prodOneSub, then transport to prodPrefix.
  refine ⟨ExpNeg.expNeg (R + R) (Q'.zero_le_add R R hRnn hRnn),
    Q'.recipPos (expPosBound1 (R + R)) (expPosBound1_pos (R + R) (Q'.zero_le_add R R hRnn hRnn)),
    Q'.recipPos_pos _ _,
    expNeg_geRat_recipPos (R + R) (Q'.zero_le_add R R hRnn hRnn),
    fun n => ?_⟩
  -- floor on prodOneSub (fun k => 1 − ρ k); the proof's nonneg term matches.
  have hfloor := prod_floor_exp_of_sum_le (fun k => 1 - ρ k) hδ R hR n
  -- prodOneSub (1−ρ) n ≃ prodPrefix ρ n, so the rational bound transfers.
  exact CReal.leRat_mono hfloor
    (Q'.le_of_eqv (ProductFloor.prodOneSub_loss_eqv ρ n))

end YMGap.Continuum.ExpProductFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ExpProductFloor.crux_int
#print axioms YMGap.Continuum.ExpProductFloor.oneOver1p_sq_le_oneSub
#print axioms YMGap.Continuum.ExpProductFloor.expNegTwoX_leRat_oneSub
#print axioms YMGap.Continuum.ExpProductFloor.expNeg_zero_leRat_one
#print axioms YMGap.Continuum.ExpProductFloor.prodOneSub_nonneg
#print axioms YMGap.Continuum.ExpProductFloor.prod_floor_exp_finite
#print axioms YMGap.Continuum.ExpProductFloor.expNeg_leRat_one
#print axioms YMGap.Continuum.ExpProductFloor.prod_floor_exp_of_sum_le
#print axioms YMGap.Continuum.ExpProductFloor.expPos_leRat
#print axioms YMGap.Continuum.ExpProductFloor.expPos_le_expPosBound
#print axioms YMGap.Continuum.ExpProductFloor.expPosBound_pos
#print axioms YMGap.Continuum.ExpProductFloor.expPosBound1_pos
#print axioms YMGap.Continuum.ExpProductFloor.expNeg_geRat_recipPos
#print axioms YMGap.Continuum.ExpProductFloor.expNegTwoR_isPositive
#print axioms YMGap.Continuum.ExpProductFloor.sum_loss_to_productFloor_exp
