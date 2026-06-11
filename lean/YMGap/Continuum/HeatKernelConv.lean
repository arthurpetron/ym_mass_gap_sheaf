/-
Heat-kernel pointwise positivity, Part 3 (gap G1, the `S`-factor) — building
the manifestly-nonnegative sum

    S(x) = Σ_{n≥1} 2·a^{2n-1} / (1 + 2·a^{2n-1}·x + a^{4n-2})

as a GENUINE convergent `CReal` with an EXPLICIT Cauchy modulus, under the
regime hypothesis `a·a ≤ 1/2`.

# What this module closes

`Continuum/HeatKernelPos2.lean` provides the product-of-nonnegatives engine
(`mul_geRat_zero`) and `Kt_geRat_zero_of_product`, the closer GIVEN that the two
factors `ϑ₃/2a` and `S` exist as nonneg-approx `CReal`s.  Its named gap (G1) is
exactly: *build those `CReal`s with an explicit modulus.*

This module closes the `S` half of G1.  `Q'` has no division, but `Q'` is the
raw `num/den` pair `⟨num : Int, denPred : Nat⟩` (unnormalized), so a genuine
nonnegative quotient of a nonnegative numerator by a positive-numerator
denominator IS constructible directly on the representation:

    divPos p D := ⟨p.num · D.den, (p.den · D.num.toNat) − 1⟩      (needs 0 < D.num)

with value `(p.num·D.den)/(p.den·D.num) = (p/D)`.  The `S`-summand at depth `n`
is then the ACTUAL `Q'` value

    sTerm a x n := divPos (two a^{2n+1}) (factor a^{2n+1} x),

a nonnegative rational (numerator `2a^{2n+1} ≥ 0`, denominator
`factor > 0` by `HKPos.factor_pos`).  The partial sums `Spart a x N = Σ_{n<N}
sTerm a x n` are genuine `Q'` values, and we feed them to the KP engine
`Continuum.crealOfGeoIncrement` (`Continuum/KPLimit.lean`).

# The modulus (the subtlety named in the HeatKernelPos2 docstring)

`crealOfGeoIncrement` wants a single-step geometric increment bound
`Spart (l+1) ≤ Spart l + C·(1/2)^l`.  The increment is exactly `sTerm a x l`,
and we prove

    sTerm a x l ≤ geoIncr C l = C·(1/2)^l,   C := divPos (two a) (factorLB a) = 2a/(1−a)²,

valid under `ha2 : a·a ≤ 1/2`.  The chain is, with `c = a^{2l+1}`:

    sTerm = 2c / factor c x
          ≤ 2c / (1−a)²            (factor ≥ (1−c)² ≥ (1−a)², division antitone in denom)
    and    2c = 2a·(a²)^l ≤ 2a·(1/2)^l   (since a² ≤ 1/2)
    so     2c / (1−a)² ≤ 2a·(1/2)^l/(1−a)² = C·(1/2)^l.

Mechanically we reduce `sTerm ≤ C·(1/2)^l` to `two c ≤ (C·(1/2)^l)·factor c x`
via `divPos_le_of_le`, then bound the RHS below by `(C·(1/2)^l)·factorLB a` and
use `C·factorLB a ≃ two a` (`divPos_mul_eqv`) plus `two c ≤ two a·(1/2)^l`.

# What is BUILT here (the deliverable)

  * `sConvCReal a x (ha0 ha1 hx ha2)` — the sum `S(x)` as a `CReal` under
    `0 < a`, `a < 1`, `−1 ≤ x`, `a·a ≤ 1/2`, with `approx N = Spart a x N`
    (the genuine finite-volume partial sum) and the explicit `HalfPow` modulus
    inherited from `crealOfGeoIncrement`.
  * `sConvCReal_approx_nonneg` — every approximation is `≥ 0`.
  * `sConvCReal_geRat_zero` — its limit is `≥ 0` (`ExpPos.geRat … 0`).
  * `R_geRat_zero_of_theta` — the end-to-end consumer: GIVEN any `CReal` `Θ`
    for `ϑ₃/2a` with nonnegative approximations, the product `Θ · S` has limit
    `≥ 0`.  This is `HKPos2.mul_geRat_zero` with the `S`-factor now genuinely
    supplied (no longer a hypothesis).

# The precise remaining gap (honest, per AGENTS.md Rule 6)

  (G1-ϑ₃) The OTHER factor `ϑ₃ = ∏_{n≥1}(1−a^{2n})(1+2a^{2n-1}x+a^{4n-2})` is a
       partial PRODUCT, not a sum; building it as a `CReal` is left open and is
       NOT closed here.  `HKPos2.thetaTruncCReal` / `thetaTruncCReal_geRat_zero`
       give every finite truncation as a positive `CReal`; the convergence of
       the infinite product to a `CReal` with modulus is the residual G1 piece.
       `R_geRat_zero_of_theta` consumes whatever `CReal` `Θ` realizes `ϑ₃/2a`.

  (a² ≤ 1/2 regime) The `S` `CReal` is built under `ha2 : a·a ≤ 1/2`
       (i.e. `a ≤ 1/√2 ≈ 0.707`).  For general `a ∈ (0,1)` the geometric ratio
       `a²` exceeds `1/2`, and the engine needs an `a`-dependent cutoff `n₀(a)`
       past which the per-term ratio dips below `1/2`; that extension is
       mechanical but lengthy and not done here.  The hypothesis is stated
       precisely on every theorem.

  (G2) The IDENTITY `K_t(x) = (ϑ₃/2a)·S(x)` (differentiated Jacobi triple
       product) remains the separate analytic gap named in `HeatKernelPos2`.

Everything below is fully proved and axiom-gated (`[propext]` or
`[propext, Quot.sound]` where `Nat`/`Int`/`omega` enter via reused helpers).
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.HeatKernelPos2
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos
import YMGap.Constructive.RationalTail
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.HKConv

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKPos
open YMGap.Continuum.HKPos2
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow

/-! ## 1. A genuine nonnegative division on `Q'`

We follow `Rationals.lean` in deliberately avoiding `ring`/`linarith`, proving
the few integer multiplicative rearrangements we need from
`Int.mul_assoc`/`Int.mul_comm` alone (keeping the axiom gate at `[propext]`).

`Q'` is the raw pair `⟨num : Int, denPred : Nat⟩`, `den = denPred + 1`.  For a
denominator `D` with `0 < D.num`, the quotient `p/D` is the `Q'`

    divPos p D = ⟨p.num · D.den,  p.den · D.num.toNat − 1⟩,

whose value is `(p.num·D.den)/(p.den·D.num)`.  We expose its numerator and
denominator and prove the three facts the modulus needs:
nonnegativity, the "cross-multiplied" `≤`-characterisation, and the
cancellation `divPos p D · D ≃ p`. -/

/-- Genuine nonnegative quotient on `Q'`: `p / D` for `0 < D.num`.
Value `(p.num·D.den)/(p.den·D.num)`. -/
def divPos (p D : Q') : Q' :=
  ⟨p.num * (D.den : Int), p.den * D.num.toNat - 1⟩

/-- The numerator of `divPos p D` is `p.num · D.den`. -/
@[simp] theorem divPos_num (p D : Q') :
    (divPos p D).num = p.num * (D.den : Int) := rfl

/-- For `0 < D.num`, the denominator of `divPos p D` casts to
`p.den · D.num` (the `toNat`/`−1` bookkeeping is exact because `p.den ≥ 1` and
`D.num.toNat ≥ 1`). -/
theorem divPos_den_cast {p D : Q'} (hD : 0 < D.num) :
    ((divPos p D).den : Int) = (p.den : Int) * D.num := by
  have hpos : 0 < D.num.toNat := by omega
  have hprodpos : 0 < p.den * D.num.toNat := Nat.mul_pos (Q'.den_pos p) hpos
  show (((p.den * D.num.toNat - 1) + 1 : Nat) : Int) = (p.den : Int) * D.num
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hprodpos))]
  rw [Int.natCast_mul]
  congr 1
  exact Int.toNat_of_nonneg (Int.le_of_lt hD)

/-- `0 ≤ divPos p D` when `0 ≤ p` (denominator positivity `0 < D.num` is not
needed for nonnegativity — `D.den > 0` structurally — but kept implicit by the
caller's data flow). -/
theorem divPos_nonneg {p D : Q'} (hp : (0 : Q') ≤ p) :
    (0 : Q') ≤ divPos p D := by
  rw [Q'.zero_le_iff_num_nonneg] at hp ⊢
  show (0 : Int) ≤ p.num * (D.den : Int)
  exact Int.mul_nonneg hp (Int.natCast_nonneg _)

/-- `0 < divPos p D` when `0 < p.num`.  `(divPos p D).num = p.num·D.den > 0`. -/
theorem divPos_pos {p D : Q'} (hp : 0 < p.num) : (0 : Q') < divPos p D := by
  apply CReal.pos_of_num_pos
  show 0 < p.num * (D.den : Int)
  exact Int.mul_pos hp (by exact_mod_cast Q'.den_pos D)

/-- `0 < (divPos p D).num` from `0 < p.num` (the numerator-positivity datum,
used to feed `divPos`/`divPos_mul_eqv` recursively). -/
theorem divPos_num_pos {p D : Q'} (hp : 0 < p.num) : 0 < (divPos p D).num := by
  show 0 < p.num * (D.den : Int)
  exact Int.mul_pos hp (by exact_mod_cast Q'.den_pos D)

/-- **The cross-multiplied `≤`-characterisation.**  For `0 < D.num`,
`divPos p D ≤ b` follows from `p ≤ b * D` (i.e. `p/D ≤ b ⟸ p ≤ b·D`). -/
theorem divPos_le_of_le {p D b : Q'} (hD : 0 < D.num)
    (h : p ≤ b * D) : divPos p D ≤ b := by
  show (divPos p D).num * (b.den : Int) ≤ b.num * ((divPos p D).den : Int)
  rw [divPos_num, divPos_den_cast hD]
  -- Goal: (p.num·D.den)·b.den ≤ b.num·(p.den·D.num)
  have hb_num : (b * D).num = b.num * D.num := rfl
  have hb_den : ((b * D).den : Int) = (b.den : Int) * (D.den : Int) := by
    show (((b.den * D.den - 1) + 1 : Nat) : Int) = (b.den : Int) * (D.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos b) (Q'.den_pos D))))]
    exact Int.natCast_mul b.den D.den
  have hh : p.num * ((b.den : Int) * (D.den : Int)) ≤ (b.num * D.num) * (p.den : Int) := by
    have h0 : p.num * ((b * D).den : Int) ≤ (b * D).num * (p.den : Int) := h
    rw [hb_num, hb_den] at h0
    exact h0
  -- (p.num·D.den)·b.den = p.num·(b.den·D.den)
  have eL : (p.num * (D.den : Int)) * (b.den : Int)
          = p.num * ((b.den : Int) * (D.den : Int)) := by
    rw [Int.mul_assoc, Int.mul_comm (D.den : Int) (b.den : Int)]
  -- b.num·(p.den·D.num) = (b.num·D.num)·p.den
  have eR : b.num * ((p.den : Int) * D.num)
          = (b.num * D.num) * (p.den : Int) := by
    rw [Int.mul_comm (p.den : Int) D.num, ← Int.mul_assoc]
  rw [eL, eR]
  exact hh

/-- **Cancellation:** `divPos p D · D ≃ p` for `0 < D.num`. -/
theorem divPos_mul_eqv {p D : Q'} (hD : 0 < D.num) :
    (divPos p D * D).eqv p := by
  show (divPos p D * D).num * (p.den : Int)
     = p.num * ((divPos p D * D).den : Int)
  have hnum : (divPos p D * D).num = (p.num * (D.den : Int)) * D.num := rfl
  have hden : ((divPos p D * D).den : Int)
            = ((divPos p D).den : Int) * (D.den : Int) := by
    show ((((divPos p D).den * D.den - 1) + 1 : Nat) : Int)
       = ((divPos p D).den : Int) * (D.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos (divPos p D)) (Q'.den_pos D))))]
    exact Int.natCast_mul (divPos p D).den D.den
  rw [hnum, hden, divPos_den_cast hD]
  -- Goal: ((p.num·D.den)·D.num)·p.den = p.num·((p.den·D.num)·D.den)
  -- Both sides = p.num · (D.den · D.num · p.den) up to reordering the inner
  -- product; pull p.num out and reorder the remaining three factors.
  rw [Int.mul_assoc (p.num * (D.den : Int)) D.num (p.den : Int),
      Int.mul_assoc p.num (D.den : Int) (D.num * (p.den : Int))]
  congr 1
  -- D.den·(D.num·p.den) = (p.den·D.num)·D.den
  rw [Int.mul_comm (D.den : Int) (D.num * (p.den : Int)),
      Int.mul_comm D.num (p.den : Int)]

/-! ## 2. The `S`-summand and partial sums as genuine `Q'` values -/

/-- The `n`-th `S`-summand `2·a^{2n+1} / (1 + 2a^{2n+1}x + a^{2(2n+1)})` as an
ACTUAL `Q'` value (numerator `two (geoAmp a n)`, denominator
`factor (geoAmp a n) x`). -/
def sTerm (a x : Q') (n : Nat) : Q' :=
  divPos (two (HKPos.geoAmp a n)) (HKPos.factor (HKPos.geoAmp a n) x)

/-- `0 < (factor c x).num` from `factor_pos` (denominator positivity datum). -/
theorem factor_num_pos {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (n : Nat) :
    0 < (HKPos.factor (HKPos.geoAmp a n) x).num := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a n :=
    Q'.le_of_lt ((pow_succ_pos_lt_one ha0 ha1 (2 * n)).1)
  have hc1 : HKPos.geoAmp a n < (1 : Q') := (pow_succ_pos_lt_one ha0 ha1 (2 * n)).2
  exact CReal.num_pos_of_pos (HKPos.factor_pos hc0 hc1 hx)

/-- Each `S`-summand is `≥ 0`. -/
theorem sTerm_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (_hx : (-1 : Q') ≤ x) (n : Nat) :
    (0 : Q') ≤ sTerm a x n := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a n :=
    Q'.le_of_lt ((pow_succ_pos_lt_one ha0 ha1 (2 * n)).1)
  exact divPos_nonneg (HKPos.two_nonneg hc0)

/-- The `S` partial sums `Spart a x N = Σ_{n<N} sTerm a x n` (genuine `Q'`). -/
def Spart (a x : Q') (N : Nat) : Q' := finSum (sTerm a x) N

@[simp] theorem Spart_succ (a x : Q') (N : Nat) :
    Spart a x (N + 1) = Spart a x N + sTerm a x N := rfl

/-- Every partial sum is `≥ 0`. -/
theorem Spart_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) :
    ∀ N, (0 : Q') ≤ Spart a x N
  | 0 => Q'.le_refl' 0
  | N + 1 => by
      rw [Spart_succ]
      exact Q'.zero_le_add _ _ (Spart_nonneg ha0 ha1 hx N) (sTerm_nonneg ha0 ha1 hx N)

/-! ## 3. The per-term geometric bound `sTerm a x l ≤ C·(1/2)^l`

The increment of the partial sum at step `l` is exactly `sTerm a x l`.  We bound
it by `geoIncr C l = C·(1/2)^l` for a constant `C` satisfying
`two a ≤ C·factorLB a` and `0 ≤ C` (the canonical witness is
`C = divPos (two a) (factorLB a) = 2a/(1−a)²`, built in §4).  The bound holds in
the regime `a·a ≤ 1/2`. -/

/-- Two-sided `Q'` product monotonicity: `0 ≤ p → 0 ≤ s → p ≤ q → s ≤ t →
p·s ≤ q·t`.  Built from the two one-sided lemmas. -/
theorem mul_le_mul' {p q s t : Q'}
    (hp : (0 : Q') ≤ p) (ht : (0 : Q') ≤ t) (hpq : p ≤ q) (hst : s ≤ t) :
    p * s ≤ q * t :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left s t p hst hp)
    (Q'.mul_le_mul_of_nonneg_right p q t hpq ht)

/-- Base-monotonicity of `Q'.pow`: `0 ≤ p → p ≤ q → p^l ≤ q^l` (with `0 ≤ q`
following from `p ≤ q`). -/
theorem pow_le_pow_base {p q : Q'} (hp : (0 : Q') ≤ p) (hpq : p ≤ q) :
    ∀ l : Nat, p ^ l ≤ q ^ l
  | 0 => by
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | l + 1 => by
      have hq : (0 : Q') ≤ q := Q'.le_trans' _ _ _ hp hpq
      show p * p ^ l ≤ q * q ^ l
      exact mul_le_mul' hp (Q'.pow_nonneg q hq l) hpq (pow_le_pow_base hp hpq l)

/-- `factorLB` is antitone in the amplitude on `[0,1]`: `0 ≤ c → c ≤ a → a ≤ 1 →
factorLB a ≤ factorLB c` (larger amplitude ⇒ smaller `(1−·)²`). -/
theorem factorLB_antitone {c a : Q'}
    (_hc0 : (0 : Q') ≤ c) (hca : c ≤ a) (ha1 : a ≤ (1 : Q')) :
    HKPos.factorLB a ≤ HKPos.factorLB c := by
  -- factorLB t = (1 + -t)*(1 + -t).  We have 0 ≤ 1 + -a ≤ 1 + -c.
  have h1a_nn : (0 : Q') ≤ 1 + (-a) := by
    -- 0 ≤ 1 - a since a ≤ 1
    have := Q'.add_le_add_right a 1 (-a) ha1   -- a + -a ≤ 1 + -a
    have hz : ((a + (-a)) : Q').eqv 0 := Q'.add_neg_self_eqv a
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz) this
  have hmono : 1 + (-a) ≤ 1 + (-c) := by
    -- from c ≤ a : -a ≤ -c, then add 1 on left
    have hneg : (-a) ≤ (-c) := by
      have := Q'.neg_le_neg hca
      exact this
    exact Q'.add_le_add_left 1 (-a) (-c) hneg
  -- (1+-a)*(1+-a) ≤ (1+-c)*(1+-c)
  show HKPos.factorLB a ≤ HKPos.factorLB c
  show (1 + (-a)) * (1 + (-a)) ≤ (1 + (-c)) * (1 + (-c))
  exact mul_le_mul' h1a_nn
    (Q'.le_trans' _ _ _ h1a_nn hmono) hmono hmono

/-- `two (geoAmp a l) ≃ two a · (a·a)^l` — the per-term numerator factors as
`2·a^{2l+1} = 2a·(a²)^l`. -/
theorem two_geoAmp_eqv (a : Q') (l : Nat) :
    (HKPos.two (HKPos.geoAmp a l)).eqv (HKPos.two a * (a * a) ^ l) := by
  -- First: geoAmp a l = a^(2l+1) ≃ a · (a·a)^l.
  have hgeo : (HKPos.geoAmp a l).eqv (a * (a * a) ^ l) := by
    show (a ^ (2 * l + 1)).eqv (a * (a * a) ^ l)
    induction l with
    | zero =>
        -- a^1 ≃ a · (a·a)^0 = a · 1
        show (a ^ 1).eqv (a * (a * a) ^ 0)
        -- a^1 = a*1 ; (a*a)^0 = 1
        refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_one_eqv a))
        show (a * a ^ 0).eqv a
        exact Q'.mul_one_eqv a
    | succ l ih =>
        -- a^(2(l+1)+1) = a^(2l+3) = a*a*(a^(2l+1)) ;  a·(a·a)^(l+1) = a·(a·a)·(a·a)^l
        show (a ^ (2 * (l + 1) + 1)).eqv (a * (a * a) ^ (l + 1))
        have he : 2 * (l + 1) + 1 = (2 * l + 1) + 2 := by omega
        rw [he]
        -- a^((2l+1)+2) = a*(a*(a^(2l+1)))
        show (a * (a * a ^ (2 * l + 1))).eqv (a * ((a * a) * (a * a) ^ l))
        refine Q'.mul_eqv_congr_left a _ _ ?_
        -- a*(a^(2l+1)) ≃ (a*a)*(a*a)^l, using ih : a^(2l+1) ≃ a*(a*a)^l
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ ih) ?_
        -- a*(a*(a*a)^l) ≃ (a*a)*(a*a)^l   (reassociate)
        exact Q'.eqv_symm (Q'.mul_assoc_eqv a a ((a * a) ^ l))
  -- two t = t + t, so two (geoAmp) ≃ (a*(a*a)^l) + (a*(a*a)^l)
  show ((HKPos.geoAmp a l) + (HKPos.geoAmp a l)).eqv ((a + a) * (a * a) ^ l)
  -- rewrite the right summand, then the left summand
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (HKPos.geoAmp a l) _ (a * (a * a) ^ l) hgeo) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ (a * (a * a) ^ l) (a * (a * a) ^ l) hgeo) ?_
  -- (a*(a*a)^l) + (a*(a*a)^l) ≃ (a+a)*(a*a)^l
  exact Q'.eqv_symm (Q'.add_mul_eqv a a ((a * a) ^ l))

/-- **The per-term geometric bound (parametrised by the constant `C`).**

For `0 < a`, `a < 1`, `−1 ≤ x`, `a·a ≤ 1/2`, and any `C ≥ 0` with
`two a ≤ C·factorLB a`, the `l`-th `S`-summand satisfies
`sTerm a x l ≤ geoIncr C l = C·(1/2)^l`. -/
theorem sTerm_le_geoIncr {a x C : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) (hC0 : (0 : Q') ≤ C)
    (hCb : HKPos.two a ≤ C * HKPos.factorLB a) (l : Nat) :
    sTerm a x l ≤ geoIncr C l := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a l :=
    Q'.le_of_lt ((pow_succ_pos_lt_one ha0 ha1 (2 * l)).1)
  have hca : HKPos.geoAmp a l ≤ a := by
    show a ^ (2 * l + 1) ≤ a
    exact HKPos.pow_succ_le_self (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) (2 * l)
  -- reduce divPos ≤ geoIncr to: two (geoAmp) ≤ geoIncr C l * factor (geoAmp) x
  refine divPos_le_of_le (factor_num_pos ha0 ha1 hx l) ?_
  -- Step A: geoIncr C l * factor (geoAmp) x ≥ geoIncr C l * factorLB a
  have hgeoIncr_nn : (0 : Q') ≤ geoIncr C l := geoIncr_nonneg C hC0 l
  have hfactorLB_le_factor : HKPos.factorLB (HKPos.geoAmp a l)
      ≤ HKPos.factor (HKPos.geoAmp a l) x :=
    HKPos.factorLB_le_factor hc0 hx
  have hfactorLB_a_le : HKPos.factorLB a ≤ HKPos.factorLB (HKPos.geoAmp a l) :=
    factorLB_antitone hc0 hca (Q'.le_of_lt ha1)
  have hLB_chain : HKPos.factorLB a ≤ HKPos.factor (HKPos.geoAmp a l) x :=
    Q'.le_trans' _ _ _ hfactorLB_a_le hfactorLB_le_factor
  have stepA : geoIncr C l * HKPos.factorLB a
      ≤ geoIncr C l * HKPos.factor (HKPos.geoAmp a l) x :=
    Q'.mul_le_mul_of_nonneg_left _ _ (geoIncr C l) hLB_chain hgeoIncr_nn
  -- Step B: geoIncr C l * factorLB a ≃ two a * half^l   (via C·factorLB a ≥ two a)
  -- Actually we use: two a ≤ C*factorLB a, so two a * half^l ≤ (C*factorLB a)*half^l
  --                = geoIncr C l * factorLB a.
  have hhalf_nn : (0 : Q') ≤ half ^ l := Q'.pow_nonneg half half_nonneg l
  have stepB : HKPos.two a * half ^ l
      ≤ geoIncr C l * HKPos.factorLB a := by
    -- two a * half^l ≤ (C*factorLB a) * half^l
    have h1 : HKPos.two a * half ^ l ≤ (C * HKPos.factorLB a) * half ^ l :=
      Q'.mul_le_mul_of_nonneg_right _ _ (half ^ l) hCb hhalf_nn
    -- (C*factorLB a)*half^l ≃ (C*half^l)*factorLB a = geoIncr C l * factorLB a
    have e : ((C * HKPos.factorLB a) * half ^ l).eqv
        (geoIncr C l * HKPos.factorLB a) := by
      show ((C * HKPos.factorLB a) * half ^ l).eqv ((C * half ^ l) * HKPos.factorLB a)
      -- (C*F)*h ≃ C*(F*h) ≃ C*(h*F) ≃ (C*h)*F
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv C (HKPos.factorLB a) (half ^ l)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left C _ _ (Q'.mul_comm_eqv (HKPos.factorLB a) (half ^ l))) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv C (half ^ l) (HKPos.factorLB a))
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e)
  -- Step C: two (geoAmp a l) ≤ two a * half^l
  have stepC : HKPos.two (HKPos.geoAmp a l) ≤ HKPos.two a * half ^ l := by
    -- two (geoAmp) ≃ two a * (a*a)^l ≤ two a * half^l
    have hpow : (a * a) ^ l ≤ half ^ l :=
      pow_le_pow_base (Q'.mul_nonneg a a (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)) ha2 l
    have htwo_a_nn : (0 : Q') ≤ HKPos.two a := HKPos.two_nonneg (Q'.le_of_lt ha0)
    have hmul : HKPos.two a * (a * a) ^ l ≤ HKPos.two a * half ^ l :=
      Q'.mul_le_mul_of_nonneg_left _ _ (HKPos.two a) hpow htwo_a_nn
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (two_geoAmp_eqv a l)) hmul
  -- Chain: two (geoAmp) ≤ two a * half^l ≤ geoIncr C l * factorLB a
  --                                       ≤ geoIncr C l * factor (geoAmp) x
  exact Q'.le_trans' _ _ _ stepC (Q'.le_trans' _ _ _ stepB stepA)

/-! ## 4. `S` as a convergent `CReal` (the deliverable)

We feed the partial sums `Spart a x` to `Continuum.crealOfGeoIncrement` with the
geometric increment bound from §3.  The single-step bounds are
`Spart (l+1) = Spart l + sTerm a x l` with `0 ≤ sTerm a x l ≤ geoIncr C l`, and
the modulus is supplied by `δ = ε/(2C)` realized as `divPos ε (2·C)` (using
`divPos_mul_eqv` to discharge `(2C)·δ ≃ ε`). -/

/-- **`S` as a `CReal`, parametrised by the constant `C` (general form).**

For `0 < a`, `a < 1`, `−1 ≤ x`, `a·a ≤ 1/2`, and a strictly-positive `C` with
`two a ≤ C·factorLB a`, the partial sums `Spart a x` form a `CReal` whose
`approx N = Spart a x N` and whose Cauchy modulus is the `HalfPow` modulus
inherited from `crealOfGeoIncrement`. -/
def sConvCRealOf (a x C : Q')
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) (hCpos : 0 < C.num)
    (hCb : HKPos.two a ≤ C * HKPos.factorLB a) : CReal :=
  crealOfGeoIncrement (Spart a x) C (Q'.le_of_lt (CReal.pos_of_num_pos hCpos))
    -- hup : Spart (l+1) ≤ Spart l + geoIncr C l
    (fun l => by
      rw [Spart_succ]
      exact Q'.add_le_add_left (Spart a x l) (sTerm a x l) (geoIncr C l)
        (sTerm_le_geoIncr ha0 ha1 hx ha2 (Q'.le_of_lt (CReal.pos_of_num_pos hCpos)) hCb l))
    -- hlo : Spart l ≤ Spart (l+1) + geoIncr C l
    (fun l => by
      rw [Spart_succ]
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg (Spart a x l) (sTerm a x l) (sTerm_nonneg ha0 ha1 hx l)) ?_
      exact Q'.add_le_self_of_nonneg (Spart a x l + sTerm a x l) (geoIncr C l)
        (geoIncr_nonneg C (Q'.le_of_lt (CReal.pos_of_num_pos hCpos)) l))
    -- modulus : ∃ δ>0, (2·C)·δ ≤ ε,  δ = divPos ε (2·C)
    (fun ε hε => by
      have h2Cpos : 0 < (Q'.ofNat 2 * C).num := by
        show 0 < (2 : Int) * C.num
        exact Int.mul_pos (by decide) hCpos
      refine ⟨divPos ε (Q'.ofNat 2 * C), divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      -- (2C)·δ ≃ δ·(2C) ≃ ε
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (Q'.ofNat 2 * C) (divPos ε (Q'.ofNat 2 * C))) ?_
      exact divPos_mul_eqv h2Cpos)

@[simp] theorem sConvCRealOf_approx (a x C : Q')
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) (hCpos : 0 < C.num)
    (hCb : HKPos.two a ≤ C * HKPos.factorLB a) (N : Nat) :
    (sConvCRealOf a x C ha0 ha1 hx ha2 hCpos hCb).approx N = Spart a x N := rfl

/-! ### The canonical constant `C⋆ = 2a/(1−a)² = divPos (two a) (factorLB a)` -/

/-- The canonical increment constant `C⋆ = divPos (two a) (factorLB a)`. -/
def Cstar (a : Q') : Q' := divPos (HKPos.two a) (HKPos.factorLB a)

/-- `0 < (Cstar a).num` for `0 < a` (numerator `= (two a).num · (factorLB a).den
> 0`). -/
theorem Cstar_num_pos {a : Q'} (ha0 : (0 : Q') < a) : 0 < (Cstar a).num := by
  have htwo_pos : (0 : Q') < HKPos.two a := by
    show (0 : Q') < a + a
    have := Q'.zero_le_add a a (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)
    -- a + a > 0 : numerator positive
    apply CReal.pos_of_num_pos
    have hn : 0 < a.num := CReal.num_pos_of_pos ha0
    show 0 < (a + a).num
    show 0 < a.num * (a.den : Int) + a.num * (a.den : Int)
    have hpos : 0 < a.num * (a.den : Int) :=
      Int.mul_pos hn (by exact_mod_cast Q'.den_pos a)
    omega
  exact divPos_num_pos (CReal.num_pos_of_pos htwo_pos)

/-- The canonical constant satisfies the increment hypothesis with EQUALITY at
the lower bound: `two a ≤ C⋆·factorLB a` (in fact `C⋆·factorLB a ≃ two a` for
`0 < 1 − a`, i.e. `a < 1`). -/
theorem Cstar_bound {a : Q'} (ha1 : a < (1 : Q')) :
    HKPos.two a ≤ Cstar a * HKPos.factorLB a := by
  -- C⋆·factorLB a = divPos (two a) (factorLB a) · factorLB a ≃ two a
  have hLBpos : 0 < (HKPos.factorLB a).num :=
    CReal.num_pos_of_pos (HKPos.factorLB_pos ha1)
  exact Q'.ge_of_eqv (divPos_mul_eqv (p := HKPos.two a) (D := HKPos.factorLB a) hLBpos)

/-- **THE DELIVERABLE: `S(x)` as a convergent `CReal` with explicit modulus,**
in the regime `a·a ≤ 1/2`.  `approx N = Spart a x N` (the genuine finite-volume
partial sum `Σ_{n<N} 2a^{2n+1}/(1+2a^{2n+1}x+a^{2(2n+1)})`); the Cauchy modulus
is the `HalfPow` modulus inherited from `crealOfGeoIncrement` at the canonical
constant `C⋆ = 2a/(1−a)²`. -/
def sConvCReal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) : CReal :=
  sConvCRealOf a x (Cstar a) ha0 ha1 hx ha2 (Cstar_num_pos ha0) (Cstar_bound ha1)

/-- `S`'s `N`-th approximation is exactly the finite-volume partial sum. -/
@[simp] theorem sConvCReal_approx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) (N : Nat) :
    (sConvCReal ha0 ha1 hx ha2).approx N = Spart a x N := rfl

/-- Every approximation of the `S` `CReal` is `≥ 0`. -/
theorem sConvCReal_approx_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) (N : Nat) :
    (0 : Q') ≤ (sConvCReal ha0 ha1 hx ha2).approx N := by
  rw [sConvCReal_approx]
  exact Spart_nonneg ha0 ha1 hx N

/-- **The `S` `CReal`'s limit is `≥ 0`** (`ExpPos.geRat … 0`).  This is the `S`
half of the manifest-positivity of `R = (ϑ₃/2a)·S`. -/
theorem sConvCReal_geRat_zero {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half) :
    ExpPos.geRat (sConvCReal ha0 ha1 hx ha2) 0 := by
  apply ExpPos.geRat_of_eventually
  exact ⟨0, fun N _ => sConvCReal_approx_nonneg ha0 ha1 hx ha2 N⟩

/-! ## 5. The end-to-end consumer: `R = Θ·S ≥ 0`

`HeatKernelPos2.mul_geRat_zero` needs both factors as nonneg-approx `CReal`s.
We now supply the `S`-factor genuinely (no longer a hypothesis); the `ϑ₃/2a`
factor `Θ` is the remaining (product-convergence) gap and is consumed as a
parameter with its nonneg-approx hypothesis. -/

/-- **`R = Θ·S ≥ 0` with `S` genuinely built.**  GIVEN any `CReal` `Θ` realizing
`ϑ₃/2a` with nonnegative approximations, the product `Θ · S` (with `S` the
convergent `CReal` of §4) has limit `≥ 0`.  This is `HKPos2.mul_geRat_zero`
with the `S`-factor's nonneg-approx hypothesis discharged by
`sConvCReal_approx_nonneg`. -/
theorem R_geRat_zero_of_theta {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (ha2 : a * a ≤ half)
    (Θ : CReal) (hΘ : ∀ n, (0 : Q') ≤ Θ.approx n) :
    ExpPos.geRat (CReal.mul Θ (sConvCReal ha0 ha1 hx ha2)) 0 :=
  HKPos2.mul_geRat_zero hΘ (sConvCReal_approx_nonneg ha0 ha1 hx ha2)

end YMGap.Continuum.HKConv

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`omega`/`finSum` helpers).
No `Classical.*`, no `native_decide`, no `sorry`. -/

#print axioms YMGap.Continuum.HKConv.divPos_den_cast
#print axioms YMGap.Continuum.HKConv.divPos_nonneg
#print axioms YMGap.Continuum.HKConv.divPos_pos
#print axioms YMGap.Continuum.HKConv.divPos_num_pos
#print axioms YMGap.Continuum.HKConv.divPos_le_of_le
#print axioms YMGap.Continuum.HKConv.divPos_mul_eqv
#print axioms YMGap.Continuum.HKConv.factor_num_pos
#print axioms YMGap.Continuum.HKConv.sTerm_nonneg
#print axioms YMGap.Continuum.HKConv.Spart_nonneg
#print axioms YMGap.Continuum.HKConv.mul_le_mul'
#print axioms YMGap.Continuum.HKConv.pow_le_pow_base
#print axioms YMGap.Continuum.HKConv.factorLB_antitone
#print axioms YMGap.Continuum.HKConv.two_geoAmp_eqv
#print axioms YMGap.Continuum.HKConv.sTerm_le_geoIncr
#print axioms YMGap.Continuum.HKConv.sConvCRealOf
#print axioms YMGap.Continuum.HKConv.Cstar_num_pos
#print axioms YMGap.Continuum.HKConv.Cstar_bound
#print axioms YMGap.Continuum.HKConv.sConvCReal
#print axioms YMGap.Continuum.HKConv.sConvCReal_approx_nonneg
#print axioms YMGap.Continuum.HKConv.sConvCReal_geRat_zero
#print axioms YMGap.Continuum.HKConv.R_geRat_zero_of_theta
