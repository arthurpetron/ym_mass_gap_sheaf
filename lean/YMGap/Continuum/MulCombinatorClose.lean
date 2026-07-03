/-
# Closing the binary finite-difference product-rule combinator (`MulCombinatorClose`)

`FiniteProductFDDeriv.MulCombinator` is the SOLE analytic datum the finite-product
induction consumes; everything scaffolding it (`abs_six_le`, `FDDerivData.const`,
`prodDeriv`, `finiteProductFDDeriv`) is already proved there.  This module
DISCHARGES that datum: it builds `FDDerivData.mul`, the binary C¹ product rule at
the increment level, and packages it as the inhabitant `mulCombinator`.

## What is proved here (genuine, axiom-clean)

* `mul_rem_expand` — the substantive ring identity: the cleared product remainder
  `f(θ+h)g(θ+h) ⊖ fθgθ ⊖ (df·gθ + fθ·dg)·h` equals the six-atom sum
  `gθ·rf + fθ·rg + rf·rg + df·(h·rg) + dg·(h·rf) + df·dg·h²`
  with `rf = fdRem f df θ h`, `rg = fdRem g dg θ h`.  Proved WITHOUT a ring tactic
  (none is available): the three genuine cancellations (`fθgθ`, `df·gθ·h`,
  `fθ·dg·h`) are isolated into short structural additive lemmas, and every
  cancellation-free distribution / AC-rearrangement is discharged by a
  `num`/`den` cross-product reduction closed with `ac_rfl` (`ring_qeqv`).
* `FDDerivData.mul` — the modulus assembly: an explicit `δ ε` splitting the `ε·|h|`
  budget as `½ε` over the five linear atoms (via `K = 1+|gθ|+|fθ|+|df|+|dg|`) plus
  `½ε` over the sole `O(h²)` atom (via `C = 1+|df||dg|`), with all six per-atom
  bounds fed to `abs_six_le`.
* `mulCombinator : MulCombinator` — the inhabitant, making `finiteProductFDDeriv`
  and everything above it UNCONDITIONAL.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.MulCombinatorClose

open YMGap.Constructive
open YMGap.Continuum.TsumDeriv (fdRem FDDerivData)
open YMGap.Continuum.FiniteProductFDDeriv (MulCombinator abs_six_le)

local infix:50 " ≈ " => Q'.eqv

/-- `(-a).num = -(a.num)` (definitional; a rewrite handle for `ac_rfl`). -/
theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

/-- Ring closer for CANCELLATION-FREE `Q'.eqv` identities: reduce to the `Int`
cross-product, expand every `num`/`den` cast and distribute, close by `ac_rfl`.
Sound only for identities requiring NO additive cancellation of `+X`/`-X` pairs
(`ac_rfl` normalises modulo associativity+commutativity but never cancels). -/
macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-! ## 1. Cancellation-free algebraic atoms (all closed by `ring_qeqv`). -/

/-- Product of two three-term sums, fully distributed. -/
theorem nine_dist (r u c s v d : Q') :
    ((r + u) + c) * ((s + v) + d)
      ≈ ((((((((r * s + r * v) + r * d) + u * s) + u * v) + u * d) + c * s) + c * v)
          + c * d) := by ring_qeqv

/-- The derivative-value increment factored into the two `O(h)` atoms. -/
theorem w_dist (df b0 a0 dg h : Q') :
    (df * b0 + a0 * dg) * h ≈ (df * h) * b0 + a0 * (dg * h) := by ring_qeqv

/-- All-positive rearrangement of the nine product atoms: pull out the three that
will cancel (`A9 = c·d`, `A6 = u·d`, `A8 = c·v`), leaving the six survivors in the
product-rule target order. -/
theorem rear9 (A1 A2 A3 A4 A5 A6 A7 A8 A9 : Q') :
    ((((((((A1 + A2) + A3) + A4) + A5) + A6) + A7) + A8) + A9)
      ≈ ((((((A3 + A7) + A1) + A4) + A2) + A5) + (A9 + (A6 + A8))) := by ring_qeqv

/-- `rf·(dg·h) = dg·(h·rf)`. -/
theorem mul_rearr_p5 (r dg h : Q') : r * (dg * h) ≈ dg * (h * r) := by ring_qeqv
/-- `(df·h)·(dg·h) = (df·dg)·(h·h)`. -/
theorem mul_rearr_p6 (df h dg : Q') : (df * h) * (dg * h) ≈ (df * dg) * (h * h) := by
  ring_qeqv

/-- `sum5` factoring: the five linear per-atom bounds sum to `K·t`. -/
theorem sum5_eq (A B D E t : Q') :
    ((((A * t + B * t) + t) + D * t) + E * t)
      ≈ ((((1 + A) + B) + D) + E) * t := by ring_qeqv

/-! ## 2. Structural cancellation lemmas (additive; `ac_rfl` cannot cancel). -/

/-- `a ≈ (a + -b) + b`  (restore a cleared subtraction). -/
theorem sub_add_cancel' (a b : Q') : a ≈ (a + (-b)) + b := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (Q'.neg_add_self_eqv b)) ?_
  exact TsumDeriv.Q'.eqv_of_eq (Q'.add_zero' a)

/-- From `nine ≈ six + (t1 + (t2 + t3))`, cancel the three tail atoms. -/
theorem collapse3 (nine six t1 t2 t3 : Q')
    (h : nine ≈ (six + (t1 + (t2 + t3)))) :
    ((nine + (-t1)) + ((-t2) + (-t3))) ≈ six := by
  have hstep : ((nine + (-t1)) + ((-t2) + (-t3)))
      ≈ (six + ((t1 + (t2 + t3)) + ((-t1) + ((-t2) + (-t3))))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((-t2) + (-t3))
        (Q'.add_eqv_congr_right _ _ (-t1) h)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (six + (t1 + (t2 + t3))) (-t1) ((-t2) + (-t3))) ?_
    exact Q'.add_assoc_eqv six (t1 + (t2 + t3)) ((-t1) + ((-t2) + (-t3)))
  refine Q'.eqv_trans _ _ _ hstep ?_
  have hin1 : ((t1 + (t2 + t3)) + (-t1)) ≈ (t2 + t3) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-t1) (Q'.add_comm_eqv t1 (t2 + t3))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (t2 + t3) t1 (-t1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (t2 + t3) _ _ (Q'.add_neg_self_eqv t1)) ?_
    exact TsumDeriv.Q'.eqv_of_eq (Q'.add_zero' (t2 + t3))
  have hin0 : ((t1 + (t2 + t3)) + ((-t1) + ((-t2) + (-t3)))) ≈ (0 : Q') := by
    -- reassociate to ((P + -t1) + R) then cancel
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (t1 + (t2 + t3)) (-t1) ((-t2) + (-t3)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((-t2) + (-t3)) hin1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_swap_inner t2 t3 (-t2) (-t3)) ?_
    refine Q'.eqv_trans _ _ _
      (TsumDeriv.Q'.add_eqv_congr (Q'.add_neg_self_eqv t2) (Q'.add_neg_self_eqv t3)) ?_
    exact TsumDeriv.Q'.eqv_of_eq (Q'.add_zero' 0)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left six _ _ hin0) ?_
  exact TsumDeriv.Q'.eqv_of_eq (Q'.add_zero' six)

/-! ## 3. THE ring identity for the product remainder. -/

/-- **The six-atom product-remainder identity.**  With `rf = (FA⊖a0)⊖df·h`,
`rg = (FB⊖b0)⊖dg·h`, the cleared product remainder equals the six atoms
`b0·rf + a0·rg + rf·rg + df·(h·rg) + dg·(h·rf) + df·dg·(h·h)`.  -/
theorem mul_rem_expand (FA FB a0 b0 df dg h : Q') :
    (((FA * FB) + (-(a0 * b0))) + (-((df * b0 + a0 * dg) * h)))
      ≈ (((((b0 * ((FA + (-a0)) + (-(df * h)))
                + a0 * ((FB + (-b0)) + (-(dg * h))))
              + ((FA + (-a0)) + (-(df * h))) * ((FB + (-b0)) + (-(dg * h))))
              + df * (h * ((FB + (-b0)) + (-(dg * h)))))
              + dg * (h * ((FA + (-a0)) + (-(df * h)))))
              + (df * dg) * (h * h)) := by
  -- abbreviations (defeq): rf, rg, and the linear parts La = df·h, Lb = dg·h.
  let rf : Q' := (FA + (-a0)) + (-(df * h))
  let rg : Q' := (FB + (-b0)) + (-(dg * h))
  -- (1) FA ≈ ((rf + df·h) + a0),  FB ≈ ((rg + dg·h) + b0)
  have hFA : FA ≈ ((rf + df * h) + a0) :=
    Q'.eqv_trans _ _ _ (sub_add_cancel' FA a0)
      (Q'.add_eqv_congr_right _ _ a0 (sub_add_cancel' (FA + (-a0)) (df * h)))
  have hFB : FB ≈ ((rg + dg * h) + b0) :=
    Q'.eqv_trans _ _ _ (sub_add_cancel' FB b0)
      (Q'.add_eqv_congr_right _ _ b0 (sub_add_cancel' (FB + (-b0)) (dg * h)))
  -- (2) FA·FB ≈ ((rf+df·h)+a0)·((rg+dg·h)+b0)
  have hprod : FA * FB ≈ ((rf + df * h) + a0) * ((rg + dg * h) + b0) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ FB hFA)
      (Q'.mul_eqv_congr_left _ _ _ hFB)
  -- (3) distribute to the nine atoms
  have h9 := nine_dist rf (df * h) a0 rg (dg * h) b0
  have hFAFB : FA * FB
      ≈ ((((((((rf * rg + rf * (dg * h)) + rf * b0) + (df * h) * rg)
                + (df * h) * (dg * h)) + (df * h) * b0) + a0 * rg) + a0 * (dg * h))
          + a0 * b0) :=
    Q'.eqv_trans _ _ _ hprod h9
  -- (4) fold the remainder onto the nine-atom sum, splitting the derivative
  -- increment into the two cancelling atoms A6 = (df·h)·b0, A8 = a0·(dg·h).
  let nine : Q' :=
    ((((((((rf * rg + rf * (dg * h)) + rf * b0) + (df * h) * rg)
        + (df * h) * (dg * h)) + (df * h) * b0) + a0 * rg) + a0 * (dg * h))
        + a0 * b0)
  have hrem1 : (((FA * FB) + (-(a0 * b0))) + (-((df * b0 + a0 * dg) * h)))
      ≈ ((nine + (-(a0 * b0))) + ((-((df * h) * b0)) + (-(a0 * (dg * h))))) := by
    refine TsumDeriv.Q'.add_eqv_congr
      (Q'.add_eqv_congr_right _ _ (-(a0 * b0)) hFAFB) ?_
    -- -((df·b0+a0·dg)·h) ≈ -(A6) + -(A8)
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (w_dist df b0 a0 dg h)) ?_
    exact Q'.neg_add_eqv ((df * h) * b0) (a0 * (dg * h))
  -- (5) collapse the three cancelling atoms (a0·b0, A6, A8) via rear9
  have hcol : ((nine + (-(a0 * b0))) + ((-((df * h) * b0)) + (-(a0 * (dg * h)))))
      ≈ ((((((rf * b0 + a0 * rg) + rf * rg) + (df * h) * rg) + rf * (dg * h))
          + (df * h) * (dg * h))) := by
    refine collapse3 nine _ (a0 * b0) ((df * h) * b0) (a0 * (dg * h)) ?_
    -- nine ≈ six + (A9 + (A6 + A8))
    exact rear9 (rf * rg) (rf * (dg * h)) (rf * b0) ((df * h) * rg)
      ((df * h) * (dg * h)) ((df * h) * b0) (a0 * rg) (a0 * (dg * h)) (a0 * b0)
  -- (6) match to the exact p-order (product commutations / associations)
  have hmatch : ((((((rf * b0 + a0 * rg) + rf * rg) + (df * h) * rg) + rf * (dg * h))
          + (df * h) * (dg * h)))
      ≈ (((((b0 * rf + a0 * rg) + rf * rg) + df * (h * rg)) + dg * (h * rf))
          + (df * dg) * (h * h)) := by
    refine TsumDeriv.Q'.add_eqv_congr
      (TsumDeriv.Q'.add_eqv_congr
        (TsumDeriv.Q'.add_eqv_congr
          (TsumDeriv.Q'.add_eqv_congr
            (TsumDeriv.Q'.add_eqv_congr (Q'.mul_comm_eqv rf b0) (Q'.eqv_refl (a0 * rg)))
            (Q'.eqv_refl (rf * rg)))
          (Q'.mul_assoc_eqv df h rg))
        (mul_rearr_p5 rf dg h))
      (mul_rearr_p6 df h dg)
  exact Q'.eqv_trans _ _ _ hrem1 (Q'.eqv_trans _ _ _ hcol hmatch)

/-! ## 4. Positivity plumbing and the modulus constants. -/

/-- `0 < a → 0 ≤ b → 0 < a + b`  (numerator positivity). -/
theorem pos_add_nonneg {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') ≤ b) :
    (0 : Q') < a + b := by
  apply CReal.pos_of_num_pos
  show (0 : Int) < (a + b).num
  rw [Q'.add_num_cast]
  have han : (0 : Int) < a.num := CReal.num_pos_of_pos ha
  have hbn : (0 : Int) ≤ b.num := (Q'.zero_le_iff_num_nonneg b).mp hb
  have had : (0 : Int) < (a.den : Int) := by exact_mod_cast Q'.den_pos a
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast Q'.den_pos b
  have t1 : (0 : Int) < a.num * (b.den : Int) := Int.mul_pos han hbd
  have t2 : (0 : Int) ≤ b.num * (a.den : Int) := Int.mul_nonneg hbn (Int.le_of_lt had)
  omega

/-- `K = 1 + |gθ| + |fθ| + |df| + |dg|`. -/
def mulK (a0 b0 df dg : Q') : Q' :=
  ((((1 + Q'.abs b0) + Q'.abs a0) + Q'.abs df) + Q'.abs dg)

theorem mulK_pos (a0 b0 df dg : Q') : (0 : Q') < mulK a0 b0 df dg := by
  unfold mulK
  exact pos_add_nonneg (pos_add_nonneg (pos_add_nonneg
    (pos_add_nonneg (CReal.pos_of_num_pos (by decide)) (Q'.abs_nonneg b0))
    (Q'.abs_nonneg a0)) (Q'.abs_nonneg df)) (Q'.abs_nonneg dg)

/-- `C = 1 + |df|·|dg|`. -/
def mulC (df dg : Q') : Q' := 1 + Q'.abs df * Q'.abs dg

theorem mulC_pos (df dg : Q') : (0 : Q') < mulC df dg := by
  unfold mulC
  exact pos_add_nonneg (CReal.pos_of_num_pos (by decide))
    (Q'.mul_nonneg _ _ (Q'.abs_nonneg df) (Q'.abs_nonneg dg))

/-- Inner tolerance `η ε = min(1, ½ε/K)`. -/
def mulEta (a0 b0 df dg ε : Q') : Q' :=
  Q'.min' 1 (Q'.divPos (HalfPow.half * ε) (mulK a0 b0 df dg) (mulK_pos a0 b0 df dg))

theorem mulEta_pos (a0 b0 df dg ε : Q') (hε : (0 : Q') < ε) :
    (0 : Q') < mulEta a0 b0 df dg ε :=
  TsumDeriv.Q'.lt_min' (CReal.pos_of_num_pos (by decide))
    (Q'.divPos_pos _ _ _ (ExpNeg.half_mul_pos ε hε))

theorem mulEta_le_one (a0 b0 df dg ε : Q') : mulEta a0 b0 df dg ε ≤ 1 :=
  TsumDeriv.Q'.min_le_left' _ _

theorem mulEta_le_div (a0 b0 df dg ε : Q') :
    mulEta a0 b0 df dg ε
      ≤ Q'.divPos (HalfPow.half * ε) (mulK a0 b0 df dg) (mulK_pos a0 b0 df dg) :=
  TsumDeriv.Q'.min_le_right' _ _

/-! ## 5. The binary product-rule combinator (the discharged datum). -/

/-- **The binary finite-difference product rule.**  From per-factor data-carrying
derivatives `Df, Dg`, the product `f·g` has finite-difference derivative
`df·gθ + fθ·dg` at `θ`, with the explicit `½ε`+`½ε` split modulus. -/
def FDDerivData.mul {f g : Q' → Q'} {df dg θ : Q'}
    (Df : FDDerivData f df θ) (Dg : FDDerivData g dg θ) :
    FDDerivData (fun t => f t * g t) (df * g θ + f θ * dg) θ where
  δ ε := Q'.min' (Df.δ (mulEta (f θ) (g θ) df dg ε))
    (Q'.min' (Dg.δ (mulEta (f θ) (g θ) df dg ε))
      (Q'.min' (Q'.divPos (HalfPow.half * ε) (mulC df dg) (mulC_pos df dg)) 1))
  δ_pos ε hε :=
    TsumDeriv.Q'.lt_min' (Df.δ_pos _ (mulEta_pos _ _ _ _ _ hε))
      (TsumDeriv.Q'.lt_min' (Dg.δ_pos _ (mulEta_pos _ _ _ _ _ hε))
        (TsumDeriv.Q'.lt_min'
          (Q'.divPos_pos _ _ _ (ExpNeg.half_mul_pos ε hε))
          (CReal.pos_of_num_pos (by decide))))
  bound ε hε h hpos hle := by
    -- inner tolerance and its facts
    let η : Q' := mulEta (f θ) (g θ) df dg ε
    have hηpos : (0 : Q') < η := mulEta_pos (f θ) (g θ) df dg ε hε
    have hη1 : η ≤ 1 := mulEta_le_one (f θ) (g θ) df dg ε
    let t : Q' := η * Q'.abs h
    have habsh_nn : (0 : Q') ≤ Q'.abs h := Q'.abs_nonneg h
    have ht_nn : (0 : Q') ≤ t := Q'.mul_nonneg _ _ (Q'.le_of_lt hηpos) habsh_nn
    -- legs of the modulus
    have la : Q'.abs h ≤ Df.δ η :=
      Q'.le_trans' _ _ _ hle (TsumDeriv.Q'.min_le_left' _ _)
    have lrest := Q'.le_trans' _ _ _ hle (TsumDeriv.Q'.min_le_right' _ _)
    have lb : Q'.abs h ≤ Dg.δ η :=
      Q'.le_trans' _ _ _ lrest (TsumDeriv.Q'.min_le_left' _ _)
    have lrest2 := Q'.le_trans' _ _ _ lrest (TsumDeriv.Q'.min_le_right' _ _)
    have lc : Q'.abs h ≤ Q'.divPos (HalfPow.half * ε) (mulC df dg) (mulC_pos df dg) :=
      Q'.le_trans' _ _ _ lrest2 (TsumDeriv.Q'.min_le_left' _ _)
    have ld : Q'.abs h ≤ 1 :=
      Q'.le_trans' _ _ _ lrest2 (TsumDeriv.Q'.min_le_right' _ _)
    -- per-factor remainder bounds
    let rf : Q' := fdRem f df θ h
    let rg : Q' := fdRem g dg θ h
    have hrf : Q'.abs rf ≤ t := Df.bound η hηpos h hpos la
    have hrg : Q'.abs rg ≤ t := Dg.bound η hηpos h hpos lb
    -- t ≤ 1
    have ht_le1 : t ≤ (1 : Q') := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right η 1 (Q'.abs h) hη1 habsh_nn) ?_
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs h))) ld
    -- |h·rg| ≤ t and |h·rf| ≤ t
    have hhr : ∀ r : Q', Q'.abs r ≤ t → Q'.abs (h * r) ≤ t := by
      intro r hr
      refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le h r) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left (Q'.abs r) t (Q'.abs h) hr habsh_nn) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right (Q'.abs h) 1 t ld ht_nn) ?_
      exact Q'.le_of_eqv (Q'.one_mul_eqv t)
    have hhrg : Q'.abs (h * rg) ≤ t := hhr rg hrg
    have hhrf : Q'.abs (h * rf) ≤ t := hhr rf hrf
    -- the six per-atom bounds
    have h1 : Q'.abs ((g θ) * rf) ≤ Q'.abs (g θ) * t :=
      Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le (g θ) rf)
        (Q'.mul_le_mul_of_nonneg_left (Q'.abs rf) t (Q'.abs (g θ)) hrf (Q'.abs_nonneg (g θ)))
    have h2 : Q'.abs ((f θ) * rg) ≤ Q'.abs (f θ) * t :=
      Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le (f θ) rg)
        (Q'.mul_le_mul_of_nonneg_left (Q'.abs rg) t (Q'.abs (f θ)) hrg (Q'.abs_nonneg (f θ)))
    have h3 : Q'.abs (rf * rg) ≤ t := by
      refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le rf rg) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right (Q'.abs rf) t (Q'.abs rg) hrf (Q'.abs_nonneg rg)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left (Q'.abs rg) t t hrg ht_nn) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left t 1 t ht_le1 ht_nn) ?_
      exact Q'.le_of_eqv (Q'.mul_one_eqv t)
    have h4 : Q'.abs (df * (h * rg)) ≤ Q'.abs df * t :=
      Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le df (h * rg))
        (Q'.mul_le_mul_of_nonneg_left (Q'.abs (h * rg)) t (Q'.abs df) hhrg (Q'.abs_nonneg df))
    have h5 : Q'.abs (dg * (h * rf)) ≤ Q'.abs dg * t :=
      Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le dg (h * rf))
        (Q'.mul_le_mul_of_nonneg_left (Q'.abs (h * rf)) t (Q'.abs dg) hhrf (Q'.abs_nonneg dg))
    have h6 : Q'.abs ((df * dg) * (h * h)) ≤ (HalfPow.half * ε) * Q'.abs h := by
      -- |df·dg|·|h·h| ≤ (|df||dg|)(|h||h|) ≤ C(|h||h|) = (C|h|)|h| ≤ (½ε)|h|
      have hCh : mulC df dg * Q'.abs h ≤ HalfPow.half * ε := by
        refine Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left (Q'.abs h) _ (mulC df dg) lc
            (Q'.le_of_lt (mulC_pos df dg))) ?_
        refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv (mulC df dg) _) ?_)
        exact Q'.divPos_mul_eqv (HalfPow.half * ε) (mulC df dg) (mulC_pos df dg)
      have hdfdg_nn : (0 : Q') ≤ Q'.abs df * Q'.abs dg :=
        Q'.mul_nonneg _ _ (Q'.abs_nonneg df) (Q'.abs_nonneg dg)
      have hhh_nn : (0 : Q') ≤ Q'.abs h * Q'.abs h :=
        Q'.mul_nonneg _ _ habsh_nn habsh_nn
      -- |df·dg| ≤ C
      have hdfdg_le : Q'.abs df * Q'.abs dg ≤ mulC df dg := by
        refine Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg (Q'.abs df * Q'.abs dg) 1
            (Q'.le_of_lt (CReal.pos_of_num_pos (by decide)))) ?_
        exact Q'.le_of_eqv (Q'.add_comm_eqv (Q'.abs df * Q'.abs dg) 1)
      refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le (df * dg) (h * h)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs (h * h))
          (TsumDeriv.Q'.abs_mul_le df dg) (Q'.abs_nonneg (h * h))) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs df * Q'.abs dg)
          (TsumDeriv.Q'.abs_mul_le h h) hdfdg_nn) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs h * Q'.abs h) hdfdg_le hhh_nn) ?_
      -- C·(|h||h|) ≈ (C·|h|)·|h| ≤ (½ε)·|h|
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (mulC df dg) (Q'.abs h) (Q'.abs h)))) ?_
      exact Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs h) hCh habsh_nn
    -- assemble via abs_six_le
    have hsplit := mul_rem_expand (f (θ + h)) (g (θ + h)) (f θ) (g θ) df dg h
    have hsix := abs_six_le hsplit h1 h2 h3 h4 h5 h6
    -- bound the five linear atoms: sum5 ≤ (½ε)·|h|
    have hKη : mulK (f θ) (g θ) df dg * η ≤ HalfPow.half * ε := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left η _ (mulK (f θ) (g θ) df dg)
          (mulEta_le_div (f θ) (g θ) df dg ε)
          (Q'.le_of_lt (mulK_pos (f θ) (g θ) df dg))) ?_
      refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (mulK (f θ) (g θ) df dg) _) ?_)
      exact Q'.divPos_mul_eqv (HalfPow.half * ε) (mulK (f θ) (g θ) df dg)
        (mulK_pos (f θ) (g θ) df dg)
    have hsum5 : ((((Q'.abs (g θ) * t + Q'.abs (f θ) * t) + t) + Q'.abs df * t)
          + Q'.abs dg * t) ≤ (HalfPow.half * ε) * Q'.abs h := by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (sum5_eq (Q'.abs (g θ)) (Q'.abs (f θ)) (Q'.abs df) (Q'.abs dg) t)) ?_
      -- ((((1+|gθ|)+|fθ|)+|df|)+|dg|)·t = mulK·(η·|h|) ≈ (mulK·η)·|h| ≤ (½ε)·|h|
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (mulK (f θ) (g θ) df dg) η (Q'.abs h)))) ?_
      exact Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs h) hKη habsh_nn
    -- combine sum5 + B6 ≤ ½ε|h| + ½ε|h| ≈ ε|h|
    have hfinal_eqv : (HalfPow.half * ε) * Q'.abs h + (HalfPow.half * ε) * Q'.abs h
        ≈ ε * Q'.abs h := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (HalfPow.half * ε) (HalfPow.half * ε) (Q'.abs h))) ?_
      exact Q'.mul_eqv_congr_right _ _ (Q'.abs h) (ExpNeg.two_halves ε)
    refine Q'.le_trans' _ _ _ hsix ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hsum5 (Q'.le_refl' ((HalfPow.half * ε) * Q'.abs h))) ?_
    exact Q'.le_of_eqv hfinal_eqv

/-- **The inhabitant.**  Feeding this to `finiteProductFDDeriv` makes the whole
iterated product rule (and everything above it) unconditional. -/
def mulCombinator : MulCombinator := ⟨fun Df Dg => FDDerivData.mul Df Dg⟩

end YMGap.Continuum.MulCombinatorClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MulCombinatorClose.mul_rem_expand
#print axioms YMGap.Continuum.MulCombinatorClose.FDDerivData.mul
#print axioms YMGap.Continuum.MulCombinatorClose.mulCombinator
