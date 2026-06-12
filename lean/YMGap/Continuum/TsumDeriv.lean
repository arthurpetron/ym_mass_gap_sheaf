/-
# A constructive Bishop-style C¹-uniform-limit engine (Wall-2 differentiation core)

This module builds the **generic, reusable analytic engine** named in
`docs/jtp-convergence-notes.md §2.3` as the single outstanding Wall-2 obligation:
the constructive theorem that *the uniform limit of derivatives is the derivative
of the limit* (Bishop's C¹-limit theorem), with EXPLICIT moduli carried as
`Type`-level data (AGENTS.md Rule 8).

## What is GENUINELY closed here (new, axiom-clean, fully reusable content)

The whole content of "differentiate a convergent sequence term by term" is the
**three-ε increment estimate**, and that estimate is proved here in full, at the
`Q'` increment level (no `CReal` division, no `Mathlib ℝ`):

    |F(θ+h) − F(θ) − g·h|
        ≤ |F(θ+h) − f_M(θ+h)|              (pointwise tail of the limit)
        + |f_M(θ+h) − f_M(θ) − f'_M(θ)·h|   (the M-th finite-difference deriv.)
        + |f_M(θ) − F(θ)|                   (pointwise tail of the limit)
        + |(f'_M(θ) − g)·h|.                (uniform derivative convergence)

Choosing `M` past the (uniform) derivative-convergence modulus and the pointwise
modulus (instantiated at the scale `(ε/4)·|h|`), and `|h|` past the common M-th
derivative modulus, makes each of the four pieces `≤ (ε/4)·|h|`, hence the whole
`≤ ε·|h|`.  This is exactly the standard Bishop proof; the genuine new content is
its constructive `Q'` assembly with all moduli as data.

The engine is packaged as:

* `FDDerivData f d θ` — a `Type`-level structure carrying a finite-difference
  derivative `d` of `f` at `θ` WITH its modulus `δ : Q' → Q'` (the data-carrying
  Bishop derivative: `|f(θ+h) − f(θ) − d·h| ≤ ε·|h|` for `0 < |h| ≤ δ ε`).
* `PtwiseConvAt`, `UnifDerivConvAt` — pointwise / uniform convergence with their
  moduli carried as data.
* `C1Inputs` — the bundled hypotheses (including the family's common
  finite-difference modulus = equicontinuity at `θ`).
* **`fdDeriv_of_unif` (CLOSED)** — the C¹-limit theorem: from `C1Inputs`, `F` has
  finite-difference derivative `g θ` at `θ`, with an explicit assembled modulus.

It introduces NO positivity content; it is a pure constructive-analysis
interchange theorem, valid for arbitrary `Q'`-valued function families.

## The honest residual (AGENTS.md Rule 6)

The engine `fdDeriv_of_unif` is COMPLETE.  What it does NOT do by itself is supply
its three hypotheses *for the specific heat-kernel / Jacobi factor families* — in
particular `UnifDerivConvAt` for the theta-product log-derivative requires the
explicit `O((a·a)^k)` geometric majorant wired to the per-factor derivative
bounds, and `FDDerivData` for each finite theta-product is the finite product rule
(`DiffProduct.leibniz`) plus the per-factor Taylor remainder.  Those instantiation
inputs are the named `Σ`-obligation downstream (`DiffProduct` / `JTPIdentity`);
they are NOT discharged here, but the ANALYTIC engine that consumes them — the
part that genuinely "commutes `d/dθ` with the limit" — is.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.AbsQ
import YMGap.Constructive.HalfPow
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealAdd

namespace YMGap.Continuum.TsumDeriv

open YMGap.Constructive
open YMGap.Constructive.Q'

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. `Q'` absolute-value and increment helpers

The three-ε estimate is assembled from elementary `Q'` triangle / scaling
inequalities.  `AbsQ.lean` provides `abs`, `abs_le`, `le_abs_self`, `neg_le_abs`,
`mul_le_of_bounds`; we add the three facts the estimate needs and which are not
there yet: `abs` respects `eqv`, `abs (−x) = abs x`, and `abs (x·y) ≤ |x|·|y|`
(in fact `= |x|·|y|`, but we only need `≤`). -/

namespace Q'

/-- A strict-positivity product helper (local; the base layer lacks `mul_pos`).
`0 < a, 0 < b ⟹ 0 < a·b`, via numerator positivity. -/
theorem mul_pos' {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) : (0 : Q') < a * b := by
  have hanum : (0 : Int) < a.num := CReal.num_pos_of_pos ha
  have hbnum : (0 : Int) < b.num := CReal.num_pos_of_pos hb
  apply CReal.pos_of_num_pos
  show (0 : Int) < (a * b).num
  have : (a * b).num = a.num * b.num := rfl
  rw [this]
  exact Int.mul_pos hanum hbnum

/-- Build `eqv` from `≤` both ways (the cross-product representation is `Int`,
where `≤` is antisymmetric). -/
theorem eqv_of_le_le {a b : Q'} (h1 : a ≤ b) (h2 : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm h1 h2

/-- An `Eq` lifts to `eqv` (local copy to avoid importing `CauchyConv`). -/
theorem eqv_of_eq {a b : Q'} (h : a = b) : a ≈ b := by subst h; exact Q'.eqv_refl a

/-- Two-sided additive congruence (composed from the two one-sided ones). -/
theorem add_eqv_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    (a + b) ≈ (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- `abs` respects `eqv`: `a ≈ b ⟹ abs a ≈ abs b`. -/
theorem abs_eqv_congr {a b : Q'} (h : a ≈ b) : (Q'.abs a) ≈ (Q'.abs b) := by
  -- abs a ≤ abs b and abs b ≤ abs a, via abs_le with the swapped bounds.
  have hab : a ≤ b := Q'.le_of_eqv h
  have hba : b ≤ a := Q'.ge_of_eqv h
  -- abs a ≤ abs b : use -|b| ≤ a (from -|b| ≤ -b... actually a ≈ b so use bounds on a via b)
  have h1 : Q'.abs a ≤ Q'.abs b := by
    refine Q'.abs_le ?_ ?_
    · -- -|b| ≤ a : since -|b| ≤ -b ≤ ... we have -|b| ≤ b (neg_le_abs gives -b ≤ |b|)
      have hnb : -(Q'.abs b) ≤ b := by
        have := Q'.neg_le_abs b
        have hh := Q'.neg_le_neg this
        exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv b))
      exact Q'.le_trans' _ _ _ hnb hba
    · exact Q'.le_trans' _ _ _ hab (Q'.le_abs_self b)
  have h2 : Q'.abs b ≤ Q'.abs a := by
    refine Q'.abs_le ?_ ?_
    · have hna : -(Q'.abs a) ≤ a := by
        have := Q'.neg_le_abs a
        have hh := Q'.neg_le_neg this
        exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv a))
      exact Q'.le_trans' _ _ _ hna hab
    · exact Q'.le_trans' _ _ _ hba (Q'.le_abs_self a)
  exact Q'.eqv_of_le_le h1 h2

/-- `abs (−x) ≈ abs x`. -/
theorem abs_neg (x : Q') : (Q'.abs (-x)) ≈ (Q'.abs x) := by
  -- |-x| ≤ |x| and |x| ≤ |-x|, both via abs_le.
  have h1 : Q'.abs (-x) ≤ Q'.abs x := by
    refine Q'.abs_le ?_ ?_
    · -- -|x| ≤ -x  ⟸  x ≤ |x|
      exact Q'.neg_le_neg (Q'.le_abs_self x)
    · -- -x ≤ |x|
      exact Q'.neg_le_abs x
  have h2 : Q'.abs x ≤ Q'.abs (-x) := by
    refine Q'.abs_le ?_ ?_
    · -- -|-x| ≤ x  ⟸  -x ≤ |-x|
      have := Q'.le_abs_self (-x)   -- -x ≤ |-x|
      have hh := Q'.neg_le_neg this  -- -|-x| ≤ -(-x)
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv x))
    · -- x ≤ |-x|  ⟸  x ≤ -(-x) ≤ ... use neg_le_abs (-x): -(-x) ≤ |-x|, and x ≈ -(-x)
      have := Q'.neg_le_abs (-x)     -- -(-x) ≤ |-x|
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv x)) this
  exact Q'.eqv_of_le_le h1 h2

/-- The "swap the sign inside abs of a difference": `abs (a ⊖ b) ≈ abs (b ⊖ a)`. -/
theorem abs_sub_comm (a b : Q') : (Q'.abs (a + (-b))) ≈ (Q'.abs (b + (-a))) := by
  -- a + -b ≈ -(b + -a), so |a+-b| ≈ |-(b+-a)| ≈ |b+-a|.
  have heq : (a + (-b)) ≈ (-(b + (-a))) := by
    -- -(b + -a) ≈ -b + -(-a) ≈ -b + a ≈ a + -b
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv b (-a)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-b) (-(-a)) a (Q'.neg_neg_eqv a)) ?_
    exact Q'.add_comm_eqv (-b) a
  refine Q'.eqv_trans _ _ _ (abs_eqv_congr heq) ?_
  exact abs_neg (b + (-a))

/-- `abs (x·y) ≤ abs x · abs y`.  (Sign-cased via `mul_le_of_bounds`.) -/
theorem abs_mul_le (x y : Q') : Q'.abs (x * y) ≤ Q'.abs x * Q'.abs y := by
  refine Q'.abs_le ?_ ?_
  · -- -(|x|·|y|) ≤ x·y
    -- x·y ≥ -(|x||y|): apply mul_le_of_bounds to (-x)·... no — use the bound on -(x·y) ≤ |x||y|.
    -- Easier: |x·y| ≤ |x||y| as upper, and -(|x||y|) ≤ x·y as lower.
    -- Lower: -(x·y) ≤ |x|·|y| (shown in the upper part for -(x·y)); negate.
    have hup : -(x * y) ≤ Q'.abs x * Q'.abs y := by
      have e : (-(x * y)) ≈ ((-x) * y) := Q'.eqv_symm (Q'.neg_mul_eqv x y)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
      exact Q'.mul_le_of_bounds (Q'.abs_nonneg x) (Q'.abs_nonneg y)
        (by -- -|x| ≤ -x ⟸ x ≤ |x|
            exact Q'.neg_le_neg (Q'.le_abs_self x))
        (by -- -x ≤ |x|
            exact Q'.neg_le_abs x)
        (by -- -|y| ≤ y ⟸ -y ≤ |y|... actually need -|y| ≤ y
            have := Q'.neg_le_abs y
            have hh := Q'.neg_le_neg this
            exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv y)))
        (Q'.le_abs_self y)
    have hh := Q'.neg_le_neg hup   -- -(|x||y|) ≤ -(-(x·y))
    exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv (x * y)))
  · -- x·y ≤ |x|·|y|
    exact Q'.mul_le_of_bounds (Q'.abs_nonneg x) (Q'.abs_nonneg y)
      (by -- -|x| ≤ x  ⟸  -x ≤ |x|
          have := Q'.neg_le_abs x
          have hh := Q'.neg_le_neg this
          exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv x)))
      (Q'.le_abs_self x)
      (by have := Q'.neg_le_abs y
          have hh := Q'.neg_le_neg this
          exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv y)))
      (Q'.le_abs_self y)

end Q'

/-! ### Triangle split for four pieces -/

/-- Triangle-type split: `a ⊖ c ≈ (a ⊖ b) + (b ⊖ c)`. -/
theorem sub_split (a b c : Q') : (a + (-c)) ≈ ((a + (-b)) + (b + (-c))) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) (b + (-c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a ((-b) + (b + (-c))) (((-b) + b) + (-c))
      (Q'.eqv_symm (Q'.add_assoc_eqv (-b) b (-c)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (((-b) + b) + (-c)) ((0 : Q') + (-c))
      (Q'.add_eqv_congr_right ((-b) + b) 0 (-c) (Q'.neg_add_self_eqv b))) ?_
  exact Q'.add_eqv_congr_left a ((0 : Q') + (-c)) (-c) (Q'.eqv_of_eq (Q'.zero_add' (-c)))

/-- Reverse-triangle for a sum of two: `abs (u + v) ≤ abs u + abs v`. -/
theorem abs_add_le (u v : Q') : Q'.abs (u + v) ≤ Q'.abs u + Q'.abs v := by
  refine Q'.abs_le ?_ ?_
  · have hu : -(Q'.abs u) ≤ u := by
      have := Q'.neg_le_abs u
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv u))
    have hv : -(Q'.abs v) ≤ v := by
      have := Q'.neg_le_abs v
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv v))
    have hneg : (-(Q'.abs u + Q'.abs v)) ≈ ((-(Q'.abs u)) + (-(Q'.abs v))) :=
      Q'.neg_add_eqv (Q'.abs u) (Q'.abs v)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) ?_
    exact Q'.add_le_add hu hv
  · exact Q'.add_le_add (Q'.le_abs_self u) (Q'.le_abs_self v)

/-- Bound a four-term difference: if `z ⊖ w ≈ ((p1+p2)+p3)+p4` and each
`|pᵢ| ≤ Bᵢ`, then `|z ⊖ w| ≤ ((B1+B2)+B3)+B4`. -/
theorem abs_four_le {z w p1 p2 p3 p4 B1 B2 B3 B4 : Q'}
    (hsplit : (z + (-w)) ≈ (((p1 + p2) + p3) + p4))
    (h1 : Q'.abs p1 ≤ B1) (h2 : Q'.abs p2 ≤ B2)
    (h3 : Q'.abs p3 ≤ B3) (h4 : Q'.abs p4 ≤ B4) :
    Q'.abs (z + (-w)) ≤ ((B1 + B2) + B3) + B4 := by
  have hchain : Q'.abs (((p1 + p2) + p3) + p4)
      ≤ ((Q'.abs p1 + Q'.abs p2) + Q'.abs p3) + Q'.abs p4 := by
    refine Q'.le_trans' _ _ _ (abs_add_le ((p1 + p2) + p3) p4) ?_
    refine Q'.add_le_add_right _ _ (Q'.abs p4) ?_
    refine Q'.le_trans' _ _ _ (abs_add_le (p1 + p2) p3) ?_
    exact Q'.add_le_add_right _ _ (Q'.abs p3) (abs_add_le p1 p2)
  have habs_eqv : Q'.abs (z + (-w)) ≤ Q'.abs (((p1 + p2) + p3) + p4) :=
    Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)
  refine Q'.le_trans' _ _ _ habs_eqv (Q'.le_trans' _ _ _ hchain ?_)
  exact Q'.add_le_add (Q'.add_le_add (Q'.add_le_add h1 h2) h3) h4

/-! ## 1. The data-carrying finite-difference derivative `FDDerivData`

`FDDerivData f d θ` packages: `d` is the derivative of `f` at `θ`, witnessed by a
modulus `δ : Q' → Q'` (a `Type`-level function, Rule 8.3) such that whenever the
increment `h` satisfies `0 < |h| ≤ δ ε`, the cleared finite-difference bound

    |f (θ + h) ⊖ f θ ⊖ (d · h)| ≤ ε · |h|

holds.  This is Bishop's division-free derivative; the `ε·|h|` form avoids
dividing by `h` (undecidable nonvanishing) yet is equivalent to
`|(f(θ+h)−f(θ))/h − d| ≤ ε` whenever `h ≠ 0`. -/

/-- The cleared finite-difference remainder `f(θ+h) ⊖ f(θ) ⊖ d·h`. -/
def fdRem (f : Q' → Q') (d θ h : Q') : Q' :=
  ((f (θ + h)) + (-(f θ))) + (-(d * h))

/-- **Data-carrying finite-difference derivative.**  `d` is the derivative of `f`
at `θ`, with explicit modulus `δ`: for `0 < |h| ≤ δ ε`, the cleared remainder is
`≤ ε·|h|`.  `Type`-valued, so the modulus is recoverable data. -/
structure FDDerivData (f : Q' → Q') (d θ : Q') : Type where
  /-- The modulus: how small `|h|` must be to get the `ε`-remainder bound. -/
  δ : Q' → Q'
  /-- The modulus is positive for positive tolerance. -/
  δ_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < δ ε
  /-- The cleared finite-difference bound at increments within the modulus. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ δ ε →
    Q'.abs (fdRem f d θ h) ≤ ε * Q'.abs h

/-! ## 2. Pointwise / uniform convergence with modulus as data -/

/-- **Pointwise convergence with modulus.**  `M ↦ f M p` is within `ε` of `F p`
past stage `Nθ ε`. -/
structure PtwiseConvAt (f : Nat → Q' → Q') (F : Q' → Q') (p : Q') : Type where
  /-- The convergence modulus at the point `p`. -/
  Nθ : Q' → Nat
  /-- Past `Nθ ε`, `f M p` is within `ε` of `F p`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Nθ ε ≤ M →
    Q'.abs ((f M p) + (-(F p))) ≤ ε

/-- **Uniform convergence of derivatives.**  `M ↦ f' M θ` is within `ε` of `g θ`
past stage `Mg ε`, uniformly in any increment. -/
structure UnifDerivConvAt (f' : Nat → Q' → Q') (g : Q' → Q') (θ : Q') : Type where
  /-- The uniform derivative-convergence modulus. -/
  Mg : Q' → Nat
  /-- Past `Mg ε`, `f' M θ` is within `ε` of `g θ`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Mg ε ≤ M →
    Q'.abs ((f' M θ) + (-(g θ))) ≤ ε

/-! ## 3. THE C¹-LIMIT THEOREM (the reusable engine) -/

/-- The assembled engine hypotheses, bundled as `Type`-level data. -/
structure C1Inputs (f f' : Nat → Q' → Q') (F g : Q' → Q') (θ : Q') : Type where
  /-- Pointwise convergence of `f M` to `F` at the base point. -/
  ptθ : PtwiseConvAt f F θ
  /-- Pointwise convergence of `f M` to `F` at every perturbed point. -/
  ptθh : ∀ h : Q', PtwiseConvAt f F (θ + h)
  /-- Uniform convergence of the derivative family `f' M θ → g θ`. -/
  unif : UnifDerivConvAt f' g θ
  /-- A common finite-difference modulus `delStar` valid for all `f M` past stage `mStar`.
  (Equicontinuity of the family at `θ`.) -/
  delStar : Q' → Q'
  /-- `delStar` is positive for positive tolerance. -/
  delStar_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delStar ε
  /-- The stage past which the common modulus is valid. -/
  mStar : Q' → Nat
  /-- For `M ≥ mStar ε'`, `f M` has the cleared finite-difference bound with `delStar`. -/
  fdbound : ∀ ε' : Q', (0 : Q') < ε' → ∀ M : Nat, mStar ε' ≤ M →
    ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ delStar ε' →
      Q'.abs (fdRem (f M) (f' M θ) θ h) ≤ ε' * Q'.abs h

/-- **The generic six-atom telescoping identity** (pure abelian-group algebra).
With atoms `Fh, fMh, fM0, dMh, F0, ghh` (all in `Q'`):

    (Fh ⊖ F0) ⊖ ghh
      ≈ (((Fh ⊖ fMh) + ((fMh ⊖ fM0) ⊖ dMh)) + (fM0 ⊖ F0)) + (dMh ⊖ ghh).

The right side telescopes (`fMh`, `fM0`, `dMh` cancel pairwise) to the left.
Proved entirely over `Q'.eqv` rearrangers — no `set`, no `ring`. -/
theorem telescope6 (Fh fMh fM0 dMh F0 ghh : Q') :
    ((Fh + (-F0)) + (-ghh))
      ≈ ((((Fh + (-fMh)) + ((fMh + (-fM0)) + (-dMh))) + (fM0 + (-F0)))
          + (dMh + (-ghh))) := by
  -- Step 1: the first three blocks telescope to (Fh ⊖ F0) ⊖ dMh.
  have hsum123 :
      (((Fh + (-fMh)) + ((fMh + (-fM0)) + (-dMh))) + (fM0 + (-F0)))
        ≈ ((Fh + (-F0)) + (-dMh)) := by
    have e1 : ((Fh + (-fMh)) + ((fMh + (-fM0)) + (-dMh)))
        ≈ (Fh + ((-fMh) + ((fMh + (-fM0)) + (-dMh)))) :=
      Q'.add_assoc_eqv Fh (-fMh) ((fMh + (-fM0)) + (-dMh))
    have e2 : ((-fMh) + ((fMh + (-fM0)) + (-dMh)))
        ≈ ((-fMh) + (fMh + ((-fM0) + (-dMh)))) :=
      Q'.add_eqv_congr_left (-fMh) _ _ (Q'.add_assoc_eqv fMh (-fM0) (-dMh))
    have e3 : ((-fMh) + (fMh + ((-fM0) + (-dMh))))
        ≈ (((-fMh) + fMh) + ((-fM0) + (-dMh))) :=
      Q'.eqv_symm (Q'.add_assoc_eqv (-fMh) fMh ((-fM0) + (-dMh)))
    have e4 : (((-fMh) + fMh) + ((-fM0) + (-dMh)))
        ≈ ((-fM0) + (-dMh)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((-fMh) + fMh) 0 ((-fM0) + (-dMh))
          (Q'.neg_add_self_eqv fMh)) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' ((-fM0) + (-dMh)))
    have einner : ((-fMh) + ((fMh + (-fM0)) + (-dMh))) ≈ ((-fM0) + (-dMh)) :=
      Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 e4)
    have eA12 : ((Fh + (-fMh)) + ((fMh + (-fM0)) + (-dMh)))
        ≈ (Fh + ((-fM0) + (-dMh))) :=
      Q'.eqv_trans _ _ _ e1 (Q'.add_eqv_congr_left Fh _ _ einner)
    have eFull : (((Fh + (-fMh)) + ((fMh + (-fM0)) + (-dMh))) + (fM0 + (-F0)))
        ≈ ((Fh + ((-fM0) + (-dMh))) + (fM0 + (-F0))) :=
      Q'.add_eqv_congr_right _ _ (fM0 + (-F0)) eA12
    refine Q'.eqv_trans _ _ _ eFull ?_
    have r1 : ((Fh + ((-fM0) + (-dMh))) + (fM0 + (-F0)))
        ≈ (Fh + (((-fM0) + (-dMh)) + (fM0 + (-F0)))) :=
      Q'.add_assoc_eqv Fh ((-fM0) + (-dMh)) (fM0 + (-F0))
    refine Q'.eqv_trans _ _ _ r1 ?_
    have inner : (((-fM0) + (-dMh)) + (fM0 + (-F0)))
        ≈ ((-dMh) + (-F0)) := by
      have s1 : (((-fM0) + (-dMh)) + (fM0 + (-F0)))
          ≈ ((-fM0) + ((-dMh) + (fM0 + (-F0)))) :=
        Q'.add_assoc_eqv (-fM0) (-dMh) (fM0 + (-F0))
      have s2 : ((-dMh) + (fM0 + (-F0)))
          ≈ (((-dMh) + fM0) + (-F0)) :=
        Q'.eqv_symm (Q'.add_assoc_eqv (-dMh) fM0 (-F0))
      have s3 : (((-dMh) + fM0) + (-F0))
          ≈ ((fM0 + (-dMh)) + (-F0)) :=
        Q'.add_eqv_congr_right _ _ (-F0) (Q'.add_comm_eqv (-dMh) fM0)
      have s4 : ((fM0 + (-dMh)) + (-F0))
          ≈ (fM0 + ((-dMh) + (-F0))) :=
        Q'.add_assoc_eqv fM0 (-dMh) (-F0)
      have sinner : ((-dMh) + (fM0 + (-F0)))
          ≈ (fM0 + ((-dMh) + (-F0))) :=
        Q'.eqv_trans _ _ _ s2 (Q'.eqv_trans _ _ _ s3 s4)
      have s5 : ((-fM0) + ((-dMh) + (fM0 + (-F0))))
          ≈ ((-fM0) + (fM0 + ((-dMh) + (-F0)))) :=
        Q'.add_eqv_congr_left (-fM0) _ _ sinner
      have s6 : ((-fM0) + (fM0 + ((-dMh) + (-F0))))
          ≈ (((-fM0) + fM0) + ((-dMh) + (-F0))) :=
        Q'.eqv_symm (Q'.add_assoc_eqv (-fM0) fM0 ((-dMh) + (-F0)))
      have s7 : (((-fM0) + fM0) + ((-dMh) + (-F0)))
          ≈ ((-dMh) + (-F0)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right ((-fM0) + fM0) 0 ((-dMh) + (-F0))
            (Q'.neg_add_self_eqv fM0)) ?_
        exact Q'.eqv_of_eq (Q'.zero_add' ((-dMh) + (-F0)))
      exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s5 (Q'.eqv_trans _ _ _ s6 s7))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left Fh _ _ inner) ?_
    have t1 : (Fh + ((-dMh) + (-F0))) ≈ (Fh + ((-F0) + (-dMh))) :=
      Q'.add_eqv_congr_left Fh _ _ (Q'.add_comm_eqv (-dMh) (-F0))
    refine Q'.eqv_trans _ _ _ t1 ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv Fh (-F0) (-dMh))
  -- Step 2: glue the last block `(dMh ⊖ ghh)` and cancel `±dMh`.
  refine Q'.eqv_symm ?_
  have hRHS_eq :
      (((((Fh + (-fMh)) + ((fMh + (-fM0)) + (-dMh))) + (fM0 + (-F0)))
        + (dMh + (-ghh))))
      ≈ (((Fh + (-F0)) + (-dMh)) + (dMh + (-ghh))) :=
    Q'.add_eqv_congr_right _ _ (dMh + (-ghh)) hsum123
  refine Q'.eqv_trans _ _ _ hRHS_eq ?_
  have g1 : (((Fh + (-F0)) + (-dMh)) + (dMh + (-ghh)))
      ≈ ((Fh + (-F0)) + ((-dMh) + (dMh + (-ghh)))) :=
    Q'.add_assoc_eqv (Fh + (-F0)) (-dMh) (dMh + (-ghh))
  refine Q'.eqv_trans _ _ _ g1 ?_
  refine Q'.add_eqv_congr_left (Fh + (-F0)) _ _ ?_
  have g2 : ((-dMh) + (dMh + (-ghh)))
      ≈ (((-dMh) + dMh) + (-ghh)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (-dMh) dMh (-ghh))
  refine Q'.eqv_trans _ _ _ g2 ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 (-ghh) (Q'.neg_add_self_eqv dMh)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (-ghh))

/-- The four-piece telescoping identity for `F(θ+h) ⊖ F θ ⊖ (g θ)·h`, obtained
from `telescope6` by setting `dMh = f'_M θ·h`, `ghh = g θ·h`, and re-expanding the
last block to `(f'_M θ ⊖ g θ)·h`. -/
theorem fdRem_telescope (F : Q' → Q') (f f' : Nat → Q' → Q') (g : Q' → Q')
    (θ h : Q') (M : Nat) :
    (fdRem F (g θ) θ h) ≈
      ((( ((F (θ + h)) + (-(f M (θ + h))))
            + fdRem (f M) (f' M θ) θ h )
          + ((f M θ) + (-(F θ))))
        + ((f' M θ) + (-(g θ))) * h) := by
  -- the generic identity at the heat-kernel atoms, with last block dMh ⊖ ghh
  have hgen := telescope6 (F (θ + h)) (f M (θ + h)) (f M θ)
    ((f' M θ) * h) (F θ) ((g θ) * h)
  -- `fdRem F (g θ) θ h` is definitionally `((F(θ+h) + -F θ) + -(g θ·h))`, the LHS of hgen.
  -- `fdRem (f M) (f' M θ) θ h` is `((f_M(θ+h) + -f_M θ) + -(f'_M θ·h))`, the A2 of hgen.
  -- So hgen says fdRem F (g θ) θ h ≈ (((A1 + A2) + A3) + (f'_M θ·h ⊖ g θ·h)).
  -- We re-fold the last block (f'_M θ·h ⊖ g θ·h) into (f'_M θ ⊖ g θ)·h.
  refine Q'.eqv_trans _ _ _ hgen ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- (f'_M θ·h + -(g θ·h)) ≈ (f'_M θ + -g θ)·h
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (f' M θ) (-(g θ)) h) ?_
  exact Q'.add_eqv_congr_left ((f' M θ) * h) ((-(g θ)) * h) (-((g θ) * h))
    (Q'.neg_mul_eqv (g θ) h)

/-- `4·q ≈ ε` when `q = (1/2)·((1/2)·ε)`, and `(4q)·|h| ≈ ε·|h|` packaged as
`(((q·|h| + q·|h|) + q·|h|) + q·|h|) ≈ ε·|h|`. -/
theorem four_q_eqv (ε h : Q') :
    let q := HalfPow.half * (HalfPow.half * ε)
    (((q * Q'.abs h + q * Q'.abs h) + q * Q'.abs h) + q * Q'.abs h) ≈ (ε * Q'.abs h) := by
  intro q
  -- q + q = half·ε  (two_halves of (half·ε)? careful: q = half·(half·ε), q+q = half·ε)
  -- Actually two_halves a : half·a + half·a ≈ a, with a = half·ε gives
  --   half·(half·ε) + half·(half·ε) ≈ half·ε.
  have hqq : (q + q) ≈ (HalfPow.half * ε) := by
    show (HalfPow.half * (HalfPow.half * ε) + HalfPow.half * (HalfPow.half * ε))
        ≈ (HalfPow.half * ε)
    exact ExpNeg.two_halves (HalfPow.half * ε)
  have hqqqq : (((q + q) + q) + q) ≈ ε := by
    -- ((q+q)+q)+q ≈ (q+q)+(q+q) ≈ half·ε + half·ε ≈ ε
    have e1 : (((q + q) + q) + q) ≈ ((q + q) + (q + q)) :=
      Q'.add_assoc_eqv (q + q) q q
    refine Q'.eqv_trans _ _ _ e1 ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr hqq hqq) ?_
    exact ExpNeg.two_halves ε
  -- distribute |h|: (((q·|h|+q·|h|)+q·|h|)+q·|h|) ≈ ((((q+q)+q)+q))·|h| ≈ ε·|h|
  have hdist : (((q * Q'.abs h + q * Q'.abs h) + q * Q'.abs h) + q * Q'.abs h)
      ≈ ((((q + q) + q) + q) * Q'.abs h) := by
    -- repeatedly: a·c + b·c ≈ (a+b)·c
    have d1 : (q * Q'.abs h + q * Q'.abs h) ≈ ((q + q) * Q'.abs h) :=
      Q'.eqv_symm (Q'.add_mul_eqv q q (Q'.abs h))
    have d2 : ((q + q) * Q'.abs h + q * Q'.abs h) ≈ (((q + q) + q) * Q'.abs h) :=
      Q'.eqv_symm (Q'.add_mul_eqv (q + q) q (Q'.abs h))
    have d3 : ((((q + q) + q) * Q'.abs h) + q * Q'.abs h)
        ≈ ((((q + q) + q) + q) * Q'.abs h) :=
      Q'.eqv_symm (Q'.add_mul_eqv ((q + q) + q) q (Q'.abs h))
    -- chain (rewrite the deepest pair first, lifting through the outer +'s)
    -- ((A+A)+A)+A ≈ (((q+q)*|h| + A)+A) ≈ ... ≈ (((q+q)+q)+q)*|h|
    have c1 : (((q * Q'.abs h + q * Q'.abs h) + q * Q'.abs h) + q * Q'.abs h)
        ≈ ((((q + q) * Q'.abs h + q * Q'.abs h)) + q * Q'.abs h) :=
      Q'.add_eqv_congr_right _ _ (q * Q'.abs h)
        (Q'.add_eqv_congr_right _ _ (q * Q'.abs h) d1)
    have c2 : ((((q + q) * Q'.abs h + q * Q'.abs h)) + q * Q'.abs h)
        ≈ (((((q + q) + q) * Q'.abs h)) + q * Q'.abs h) :=
      Q'.add_eqv_congr_right _ _ (q * Q'.abs h) d2
    exact Q'.eqv_trans _ _ _ c1 (Q'.eqv_trans _ _ _ c2 d3)
  refine Q'.eqv_trans _ _ _ hdist ?_
  exact Q'.mul_eqv_congr_right _ _ (Q'.abs h) hqqqq

/-- **THE C¹-UNIFORM-LIMIT THEOREM (constructive, data-carrying, CLOSED).**

From `C1Inputs`, the pointwise limit `F` has finite-difference derivative `g θ` at
`θ`, with explicit modulus `δ ε := delStar (ε/4)`.  The proof is the four-piece
triangle estimate: pick `M` past `mStar(ε/4)`, the uniform derivative modulus
`Mg(ε/4)`, and the two pointwise moduli at scale `(ε/4)·|h|`; then the four pieces
are each `≤ (ε/4)·|h|`, summing to `ε·|h|`. -/
def fdDeriv_of_unif {f f' : Nat → Q' → Q'} {F g : Q' → Q'} {θ : Q'}
    (H : C1Inputs f f' F g θ) :
    FDDerivData F (g θ) θ where
  δ ε := H.delStar (HalfPow.half * (HalfPow.half * ε))
  δ_pos ε hε := H.delStar_pos _
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε))
  bound := by
    intro ε hε h hhpos hhle
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hqh_pos : (0 : Q') < q * Q'.abs h := Q'.mul_pos' hqpos hhpos
    -- choose the stage M past all four moduli
    let Mlevel : Nat :=
      max (H.mStar q)
        (max (H.unif.Mg q)
          (max ((H.ptθ).Nθ (q * Q'.abs h))
               ((H.ptθh h).Nθ (q * Q'.abs h))))
    have hMstar : H.mStar q ≤ Mlevel := Nat.le_max_left _ _
    have hMg : H.unif.Mg q ≤ Mlevel :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hNθ : (H.ptθ).Nθ (q * Q'.abs h) ≤ Mlevel :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)
    have hNθh : (H.ptθh h).Nθ (q * Q'.abs h) ≤ Mlevel :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)
    -- Piece 1: |F(θ+h) ⊖ f_M(θ+h)| ≤ q·|h|
    have hP1 : Q'.abs ((F (θ + h)) + (-(f Mlevel (θ + h)))) ≤ q * Q'.abs h := by
      have h0 := (H.ptθh h).conv (q * Q'.abs h) hqh_pos Mlevel hNθh
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_sub_comm (F (θ + h)) (f Mlevel (θ + h)))) h0
    -- Piece 2: the M-th finite-difference deriv
    have hP2 : Q'.abs (fdRem (f Mlevel) (f' Mlevel θ) θ h) ≤ q * Q'.abs h :=
      H.fdbound q hqpos Mlevel hMstar h hhpos hhle
    -- Piece 3: |f_M(θ) ⊖ F θ| ≤ q·|h|
    have hP3 : Q'.abs ((f Mlevel θ) + (-(F θ))) ≤ q * Q'.abs h :=
      (H.ptθ).conv (q * Q'.abs h) hqh_pos Mlevel hNθ
    -- Piece 4: |(f'_M θ ⊖ g θ)·h| ≤ q·|h|
    have hP4 : Q'.abs (((f' Mlevel θ) + (-(g θ))) * h) ≤ q * Q'.abs h := by
      have hdc := H.unif.conv q hqpos Mlevel hMg
      refine Q'.le_trans' _ _ _ (Q'.abs_mul_le ((f' Mlevel θ) + (-(g θ))) h) ?_
      exact Q'.mul_le_mul_of_nonneg_right _ _ _ hdc (Q'.abs_nonneg h)
    -- four-piece telescoping identity
    have hsplit := fdRem_telescope F f f' g θ h Mlevel
    -- rewrite fdRem F (g θ) θ h as the z ⊖ w form: z = F(θ+h), w = F θ + (g θ·h).
    -- fdRem F (g θ) θ h = (F(θ+h) + -F θ) + -(g θ·h) ≈ F(θ+h) + -(F θ + g θ·h).
    have hzw : (fdRem F (g θ) θ h) ≈ ((F (θ + h)) + (-((F θ) + (g θ) * h))) := by
      show (((F (θ + h)) + (-(F θ))) + (-((g θ) * h))) ≈ ((F (θ + h)) + (-((F θ) + (g θ) * h)))
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (F (θ + h)) (-(F θ)) (-((g θ) * h))) ?_
      exact Q'.add_eqv_congr_left (F (θ + h)) _ _ (Q'.eqv_symm (Q'.neg_add_eqv (F θ) ((g θ) * h)))
    -- combine hzw and hsplit to get the z⊖w split
    have hsplit' : ((F (θ + h)) + (-((F θ) + (g θ) * h)))
        ≈ ((( ((F (θ + h)) + (-(f Mlevel (θ + h))))
                + fdRem (f Mlevel) (f' Mlevel θ) θ h )
              + ((f Mlevel θ) + (-(F θ))))
            + ((f' Mlevel θ) + (-(g θ))) * h) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hzw) hsplit
    have hfour := abs_four_le (z := F (θ + h)) (w := (F θ) + ((g θ) * h))
      hsplit' hP1 hP2 hP3 hP4
    -- |F(θ+h) ⊖ (F θ + g θ·h)| ≤ ((q|h| + q|h|) + q|h|) + q|h| ≈ ε|h|
    -- transport back to |fdRem F (g θ) θ h|
    have hgoal : Q'.abs (fdRem F (g θ) θ h)
        ≤ (((q * Q'.abs h + q * Q'.abs h) + q * Q'.abs h) + q * Q'.abs h) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hzw)) hfour
    refine Q'.le_trans' _ _ _ hgoal ?_
    exact Q'.le_of_eqv (four_q_eqv ε h)

end YMGap.Continuum.TsumDeriv

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TsumDeriv.Q'.mul_pos'
#print axioms YMGap.Continuum.TsumDeriv.Q'.abs_eqv_congr
#print axioms YMGap.Continuum.TsumDeriv.Q'.abs_neg
#print axioms YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
#print axioms YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
#print axioms YMGap.Continuum.TsumDeriv.sub_split
#print axioms YMGap.Continuum.TsumDeriv.abs_add_le
#print axioms YMGap.Continuum.TsumDeriv.abs_four_le
#print axioms YMGap.Continuum.TsumDeriv.fdRem_telescope
#print axioms YMGap.Continuum.TsumDeriv.four_q_eqv
#print axioms YMGap.Continuum.TsumDeriv.fdDeriv_of_unif
