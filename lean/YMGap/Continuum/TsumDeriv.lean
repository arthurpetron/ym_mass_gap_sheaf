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

/-! ## 4. DERIVATIVE UNIQUENESS over `Q'` (Route A — the structural blocker fix)

The reason the differentiated-JTP residual stalls is that it tries to equate two
truncation SEQUENCES converging at different rates (`a^{(M+1)²}` vs `(a·a)^M`),
agreeing at no finite `M`.  The constructive fix is the CoRN-style
`Derivative_I_unique`: do NOT compare the sequences — instead observe that two
finite-difference derivatives of the SAME function `F` at the SAME point `θ` are
EQUAL.  This section builds that lemma over `Q'`, with NO uniformity needed (it is
purely per-`θ`): from `FDDerivData F d₁ θ` and `FDDerivData F d₂ θ` we get
`d₁ ≃ d₂`.

The proof is the short Bishop uniqueness argument.  The two cleared remainders
`fdRem F d₁ θ h` and `fdRem F d₂ θ h` differ by exactly `(d₂ − d₁)·h`
(the common `F(θ+h) − F θ` cancels), so for every `ε > 0` and every `h` past both
moduli, `|(d₁ − d₂)·h| ≤ 2ε·|h|`.  Cancelling the positive `|h|` gives
`|d₁ − d₂| ≤ 2ε` for all `ε > 0`, whence `d₁ ≃ d₂` by the Archimedean lemma. -/

namespace Q'

/-- **Multiplicative cancellation on the left** (local copy; the `TsumDeriv`
import chain does not reach `Sqrt.lean`).  `c·a ≤ c·b` and `0 < c` give `a ≤ b`,
through the `Int` cross-product representation. -/
theorem le_of_mul_le_mul_left {a b c : Q'} (h : c * a ≤ c * b) (hc : (0 : Q') < c) :
    a ≤ b := by
  have hh : (c * a).num * ((c * b).den : Int) ≤ (c * b).num * ((c * a).den : Int) := h
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  have hcn : 0 < c.num := CReal.num_pos_of_pos hc
  rw [show (c * a).num = c.num * a.num from rfl,
      show (c * b).num = c.num * b.num from rfl,
      Q'.mul_den_cast c b, Q'.mul_den_cast c a] at hh
  have hh2 : (c.num * (c.den : Int)) * (a.num * (b.den : Int))
           ≤ (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by
    have e1 : (c.num * a.num) * ((c.den : Int) * (b.den : Int))
            = (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
    have e2 : (c.num * b.num) * ((c.den : Int) * (a.den : Int))
            = (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
    rw [← e1, ← e2]; exact hh
  have hcc : 0 < c.num * (c.den : Int) :=
    Int.mul_pos hcn (by exact_mod_cast c.den_pos)
  exact Int.le_of_mul_le_mul_left hh2 hcc

/-- `half > 0`. -/
theorem half_pos : (0 : Q') < HalfPow.half := CReal.pos_of_num_pos (by decide)

/-- `abs q ≈ q` when `0 ≤ q` (the `if`-branch of `abs`). -/
theorem abs_of_nonneg {q : Q'} (hq : (0 : Q') ≤ q) : Q'.abs q ≈ q := by
  show Q'.abs q ≈ q
  unfold Q'.abs
  rw [if_pos hq]; exact Q'.eqv_refl q

/-- `¬ (p ≤ q) → q < p` (decidable trichotomy at the `Int`-num level). -/
theorem lt_of_not_le {p q : Q'} (h : ¬ (p ≤ q)) : q < p := by
  have hnum : ¬ (p.num * (q.den : Int) ≤ q.num * (p.den : Int)) := h
  show q.num * (p.den : Int) < p.num * (q.den : Int)
  exact Int.not_le.mp hnum

/-- `min p q ≤ p`. -/
theorem min_le_left' (p q : Q') : Q'.min' p q ≤ p := by
  show Q'.min' p q ≤ p
  unfold Q'.min'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact Q'.le_refl' p
  · rw [if_neg h]; exact Q'.le_of_lt (lt_of_not_le h)

/-- `min p q ≤ q`. -/
theorem min_le_right' (p q : Q') : Q'.min' p q ≤ q := by
  show Q'.min' p q ≤ q
  unfold Q'.min'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Q'.le_refl' q

/-- `0 < p → 0 < q → 0 < min p q`. -/
theorem lt_min' {p q : Q'} (hp : (0 : Q') < p) (hq : (0 : Q') < q) :
    (0 : Q') < Q'.min' p q := by
  show (0 : Q') < Q'.min' p q
  unfold Q'.min'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact hp
  · rw [if_neg h]; exact hq

/-- `¬(c ≤ 0) → 0 < c` over `Q'` (decidable trichotomy at the `Int`-num level). -/
theorem pos_of_not_nonpos {c : Q'} (h : ¬ (c ≤ (0 : Q'))) : (0 : Q') < c := by
  -- c ≤ 0  ↔  c.num * 1 ≤ 0 * c.den  ↔  c.num ≤ 0 ; ¬ of that is 0 < c.num ↔ 0 < c.
  have hnum : ¬ (c.num ≤ 0) := by
    intro hc
    apply h
    show c.num * ((0 : Q').den : Int) ≤ (0 : Q').num * (c.den : Int)
    have e1 : ((0 : Q').den : Int) = 1 := rfl
    have e2 : (0 : Q').num = 0 := rfl
    rw [e1, e2]; simpa using hc
  have : 0 < c.num := Int.not_le.mp hnum
  exact CReal.pos_of_num_pos this

/-- **The constructive Archimedean lemma over `Q'`.**  If `c ≤ ε` for EVERY
`ε > 0`, then `c ≤ 0`.  Decidable case split on `c ≤ 0`; in the `0 < c` branch,
instantiating at `ε = (1/2)·c` gives `c ≤ (1/2)·c`, i.e. `(1/2)·c ≤ 0`
(`c ≃ (1/2)c + (1/2)c`), contradicting `0 < (1/2)·c`. -/
theorem le_zero_of_le_all_pos {c : Q'} (h : ∀ ε : Q', (0 : Q') < ε → c ≤ ε) :
    c ≤ (0 : Q') := by
  by_cases hc : c ≤ (0 : Q')
  · exact hc
  · exfalso
    have hcpos : (0 : Q') < c := pos_of_not_nonpos hc
    have hhc : (0 : Q') < HalfPow.half * c := ExpNeg.half_mul_pos c hcpos
    have hle : c ≤ HalfPow.half * c := h (HalfPow.half * c) hhc
    -- c ≃ half·c + half·c, so c ≤ half·c gives half·c + half·c ≤ half·c, i.e. half·c ≤ 0.
    have hcc : (HalfPow.half * c + HalfPow.half * c) ≤ HalfPow.half * c :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves c)) hle
    -- subtract half·c: half·c ≤ 0
    have hsub : HalfPow.half * c ≤ (0 : Q') := by
      have hadd := Q'.add_le_add_right _ _ (-(HalfPow.half * c)) hcc
      -- (half·c + half·c) + (−half·c) ≤ half·c + (−half·c)
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.add_neg_self_eqv (HalfPow.half * c))))
      -- LHS ≃ half·c
      refine Q'.ge_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (HalfPow.half * c) (HalfPow.half * c) (-(HalfPow.half * c))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (HalfPow.half * c) _ _
          (Q'.add_neg_self_eqv (HalfPow.half * c))) ?_
      exact eqv_of_eq (Q'.add_zero' (HalfPow.half * c))
    -- 0 < half·c (hhc) and half·c ≤ 0 (hsub) ⟹ 0 < (half·c).num and (half·c).num ≤ 0 ⟹ False.
    have hposnum : 0 < (HalfPow.half * c).num := CReal.num_pos_of_pos hhc
    have hnonpos : (HalfPow.half * c).num ≤ 0 := by
      have hh : (HalfPow.half * c).num * ((0:Q').den : Int)
          ≤ (0:Q').num * ((HalfPow.half * c).den : Int) := hsub
      have e1 : ((0:Q').den : Int) = 1 := rfl
      have e2 : (0:Q').num = 0 := rfl
      rw [e1, e2] at hh; simpa using hh
    omega

/-- **`c ≃ 0` from `|c| ≤ ε` for all `ε > 0`.**  Both `c ≤ 0` and `−c ≤ 0`
follow from the Archimedean lemma applied to `|c|` (since `c ≤ |c|` and
`−c ≤ |c|`), giving `c ≃ 0`. -/
theorem eqv_zero_of_abs_le_all_pos {c : Q'}
    (h : ∀ ε : Q', (0 : Q') < ε → Q'.abs c ≤ ε) : c ≈ (0 : Q') := by
  have habs0 : Q'.abs c ≤ (0 : Q') := le_zero_of_le_all_pos h
  -- c ≤ |c| ≤ 0 and −c ≤ |c| ≤ 0, so c ≤ 0 and 0 ≤ c.
  have hcle : c ≤ (0 : Q') := Q'.le_trans' _ _ _ (Q'.le_abs_self c) habs0
  have hnegle : -c ≤ (0 : Q') := Q'.le_trans' _ _ _ (Q'.neg_le_abs c) habs0
  have hge : (0 : Q') ≤ c := by
    have h1 := Q'.neg_le_neg hnegle   -- −0 ≤ −(−c)
    have h2 : (0 : Q') ≤ -(-c) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (eqv_of_eq (by rfl : -(0:Q') = (0:Q'))))) h1
    exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.neg_neg_eqv c))
  exact Q'.eqv_of_le_le hcle hge

end Q'

/-- **The algebraic core** (arbitrary common block `A`):
`(A + −(d₂·h)) + −(A + −(d₁·h)) ≈ (d₁ − d₂)·h`. -/
theorem sub_rem_alg (A d₁ d₂ h : Q') :
    ((A + (-(d₂ * h))) + (-(A + (-(d₁ * h))))) ≈ ((d₁ + (-d₂)) * h) := by
  -- Step 1: −(A + −(d₁h)) ≈ (−A) + (d₁h)
  have hneg : (-(A + (-(d₁ * h)))) ≈ ((-A) + (d₁ * h)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv A (-(d₁ * h))) ?_
    exact Q'.add_eqv_congr_left (-A) _ _ (Q'.neg_neg_eqv (d₁ * h))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (A + (-(d₂ * h))) _ _ hneg) ?_
  -- (A + −(d₂h)) + ((−A) + (d₁h)) ≈ (d₁h) + (−(d₂h))  [cancel A]
  have hcancel : ((A + (-(d₂ * h))) + ((-A) + (d₁ * h)))
      ≈ ((d₁ * h) + (-(d₂ * h))) := by
    -- regroup to (A + −A) + (−(d₂h) + d₁h)
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv A (-(d₂ * h)) ((-A) + (d₁ * h))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left A _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-(d₂ * h)) (-A) (d₁ * h)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left A _ _
        (Q'.add_eqv_congr_right _ _ (d₁ * h) (Q'.add_comm_eqv (-(d₂ * h)) (-A)))) ?_
    -- A + (((−A) + −(d₂h)) + d₁h) ≈ (A + (−A)) + (−(d₂h) + d₁h)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left A _ _
        (Q'.add_assoc_eqv (-A) (-(d₂ * h)) (d₁ * h))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv A (-A) ((-(d₂ * h)) + (d₁ * h)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((-(d₂ * h)) + (d₁ * h)) (Q'.add_neg_self_eqv A)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' ((-(d₂ * h)) + (d₁ * h)))) ?_
    exact Q'.add_comm_eqv (-(d₂ * h)) (d₁ * h)
  refine Q'.eqv_trans _ _ _ hcancel ?_
  -- (d₁h) + −(d₂h) ≈ (d₁ + −d₂)·h
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv d₁ (-d₂) h) ?_
  exact Q'.add_eqv_congr_left (d₁ * h) _ _ (Q'.neg_mul_eqv d₂ h)

/-- **The difference of the two cleared remainders is `(d₁ − d₂)·h`.**
`fdRem F d₂ θ h ⊖ fdRem F d₁ θ h ≈ (d₁ − d₂)·h` — the common `F(θ+h) − F θ`
telescopes away.  Definitional unfold of `fdRem` then `sub_rem_alg`. -/
theorem fdRem_sub (F : Q' → Q') (d₁ d₂ θ h : Q') :
    ((fdRem F d₂ θ h) + (-(fdRem F d₁ θ h))) ≈ ((d₁ + (-d₂)) * h) :=
  sub_rem_alg ((F (θ + h)) + (-(F θ))) d₁ d₂ h

/-- **DERIVATIVE UNIQUENESS (constructive, `Q'`-level, per-`θ`, no uniformity).**
Two finite-difference derivatives of the SAME function `F` at the SAME point `θ`
are equal: `FDDerivData F d₁ θ → FDDerivData F d₂ θ → d₁ ≃ d₂`.

This is the CoRN `Derivative_I_unique` analogue.  It needs only the per-`θ`
`FDDerivData` (NO uniform modulus): pick any `ε > 0` and any nonzero `h` past both
moduli `D₁.δ ε`, `D₂.δ ε`; then `(d₁−d₂)·h = fdRem F d₂ ⊖ fdRem F d₁`
(`fdRem_sub`), so `|(d₁−d₂)·h| ≤ |fdRem F d₂| + |fdRem F d₁| ≤ ε|h| + ε|h|`.
Cancelling `|h|` (`|c·h| = |c|·|h|`, `|h| > 0`) gives `|d₁−d₂| ≤ ε + ε = 2ε`, for
every `ε`, hence `d₁ ≃ d₂` (Archimedean). -/
theorem fdDeriv_unique {F : Q' → Q'} {d₁ d₂ θ : Q'}
    (D₁ : FDDerivData F d₁ θ) (D₂ : FDDerivData F d₂ θ) : d₁ ≈ d₂ := by
  -- It suffices: |d₁ − d₂| ≤ ε for all ε > 0  (Archimedean ⟹ d₁−d₂ ≃ 0 ⟹ d₁ ≃ d₂).
  have hkey : ∀ ε : Q', (0 : Q') < ε → Q'.abs (d₁ + (-d₂)) ≤ ε := by
    intro ε hε
    -- work at tolerance ε' = (1/2)·ε on each remainder; pick h = min of the two moduli.
    have hε' : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    -- a concrete nonzero increment h within both moduli: h = min(δ₁ ε', δ₂ ε')
    let δ₁ := D₁.δ (HalfPow.half * ε)
    let δ₂ := D₂.δ (HalfPow.half * ε)
    have hδ₁ : (0 : Q') < δ₁ := D₁.δ_pos _ hε'
    have hδ₂ : (0 : Q') < δ₂ := D₂.δ_pos _ hε'
    let h : Q' := Q'.min' δ₁ δ₂
    have hhpos : (0 : Q') < h := Q'.lt_min' hδ₁ hδ₂
    have hh_abs_pos : (0 : Q') < Q'.abs h := by
      show (0 : Q') < Q'.abs h
      unfold Q'.abs; rw [if_pos (Q'.le_of_lt hhpos)]; exact hhpos
    have habsh_eqv : Q'.abs h ≈ h := Q'.abs_of_nonneg (Q'.le_of_lt hhpos)
    have hhle₁ : Q'.abs h ≤ δ₁ :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv habsh_eqv) (Q'.min_le_left' δ₁ δ₂)
    have hhle₂ : Q'.abs h ≤ δ₂ :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv habsh_eqv) (Q'.min_le_right' δ₁ δ₂)
    -- the two remainder bounds
    have hb₁ : Q'.abs (fdRem F d₁ θ h) ≤ (HalfPow.half * ε) * Q'.abs h :=
      D₁.bound _ hε' h hh_abs_pos hhle₁
    have hb₂ : Q'.abs (fdRem F d₂ θ h) ≤ (HalfPow.half * ε) * Q'.abs h :=
      D₂.bound _ hε' h hh_abs_pos hhle₂
    -- |(d₁−d₂)·h| ≤ |fdRem F d₂| + |fdRem F d₁| ≤ 2·(½ε)·|h| = ε·|h|
    have hsub := fdRem_sub F d₁ d₂ θ h
    have htri : Q'.abs ((d₁ + (-d₂)) * h)
        ≤ Q'.abs (fdRem F d₂ θ h) + Q'.abs (fdRem F d₁ θ h) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hsub))) ?_
      refine Q'.le_trans' _ _ _ (abs_add_le (fdRem F d₂ θ h) (-(fdRem F d₁ θ h))) ?_
      exact Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (Q'.abs_neg (fdRem F d₁ θ h)))
    have hbound : Q'.abs ((d₁ + (-d₂)) * h) ≤ ε * Q'.abs h := by
      refine Q'.le_trans' _ _ _ htri ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hb₂ hb₁) ?_
      -- (½ε)|h| + (½ε)|h| ≈ ε|h|
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr (Q'.mul_comm_eqv (HalfPow.half * ε) (Q'.abs h))
          (Q'.mul_comm_eqv (HalfPow.half * ε) (Q'.abs h))) ?_
      -- |h|·(½ε) + |h|·(½ε) ≈ |h|·(½ε+½ε) ≈ |h|·ε ≈ ε·|h|
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv (Q'.abs h) (HalfPow.half * ε) (HalfPow.half * ε))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.abs h) _ _ (ExpNeg.two_halves ε)) ?_
      exact Q'.mul_comm_eqv (Q'.abs h) ε
    -- Now cancel |h| via the SIGNED route (no abs_mul): bound c·h and (−c)·h by ε·|h|,
    -- rewrite |h| ≈ h, cancel h > 0, get c ≤ ε and −c ≤ ε ⟹ |c| ≤ ε.
    let c : Q' := d₁ + (-d₂)
    -- c·h ≤ |c·h| ≤ ε·|h| ≈ ε·h
    have hεh : ε * Q'.abs h ≈ ε * h := Q'.mul_eqv_congr_left ε _ _ habsh_eqv
    have hch_le : c * h ≤ ε * h :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self (c * h))
        (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hεh))
    -- −(c·h) ≤ |c·h| ≤ ε·h, and −(c·h) ≈ (−c)·h
    have hnegch_le : (-c) * h ≤ ε * h := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_mul_eqv c h)) ?_
      exact Q'.le_trans' _ _ _ (Q'.neg_le_abs (c * h))
        (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hεh))
    -- cancel h > 0 (commute to h·· form): c ≤ ε and −c ≤ ε
    have hc_le : c ≤ ε := by
      refine Q'.le_of_mul_le_mul_left (c := h) ?_ hhpos
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv h c)) ?_
      exact Q'.le_trans' _ _ _ hch_le (Q'.le_of_eqv (Q'.mul_comm_eqv ε h))
    have hnegc_le : -c ≤ ε := by
      refine Q'.le_of_mul_le_mul_left (c := h) ?_ hhpos
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv h (-c))) ?_
      exact Q'.le_trans' _ _ _ hnegch_le (Q'.le_of_eqv (Q'.mul_comm_eqv ε h))
    -- −ε ≤ c from −c ≤ ε
    have hge : -ε ≤ c := by
      have h1 := Q'.neg_le_neg hnegc_le   -- −ε ≤ −(−c)
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.neg_neg_eqv c))
    exact Q'.abs_le hge hc_le
  -- Archimedean ⟹ d₁ − d₂ ≃ 0 ⟹ d₁ ≃ d₂.
  have hz : (d₁ + (-d₂)) ≈ (0 : Q') := Q'.eqv_zero_of_abs_le_all_pos hkey
  -- d₁ ≈ d₂ from d₁ − d₂ ≈ 0
  have : (d₁ + (-d₂)) + d₂ ≈ (0 : Q') + d₂ := Q'.add_eqv_congr_right _ _ d₂ hz
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm ?_) (Q'.eqv_trans _ _ _ this ?_)
  · -- (d₁ + −d₂) + d₂ ≈ d₁ : regroup to d₁ + (−d₂ + d₂) ≈ d₁ + 0 ≈ d₁.
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv d₁ (-d₂) d₂) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left d₁ _ _ (Q'.neg_add_self_eqv d₂)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' d₁)
  · -- 0 + d₂ ≈ d₂
    exact Q'.eqv_of_eq (Q'.zero_add' d₂)

end YMGap.Continuum.TsumDeriv

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TsumDeriv.Q'.mul_pos'
#print axioms YMGap.Continuum.TsumDeriv.Q'.le_of_mul_le_mul_left
#print axioms YMGap.Continuum.TsumDeriv.Q'.le_zero_of_le_all_pos
#print axioms YMGap.Continuum.TsumDeriv.Q'.eqv_zero_of_abs_le_all_pos
#print axioms YMGap.Continuum.TsumDeriv.fdRem_sub
#print axioms YMGap.Continuum.TsumDeriv.fdDeriv_unique
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
