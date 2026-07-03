/-
# Finite-product finite-difference derivative (`FiniteProductFDDeriv`)

The C¹ product rule, iterated: if each factor `fk k` of a finite product
`pre (fun k => fk k ·) M` carries a data-carrying finite-difference derivative
(`FDDerivData`), then the whole product does, with the term-by-term
product-rule derivative value

    D(0)   = 0
    D(M+1) = D(M) · fk M θ  +  (∏_{k<M} fk k θ) · dk M.

This value `prodDeriv fk dk θ M` is the binary Leibniz sum: the recursion
distributes `fk M θ` into every earlier suffix.

## What is proved here (genuine, axiom-clean)

* `FDDerivData.const` — the constant function has derivative `0` (full proof).
* `abs_six_le` — a six-fold triangle bound (mirror of `TsumDeriv.abs_four_le`).
* `prodDeriv` — the recursive product-rule derivative value.
* `finiteProductFDDeriv` — the FULL finite-product induction, reducing the
  `M`-fold product derivative to `M` applications of the **binary**
  product-rule combinator, plus the `const` base case.  Proved completely by
  induction; both cases are definitionally well-typed (`pre_succ` on the
  function, the `prodDeriv` recursion on the value).

## The single honest residual

The binary combinator `FDDerivData.mul` itself — building a *new modulus* for
`f·g` (which needs division by a positive rational to split the `ε` budget
across the six remainder atoms and to kill the sole `O(h²)` cross term
`df·dg·h²`) — is packaged as the Type-level datum `MulCombinator`.  It is the
only analytic obligation the finite-product induction consumes; everything
scaffolding it (the six-atom triangle bound `abs_six_le`, the base combinator
`const`, the value recursion, the induction) is proved here.  No `sorry`,
no `admit`, no extra axioms.
-/
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.DiffProduct

namespace YMGap.Continuum.FiniteProductFDDeriv

open YMGap.Constructive
open YMGap.Continuum.TsumDeriv (fdRem FDDerivData abs_add_le)
open YMGap.Continuum.DiffProduct (pre pre_succ pre_zero)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The base combinator: constant function has derivative `0`. -/

/-- The constant function `fun _ => c` has finite-difference derivative `0` at
`θ`.  The cleared remainder `fdRem (fun _ => c) 0 θ h = (c ⊖ c) ⊖ (0·h) ≈ 0`,
so `|rem| = 0 ≤ ε·|h|` for any modulus (we pick `δ ≡ 1`). -/
def FDDerivData.const (c θ : Q') : FDDerivData (fun _ => c) 0 θ where
  δ := fun _ => 1
  δ_pos := fun _ _ => CReal.pos_of_num_pos (by decide)
  bound := fun ε hε h _hpos _hle => by
    -- fdRem (fun _ => c) 0 θ h  =  ((c + (-c)) + (-(0*h)))  ≈  0
    have hz : fdRem (fun _ => c) 0 θ h ≈ (0 : Q') := by
      show ((c + (-c)) + (-((0 : Q') * h))) ≈ (0 : Q')
      have e1 : (c + (-c)) ≈ (0 : Q') := Q'.add_neg_self_eqv c
      have e2 : (-((0 : Q') * h)) ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv h))
          (Q'.eqv_of_eq rfl)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' e1 e2) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' 0)
    -- |fdRem| ≈ |0| = 0 ≤ ε·|h|
    have habs0 : Q'.abs (fdRem (fun _ => c) 0 θ h) ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hz)
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv habs0) ?_
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt hε) (Q'.abs_nonneg h)

/-! ## 2. A six-fold triangle bound (mirror of `TsumDeriv.abs_four_le`). -/

/-- Bound a six-term difference: if `z ⊖ w ≈ (((((p1+p2)+p3)+p4)+p5)+p6)` and
each `|pᵢ| ≤ Bᵢ`, then `|z ⊖ w| ≤ (((((B1+B2)+B3)+B4)+B5)+B6)`.  Five nested
`abs_add_le`, exactly as `abs_four_le`. -/
theorem abs_six_le {z w p1 p2 p3 p4 p5 p6 B1 B2 B3 B4 B5 B6 : Q'}
    (hsplit : (z + (-w)) ≈ (((((p1 + p2) + p3) + p4) + p5) + p6))
    (h1 : Q'.abs p1 ≤ B1) (h2 : Q'.abs p2 ≤ B2) (h3 : Q'.abs p3 ≤ B3)
    (h4 : Q'.abs p4 ≤ B4) (h5 : Q'.abs p5 ≤ B5) (h6 : Q'.abs p6 ≤ B6) :
    Q'.abs (z + (-w)) ≤ (((((B1 + B2) + B3) + B4) + B5) + B6) := by
  have hchain : Q'.abs (((((p1 + p2) + p3) + p4) + p5) + p6)
      ≤ (((((Q'.abs p1 + Q'.abs p2) + Q'.abs p3) + Q'.abs p4) + Q'.abs p5)
          + Q'.abs p6) := by
    refine Q'.le_trans' _ _ _ (abs_add_le ((((p1 + p2) + p3) + p4) + p5) p6) ?_
    refine Q'.add_le_add_right _ _ (Q'.abs p6) ?_
    refine Q'.le_trans' _ _ _ (abs_add_le (((p1 + p2) + p3) + p4) p5) ?_
    refine Q'.add_le_add_right _ _ (Q'.abs p5) ?_
    refine Q'.le_trans' _ _ _ (abs_add_le ((p1 + p2) + p3) p4) ?_
    refine Q'.add_le_add_right _ _ (Q'.abs p4) ?_
    refine Q'.le_trans' _ _ _ (abs_add_le (p1 + p2) p3) ?_
    exact Q'.add_le_add_right _ _ (Q'.abs p3) (abs_add_le p1 p2)
  have habs_eqv : Q'.abs (z + (-w))
      ≤ Q'.abs (((((p1 + p2) + p3) + p4) + p5) + p6) :=
    Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)
  refine Q'.le_trans' _ _ _ habs_eqv (Q'.le_trans' _ _ _ hchain ?_)
  exact Q'.add_le_add
    (Q'.add_le_add (Q'.add_le_add (Q'.add_le_add (Q'.add_le_add h1 h2) h3) h4) h5)
    h6

/-! ## 3. The product-rule derivative value. -/

/-- The term-by-term product derivative value at `θ`.  The recursion
`D(M+1) = D(M)·fk M θ + (∏_{k<M} fk k θ)·dk M` is the binary Leibniz value:
`fk M θ` is distributed into every earlier suffix. -/
def prodDeriv (fk : Nat → Q' → Q') (dk : Nat → Q') (θ : Q') : Nat → Q'
  | 0     => 0
  | M + 1 => prodDeriv fk dk θ M * fk M θ + pre (fun k => fk k θ) M * dk M

@[simp] theorem prodDeriv_zero (fk : Nat → Q' → Q') (dk : Nat → Q') (θ : Q') :
    prodDeriv fk dk θ 0 = 0 := rfl

@[simp] theorem prodDeriv_succ (fk : Nat → Q' → Q') (dk : Nat → Q') (θ : Q')
    (M : Nat) :
    prodDeriv fk dk θ (M + 1)
      = prodDeriv fk dk θ M * fk M θ + pre (fun k => fk k θ) M * dk M := rfl

/-! ## 4. The binary product-rule combinator, as an honest Type-level residual.

Building `FDDerivData` for a *product* `f·g` needs a fresh, concrete modulus:
substituting `f(θ+h)=fθ+df·h+rf`, `g(θ+h)=gθ+dg·h+rg` into the product cleared
remainder yields exactly six atoms

    fθ·rg + gθ·rf + rf·rg + df·(h·rg) + dg·(h·rf) + df·dg·h²,

the last of which is `O(h²)`.  A modulus `δ ε = min (δf (η ε)) (δg (η ε))
(divPos (½ε) (1+|df·dg|)) 1` (all concrete rationals, no sup over `θ`) tames
the first five via `abs_six_le` and kills the cross term.  This binary builder
is the sole analytic obligation the finite-product induction below consumes;
we package it as `Type`-level data (Rule 8) rather than assert it. -/

/-- The binary finite-difference product-rule combinator, as consumed data.
A term of this type is exactly `FDDerivData.mul`: from per-factor derivatives it
produces the product derivative with the standard Leibniz value
`df·(g θ) + (f θ)·dg`. -/
structure MulCombinator : Type where
  /-- Product rule: `(f·g)' = f'·g + f·g'` at `θ`, as a modulus-carrying
  finite-difference derivative. -/
  mul : ∀ {f g : Q' → Q'} {df dg θ : Q'},
    FDDerivData f df θ → FDDerivData g dg θ →
    FDDerivData (fun t => f t * g t) (df * g θ + f θ * dg) θ

/-! ## 5. The finite-product induction (fully proved). -/

/-- **Iterated product rule.**  Given the binary combinator `C` and a
per-factor derivative family `Dk`, the finite product
`fun t => pre (fun k => fk k t) M` has finite-difference derivative
`prodDeriv fk dk θ M` at `θ`, for every `M`.

Both cases are definitionally well-typed:
* `M = 0`: `pre _ 0 ≡ 1` and `prodDeriv _ 0 ≡ 0`, so the goal is exactly
  `FDDerivData.const 1 θ`.
* `M+1`: `pre (fun k => fk k t) (M+1) ≡ pre (fun k => fk k t) M * fk M t`
  (`pre_succ`, defeq) and `prodDeriv _ (M+1) ≡ prodDeriv _ M * fk M θ +
  pre _ M * dk M` (defeq) is precisely `C.mul`'s value with
  `f := pre … M`, `g := fk M`, `df := prodDeriv … M`, `dg := dk M`. -/
def finiteProductFDDeriv (C : MulCombinator)
    {fk : Nat → Q' → Q'} {dk : Nat → Q'} {θ : Q'}
    (Dk : ∀ k, FDDerivData (fun t => fk k t) (dk k) θ) :
    ∀ M, FDDerivData (fun t => pre (fun k => fk k t) M) (prodDeriv fk dk θ M) θ
  | 0     => FDDerivData.const 1 θ
  | M + 1 => C.mul (finiteProductFDDeriv C Dk M) (Dk M)

end YMGap.Continuum.FiniteProductFDDeriv
