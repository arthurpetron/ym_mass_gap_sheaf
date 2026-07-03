/-
# Closing the `Dk` leaf of `Wall2FinalResiduals` (the `Q'`-layer Jacobi factor
  finite-difference derivative)

`Wall2FinalResiduals.Dk : ∀ k, FDDerivData (fun t => fk k t) (dk k) x` is, at the
`Q'` layer, instantiated with

    fk k = fun t => JTPInstance.jFac a k t        -- the k-th Jacobi factor in c = cos 2θ
    dk k = JTPInstance.amp a k + JTPInstance.amp a k    -- its rational c-slope 2·a^{2k+1}

Both are **rational-valued** (`Nat → Q' → Q'`, `Nat → Q'`).  At that layer the
working point `x` is the Chebyshev/cos variable `c`, and

    jFac a k c = 1 + ((A + A)·c + A·A),        A = amp a k = a^{2k+1}

is a genuine degree-1 (**affine**) polynomial in `c` with slope `b = A + A`.  For an
affine `f` with `d` its slope, the cleared finite-difference remainder

    fdRem f d x h = (f (x+h)) ⊖ (f x) ⊖ (d·h)

is **identically ≈ 0** by pure `Q'` ring cancellation (the constant `1 + A·A` cancels
in `f(x+h) ⊖ f(x)`).  There is NO quadratic bound, NO cos second-difference, and NO
`fddOfQuadBound` analog at this layer: those live at the CReal / angle-variable factor
whose value is the transcendental `−4·A·sin 2θ`, correctly type-mismatched against the
`Q'`-layer `Dk` and NOT routed here (see `JacobiFactorFDDeriv.fddOfQuadBound`).

## What is GENUINELY closed here

* `affine_fd_cancel` — the pure `Q'` ring identity: for any constant term `e₀`, slope
  `b`, constant `C₁`, the affine finite difference cancels to the slope times the
  increment:  `(e₀ + (b·(x+h) + C₁)) ⊖ (e₀ + (b·x + C₁)) ≈ b·h`.  (Mirror of
  `ThetaFDDerivAssembly.linFDDerivData`'s `hcancel`, wrapped by the cancelling
  constants `e₀`, `C₁`.)
* `jacFdRem_vanishes` — the whole analytic content of the leaf: the Jacobi-factor
  cleared remainder is `≈ 0`, unconditionally in `x` (a ring fact; needs neither
  `-1 ≤ x` nor `x ≤ 1`).
* `jacFDDerivData` — the per-factor witness: the degenerate `fddOfQuadBound` analog
  with FLAT modulus `δ ≡ 1` and remainder exactly `0`.  The flat, `k`-independent
  modulus is exactly what the downstream uniform product modulus (`Huni`) wants.
* `dkProducer` — the leaf itself, matching `Wall2FinalResiduals.Dk` (with `q := a`).

## Honesty flag (belongs to leaf 6, NOT to `Dk`)

`dk k = 2·a^{2k+1}` is the **c-slope** `d/dc jFac`, NOT the θ-derivative
`jDeriv a k s = −(4·A)·sin 2θ` (transcendental, could never inhabit `dk : Nat → Q'`).
The chain-rule factor `−2 sin 2θ` and the reconciliation to `Rhalf = (½)·Θ·S` are
absorbed at the CReal identity crux `Hdconv` (leaf 6), NOT here.  So `dkProducer` is
the correct self-contained closure of the `Dk` leaf **in isolation**.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused helpers).  No
`Classical.*`, no `native_decide`, no `sorry`, no custom axiom.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.JTPInstance
import YMGap.Constructive.Reals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.DkProducerClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv (fdRem FDDerivData)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The pure `Q'` ring identity: affine finite differences cancel.

For any constant term `e₀`, slope `b`, and constant `C₁`, the cleared finite
difference of the affine map `t ↦ e₀ + (b·t + C₁)` equals the slope times the
increment.  This is exactly `linFDDerivData`'s `hcancel`, wrapped by the two
cancelling constants `e₀` and `C₁`. -/

theorem affine_fd_cancel (e0 b C1 x h : Q') :
    ((e0 + (b * (x + h) + C1)) + (-(e0 + (b * x + C1)))) ≈ (b * h) := by
  -- distribute the increment inside the perturbed value
  have hd : (b * (x + h)) ≈ ((b * x) + (b * h)) := Q'.mul_add_eqv b x h
  have h1 : ((b * (x + h)) + C1) ≈ (((b * x) + (b * h)) + C1) :=
    Q'.add_eqv_congr_right _ _ C1 hd
  have h2 : (e0 + ((b * (x + h)) + C1)) ≈ (e0 + (((b * x) + (b * h)) + C1)) :=
    Q'.add_eqv_congr_left e0 _ _ h1
  -- rearrange the inner sum: ((b·x)+(b·h))+C₁ ≈ ((b·x)+C₁)+(b·h)
  have hinner : (((b * x) + (b * h)) + C1) ≈ (((b * x) + C1) + (b * h)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (b * x) (b * h) C1) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (b * x) _ _ (Q'.add_comm_eqv (b * h) C1)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (b * x) C1 (b * h))
  have h3 : (e0 + (((b * x) + (b * h)) + C1)) ≈ (e0 + (((b * x) + C1) + (b * h))) :=
    Q'.add_eqv_congr_left e0 _ _ hinner
  -- pull the increment out to the top level: ≈ (e₀ + (b·x + C₁)) + b·h
  have h4 : (e0 + (((b * x) + C1) + (b * h))) ≈ ((e0 + ((b * x) + C1)) + (b * h)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv e0 ((b * x) + C1) (b * h))
  have lhsA : (e0 + ((b * (x + h)) + C1)) ≈ ((e0 + ((b * x) + C1)) + (b * h)) :=
    Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3 h4)
  -- subtract the base value; the constant `e₀ + (b·x + C₁)` cancels (linFDDerivData tail)
  have g1 :
      ((e0 + ((b * (x + h)) + C1)) + (-(e0 + ((b * x) + C1)))) ≈
        (((e0 + ((b * x) + C1)) + (b * h)) + (-(e0 + ((b * x) + C1)))) :=
    Q'.add_eqv_congr_right _ _ (-(e0 + ((b * x) + C1))) lhsA
  -- (w + b·h) + (−w) ≈ b·h    (w := e₀ + (b·x + C₁))
  have tail :
      (((e0 + ((b * x) + C1)) + (b * h)) + (-(e0 + ((b * x) + C1)))) ≈ (b * h) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(e0 + ((b * x) + C1)))
        (Q'.add_comm_eqv (e0 + ((b * x) + C1)) (b * h))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (b * h) (e0 + ((b * x) + C1)) (-(e0 + ((b * x) + C1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (b * h) _ _ (Q'.add_neg_self_eqv (e0 + ((b * x) + C1)))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (b * h))
  exact Q'.eqv_trans _ _ _ g1 tail

/-! ## 2. The leaf's analytic content: the Jacobi-factor cleared remainder vanishes.

`jFac q k c = 1 + ((amp q k + amp q k)·c + amp q k · amp q k)` unfolds by `def` to
the affine form; instantiate `affine_fd_cancel` at `e₀ := 1`, `C₁ := amp·amp`,
`b := amp + amp`.  Unconditional in `x`. -/

theorem jacFdRem_vanishes (q : Q') (k : Nat) (x h : Q') :
    fdRem (fun t => JTPInstance.jFac q k t)
      (JTPInstance.amp q k + JTPInstance.amp q k) x h ≈ (0 : Q') := by
  -- fdRem f d x h = ((f (x+h)) + (-(f x))) + (-(d·h)); unfold `jFac` (def) to the affine form
  show (((1 + ((JTPInstance.amp q k + JTPInstance.amp q k) * (x + h)
              + JTPInstance.amp q k * JTPInstance.amp q k))
          + (-(1 + ((JTPInstance.amp q k + JTPInstance.amp q k) * x
              + JTPInstance.amp q k * JTPInstance.amp q k))))
        + (-((JTPInstance.amp q k + JTPInstance.amp q k) * h))) ≈ (0 : Q')
  -- the bracketed difference ≈ b·h by the affine cancellation
  have hcancel :
      ((1 + ((JTPInstance.amp q k + JTPInstance.amp q k) * (x + h)
              + JTPInstance.amp q k * JTPInstance.amp q k))
          + (-(1 + ((JTPInstance.amp q k + JTPInstance.amp q k) * x
              + JTPInstance.amp q k * JTPInstance.amp q k)))) ≈
        ((JTPInstance.amp q k + JTPInstance.amp q k) * h) :=
    affine_fd_cancel 1 (JTPInstance.amp q k + JTPInstance.amp q k)
      (JTPInstance.amp q k * JTPInstance.amp q k) x h
  -- remainder ≈ (b·h) + (−(b·h)) ≈ 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-((JTPInstance.amp q k + JTPInstance.amp q k) * h)) hcancel) ?_
  exact Q'.add_neg_self_eqv ((JTPInstance.amp q k + JTPInstance.amp q k) * h)

/-! ## 3. The per-factor `FDDerivData` witness (degenerate `fddOfQuadBound` analog).

FLAT modulus `δ ≡ 1`, remainder exactly `0`.  The `bound` field is byte-for-byte the
`bound` of `FiniteProductFDDeriv.FDDerivData.const` / `linFDDerivData`, with
`jacFdRem_vanishes` in place of the inline zero-remainder proof. -/

def jacFDDerivData (q : Q') (k : Nat) (x : Q') :
    FDDerivData (fun t => JTPInstance.jFac q k t)
      (JTPInstance.amp q k + JTPInstance.amp q k) x where
  δ := fun _ => 1
  δ_pos := fun _ _ => CReal.pos_of_num_pos (by decide)
  bound := fun ε hε h _ _ => by
    -- |fdRem| ≈ |0| = 0 ≤ ε·|h|
    have habs0 :
        Q'.abs (fdRem (fun t => JTPInstance.jFac q k t)
          (JTPInstance.amp q k + JTPInstance.amp q k) x h) ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_eqv_congr (jacFdRem_vanishes q k x h))
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv habs0) ?_
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt hε) (Q'.abs_nonneg h)

/-! ## 4. The leaf producer, matching `Wall2FinalResiduals.Dk` (with `q := a`).

`Dk : ∀ k, FDDerivData (fun t => JTPInstance.jFac a k t) (JTPInstance.amp a k +
JTPInstance.amp a k) x`.  Both the function family and the derivative-value family
unify definitionally with `jacFDDerivData`'s output type.  The positivity hypothesis
`ha0 : 0 < a` is carried for interface uniformity with the upstream field (the leaf is
in fact unconditional). -/

def dkProducer {a : Q'} (_ha0 : (0 : Q') < a) (x : Q') :
    ∀ k, FDDerivData (fun t => JTPInstance.jFac a k t)
      (JTPInstance.amp a k + JTPInstance.amp a k) x :=
  fun k => jacFDDerivData a k x

/-! ## 5. Non-vacuity: the producer fires at a concrete point. -/

/-- Sanity check that `dkProducer` is inhabited (non-vacuous): instantiate at `a := 1`
(so `0 < a`), point `x := 0`, factor index `k := 3`. -/
example : FDDerivData (fun t => JTPInstance.jFac (1 : Q') 3 t)
    (JTPInstance.amp (1 : Q') 3 + JTPInstance.amp (1 : Q') 3) 0 :=
  dkProducer (a := (1 : Q')) (CReal.pos_of_num_pos (by decide)) 0 3

#print axioms dkProducer

end YMGap.Continuum.DkProducerClose
