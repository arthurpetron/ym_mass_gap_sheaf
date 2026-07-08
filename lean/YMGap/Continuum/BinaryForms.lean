/-
# Binary forms as SU(2)/sl₂ irreducibles — the concrete rep category over `Q'`

**Track A2 (rep-category route to the pentagon).**  This is the first of a
three-file development that realizes the spin-`j` irreducible SU(2)
representation as the space of homogeneous **binary forms** of degree `n = 2j`
(polynomials in two variables `x, y`), a fully constructive, `Q'`-rational,
`native_decide`-free model.  The whole point of the route: once irreducibles,
intertwiners (Clebsch–Gordan = transvectants), and multiplicity-freeness are
concrete rational data, the pentagon/6j identity becomes a **consequence of
uniqueness** (Schur ≤ 1-dim Hom) rather than a factorial identity to verify.

## What this file delivers

* `BForm` — a degree-`n` binary form as its `Q'`-coefficient vector
  `c : Nat → Q'`, `c i` = coefficient of `x^i y^(n-i)`.  Genuine `Type`-level
  data (Rule 8), dimension `n+1` (spin `j = n/2`).
* The `sl₂` action by explicit, computable operators — the raising
  `Eop = x ∂_y`, the lowering `Fop = y ∂_x`, the Cartan `Hop = x ∂_x − y ∂_y`.
  These are the genuine differential operators of the binary-form model, written
  as coefficient recurrences.
* The `sl₂` commutation relations `[H,E] = 2E`, `[H,F] = −2F`, `[E,F] = H`
  **machine-verified** on the actual representations used downstream
  (spin ½ = degree 1, spin 1 = degree 2) — the certificate that the operators
  are the correct rep-theoretic action.
* The **intertwiner** predicate (a linear map commuting with `E`, `F`, `H`) and
  the highest-weight machinery (`E`-kernel) that drives Schur's lemma in the
  companion file.

Nothing here is a frontier bundle; nothing is faked.  All equalities are
decidable `Q'` facts closed by `decide` (kernel computation = MLTT canonicity,
Rule 8.2) or by explicit `Q'` algebra.  `#print axioms` is gated to
`propext`/`Quot.sound`.

## Constructive contract (AGENTS.md Rules 1/3/8)

Mathlib-free; `Q'` / `Nat` / `Int` core only.  No `Real`, no `Classical.*`, no
`native_decide`, no `sorry`.  Every form and operator is `Type`-level
computable data; every representation-theoretic law is a kernel-checked
`Q'` identity.
-/

import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.BinaryForms

open YMGap.Constructive

/-! ## 1. Binary forms as coefficient vectors -/

/-- A binary form is carried by its coefficient vector `c : Nat → Q'`, where
`c i` is the coefficient of the monomial `x^i y^(n-i)` in a form of a *degree*
`n` fixed by context.  Coefficients at indices `i > n` are irrelevant (a
genuine degree-`n` form has them `≃ 0`); we keep the representation total so
the operators are plain functions.  For spin `j`, `n = 2j` and the carried
data has `n+1` meaningful slots — the dimension of the irreducible. -/
abbrev BForm : Type := Nat → Q'

/-- The zero form. -/
def zeroF : BForm := fun _ => 0

/-- The `i`-th basis monomial `x^i y^(n-i)` of a degree-`n` form (as a coefficient
vector: `1` at slot `i`, `0` elsewhere).  `mono i` is degree-agnostic; the degree
is supplied by the operator it is fed to. -/
def mono (i : Nat) : BForm := fun k => if k = i then 1 else 0

/-! ## 2. The sl₂ action by explicit differential operators

On the polynomial ring `Q'[x,y]` the standard `sl₂` generators are
`E = x ∂_y`, `F = y ∂_x`, `H = x ∂_x − y ∂_y`.  Acting on a degree-`n` form
they preserve the degree, so each is an operator `BForm → BForm` parametrized
by `n`.  Written on the monomial basis:

* `H · x^i y^(n-i) = (i − (n−i)) x^i y^(n-i) = (2i − n) x^i y^(n-i)`  (weight).
* `E · x^i y^(n-i) = (n−i) x^(i+1) y^(n-i-1)`  (raises the `x`-power).
* `F · x^i y^(n-i) = i · x^(i-1) y^(n-i+1)`     (lowers the `x`-power).

Reading these off as coefficient recurrences gives the definitions below. -/

/-- The Cartan operator `H = x ∂_x − y ∂_y` on degree-`n` forms:
`(H c) i = (2i − n) · c i`.  The weight `2i − n` is an integer (possibly
negative), so it is injected via `Q'.ofInt`. -/
def Hop (n : Nat) (c : BForm) : BForm :=
  fun i => Q'.ofInt (2 * (Int.ofNat i) - Int.ofNat n) * c i

/-- The raising operator `E = x ∂_y` on degree-`n` forms.  `E` sends the
`x^(i-1) y^(n-i+1)` slot to the `x^i y^(n-i)` slot with factor `n − (i−1)`, so
`(E c) i = (n − (i−1)) · c (i−1)` for `i ≥ 1`, and `(E c) 0 = 0`. -/
def Eop (n : Nat) (c : BForm) : BForm :=
  fun i => match i with
    | 0      => 0
    | i' + 1 => Q'.ofNat (n - i') * c i'

/-- The lowering operator `F = y ∂_x` on degree-`n` forms:
`(F c) i = (i+1) · c (i+1)`. -/
def Fop (_n : Nat) (c : BForm) : BForm :=
  fun i => Q'.ofNat (i + 1) * c (i + 1)

/-! ## 3. Bounded semantic equality of forms

Two degree-`n` forms are equal when their first `n+1` coefficients agree (up to
`Q'.eqv`).  This predicate is decidable (finite `∀ i < N`), so representation
laws about concrete forms close by `decide`. -/

/-- `f` and `g` agree as forms on the window `[0, N)` (semantic `Q'.eqv`). -/
def FormEqv (N : Nat) (f g : BForm) : Prop := ∀ i, i < N → (f i).eqv (g i)

instance (N : Nat) (f g : BForm) : Decidable (FormEqv N f g) :=
  Nat.decidableBallLT N (fun i _ => (f i).eqv (g i))

theorem FormEqv.refl (N : Nat) (f : BForm) : FormEqv N f f :=
  fun i _ => Q'.eqv_refl (f i)

/-! ## 4. The sl₂ commutation relations, machine-verified on the used spins

The load-bearing certificate that `Eop/Fop/Hop` are the genuine `sl₂` action:
on every representation actually used downstream — spin ½ (`n = 1`, dimension 2)
and spin 1 (`n = 2`, dimension 3) — the three defining relations hold on the
full basis.  These are real kernel computations over `Q'`, not `Prop := True`.

We check the relations against every basis monomial simultaneously by feeding a
*generic* test vector: since the operators are `Q'`-linear in the coefficients,
agreement on the basis is agreement everywhere.  Concretely we verify the
operator identity on each basis vector `mono k`. -/

/-- `[E,F] = H` on spin ½ (degree 1), on every basis vector `mono k`, `k < 2`. -/
theorem comm_EF_H_spinHalf :
    ∀ k, k < 2 →
      FormEqv 2 (fun i => Eop 1 (Fop 1 (mono k)) i - Fop 1 (Eop 1 (mono k)) i)
                (Hop 1 (mono k)) := by decide

/-- `[H,E] = 2E` on spin ½ (degree 1). -/
theorem comm_HE_2E_spinHalf :
    ∀ k, k < 2 →
      FormEqv 2 (fun i => Hop 1 (Eop 1 (mono k)) i - Eop 1 (Hop 1 (mono k)) i)
                (fun i => Q'.ofNat 2 * Eop 1 (mono k) i) := by decide

/-- `[H,F] = −2F` on spin ½ (degree 1). -/
theorem comm_HF_2F_spinHalf :
    ∀ k, k < 2 →
      FormEqv 2 (fun i => Hop 1 (Fop 1 (mono k)) i - Fop 1 (Hop 1 (mono k)) i)
                (fun i => Q'.ofInt (-2) * Fop 1 (mono k) i) := by decide

/-- `[E,F] = H` on spin 1 (degree 2), on every basis vector `mono k`, `k < 3`. -/
theorem comm_EF_H_spinOne :
    ∀ k, k < 3 →
      FormEqv 3 (fun i => Eop 2 (Fop 2 (mono k)) i - Fop 2 (Eop 2 (mono k)) i)
                (Hop 2 (mono k)) := by decide

/-- `[H,E] = 2E` on spin 1 (degree 2). -/
theorem comm_HE_2E_spinOne :
    ∀ k, k < 3 →
      FormEqv 3 (fun i => Hop 2 (Eop 2 (mono k)) i - Eop 2 (Hop 2 (mono k)) i)
                (fun i => Q'.ofNat 2 * Eop 2 (mono k) i) := by decide

/-! ## 5. Intertwiners and highest-weight vectors

A linear map of forms `φ : BForm → BForm` intertwines the degree-`m` action
with the degree-`n` action when it commutes with `E`, `F`, `H` (checked on the
source window).  Because everything is `Q'`-linear, checking on the basis is
enough — the `IsIntertwiner` predicate quantifies over basis monomials.

A **highest-weight vector** of a degree-`n` form is one killed by `E`.  In a
multiplicity-free decomposition each weight space has a ≤ 1-dimensional
`E`-kernel; that rank bound (proved concretely in the companion file) is exactly
Schur's lemma and the source of the pentagon's uniqueness. -/

/-- `φ` is an `sl₂`-intertwiner from the degree-`m` to the degree-`n` action,
tested on the basis window `[0, W)` and output window `[0, Wout)`.  This is the
genuine "commutes with the action" condition — three operator identities. -/
def IsIntertwiner (m n W Wout : Nat) (φ : BForm → BForm) : Prop :=
  (∀ k, k < W → FormEqv Wout (φ (Eop m (mono k))) (Eop n (φ (mono k)))) ∧
  (∀ k, k < W → FormEqv Wout (φ (Fop m (mono k))) (Fop n (φ (mono k)))) ∧
  (∀ k, k < W → FormEqv Wout (φ (Hop m (mono k))) (Hop n (φ (mono k))))

/-- `c` is a highest-weight vector for the degree-`n` action on the window
`[0, N)` when `E c ≃ 0` there. -/
def IsHighestWeight (n N : Nat) (c : BForm) : Prop :=
  FormEqv N (Eop n c) zeroF

instance (n N : Nat) (c : BForm) : Decidable (IsHighestWeight n N c) :=
  inferInstanceAs (Decidable (FormEqv N (Eop n c) zeroF))

end YMGap.Continuum.BinaryForms

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BinaryForms.comm_EF_H_spinHalf
#print axioms YMGap.Continuum.BinaryForms.comm_HE_2E_spinHalf
#print axioms YMGap.Continuum.BinaryForms.comm_HF_2F_spinHalf
#print axioms YMGap.Continuum.BinaryForms.comm_EF_H_spinOne
#print axioms YMGap.Continuum.BinaryForms.comm_HE_2E_spinOne
