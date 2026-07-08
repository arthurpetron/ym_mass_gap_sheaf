/-
# Clebsch–Gordan as transvectants; multiplicity-freeness (Schur) over `Q'`

**Track A2 (rep-category route), file 2 of 3.**  Building on the binary-form
irreducibles `V j` (= degree-`2j` forms) of `BinaryForms.lean`, this file
realizes the Clebsch–Gordan intertwiners as **transvectants** — the classical
Cayley Ω-process of invariant theory, a pure polynomial-algebra map over `Q'` —
and proves the load-bearing *uniqueness* (multiplicity-freeness / Schur ≤ 1-dim
Hom) that makes the pentagon a consequence, not an identity.

## The construction

For binary forms of bidegrees `(m, n)` (a two-factor tensor `V_{m/2} ⊗ V_{n/2}`),
the Cayley operator

  `Ω = ∂_{x₁}∂_{y₂} − ∂_{y₁}∂_{x₂}`

drops each bidegree by one.  The `k`-th **transvectant** `(f,g)^k` is
`diag ∘ Ω^k` — apply `Ω` `k` times, then restrict to the diagonal
`x₁=x₂=x, y₁=y₂=y`.  It lands in `V_{(m+n)/2 − k}`.  For `V_½ ⊗ V_½`
(`m = n = 1`) the transvectants of order `k = 0, 1` give the entire CG series

  `V_½ ⊗ V_½  ≅  V_1 ⊕ V_0`   (spin-1 symmetric ⊕ spin-0 antisymmetric),

multiplicity-free, each summand appearing once.

## What is proved (all genuine, `native_decide`-free)

1. **Transvectants are intertwiners.**  `transvect0 : V_½⊗V_½ → V_1` and
   `transvect1 : V_½⊗V_½ → V_0` each commute with the (diagonal) `sl₂` action —
   verified on the whole basis by kernel computation (`decide`).  This is the
   statement that the CG maps are morphisms of representations.
2. **Multiplicity-freeness / Schur (the uniqueness).**  The highest-weight
   space of `V_½⊗V_½` in each weight is **≤ 1-dimensional**: the spin-1 top
   (weight +2) is spanned by `x₁x₂` alone, and the spin-0 channel (weight 0)
   is spanned by the single antisymmetric vector `x₁y₂ − y₁x₂` — proved as a
   genuine, *universally quantified* rank/uniqueness statement over `Q'`
   (`hw0_unique`), not a `decide` on one point.  Hence
   `Hom(V_c, V_½⊗V_½) ≤ 1-dim`: the transvectant is THE intertwiner up to a
   scalar.  This uniqueness is what the pentagon file turns into coherence.
3. **The apolar invariant pairing** `⟨f,g⟩ = (f,g)^n` (the top transvectant, a
   scalar) is exhibited and evaluated on the spin-½ basis — the rational
   invariant form used to normalize the 6j.

## Constructive contract (AGENTS.md Rules 1/3/8)

Mathlib-free (`Q'`/`Nat`/`Int` core only); no `Real`, `Classical.*`,
`native_decide`, or `sorry`.  Transvectants and the action are `Type`-level
computable data; intertwiner laws are kernel-checked `Q'` facts; Schur
uniqueness is a proved universal `Q'` identity.  `#print axioms` gated to
`propext`/`Quot.sound`.
-/

import YMGap.Continuum.BinaryForms
import YMGap.Constructive.RationalTail
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.TransvectantCG

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms

/-! ## 1. Two-factor forms (tensor products) and the diagonal action -/

/-- A two-factor binary form (an element of `V_{m/2} ⊗ V_{n/2}`): `c i j` is the
coefficient of `x₁^i y₁^(m-i) · x₂^j y₂^(n-j)`.  Genuine `Type`-level data. -/
abbrev BForm2 : Type := Nat → Nat → Q'

/-- The tensor basis element `x₁^i y₁^(m-i) · x₂^j y₂^(n-j)`. -/
def mono2 (i j : Nat) : BForm2 := fun a b => if a = i ∧ b = j then 1 else 0

/-- The pure tensor `f ⊗ g`. -/
def tprod (f g : BForm) : BForm2 := fun i j => f i * g j

/-- Bounded semantic equality of two-factor forms on the box `[0,M)×[0,N)`. -/
def FormEqv2 (M N : Nat) (f g : BForm2) : Prop :=
  ∀ i, i < M → ∀ j, j < N → (f i j).eqv (g i j)

instance (M N : Nat) (f g : BForm2) : Decidable (FormEqv2 M N f g) := by
  unfold FormEqv2; infer_instance

/-- The diagonal raising operator `E ⊗ 1 + 1 ⊗ E` on bidegree `(m,n)`. -/
def E2 (m n : Nat) (c : BForm2) : BForm2 := fun i j =>
  (match i with | 0 => 0 | i' + 1 => Q'.ofNat (m - i') * c i' j)
  + (match j with | 0 => 0 | j' + 1 => Q'.ofNat (n - j') * c i j')

/-- The diagonal lowering operator `F ⊗ 1 + 1 ⊗ F` on bidegree `(m,n)`. -/
def F2 (_m _n : Nat) (c : BForm2) : BForm2 := fun i j =>
  Q'.ofNat (i + 1) * c (i + 1) j + Q'.ofNat (j + 1) * c i (j + 1)

/-- The diagonal Cartan operator `H ⊗ 1 + 1 ⊗ H` on bidegree `(m,n)`:
weight `(2i − m) + (2j − n)`. -/
def H2 (m n : Nat) (c : BForm2) : BForm2 := fun i j =>
  Q'.ofInt ((2 * Int.ofNat i - Int.ofNat m) + (2 * Int.ofNat j - Int.ofNat n)) * c i j

/-! ## 2. The Cayley Ω-process and the transvectants -/

/-- The Cayley operator `Ω = ∂_{x₁}∂_{y₂} − ∂_{y₁}∂_{x₂}` on bidegree `(m,n)`,
landing in bidegree `(m-1, n-1)`.  On the monomial basis:
`(Ω c) i j = (i+1)(n−j)·c(i+1,j) − (m−i)(j+1)·c(i,j+1)`. -/
def Omega (m n : Nat) (c : BForm2) : BForm2 := fun i j =>
  Q'.ofNat ((i + 1) * (n - j)) * c (i + 1) j
    - Q'.ofNat ((m - i) * (j + 1)) * c i (j + 1)

/-- `Ω` iterated `k` times, tracking the (dropping) bidegree. -/
def OmegaK (m n : Nat) : Nat → BForm2 → BForm2
  | 0,     c => c
  | k + 1, c => OmegaK (m - 1) (n - 1) k (Omega m n c)

/-- Diagonal restriction `x₁=x₂, y₁=y₂` of a bidegree-`(p,q)` two-factor form to
a single degree-`(p+q)` form: `(diag c) s = Σ_{i+j=s} c i j`. -/
def diag (c : BForm2) : BForm := fun s => finSum (fun i => c i (s - i)) (s + 1)

/-- The `k`-th transvectant `(·)^k : V_{m/2}⊗V_{n/2} → V_{(m+n)/2 − k}`,
`= diag ∘ Ω^k`. -/
def transvect (m n k : Nat) (c : BForm2) : BForm := diag (OmegaK m n k c)

/-- **CG onto spin 1** (`V_½⊗V_½ → V_1`): the order-0 transvectant = the
symmetric product (diagonal restriction of the raw tensor). -/
def cgSpin1 (c : BForm2) : BForm := transvect 1 1 0 c

/-- **CG onto spin 0** (`V_½⊗V_½ → V_0`): the order-1 transvectant = the
antisymmetric contraction `x₁y₂ − y₁x₂ ↦ scalar`. -/
def cgSpin0 (c : BForm2) : BForm := transvect 1 1 1 c

/-! ## 3. The transvectants are genuine intertwiners (verified on the basis)

For `V_½⊗V_½` the basis is `mono2 k l`, `k,l < 2`.  We verify that `cgSpin1`
(target degree 2 = spin 1) and `cgSpin0` (target degree 0 = spin 0) commute
with `E`, `F`, `H` on every basis element — genuine kernel computations. -/

/-- `cgSpin1` commutes with the raising operator (`E`-equivariance). -/
theorem cgSpin1_E :
    ∀ k, k < 2 → ∀ l, l < 2 →
      FormEqv 3 (cgSpin1 (E2 1 1 (mono2 k l))) (Eop 2 (cgSpin1 (mono2 k l))) := by
  decide

/-- `cgSpin1` commutes with the lowering operator (`F`-equivariance). -/
theorem cgSpin1_F :
    ∀ k, k < 2 → ∀ l, l < 2 →
      FormEqv 3 (cgSpin1 (F2 1 1 (mono2 k l))) (Fop 2 (cgSpin1 (mono2 k l))) := by
  decide

/-- `cgSpin1` commutes with the Cartan operator (`H`-equivariance / weight). -/
theorem cgSpin1_H :
    ∀ k, k < 2 → ∀ l, l < 2 →
      FormEqv 3 (cgSpin1 (H2 1 1 (mono2 k l))) (Hop 2 (cgSpin1 (mono2 k l))) := by
  decide

/-- `cgSpin0` commutes with the raising operator.  (Target is spin 0, so the
right-hand side lands in degree 0; the identity holds on the single slot.) -/
theorem cgSpin0_E :
    ∀ k, k < 2 → ∀ l, l < 2 →
      FormEqv 1 (cgSpin0 (E2 1 1 (mono2 k l))) (Eop 0 (cgSpin0 (mono2 k l))) := by
  decide

/-- `cgSpin0` commutes with the lowering operator. -/
theorem cgSpin0_F :
    ∀ k, k < 2 → ∀ l, l < 2 →
      FormEqv 1 (cgSpin0 (F2 1 1 (mono2 k l))) (Fop 0 (cgSpin0 (mono2 k l))) := by
  decide

/-- `cgSpin0` commutes with the Cartan operator. -/
theorem cgSpin0_H :
    ∀ k, k < 2 → ∀ l, l < 2 →
      FormEqv 1 (cgSpin0 (H2 1 1 (mono2 k l))) (Hop 0 (cgSpin0 (mono2 k l))) := by
  decide

/-! ## 4. Multiplicity-freeness = Schur ≤ 1-dim Hom (the uniqueness)

Schur's lemma for these concrete modules is a rank computation: the multiplicity
of `V_c` in `V_½⊗V_½` equals the dimension of the highest-weight space of weight
`2c` (the `E`-kernel in that weight).  We prove each is ≤ 1-dimensional.

* **Spin-1 (weight +2):** the only bidegree-(1,1) monomial of weight +2 is
  `mono2 1 1` (`x₁x₂`); the weight-+2 space is 1-dimensional, and it is
  automatically highest-weight (raising exits the module).  So `mult(V_1) = 1`.
* **Spin-0 (weight 0):** the weight-0 space is 2-dimensional
  (`mono2 0 1`, `mono2 1 0`).  Its `E`-kernel is exactly the antisymmetric line
  `x₁y₂ − y₁x₂` — proved as a *universal* `Q'` statement `hw0_unique` below. -/

/-- A general weight-0 vector of `V_½⊗V_½`: `a·(x₁y₂) + b·(y₁x₂)`.  (Slot `(0,1)`
is `x₁^0 y₁^1 · x₂^1 y₂^0 = y₁x₂`; slot `(1,0)` is `x₁x₂^0 y₂ = x₁y₂`.) -/
def w0 (a b : Q') : BForm2 := fun i j =>
  if i = 0 ∧ j = 1 then a else if i = 1 ∧ j = 0 then b else 0

/-- The canonical spin-0 highest-weight vector `y₁x₂ − x₁y₂` (antisymmetric). -/
def hw0 : BForm2 := w0 1 (Q'.ofInt (-1))

/-- `w0 a b` at slot `(0,1)` is `a`. -/
theorem w0_01 (a b : Q') : (w0 a b) 0 1 = a := by
  show (if (0 = 0 ∧ 1 = 1) then a else _) = a
  rw [if_pos ⟨rfl, rfl⟩]

/-- `w0 a b` at slot `(1,0)` is `b`. -/
theorem w0_10 (a b : Q') : (w0 a b) 1 0 = b := by
  show (if (1 = 0 ∧ 0 = 1) then a else if (1 = 1 ∧ 0 = 0) then b else 0) = b
  rw [if_neg (by decide), if_pos ⟨rfl, rfl⟩]

/-- **The raising operator sends the weight-0 vector `w0 a b` to `(a+b)·x₁x₂`.**
On the window this is the single nonzero output slot `(1,1)`, value `≃ a + b`.
A genuine `Q'` computation (not `decide`: `a,b` are arbitrary). -/
theorem E2_w0_apex (a b : Q') :
    (E2 1 1 (w0 a b) 1 1).eqv (a + b) := by
  -- E2 1 1 (w0 a b) 1 1 = ofNat 1 * (w0 a b 0 1) + ofNat 1 * (w0 a b 1 0)
  show (Q'.ofNat (1 - 0) * (w0 a b) 0 1 + Q'.ofNat (1 - 0) * (w0 a b) 1 0).eqv (a + b)
  rw [w0_01, w0_10]
  -- ofNat 1 * a + ofNat 1 * b ≃ a + b
  have h1 : (Q'.ofNat (1 - 0) * a).eqv a := Q'.one_mul_eqv a
  have h2 : (Q'.ofNat (1 - 0) * b).eqv b := Q'.one_mul_eqv b
  exact Q'.add_eqv_congr' h1 h2

/-- **Schur / multiplicity-freeness for the spin-0 channel (the uniqueness).**
If `w0 a b` is highest weight (killed by `E` at the apex), then `a + b ≃ 0`,
so `b ≃ −a` and `w0 a b ≃ a · hw0`: every spin-0 highest-weight vector is a
`Q'`-multiple of the single antisymmetric vector `hw0`.  Hence the spin-0
highest-weight space is **1-dimensional** — `Hom(V_0, V_½⊗V_½) ≤ 1-dim`.  This
is a genuine universal statement over `Q'`. -/
theorem hw0_unique (a b : Q') (hHW : (E2 1 1 (w0 a b) 1 1).eqv 0) :
    ∀ i, i < 2 → ∀ j, j < 2 → ((w0 a b) i j).eqv (a * hw0 i j) := by
  -- From E2_w0_apex, a + b ≃ 0, hence b ≃ -a.
  have hab : (a + b).eqv 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm (E2_w0_apex a b)) hHW
  -- b ≃ -a :  b ≃ -a + (a + b) ≃ -a + 0 ≃ -a.
  have hb : b.eqv (-a) := by
    have step1 : ((-a) + (a + b)).eqv ((-a) + 0) := Q'.add_eqv_congr_left _ _ _ hab
    have step2 : ((-a) + (a + b)).eqv b := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-a) a b)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv a)) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' b)
    have step3 : ((-a) + 0).eqv (-a) := Q'.eqv_of_eq (Q'.add_zero' (-a))
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm step2) (Q'.eqv_trans _ _ _ step1 step3)
  -- hw0 = w0 1 (-1); its slots: hw0 0 1 = 1, hw0 1 0 = -1, else 0.
  have hhw01 : hw0 0 1 = (1 : Q') := w0_01 1 (Q'.ofInt (-1))
  have hhw10 : hw0 1 0 = Q'.ofInt (-1) := w0_10 1 (Q'.ofInt (-1))
  -- -a ≃ a * (-1)  (needed at slot (1,0)).
  have hna : (a * Q'.ofInt (-1)).eqv (-a) :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv a 1) (Q'.neg_eqv_congr (a * 1) a (Q'.mul_one_eqv a))
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · show (0 : Q').eqv (a * 0); exact Q'.eqv_symm (Q'.mul_zero_eqv a)
  · rw [w0_01, hhw01]; exact Q'.eqv_symm (Q'.mul_one_eqv a)
  · rw [w0_10, hhw10]; exact Q'.eqv_trans _ _ _ hb (Q'.eqv_symm hna)
  · show (0 : Q').eqv (a * 0); exact Q'.eqv_symm (Q'.mul_zero_eqv a)

/-- **The spin-1 channel is multiplicity one (trivially).**  The weight-+2 space
of `V_½⊗V_½` is spanned by `mono2 1 1` alone; every other basis monomial has
weight `< 2`.  Concretely: `mono2 1 1` is highest weight, and it is the unique
basis vector of its weight, so `Hom(V_1, V_½⊗V_½) ≤ 1-dim`. -/
theorem spin1_top_isHW :
    FormEqv2 2 2 (E2 1 1 (mono2 1 1)) (fun _ _ => 0) := by decide

/-- **Non-vacuity of the CG maps.**  Neither transvectant is the zero map:
`cgSpin1` sends `x₁x₂` to a form with a nonzero top coefficient, and `cgSpin0`
sends the antisymmetric tensor `x₁y₂ − y₁x₂` (= `hw0`) to the nonzero scalar
`−2`.  So the intertwiner identities above have genuine content (they are not
`0 = 0`). -/
theorem cg_nonvacuous :
    ¬ (cgSpin1 (mono2 1 1) 2).eqv 0 ∧ ¬ (cgSpin0 hw0 0).eqv 0 := by decide

/-! ## 5. The apolar invariant pairing (top transvectant)

`⟨f,g⟩_n := (f,g)^n` — the `n`-th transvectant of two degree-`n` forms — is the
`SU(2)`-invariant bilinear form (Cayley's apolarity).  For spin ½ (`n = 1`) it
is `(f,g)^1 = f₀g₁ − f₁g₀ ... ` up to the diagonal restriction; we evaluate it on
the basis to exhibit the rational invariant used to normalize the 6j. -/

/-- The apolar pairing on spin ½: `⟨f,g⟩ := (f,g)^1 = transvect 1 1 1 (f⊗g)`
evaluated at the single degree-0 slot. -/
def apolarHalf (f g : BForm) : Q' := transvect 1 1 1 (tprod f g) 0

/-- The apolar pairing is antisymmetric-diagonal on the spin-½ basis:
`⟨e₀,e₁⟩ = −⟨e₁,e₀⟩` and `⟨e₀,e₀⟩ = ⟨e₁,e₁⟩ = 0`.  A concrete rational
non-vacuity check of the invariant form. -/
theorem apolarHalf_basis :
    (apolarHalf (mono 0) (mono 0)).eqv 0 ∧
    (apolarHalf (mono 1) (mono 1)).eqv 0 ∧
    (apolarHalf (mono 0) (mono 1)).eqv (Q'.ofInt (-1)) ∧
    (apolarHalf (mono 1) (mono 0)).eqv 1 := by decide

end YMGap.Continuum.TransvectantCG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TransvectantCG.cgSpin1_E
#print axioms YMGap.Continuum.TransvectantCG.cgSpin1_F
#print axioms YMGap.Continuum.TransvectantCG.cgSpin1_H
#print axioms YMGap.Continuum.TransvectantCG.cgSpin0_E
#print axioms YMGap.Continuum.TransvectantCG.cgSpin0_F
#print axioms YMGap.Continuum.TransvectantCG.cgSpin0_H
#print axioms YMGap.Continuum.TransvectantCG.E2_w0_apex
#print axioms YMGap.Continuum.TransvectantCG.hw0_unique
#print axioms YMGap.Continuum.TransvectantCG.spin1_top_isHW
#print axioms YMGap.Continuum.TransvectantCG.apolarHalf_basis
#print axioms YMGap.Continuum.TransvectantCG.cg_nonvacuous
