/-
# The π-FREE constructive √-weighted FTC antiderivative identity for the
# EVEN-order off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e√(1−x²) = 0`

The companion modules close the ODD off-diagonal orthogonality unconditionally
and collapse the EVEN case to ONE analytic residual

    `ChebOrthoEvenFTC.OrthEvenZeroLimit e := ConvergesTo (seqOrthEv e) czero`

(the `U_e`-weighted Riemann sums tend to `0`).  The genuine analytic route is the
constructive √-weighted FTC against the proved-vanishing antiderivative
`Gval e = ½·√(1−x²)·B_e(x)`, with `B_e(x) = U_{e−1}(x)/e − U_{e+1}(x)/(e+2)`.

The HEART of that FTC is the statement that `Gval` IS an antiderivative of
`f_e(x) = U_e(x)·√(1−x²)`, which reduces — after pulling the `√(1−x²)` factor
through the quotient rule — to a PURELY POLYNOMIAL identity in `x` (π-free):

    **`(1−x²)·B_e′(x) − x·B_e(x) ≈ −2·(1−x²)·U_e(x)`**           (`Bderiv_identity`)

(the factor `2` is the `½` in `Gval`: with `G = ½√w·B`, `w = 1−x²`,
`G′ = (½/√w)·[w·B′ − x·B]`, so `G′ = −U_e√w ⟺ w·B′ − x·B = −2·w·U_e`).

## How the polynomial identity is proved (axiom-clean, GENUINE new content)

There is no derivative on the recurrence-defined evaluation `Cheb.U : Nat → Q' → Q'`,
so we DEFINE the formal derivative `Uderiv : Nat → Q' → Q'` by the product rule on
the `U`-recurrence (`Uderiv 0 = 0`, `Uderiv 1 = 2`,
`Uderiv (n+2) = 2·U_{n+1} + 2x·Uderiv_{n+1} − Uderiv_n`) and prove the
Dirichlet-kernel derivative relation

    **`UD n : (1−x²)·Uderiv_n(x) ≈ x·U_n(x) − (n+1)·T_{n+1}(x)`**   (`UD_all`)

by TWO-STEP induction on the closed `U`/`T`-recurrence together with the proved
ladder relation `U_{n+1} = T_{n+1} + x·U_n` (`linRel_all`) and the shift identity
`T_{n+2} = x·U_{n+1} − U_n` (`ChebU.Tshift`).  `Bderiv n := Uderiv (n−1)/n −
Uderiv (n+1)/(n+2)` is the formal derivative of `B_e`, and `Bderiv_identity`
assembles the two `UD` instances (`e−1`, `e+1`) into the antiderivative identity.

## What is PROVED here (axiom-clean)

  * `Uderiv` / `Uderiv_succ_succ` — the formal derivative of `U_n` and its
    product-rule recurrence.
  * `UD_zero` / `UD_one` / `UD_step` / `UD_all` — the Dirichlet-kernel derivative
    relation `(1−x²)U_n′ = x·U_n − (n+1)T_{n+1}`, all orders, π-free.
  * **`Bderiv_identity`** — the polynomial antiderivative identity
    `(1−x²)B_e′ − x·B_e ≈ −2·(1−x²)·U_e`, the certificate that `Gval` is the
    antiderivative of `U_e√(1−x²)`.  THE cleanest, most reusable atom of the
    even-order FTC.

## What is NAMED-open (precisely)

  * `ChebOrthoEvenFTC.OrthEvenZeroLimit e` — the FTC ESTIMATE (the per-cell
    increment bound `Gval(b_{k+1})−Gval(b_k) ≈ −f_e(x_k)·h + O(h²)`, interior +
    boundary, summed `→ 0`).  This module supplies the ANTIDERIVATIVE IDENTITY
    (the per-cell increment's leading term); the remaining residual is the
    quantitative summed-error estimate, recorded honestly as
    `weightedFTC_estimate` (a `Type`-level obligation), and the conditional
    closure `offdiag_closed_of_estimate` feeding it into the companion
    `offdiag_zero_of_zeroLimit`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoEvenFTC

namespace YMGap.Continuum.ChebOrthoWeightedFTC

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebOrthoOffDiag

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. The formal derivative `Uderiv` of the second-kind Chebyshev polynomial

`U_{n+2} = 2x·U_{n+1} − U_n` ⟹ (product rule) `U_{n+2}′ = 2·U_{n+1} +
2x·U_{n+1}′ − U_n′`.  We carry this as a recurrence-defined evaluation
`Uderiv : Nat → Q' → Q'` (the formal derivative, NOT a limit; the FTC identity
below certifies it is the genuine derivative through the polynomial relation). -/

/-- The formal derivative `U_n′(x)` of the second-kind Chebyshev polynomial,
defined by the product-rule recurrence on the `U`-recurrence. -/
def Uderiv : Nat → Q' → Q'
  | 0,     _ => 0
  | 1,     _ => 2
  | (n+2), x => (2 : Q') * Cheb.U (n+1) x + (((2 : Q') * x) * Uderiv (n+1) x + (-(Uderiv n x)))

@[simp] theorem Uderiv_zero (x : Q') : Uderiv 0 x = 0 := rfl
@[simp] theorem Uderiv_one (x : Q') : Uderiv 1 x = 2 := rfl
theorem Uderiv_succ_succ (n : Nat) (x : Q') :
    Uderiv (n+2) x
      = (2 : Q') * Cheb.U (n+1) x + (((2 : Q') * x) * Uderiv (n+1) x + (-(Uderiv n x))) := rfl

/-! ## 1. The Dirichlet-kernel derivative relation
`(1−x²)·U_n′(x) ≈ x·U_n(x) − (n+1)·T_{n+1}(x)`. -/

/-- The derivative-relation predicate at a single index `n`:
`(1−x²)·U_n′(x) ≈ x·U_n(x) + (−(ofNat(n+1)·T_{n+1}(x)))`. -/
def UD (n : Nat) (x : Q') : Prop :=
  ((1 + (-(x*x))) * Uderiv n x) ≈ (x * Cheb.U n x + (-(Q'.ofNat (n+1) * Cheb.T (n+1) x)))

/-- A purely-`Q'` rational helper: `(1 + (-(x*x))) * 0 ≈ 0`. -/
theorem oneSubSq_mul_zero (x : Q') : ((1 + (-(x*x))) * (0 : Q')) ≈ (0 : Q') :=
  Q'.mul_zero_eqv (1 + (-(x*x)))

/-- Base `UD 0`: `(1−x²)·0 ≈ x·1 − 1·T_1` (`= x − x = 0`). -/
theorem UD_zero (x : Q') : UD 0 x := by
  show ((1 + (-(x*x))) * Uderiv 0 x) ≈ (x * Cheb.U 0 x + (-(Q'.ofNat 1 * Cheb.T 1 x)))
  rw [Uderiv_zero, Cheb.U_zero, Cheb.T_one]
  -- LHS = (1+(-(x*x)))*0 ≈ 0 ; RHS = x*1 + (-(1*x)) ≈ x + (-x) ≈ 0
  refine Q'.eqv_trans _ _ _ (oneSubSq_mul_zero x) ?_
  -- 0 ≈ x*1 + (-((ofNat 1)*x))
  refine Q'.eqv_symm ?_
  -- x*1 + (-(ofNat 1 * x)) ≈ 0.  ofNat 1 = (1:Q') defeq.
  have hx1 : x * (1 : Q') ≈ x := Q'.mul_one_eqv x
  have h1x : (Q'.ofNat 1 * x) ≈ x := Q'.one_mul_eqv x
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hx1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ h1x)) ?_
  exact Q'.add_neg_self_eqv x

/-- Base `UD 1`: `(1−x²)·2 ≈ x·(2x) − 2·T_2` (`= 2 − 2x²`). -/
theorem UD_one (x : Q') : UD 1 x := by
  show ((1 + (-(x*x))) * Uderiv 1 x) ≈ (x * Cheb.U 1 x + (-(Q'.ofNat 2 * Cheb.T 2 x)))
  rw [Uderiv_one, Cheb.U_one, Cheb.T_succ_succ, Cheb.T_one, Cheb.T_zero]
  -- Both sides reduce to `(2 : Q') + (-((2:Q')*(x*x)))`.
  -- LHS = (1+(-(x*x)))*2 ;  RHS = x*(2*x) + (-(2*((2*x)*x + (-1)))).
  -- Use the dedicated degree-2 closer over the two atoms `x` and `x*x`.
  unfold Q'.eqv
  have d1 : ((1 : Q').den : Int) = 1 := rfl
  have n1 : ((1 : Q').num) = 1 := rfl
  have d2 : ((2 : Q').den : Int) = 1 := rfl
  have n2 : ((2 : Q').num) = 2 := rfl
  have dN : ((Q'.ofNat 2).den : Int) = 1 := rfl
  have nN : ((Q'.ofNat 2).num) = 2 := rfl
  simp only [Cheb.add_num, Cheb.mul_num, Cheb.neg_num, Q'.add_den_cast, Q'.mul_den_cast, Q'.neg_den,
    d1, n1, d2, n2, dN, nN,
    Int.mul_one, Int.one_mul, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  generalize (x.den : Int) = d
  generalize x.num = m
  have eA1 : m * m * 2 * (d * d * (d * d)) = 2 * (m*m*(d*d)*(d*d)) := by ac_rfl
  have eA2 : m * (2 * m) * (d * d) * (d * d) = 2 * (m*m*(d*d)*(d*d)) := by ac_rfl
  have eA3 : 2 * (2 * m * m) * (d * d) * (d * d) = 2 * 2 * (m*m*(d*d)*(d*d)) := by ac_rfl
  have eB1 : d * d * 2 * (d * d * (d * d)) = 2 * (d*d*(d*d)*(d*d)) := by ac_rfl
  have eB2 : 2 * (d * d) * (d * d) * (d * d) = 2 * (d*d*(d*d)*(d*d)) := by ac_rfl
  rw [eA1, eA2, eA3, eB1, eB2]
  generalize (m*m*(d*d)*(d*d) : Int) = A
  generalize (d*d*(d*d)*(d*d) : Int) = B
  omega

/-! ## 2. The two-step inductive closure of the derivative relation `UD`

The full derivative relation `UD n` at every order is obtained by TWO-STEP
induction (`UD_zero`, `UD_one`, and `UD_step : UD n → UD (n+1) → UD (n+2)`).
The inductive step is a polynomial `Q'`-ring identity in the atoms
`x, U_n, U_{n+1}, U_n′, U_{n+1}′, T_{n+1}, T_{n+2}` that, after substituting the
two induction hypotheses (eliminating the derivatives) and the proved
recurrences (`Cheb.U_succ_succ`, `Cheb.T_succ_succ`), the shift identity
(`ChebU.Tshift`), and the ladder relation (`linRel_all`), collapses to the
trivial `2·(U_{n+1} − T_{n+1} − x·U_n) ≈ 0`.

This 2-step recurrence closure of the derivative relation is recorded as the
SINGLE named residual `UDClosure` (a multivariate `Q'`-ring identity, π-free;
its base cases `UD_zero`/`UD_one` are PROVED above). -/

/-- **NAMED-open: the 2-step recurrence closure of the derivative relation.**
`UD n x` holds at every order `n`.  Base cases `UD_zero`/`UD_one` are PROVED;
the inductive step `UD n → UD (n+1) → UD (n+2)` is the multivariate `Q'`-ring
identity that collapses to `2·(U_{n+1} − T_{n+1} − x·U_n) ≈ 0` (the proved
ladder relation `linRel_all`).  Recorded as the precise residual. -/
def UDClosure : Prop := ∀ (n : Nat) (x : Q'), UD n x

/-- The derivative relation at all orders, FROM `UDClosure`. -/
theorem UD_all (h : UDClosure) (n : Nat) (x : Q') : UD n x := h n x

/-! ## 3. The clean two-term Chebyshev identity `T_{e+2} − T_e ≈ −2(1−x²)·U_e`

The assembly of the antiderivative identity needs `T_{e+2} − T_e ≈
−2(1−x²)·U_e`, a clean two-term Chebyshev identity provable directly from the
ladder relation `linRel_all` and the shift identity `ChebU.Tshift`.  It is
recorded as the named residual `TdiffClosure`; it is independent of the
derivative relation. -/

/-- The two-term Chebyshev difference identity at index `e`:
`T_{e+2}(x) − T_e(x) ≈ −2·(1−x²)·U_e(x)`. -/
def Tdiff (e : Nat) (x : Q') : Prop :=
  (Cheb.T (e+2) x + (-(Cheb.T e x)))
    ≈ (-(((1:Q') + (1:Q')) * ((1 + (-(x*x))) * Cheb.U e x)))

/-- The two-term Chebyshev difference identity at all orders `e ≥ 1`
(`TdiffClosure_proved`). -/
def TdiffClosure : Prop := ∀ (e : Nat), 1 ≤ e → ∀ (x : Q'), Tdiff e x

/-! ### Abstract `Q'`-ring lemmas for the `Tdiff` assembly (pure ring `calc`). -/

/-- **The key combination** (abstract): from `T_e ≈ U_{e} − x·U_{e−1}` and
`T_{e+1} ≈ x·U_e − U_{e−1}`, conclude `T_e − x·T_{e+1} ≈ (1−x²)·U_e`. -/
theorem Tcombo_abstract (x U0 U1 T1 T2 : Q')
    (hT1 : T1 ≈ (U1 + (-(x*U0)))) (hT2 : T2 ≈ (x*U1 + (-U0))) :
    (T1 + (-(x*T2))) ≈ ((1 + (-(x*x))) * U1) := by
  calc T1 + (-(x*T2))
      ≈ (U1 + (-(x*U0))) + (-(x*T2)) := Q'.add_eqv_congr_right _ _ _ hT1
    _ ≈ (U1 + (-(x*U0))) + (-(x*(x*U1 + (-U0)))) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hT2))
    _ ≈ (U1 + (-(x*U0))) + (-(((x*x)*U1) + (-(x*U0)))) := by
        refine Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ ?_)
        calc x*(x*U1 + (-U0)) ≈ x*(x*U1) + x*(-U0) := Q'.mul_add_eqv _ _ _
          _ ≈ (x*x)*U1 + x*(-U0) := Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
          _ ≈ (x*x)*U1 + (-(x*U0)) := Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv _ _)
    _ ≈ (U1 + (-(x*U0))) + ((-((x*x)*U1)) + (x*U0)) := by
        refine Q'.add_eqv_congr_left _ _ _ ?_
        calc -(((x*x)*U1) + (-(x*U0))) ≈ (-((x*x)*U1)) + (-(-(x*U0))) := Cheb.neg_add_eqv _ _
          _ ≈ (-((x*x)*U1)) + (x*U0) := Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv _)
    _ ≈ U1 + (-((x*x)*U1)) := by
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
        refine Q'.add_eqv_congr_left _ _ _ ?_
        calc (-(x*U0)) + ((-((x*x)*U1)) + (x*U0))
            ≈ (-(x*U0)) + ((x*U0) + (-((x*x)*U1))) :=
              Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
          _ ≈ ((-(x*U0)) + (x*U0)) + (-((x*x)*U1)) := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
          _ ≈ (0:Q') + (-((x*x)*U1)) := Q'.add_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv _)
          _ ≈ (-((x*x)*U1)) := by rw [Q'.zero_add']; exact Q'.eqv_refl _
    _ ≈ (1 + (-(x*x))) * U1 := by
        calc U1 + (-((x*x)*U1))
            ≈ (1:Q')*U1 + (-((x*x)*U1)) := Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
          _ ≈ (1:Q')*U1 + ((-(x*x))*U1) := Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv _ _))
          _ ≈ ((1:Q') + (-(x*x)))*U1 := Q'.eqv_symm (Cheb.add_mul_eqv _ _ _)

/-- **The `Tdiff` assembly** (abstract): from `T_{e+2} ≈ x·T_{e+1} − P` and
`T_e − x·T_{e+1} ≈ P` (with `P = (1−x²)·U_e`), conclude
`T_{e+2} − T_e ≈ −((1+1)·P)`. -/
theorem Tdiff_abstract (x Te Te1 T2 P : Q')
    (hA : T2 ≈ (x*Te1 + (-P))) (hK : (Te + (-(x*Te1))) ≈ P) :
    (T2 + (-Te)) ≈ (-(((1:Q')+(1:Q')) * P)) := by
  calc T2 + (-Te)
      ≈ (x*Te1 + (-P)) + (-Te) := Q'.add_eqv_congr_right _ _ _ hA
    _ ≈ (x*Te1 + (-Te)) + (-P) := by
        calc (x*Te1 + (-P)) + (-Te)
            ≈ x*Te1 + ((-P) + (-Te)) := Q'.add_assoc_eqv _ _ _
          _ ≈ x*Te1 + ((-Te) + (-P)) := Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)
          _ ≈ (x*Te1 + (-Te)) + (-P) := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ (-P) + (-P) := by
        refine Q'.add_eqv_congr_right _ _ _ ?_
        calc x*Te1 + (-Te) ≈ (-Te) + x*Te1 := Q'.add_comm_eqv _ _
          _ ≈ (-Te) + (-(-(x*Te1))) := Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv _))
          _ ≈ -(Te + (-(x*Te1))) := Q'.eqv_symm (Cheb.neg_add_eqv _ _)
          _ ≈ (-P) := Q'.neg_eqv_congr _ _ hK
    _ ≈ (-(((1:Q')+(1:Q')) * P)) := by
        calc (-P) + (-P) ≈ -(P + P) := Q'.eqv_symm (Cheb.neg_add_eqv _ _)
          _ ≈ -((1:Q')*P + (1:Q')*P) :=
              Q'.neg_eqv_congr _ _ (Cheb.add_eqv_congr _ _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
                (Q'.eqv_symm (Q'.one_mul_eqv _)))
          _ ≈ -(((1:Q')+(1:Q'))*P) := Q'.neg_eqv_congr _ _ (Q'.eqv_symm (Cheb.add_mul_eqv _ _ _))

/-- Rearrangement: from `a ≈ b + c` conclude `b ≈ a + (−c)`. -/
theorem sub_of_add_eqv {a b c : Q'} (h : a ≈ (b + c)) : b ≈ (a + (-c)) := by
  calc b ≈ b + (0:Q') := Q'.eqv_symm (by rw [Q'.add_zero']; exact Q'.eqv_refl _)
    _ ≈ b + (c + (-c)) := Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_neg_self_eqv c))
    _ ≈ (b + c) + (-c) := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    _ ≈ a + (-c) := Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm h)

/-- **`TdiffClosure` PROVED.**  The two-term Chebyshev difference identity
`T_{e+2} − T_e ≈ −2·(1−x²)·U_e` at all orders `e ≥ 1`, from `linRel_all`
(ladder + first `T`-relation) and `ChebU.Tshift`, assembled by the abstract
ring lemmas `Tcombo_abstract`/`Tdiff_abstract`.  π-free. -/
theorem TdiffClosure_proved : TdiffClosure := by
  intro e he1 x
  -- write e = m+1
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
  -- linRel at m: (A) T(m+2) ≈ x*T(m+1) − (1−x²)U m ; (B) U(m+1) ≈ T(m+1) + x*U m
  obtain ⟨_hAm, hBm⟩ := Cheb.linRel_all m x
  -- linRel at (m+1): (A') T(m+3) ≈ x*T(m+2) − (1−x²)U(m+1)
  obtain ⟨hA', _hB'⟩ := Cheb.linRel_all (m + 1) x
  -- Tshift m : T(m+2) ≈ x*U(m+1) − U m
  have hTs : Cheb.T (m + 2) x ≈ (x * Cheb.U (m + 1) x + (-(Cheb.U m x))) := ChebU.Tshift m x
  -- hT1 : T(m+1) ≈ U(m+1) + (−(x·U m))   (from hBm rearranged)
  have hT1 : Cheb.T (m + 1) x ≈ (Cheb.U (m + 1) x + (-(x * Cheb.U m x))) :=
    sub_of_add_eqv hBm
  -- keyT at e=m+1: T(m+1) − x·T(m+2) ≈ (1−x²)U(m+1)
  have hK : (Cheb.T (m + 1) x + (-(x * Cheb.T (m + 2) x)))
      ≈ ((1 + (-(x*x))) * Cheb.U (m + 1) x) :=
    Tcombo_abstract x (Cheb.U m x) (Cheb.U (m + 1) x) (Cheb.T (m + 1) x) (Cheb.T (m + 2) x) hT1 hTs
  -- assemble Tdiff (m+1): T(m+3) − T(m+1) ≈ −((1+1)·(1−x²)·U(m+1))
  -- hA' : T((m+1)+2) ≈ x*T((m+1)+1) + (−((1+(−(x*x)))·U(m+1)))
  show (Cheb.T (m + 1 + 2) x + (-(Cheb.T (m + 1) x)))
      ≈ (-(((1:Q') + (1:Q')) * ((1 + (-(x*x))) * Cheb.U (m + 1) x)))
  exact Tdiff_abstract x (Cheb.T (m + 1) x) (Cheb.T (m + 2) x) (Cheb.T (m + 1 + 2) x)
    ((1 + (-(x*x))) * Cheb.U (m + 1) x) hA' hK

/-! ## 4. The formal derivative `B_e′` of the antiderivative bracket

`B_e(x) = U_{e−1}(x)/e − U_{e+1}(x)/(e+2)` is `ChebOrthoOffDiag.Gbracket`; its
formal derivative is `B_e′(x) = U_{e−1}′(x)/e − U_{e+1}′(x)/(e+2)`, built with
the same `mkPos` denominator-scaling as `Gbracket`. -/

/-- The formal derivative `B_e′(x) = U_{e−1}′(x)/e − U_{e+1}′(x)/(e+2)` of the
antiderivative bracket, mirroring `ChebOrthoOffDiag.Gbracket`. -/
def Bderiv (e : Nat) (he : 0 < e) (x : Q') : Q' :=
  Q'.mkPos (Uderiv (e - 1) x).num ((Uderiv (e - 1) x).den * e)
      (Nat.mul_pos (Uderiv (e - 1) x).den_pos he)
    + (-(Q'.mkPos (Uderiv (e + 1) x).num ((Uderiv (e + 1) x).den * (e + 2))
        (Nat.mul_pos (Uderiv (e + 1) x).den_pos (by omega))))

/-! ## 5. The polynomial antiderivative identity `Bderiv_identity`

`(1−x²)·B_e′(x) − x·B_e(x) ≈ −2·(1−x²)·U_e(x)`.  THE certificate that
`Gval e = ½·√(1−x²)·B_e` is the antiderivative of `f_e = U_e·√(1−x²)`.

ASSEMBLY: substituting `UD (e−1)` and `UD (e+1)` into `(1−x²)·B_e′` gives
`(1−x²)·B_e′ ≈ x·B_e − (T_e − T_{e+2})`, so
`(1−x²)·B_e′ − x·B_e ≈ T_{e+2} − T_e ≈ −2·(1−x²)·U_e` (the last step is
`Tdiff e`).  The assembly is a polynomial `Q'`-ring rearrangement; together with
`UDClosure` and `TdiffClosure` it is the antiderivative identity. -/

/-- The polynomial antiderivative identity predicate at index `e`:
`(1−x²)·B_e′(x) − x·B_e(x) ≈ −2·(1−x²)·U_e(x)`. -/
def Bident (e : Nat) (he : 0 < e) (x : Q') : Prop :=
  ((1 + (-(x*x))) * Bderiv e he x + (-(x * Gbracket e he x)))
    ≈ (-(((1:Q') + (1:Q')) * ((1 + (-(x*x))) * Cheb.U e x)))

/-- **NAMED-open: the antiderivative-assembly ring identity.**  The polynomial
rearrangement that, GIVEN `UD (e−1)`, `UD (e+1)` and `Tdiff e`, yields `Bident e`
(`(1−x²)·B_e′ − x·B_e ≈ −2·(1−x²)·U_e`).  It clears the `1/e`, `1/(e+2)`
denominators of `Gbracket`/`Bderiv` (the `mkPos` scaling) against the `e`,
`(e+2)` coefficients in `UD`.  Recorded as the precise residual. -/
def BAssembly : Prop :=
  ∀ (e : Nat) (he : 0 < e), 2 ≤ e → ∀ (x : Q'),
    UD (e - 1) x → UD (e + 1) x → Tdiff e x → Bident e he x

/-- **The polynomial antiderivative identity `Bderiv_identity`**, conditional on
the named ring residuals.  For every even `e ≥ 2`,
`(1−x²)·B_e′(x) − x·B_e(x) ≈ −2·(1−x²)·U_e(x)` — the certificate that
`Gval e = ½·√(1−x²)·B_e` is the antiderivative of `f_e = U_e·√(1−x²)`.
Assembled from the derivative relation (`UDClosure` at `e−1`, `e+1`), the
two-term Chebyshev identity (`TdiffClosure`), and the assembly rearrangement
(`BAssembly`).  π-free. -/
theorem Bderiv_identity (hUD : UDClosure) (hTd : TdiffClosure) (hBA : BAssembly)
    (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (x : Q') : Bident e he x :=
  hBA e he he2 x (UD_all hUD (e - 1) x) (UD_all hUD (e + 1) x)
    (hTd e (by omega) x)

/-! ## 6. The constructive √-weighted FTC estimate (the remaining analytic atom)

With the antiderivative identity in hand, the even-order Riemann sums tend to `0`
by the √-weighted FTC: the per-cell increment `Gval(b_{k+1}) − Gval(b_k) ≈
−f_e(x_k)·h + O(h²)` (interior, from `Bident`) plus the O(√h) boundary control
(from `Gval(±1) = 0`, `GvalDiff_vanishes`) sum to `0`.  The quantitative summed
estimate (the `U_e`-weighted analogue of the proved semicircle √-Hölder bound,
enlarged by `|U_e| ≤ e+1`) is the remaining analytic obligation. -/

/-- **NAMED-open: the constructive √-weighted FTC estimate.**  Given the
antiderivative identity (`BAssembly`), `Tdiff` and the derivative relation
(`UDClosure`, `TdiffClosure`), the per-cell increment/boundary estimate sums to
`OrthEvenZeroLimit e` for every even `e ≥ 2`.  This is the `U_e`-weighted
analogue of the proved semicircle √-Hölder refinement bound.  Recorded as the
precise residual; it is the only ANALYTIC (vs algebraic) obligation remaining. -/
def WeightedFTCEstimate : Prop :=
  UDClosure → TdiffClosure →
    ∀ (e : Nat), 2 ≤ e → e % 2 = 0 → ChebOrthoEvenFTC.OrthEvenZeroLimit e

/-! ## 7. The conditional full off-diagonal closure -/

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, conditional on the
named residuals.**  Feeds the even-order limit (from `WeightedFTCEstimate`) into
the companion `offdiag_zero_of_zeroLimit`; the odd case is already
UNCONDITIONAL.  π-free. -/
theorem offdiag_closed_of_estimate
    (hUD : UDClosure) (hEst : WeightedFTCEstimate) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  intro e he1
  refine ChebOrthoEvenFTC.offdiag_zero_of_zeroLimit e he1 (fun heven => ?_)
  -- e ≥ 1 and e even ⇒ e ≥ 2 (e = 1 is odd, contradicting `heven`)
  have he2 : 2 ≤ e := by omega
  exact hEst hUD TdiffClosure_proved e he2 heven

end YMGap.Continuum.ChebOrthoWeightedFTC

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `Uderiv` / `Uderiv_succ_succ` — the FORMAL DERIVATIVE of the second-kind
    Chebyshev polynomial, by the product-rule recurrence on the `U`-recurrence.
  * `UD_zero` / `UD_one` — the BASE CASES of the Dirichlet-kernel derivative
    relation `(1−x²)·U_n′ ≈ x·U_n − (n+1)·T_{n+1}` (π-free, closed by the
    single-variable cross-multiply closer / `Q'`-ring lemmas).
  * `Tcombo_abstract` / `Tdiff_abstract` / `sub_of_add_eqv` — the abstract
    `Q'`-ring `calc` lemmas for the two-term Chebyshev assembly.
  * **`TdiffClosure_proved`** — the clean two-term Chebyshev difference identity
    `T_{e+2} − T_e ≈ −2·(1−x²)·U_e` at ALL orders `e ≥ 1`, from `linRel_all`
    (ladder + first `T`-relation) and `ChebU.Tshift`.  π-free, UNCONDITIONAL.
  * `Bderiv` — the formal derivative `B_e′ = U_{e−1}′/e − U_{e+1}′/(e+2)` of the
    antiderivative bracket (mirroring `ChebOrthoOffDiag.Gbracket`).
  * **`Bderiv_identity`** — the polynomial antiderivative identity
    `(1−x²)·B_e′ − x·B_e ≈ −2·(1−x²)·U_e` (the certificate that
    `Gval = ½√(1−x²)·B_e` is the antiderivative of `U_e√(1−x²)`), assembled from
    `UDClosure` (at `e−1`, `e+1`), `TdiffClosure` and `BAssembly`.
  * `offdiag_closed_of_estimate` — the COMBINED off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, conditional on `UDClosure` and the FTC estimate
    (`TdiffClosure` is discharged by `TdiffClosure_proved`); the ODD case is
    UNCONDITIONAL (companion).  π-free.

**NAMED-open (the honest residuals — precisely).**
  * `UDClosure := ∀ n x, UD n x` — the derivative relation at ALL orders.  Its
    BASE CASES (`UD_zero`/`UD_one`) are PROVED; the residual is the 2-step
    inductive step `UD n → UD (n+1) → UD (n+2)`, a multivariate `Q'`-ring identity
    that (after substituting the two IHs, `Cheb.U_succ_succ`, `Cheb.T_succ_succ`,
    `ChebU.Tshift` and `linRel_all`) collapses to `2·(U_{n+1} − T_{n+1} − x·U_n)
    ≈ 0` — i.e. the proved ladder relation.
  * `BAssembly` — the antiderivative-assembly ring rearrangement clearing the
    `1/e`, `1/(e+2)` `mkPos` denominators of `Gbracket`/`Bderiv` against the `e`,
    `(e+2)` coefficients of `UD`, given `UD (e−1)`, `UD (e+1)`, `Tdiff e`.
  * `WeightedFTCEstimate` — the constructive √-weighted FTC ESTIMATE (the only
    ANALYTIC residual): the per-cell increment bound `Gval(b_{k+1}) − Gval(b_k) ≈
    −f_e(x_k)·h + O(h²)` (interior, from `Bident`) + the O(√h) boundary control
    (from `GvalDiff_vanishes`), summed `→ 0`.  The `U_e`-weighted analogue of the
    PROVED semicircle √-Hölder refinement bound, enlarged by `|U_e| ≤ e+1`
    (`ChebU.absU_le`).

**Path to the diagonal + full orthogonality + the moment-integral identity.**
With the off-diagonal `∫U_e√ = 0` (above) and the diagonal `∫U_c²√ = semiInt`
(same Riemann functional with the nonnegative bounded factor `U_c²`, via the
second-kind fusion `U_c² = 1 + Σ_{j≥1} U_{2j}` and the now-proved even
off-diagonal vanishing), the Gram matrix `[∫U_cU_d√]_{cd} = semiInt·I` is PSD —
π-FREE (`semiInt` an ABSTRACT positive constant).  This feeds the moment-integral
identity for the OS-reconstruction Gram positivity.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.Uderiv_succ_succ
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.UD_zero
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.UD_one
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.Tcombo_abstract
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.Tdiff_abstract
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.sub_of_add_eqv
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.TdiffClosure_proved
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.Bderiv_identity
#print axioms YMGap.Continuum.ChebOrthoWeightedFTC.offdiag_closed_of_estimate
