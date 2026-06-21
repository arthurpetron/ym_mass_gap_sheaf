/-
Shared `Pivot2`-level constructive-real algebra — the Continuum-level canonical home
for the `CReal` helpers that the matched-retune / fusion cluster had each rebuilt
locally, and that cannot live at the pointwise `Constructive` level because they need
the genuine `CReal.Equiv` congruences (`Pivot2.mul_congr*`, `Pivot2.add_congr`).

# Layering

  * `Constructive/CRealAlg.lean` — the POINTWISE / limit-free laws (`cmul_assoc`,
    `cmul_comm`, `cone_mul`, `cmul_cone`, `ofQ'_mul`, `csum_add`): each reduces to the
    corresponding `Q'` identity at every approximation index via
    `SumOfSquares.Equiv_of_approx_eqv`, so it needs no product-bound estimate.
  * THIS file (`Continuum/CRealContinuumAlg.lean`) — the `Pivot2`-LEVEL laws: the
    `CReal.Equiv` congruences under `mul`/`add` (`cmul_congr_left`/`_right`,
    `csum_congr`), the constant-pull `csum_const_mul`, the multiplicative-`ofQ'`
    re-export `cofQ'_mul`, and the `crealPowNat` `Nat`-power with its exponent laws
    (`crealPowNat_add`, `crealPowNat_mul3`, `crealPowNat_three_equiv`).  These all rest
    on the genuine `Pivot2` congruences, which need a local-bound product estimate and
    therefore cannot sit at the `Constructive` level.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pointwise `CReal` reductions plus the `Pivot2` congruences; pure `Q'`/`Nat`
arithmetic.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.Pivot2Moments
import YMGap.Continuum.RGTransport
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.CRealContinuumAlg

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.RGTransport

/-! ## 1. `CReal`-multiplication `Equiv` congruences (`Pivot2`-level)

`CReal.mul` is `Equiv`-congruent in each argument; the proof needs the genuine
local-bound product estimate behind `Pivot2.mul_congr_left` / `mul_congr_right`, so
these live here, not at the pointwise `Constructive` level. -/

/-- `CReal.mul` is left-`Equiv`-congruent. -/
theorem cmul_congr_left {A A' B : CReal} (h : CReal.Equiv A A') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B) :=
  Pivot2.mul_congr_left h

/-- `CReal.mul` is right-`Equiv`-congruent. -/
theorem cmul_congr_right {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  Pivot2.mul_congr_right h

/-- `ofQ' (a·b) ≃ ofQ' a · ofQ' b` (re-export of the canonical pointwise
`CRealAlg.ofQ'_mul`, named here for the Continuum-level callers). -/
theorem cofQ'_mul (a b : Q') :
    CReal.Equiv (CReal.ofQ' (a * b)) (CReal.mul (CReal.ofQ' a) (CReal.ofQ' b)) :=
  CRealAlg.ofQ'_mul a b

/-! ## 2. `CReal` finite-sum (`csum`) congruence and constant-pull

`csum` termwise congruence and the left-constant pull `∑(c·A) ≃ c·∑A`.  The
congruence uses `Pivot2.add_congr`; the constant pull uses the pointwise
left-distributivity reduction.  Both are `Pivot2`-level. -/

/-- **`csum` termwise congruence** (via `Pivot2.add_congr`). -/
theorem csum_congr {A B : Nat → CReal} (h : ∀ i, CReal.Equiv (A i) (B i)) (n : Nat) :
    CReal.Equiv (CReal.csum A n) (CReal.csum B n) := by
  induction n with
  | zero => exact Pivot2.equiv_refl _
  | succ m ih =>
      show CReal.Equiv (CReal.add (CReal.csum A m) (A m)) (CReal.add (CReal.csum B m) (B m))
      exact Pivot2.add_congr ih (h m)

/-- **`csum` pulls a `CReal` constant on the left**: `∑(c·A) ≃ c·∑A`. -/
theorem csum_const_mul (c : CReal) (A : Nat → CReal) (n : Nat) :
    CReal.Equiv (CReal.csum (fun i => CReal.mul c (A i)) n)
      (CReal.mul c (CReal.csum A n)) := by
  induction n with
  | zero =>
      -- ∑_{<0}(c·A) = czero ≃ c·czero
      refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
      show (0 : Q').eqv (c.approx p * (0 : Q'))
      exact Q'.eqv_symm (Q'.mul_zero_eqv (c.approx p))
  | succ m ih =>
      show CReal.Equiv (CReal.add (CReal.csum (fun i => CReal.mul c (A i)) m) (CReal.mul c (A m)))
        (CReal.mul c (CReal.add (CReal.csum A m) (A m)))
      refine Pivot2.equiv_trans (Pivot2.add_congr ih (Pivot2.equiv_refl _)) ?_
      -- c·(∑A) + c·(A m) ≃ c·(∑A + A m)  : left-distributivity, pointwise
      refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
      show (c.approx p * (CReal.csum A m).approx p + c.approx p * (A m).approx p).eqv
        (c.approx p * ((CReal.csum A m).approx p + (A m).approx p))
      exact Q'.eqv_symm (Q'.mul_add_eqv (c.approx p) ((CReal.csum A m).approx p) ((A m).approx p))

/-! ## 3. The `CReal`-to-`Nat` power `crealPowNat` and its exponent laws

The matched full-mode coefficient is `ĉ_s = (s+1)·ρ^{C₄(s)}`, so the matched-retune
carrier needs a `Nat` power of the `CReal` base `ρ`.  We define it pointwise via
`CReal.mul` and prove the exponent laws here (they need the `Pivot2` congruences),
so both the carrier (`MatchedRetune`) and its bracket bridge can reuse them. -/

/-- The `Nat` power of a constructive real, `x^n`, defined by `x^0 = 1`,
`x^(n+1) = x^n · x` (pointwise via `CReal.mul`). -/
def crealPowNat (x : CReal) : Nat → CReal
  | 0 => CReal.cone
  | n + 1 => CReal.mul (crealPowNat x n) x

@[simp] theorem crealPowNat_zero (x : CReal) : crealPowNat x 0 = CReal.cone := rfl
@[simp] theorem crealPowNat_succ (x : CReal) (n : Nat) :
    crealPowNat x (n + 1) = CReal.mul (crealPowNat x n) x := rfl

/-- `crealPowNat x 3 ≃ (x·x)·x` (drop the `crealPowNat` base `cone`). -/
theorem crealPowNat_three_equiv (x : CReal) :
    CReal.Equiv (crealPowNat x 3) (CReal.mul (CReal.mul x x) x) := by
  -- crealPowNat x 3 = (((cone·x)·x)·x); strip the leading `cone·x ≃ x`.
  show CReal.Equiv (CReal.mul (CReal.mul (CReal.mul CReal.cone x) x) x)
      (CReal.mul (CReal.mul x x) x)
  exact cmul_congr_left (cmul_congr_left (cone_mul x))

/-- **`crealPowNat` additive exponent law** `x^{a+b} ≃ x^a · x^b`. -/
theorem crealPowNat_add (x : CReal) (a : Nat) :
    ∀ b, CReal.Equiv (crealPowNat x (a + b))
      (CReal.mul (crealPowNat x a) (crealPowNat x b))
  | 0 => by
      -- x^{a+0} = x^a ≃ x^a·1 = x^a·x^0
      show CReal.Equiv (crealPowNat x a)
        (CReal.mul (crealPowNat x a) CReal.cone)
      exact CReal.Equiv.symm (cmul_cone (crealPowNat x a))
  | b + 1 => by
      -- x^{a+(b+1)} = x^{(a+b)+1} = x^{a+b}·x ≃ (x^a·x^b)·x ≃ x^a·(x^b·x) = x^a·x^{b+1}
      show CReal.Equiv (CReal.mul (crealPowNat x (a + b)) x)
        (CReal.mul (crealPowNat x a) (CReal.mul (crealPowNat x b) x))
      refine CReal.Equiv.trans (cmul_congr_left (crealPowNat_add x a b)) ?_
      exact cmul_assoc (crealPowNat x a) (crealPowNat x b) x

/-- **`crealPowNat` triple-exponent collapse** `x^{3m} ≃ ofQ'(Rᵐ)`, given the cube
identity `x³ ≃ ofQ' R`.  Induction on `m`: `x^{3(m+1)} = x^{3m+3} ≃ x^{3m}·x³ ≃
ofQ'(Rᵐ)·ofQ' R ≃ ofQ'(Rᵐ·R) = ofQ'(R^{m+1})`. -/
theorem crealPowNat_mul3 (x : CReal) (R : Q') (hcube : CReal.Equiv (crealPowNat x 3) (CReal.ofQ' R)) :
    ∀ m, CReal.Equiv (crealPowNat x (3 * m)) (CReal.ofQ' (qpow R m))
  | 0 => by
      -- x^0 = cone = ofQ' 1 = ofQ'(R^0)
      show CReal.Equiv (crealPowNat x (3 * 0)) (CReal.ofQ' (qpow R 0))
      rw [Nat.mul_zero, qpow_zero]
      exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  | m + 1 => by
      -- x^{3(m+1)} = x^{3m + 3}
      have hsplit : 3 * (m + 1) = 3 * m + 3 := by omega
      rw [hsplit]
      -- x^{3m+3} ≃ x^{3m}·x^3
      refine CReal.Equiv.trans (crealPowNat_add x (3 * m) 3) ?_
      -- x^{3m}·x^3 ≃ ofQ'(R^m)·ofQ' R
      refine CReal.Equiv.trans
        (Pivot2.mul_congr (crealPowNat_mul3 x R hcube m) hcube) ?_
      -- ofQ'(R^m)·ofQ' R ≃ ofQ'(R^m · R) = ofQ'(R^{m+1})
      show CReal.Equiv (CReal.mul (CReal.ofQ' (qpow R m)) (CReal.ofQ' R))
        (CReal.ofQ' (qpow R (m + 1)))
      refine CReal.Equiv.symm ?_
      show CReal.Equiv (CReal.ofQ' (qpow R m * R))
        (CReal.mul (CReal.ofQ' (qpow R m)) (CReal.ofQ' R))
      exact ofQ'_mul (qpow R m) R

end YMGap.Continuum.CRealContinuumAlg

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CRealContinuumAlg.cmul_congr_left
#print axioms YMGap.Continuum.CRealContinuumAlg.cmul_congr_right
#print axioms YMGap.Continuum.CRealContinuumAlg.cofQ'_mul
#print axioms YMGap.Continuum.CRealContinuumAlg.csum_congr
#print axioms YMGap.Continuum.CRealContinuumAlg.csum_const_mul
#print axioms YMGap.Continuum.CRealContinuumAlg.crealPowNat_three_equiv
#print axioms YMGap.Continuum.CRealContinuumAlg.crealPowNat_add
#print axioms YMGap.Continuum.CRealContinuumAlg.crealPowNat_mul3
