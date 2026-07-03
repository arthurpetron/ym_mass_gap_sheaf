/-
# Closing the series-side `fdbound` / pointwise fields of the theta `C¹` inputs

`ThetaSeriesFieldsClose` reduced the series-side finite-difference derivative
`Dser` to the named residual `ThetaSeriesResidual` (fields `ptθ`, `ptθh`,
`fdbound`), with the `unif` field genuinely discharged (`seriesUnif`).  This
module SHARPENS that reduction on the load-bearing `fdbound` field.

## What is GENUINELY proved here (new, axiom-clean content)

* **`fdRem_split`** — THE structural bridge.  The finite-difference remainder of
  the Chebyshev-`T` truncation `chebTTrunc a M` against its termwise derivative
  `dPartial a x M` splits, termwise, into the per-term forward Taylor remainders:

      fdRem (chebTTrunc a M) (dPartial a x M) x h
        ≈ Σ_{n<M} fwdTermRem a x n h ,

  `fwdTermRem a x n h = a^{(n+1)²}·[T_{n+1}(x+h) − T_{n+1}(x) − (n+1)·U_n(x)·h]`.
  Proved by the `finSum` algebra (`finSum_add`, `finSum_neg`, `finSum_mul_const`);
  this turns the monolithic `fdbound` field into a per-term obligation.

* **`mul_bracket_eqv` / `abs_fwdTermRem_le`** — the per-term factoring
  `fwdTermRem = a^{(n+1)²}·chebTBracket` and the resulting magnitude bound
  `|fwdTermRem a x n h| ≤ (a^{(n+1)²}·K)·(|h|·|h|)` from the bracket bound.

* **`fdbound_holds`** — the FULLY ASSEMBLED `fdbound` field, built from the two
  honest per-term residuals (`ChebTFwdBound`, `FwdSummable`) via `fdRem_split`,
  the finite-sum triangle inequality, and the `divPos` modulus algebra.  The
  cleared bound `|fdRem| ≤ ε'·|h|` holds with `delStar ε' = min(½, ε'/Csum)`.

## The honest residuals (AGENTS.md Rule 6)

* **`ChebTFwdBound x`** — the per-term second-order forward Taylor bound
  `|T_{n+1}(x+h) − T_{n+1}(x) − (n+1)·U_n(x)·h| ≤ K_T(n)·|h|²` on `|h| ≤ ½`
  (the one-sided `T`-analogue of the centered `U`-remainder `ChebMarkovModulus`;
  a bounded-modulus induction, NOT an open theorem).

* **`FwdSummable a K_T`** — the uniform-in-`M` partial-sum bound
  `Σ_{n<M} a^{(n+1)²}·K_T(n) ≤ Csum` (Gaussian decay beats the polynomial
  majorant `K_T`; a convergent-`CReal` construction).

* **`ThetaPtwiseData a x F`** — the two `F`-entangled undifferentiated theta
  pointwise limits `chebTTrunc a M · → F` at `x` and every `x+h`.

`thetaSeriesC1` assembles the full series-side `Dser` from these three residuals
plus the proved `seriesUnif`: a sharp honest reduction with the `unif` and
`fdbound` engines genuinely discharged, and only the per-term Taylor / summability
/ pointwise data remaining.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.ChebyshevBound
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.ThetaSeriesC1Close

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small `Q'`/`finSum` helpers re-proved locally (no heavy imports) -/

/-- `min' p q ≤ p`. -/
theorem min'_le_left (p q : Q') : Q'.min' p q ≤ p := by
  unfold Q'.min'
  split
  · exact Q'.le_refl' p
  · rename_i hnp
    show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
    exact Int.le_of_lt (Int.not_le.mp hnp)

/-- `min' p q ≤ q`. -/
theorem min'_le_right (p q : Q') : Q'.min' p q ≤ q := by
  unfold Q'.min'
  split
  · rename_i h; exact h
  · exact Q'.le_refl' q

/-- A located min of two strictly-positive rationals is strictly positive. -/
theorem min'_pos {p q : Q'} (hp : (0 : Q') < p) (hq : (0 : Q') < q) :
    (0 : Q') < Q'.min' p q := by
  unfold Q'.min'
  split
  · exact hp
  · exact hq

/-- `0 < ½`. -/
theorem half_pos : (0 : Q') < HalfPow.half := by decide

/-- `Σ (−f) ≃ −(Σ f)`. -/
theorem finSum_neg (f : Nat → Q') :
    ∀ n, (RationalTail.finSum (fun i => -(f i)) n) ≈ (-(RationalTail.finSum f n))
  | 0 => by
    show (0 : Q') ≈ -(0 : Q')
    decide
  | n + 1 => by
    show (RationalTail.finSum (fun i => -(f i)) n + -(f n))
        ≈ (-(RationalTail.finSum f n + f n))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(f n)) (finSum_neg f n)) ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv (RationalTail.finSum f n) (f n))

/-- The finite-sum triangle inequality. -/
theorem abs_finSum_le (g : Nat → Q') :
    ∀ n, Q'.abs (RationalTail.finSum g n)
        ≤ RationalTail.finSum (fun k => Q'.abs (g k)) n
  | 0 => by
    show Q'.abs (0 : Q') ≤ (0 : Q')
    exact Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0))
  | n + 1 => by
    show Q'.abs (RationalTail.finSum g n + g n)
        ≤ RationalTail.finSum (fun k => Q'.abs (g k)) n + Q'.abs (g n)
    exact Q'.le_trans' _ _ _
      (TsumDeriv.abs_add_le (RationalTail.finSum g n) (g n))
      (Q'.add_le_add_right _ _ _ (abs_finSum_le g n))

/-- Termwise `≤` lifts to finite sums. -/
theorem finSum_le_termwise (f g : Nat → Q') (h : ∀ k, f k ≤ g k) :
    ∀ n, RationalTail.finSum f n ≤ RationalTail.finSum g n
  | 0 => by
    show (0 : Q') ≤ (0 : Q')
    exact Q'.le_refl' 0
  | n + 1 => by
    show RationalTail.finSum f n + f n ≤ RationalTail.finSum g n + g n
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (RationalTail.finSum f n) (f n) (g n) (h n))
      (Q'.add_le_add_right (RationalTail.finSum f n) (RationalTail.finSum g n) (g n)
        (finSum_le_termwise f g h n))

/-! ## 1. The per-term objects -/

/-- The `n`-th Chebyshev-`T` truncation term `a^{(n+1)²}·T_{n+1}(y)`.  Defeq to the
per-index summand of `ThetaSeriesFDDeriv.chebTTrunc`. -/
def chebTTerm (a : Q') (n : Nat) (y : Q') : Q' :=
  a ^ ((n + 1) * (n + 1)) * Cheb.T (n + 1) y

/-- The per-term forward second-order Taylor remainder (linear part cancelled):
`a^{(n+1)²}·T_{n+1}(x+h) − a^{(n+1)²}·T_{n+1}(x) − dTerm a x n·h`.  This is the
`n`-th summand of the split of `fdRem (chebTTrunc a M) (dPartial a x M) x h`. -/
def fwdTermRem (a x : Q') (n : Nat) (h : Q') : Q' :=
  ((chebTTerm a n (x + h)) + (-(chebTTerm a n x))) + (-(JTPIdentity.dTerm a x n * h))

/-- The dimensionless forward Taylor bracket
`T_{n+1}(x+h) − T_{n+1}(x) − (n+1)·U_n(x)·h`.  `fwdTermRem = a^{(n+1)²}·bracket`. -/
def chebTBracket (x : Q') (n : Nat) (h : Q') : Q' :=
  ((Cheb.T (n + 1) (x + h)) + (-(Cheb.T (n + 1) x)))
    + (-((Q'.ofNat (n + 1) * Cheb.U n x) * h))

/-! ## 2. The per-term factoring `fwdTermRem = a^{(n+1)²}·chebTBracket` -/

/-- The linear-term reassociation `a^{(n+1)²}·((n+1)·U_n(x)·h) ≃ dTerm a x n·h`. -/
theorem cN_lin_eqv (a x : Q') (n : Nat) (h : Q') :
    a ^ ((n + 1) * (n + 1)) * ((Q'.ofNat (n + 1) * Cheb.U n x) * h)
      ≈ JTPIdentity.dTerm a x n * h := by
  -- inner : cN·((of·U)) ≃ (of·cN)·U
  have hInner :
      a ^ ((n + 1) * (n + 1)) * (Q'.ofNat (n + 1) * Cheb.U n x)
        ≈ (Q'.ofNat (n + 1) * a ^ ((n + 1) * (n + 1))) * Cheb.U n x := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (a ^ ((n + 1) * (n + 1))) (Q'.ofNat (n + 1))
        (Cheb.U n x))) ?_
    exact Q'.mul_eqv_congr_right _ _ (Cheb.U n x)
      (Q'.mul_comm_eqv (a ^ ((n + 1) * (n + 1))) (Q'.ofNat (n + 1)))
  -- cN·((of·U)·h) ≃ (cN·(of·U))·h ≃ ((of·cN)·U)·h = dTerm·h
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (a ^ ((n + 1) * (n + 1)))
      (Q'.ofNat (n + 1) * Cheb.U n x) h)) ?_
  exact Q'.mul_eqv_congr_right _ _ h hInner

/-- **The per-term factoring** `a^{(n+1)²}·chebTBracket ≃ fwdTermRem`. -/
theorem mul_bracket_eqv (a x : Q') (n : Nat) (h : Q') :
    a ^ ((n + 1) * (n + 1)) * chebTBracket x n h ≈ fwdTermRem a x n h := by
  show a ^ ((n + 1) * (n + 1))
      * (((Cheb.T (n + 1) (x + h)) + (-(Cheb.T (n + 1) x)))
          + (-((Q'.ofNat (n + 1) * Cheb.U n x) * h)))
      ≈ fwdTermRem a x n h
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (a ^ ((n + 1) * (n + 1)))
      ((Cheb.T (n + 1) (x + h)) + (-(Cheb.T (n + 1) x)))
      (-((Q'.ofNat (n + 1) * Cheb.U n x) * h))) ?_
  refine TsumDeriv.Q'.add_eqv_congr ?_ ?_
  · -- cN·(T(x+h) + -T(x)) ≃ cN·T(x+h) + -(cN·T(x))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (a ^ ((n + 1) * (n + 1))) (Cheb.T (n + 1) (x + h))
        (-(Cheb.T (n + 1) x))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv (a ^ ((n + 1) * (n + 1))) (Cheb.T (n + 1) x))
  · -- cN·(-(lin)) ≃ -(dTerm·h)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_neg_eqv (a ^ ((n + 1) * (n + 1)))
        ((Q'.ofNat (n + 1) * Cheb.U n x) * h)) ?_
    exact Q'.neg_eqv_congr _ _ (cN_lin_eqv a x n h)

/-! ## 3. The structural split of the truncation remainder -/

/-- **THE STRUCTURAL BRIDGE.**  The Chebyshev-`T` truncation finite-difference
remainder splits termwise into per-term forward Taylor remainders. -/
theorem fdRem_split (a x h : Q') (M : Nat) :
    TsumDeriv.fdRem (ThetaSeriesFDDeriv.chebTTrunc a M)
        (ThetaSeriesFDDeriv.dPartialFam a M x) x h
      ≈ RationalTail.finSum (fun n => fwdTermRem a x n h) M := by
  refine Q'.eqv_symm ?_
  show RationalTail.finSum (fun n => fwdTermRem a x n h) M
      ≈ (((ThetaSeriesFDDeriv.chebTTrunc a M (x + h))
            + (-(ThetaSeriesFDDeriv.chebTTrunc a M x)))
          + (-((ThetaSeriesFDDeriv.dPartialFam a M x) * h)))
  -- outer split : Σ fwdTermRem ≃ Σ (chebTTerm(x+h) + -chebTTerm(x)) + Σ (-(dTerm·h))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add
      (fun n => chebTTerm a n (x + h) + (-(chebTTerm a n x)))
      (fun n => -(JTPIdentity.dTerm a x n * h)) M) ?_
  refine TsumDeriv.Q'.add_eqv_congr ?_ ?_
  · -- Σ (chebTTerm(x+h) + -chebTTerm(x)) ≃ chebTTrunc(x+h) + -chebTTrunc(x)
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_add (fun n => chebTTerm a n (x + h))
        (fun n => -(chebTTerm a n x)) M) ?_
    exact Q'.add_eqv_congr_left _ _ _ (finSum_neg (fun n => chebTTerm a n x) M)
  · -- Σ (-(dTerm·h)) ≃ -(dPartial·h)
    refine Q'.eqv_trans _ _ _ (finSum_neg (fun n => JTPIdentity.dTerm a x n * h) M) ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.eqv_symm (RationalTail.finSum_mul_const (JTPIdentity.dTerm a x) h M))

/-! ## 4. The per-term magnitude bound from a bracket bound -/

/-- From a bracket bound `|chebTBracket x n h| ≤ K·|h|²`, the per-term remainder is
bounded by `(a^{(n+1)²}·K)·|h|²`. -/
theorem abs_fwdTermRem_le {a x : Q'} (ha0 : (0 : Q') < a) (n : Nat) (h : Q') (K : Nat)
    (hbr : Q'.abs (chebTBracket x n h) ≤ Q'.ofNat K * (Q'.abs h * Q'.abs h)) :
    Q'.abs (fwdTermRem a x n h)
      ≤ (a ^ ((n + 1) * (n + 1)) * Q'.ofNat K) * (Q'.abs h * Q'.abs h) := by
  have hcN : (0 : Q') ≤ a ^ ((n + 1) * (n + 1)) :=
    Q'.pow_nonneg a (Q'.le_of_lt ha0) _
  have hfac : fwdTermRem a x n h ≈ a ^ ((n + 1) * (n + 1)) * chebTBracket x n h :=
    Q'.eqv_symm (mul_bracket_eqv a x n h)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr hfac)) ?_
  refine Q'.le_trans' _ _ _
    (TsumDeriv.Q'.abs_mul_le (a ^ ((n + 1) * (n + 1))) (chebTBracket x n h)) ?_
  -- |cN|·|bracket| ≤ cN·|bracket|
  have hAbsCN : Q'.abs (a ^ ((n + 1) * (n + 1))) ≈ a ^ ((n + 1) * (n + 1)) :=
    TsumDeriv.Q'.abs_of_nonneg hcN
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (Q'.abs (a ^ ((n + 1) * (n + 1))))
      (a ^ ((n + 1) * (n + 1))) (Q'.abs (chebTBracket x n h))
      (Q'.le_of_eqv hAbsCN) (Q'.abs_nonneg _)) ?_
  -- cN·|bracket| ≤ cN·(K·|h|²) ≃ (cN·K)·|h|²
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hbr hcN) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_assoc_eqv (a ^ ((n + 1) * (n + 1))) (Q'.ofNat K)
      (Q'.abs h * Q'.abs h)))

/-! ## 5. The honest per-term residuals -/

/-- **The per-term forward Taylor bound** (the `ChebTFwdTaylor` atom): a `Nat`
majorant `K_T` with `|T_{n+1}(x+h) − T_{n+1}(x) − (n+1)·U_n(x)·h| ≤ K_T(n)·|h|²`
on the box `|h| ≤ ½`.  The one-sided `T`-analogue of the centered `U`-remainder
`ChebMarkovModulus.QB_all` — a bounded-modulus induction, NOT closed here. -/
structure ChebTFwdBound (x : Q') : Type where
  /-- The degree-4 forward-Taylor majorant. -/
  KT : Nat → Nat
  /-- The per-term second-order bound on the box `|h| ≤ ½`. -/
  bound : ∀ n : Nat, ∀ h : Q', Q'.abs h ≤ HalfPow.half →
    Q'.abs (chebTBracket x n h) ≤ Q'.ofNat (KT n) * (Q'.abs h * Q'.abs h)

/-- **The uniform partial-sum bound** for the Gaussian-weighted majorant:
`Σ_{n<M} a^{(n+1)²}·K_T(n) ≤ Csum` for all `M`, with `Csum > 0`.  The
Gaussian-beats-polynomial summability of the forward-Taylor constants — a
convergent-`CReal` construction, NOT closed here. -/
structure FwdSummable (a : Q') (KT : Nat → Nat) : Type where
  /-- The summed constant. -/
  Csum : Q'
  /-- `Csum` is strictly positive. -/
  Csum_pos : (0 : Q') < Csum
  /-- Uniform-in-`M` partial-sum bound. -/
  partial_le : ∀ M : Nat,
    RationalTail.finSum (fun n => a ^ ((n + 1) * (n + 1)) * Q'.ofNat (KT n)) M ≤ Csum

/-- **The two `F`-entangled undifferentiated theta pointwise limits.** -/
structure ThetaPtwiseData (a x : Q') (F : Q' → CReal) : Type where
  /-- Pointwise convergence of the Chebyshev truncations to `F` at `x`. -/
  ptθ : ThetaSeriesFDDeriv.PtwiseConvC (ThetaSeriesFDDeriv.chebTTrunc a) F x
  /-- Pointwise convergence of the Chebyshev truncations to `F` at every `x+h`. -/
  ptθh : ∀ h : Q',
    ThetaSeriesFDDeriv.PtwiseConvC (ThetaSeriesFDDeriv.chebTTrunc a) F (x + h)

/-! ## 6. The assembled `fdbound` field -/

/-- **THE ASSEMBLED `fdbound` FIELD.**  From the per-term Taylor bound
(`ChebTFwdBound`) and the uniform summability (`FwdSummable`), the Chebyshev-`T`
truncation has the cleared finite-difference bound `|fdRem| ≤ ε'·|h|` with modulus
`delStar ε' = min(½, ε'/Csum)`.  Routes through `fdRem_split`, the finite-sum
triangle inequality, and the `divPos` cancellation. -/
theorem fdbound_holds {a x : Q'} (ha0 : (0 : Q') < a)
    (fb : ChebTFwdBound x) (sm : FwdSummable a fb.KT) :
    ∀ ε' : Q', (0 : Q') < ε' → ∀ M : Nat, (0 : Nat) ≤ M →
      ∀ h : Q', (0 : Q') < Q'.abs h →
        Q'.abs h ≤ Q'.min' HalfPow.half (HKConv.divPos ε' sm.Csum) →
          Q'.abs (TsumDeriv.fdRem (ThetaSeriesFDDeriv.chebTTrunc a M)
            (ThetaSeriesFDDeriv.dPartialFam a M x) x h) ≤ ε' * Q'.abs h := by
  intro ε' hε' M _ h hhpos hhle
  have hhalf : Q'.abs h ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ hhle (min'_le_left _ _)
  have hdiv : Q'.abs h ≤ HKConv.divPos ε' sm.Csum :=
    Q'.le_trans' _ _ _ hhle (min'_le_right _ _)
  -- Step 1 : |fdRem| ≤ Σ |fwdTermRem|
  have hsplit := fdRem_split a x h M
  have habs1 :
      Q'.abs (TsumDeriv.fdRem (ThetaSeriesFDDeriv.chebTTrunc a M)
          (ThetaSeriesFDDeriv.dPartialFam a M x) x h)
        ≤ RationalTail.finSum (fun n => Q'.abs (fwdTermRem a x n h)) M := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr hsplit)) ?_
    exact abs_finSum_le (fun n => fwdTermRem a x n h) M
  -- Step 2 : termwise bound
  have hterm : ∀ n,
      Q'.abs (fwdTermRem a x n h)
        ≤ (a ^ ((n + 1) * (n + 1)) * Q'.ofNat (fb.KT n)) * (Q'.abs h * Q'.abs h) :=
    fun n => abs_fwdTermRem_le ha0 n h (fb.KT n) (fb.bound n h hhalf)
  have hsum2 :
      RationalTail.finSum (fun n => Q'.abs (fwdTermRem a x n h)) M
        ≤ RationalTail.finSum
            (fun n => (a ^ ((n + 1) * (n + 1)) * Q'.ofNat (fb.KT n))
              * (Q'.abs h * Q'.abs h)) M :=
    finSum_le_termwise _ _ hterm M
  -- Step 3 : Σ coef·|h|² ≃ (Σ coef)·|h|² ≤ Csum·|h|²
  have hhh_nn : (0 : Q') ≤ Q'.abs h * Q'.abs h :=
    Q'.mul_nonneg _ _ (Q'.abs_nonneg h) (Q'.abs_nonneg h)
  have hsum3 :
      RationalTail.finSum
          (fun n => (a ^ ((n + 1) * (n + 1)) * Q'.ofNat (fb.KT n))
            * (Q'.abs h * Q'.abs h)) M
        ≈ (RationalTail.finSum
            (fun n => a ^ ((n + 1) * (n + 1)) * Q'.ofNat (fb.KT n)) M)
            * (Q'.abs h * Q'.abs h) :=
    Q'.eqv_symm (RationalTail.finSum_mul_const
      (fun n => a ^ ((n + 1) * (n + 1)) * Q'.ofNat (fb.KT n)) (Q'.abs h * Q'.abs h) M)
  have hcoef_le :
      (RationalTail.finSum
          (fun n => a ^ ((n + 1) * (n + 1)) * Q'.ofNat (fb.KT n)) M)
          * (Q'.abs h * Q'.abs h)
        ≤ sm.Csum * (Q'.abs h * Q'.abs h) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (sm.partial_le M) hhh_nn
  -- Step 4 : Csum·|h|² ≤ ε'·|h|
  have hCsumnum : 0 < sm.Csum.num := CReal.num_pos_of_pos sm.Csum_pos
  have hcancel : sm.Csum * HKConv.divPos ε' sm.Csum ≈ ε' :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv sm.Csum (HKConv.divPos ε' sm.Csum))
      (HKConv.divPos_mul_eqv hCsumnum)
  have hCh : sm.Csum * Q'.abs h ≤ ε' :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (Q'.abs h) (HKConv.divPos ε' sm.Csum)
        sm.Csum hdiv (Q'.le_of_lt sm.Csum_pos))
      (Q'.le_of_eqv hcancel)
  have hstep5 : sm.Csum * (Q'.abs h * Q'.abs h) ≤ ε' * Q'.abs h := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.mul_assoc_eqv sm.Csum (Q'.abs h) (Q'.abs h)))) ?_
    exact Q'.mul_le_mul_of_nonneg_right (sm.Csum * Q'.abs h) ε' (Q'.abs h)
      hCh (Q'.abs_nonneg h)
  -- assemble
  refine Q'.le_trans' _ _ _ habs1 ?_
  refine Q'.le_trans' _ _ _ hsum2 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum3) ?_
  exact Q'.le_trans' _ _ _ hcoef_le hstep5

/-! ## 7. The assembled series-side theta derivative -/

/-- **THE SERIES-SIDE THETA DERIVATIVE (reduced to the sharp per-term residuals).**
From the two `F`-entangled pointwise limits (`ThetaPtwiseData`), the per-term
forward Taylor bound (`ChebTFwdBound`), and the uniform summability
(`FwdSummable`), the `K_t`-side series `dSeriesCReal` is a CReal-valued
finite-difference derivative of the common `F` at `x`.  The `unif` and `fdbound`
engines are BOTH genuinely discharged here (`seriesUnif`, `fdbound_holds`); only
the per-term Taylor / summability / pointwise data remain as honest residuals. -/
def thetaSeriesC1 {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (pt : ThetaPtwiseData a x F)
    (fb : ChebTFwdBound x)
    (sm : FwdSummable a fb.KT) :
    TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x :=
  ThetaSeriesFieldsClose.thetaSeriesFDDeriv_of_residual ha0 ha1 hx hx1 F
    { ptθ := pt.ptθ
      ptθh := pt.ptθh
      delStar := fun ε' => Q'.min' HalfPow.half (HKConv.divPos ε' sm.Csum)
      delStar_pos := fun _ε' hε' =>
        min'_pos half_pos (HKConv.divPos_pos (CReal.num_pos_of_pos hε'))
      mStar := fun _ => 0
      fdbound := fdbound_holds ha0 fb sm }

end YMGap.Continuum.ThetaSeriesC1Close

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaSeriesC1Close.finSum_neg
#print axioms YMGap.Continuum.ThetaSeriesC1Close.abs_finSum_le
#print axioms YMGap.Continuum.ThetaSeriesC1Close.mul_bracket_eqv
#print axioms YMGap.Continuum.ThetaSeriesC1Close.fdRem_split
#print axioms YMGap.Continuum.ThetaSeriesC1Close.abs_fwdTermRem_le
#print axioms YMGap.Continuum.ThetaSeriesC1Close.fdbound_holds
#print axioms YMGap.Continuum.ThetaSeriesC1Close.thetaSeriesC1
