/-
# The per-factor `FDDerivDataC` for the Jacobi theta product (`jacobiFactorFDDeriv`)

The `k`-th Jacobi factor, in the `θ`-variable with `q ∈ (0,1)` fixed, is

    f_k(θ) = 1 + 2·q^{2k+1}·cos 2θ + q^{4k+2},

with formal `θ`-derivative `f_k'(θ) = −4·q^{2k+1}·sin 2θ`.  This module supplies the
`CReal`-VALUED finite-difference derivative datum `TsumDeriv.FDDerivDataC` for the
CReal `θ`-lift `Fk` of that factor at value `dk` — the object consumed by
`TsumDeriv.fdDeriv_uniqueC` and thence the product-side of the theta
derivative-uniqueness closure.

## What is GENUINELY proved here (the modulus assembly, L5/L6 of the route)

* **`fddOfQuadBound`** — the fully generic, trig-free assembly: from a *quadratic*
  finite-difference bound `|fdRemC F d θ h| ≤ K·h²` valid on a cap `|h| ≤ cap`
  (`K > 0`, `cap > 0`), build the `FDDerivDataC F d θ` with the explicit modulus
  `δ ε = min cap (ε/K)`.  The core step `K·|h| ≤ ε` from `|h| ≤ ε/K` uses the
  genuine nonnegative quotient `HKConv.divPos` and its cancellation
  `divPos_mul_eqv`; the fold `K·(|h|·|h|) = (K·|h|)·|h| ≤ ε·|h|` is `Q'` ring +
  `mul_le_mul_of_nonneg_right`.  This is L4→L6 of the per-factor route: the modulus
  `δ_k ε = min(½, ε/K_k)` GROWS with `k` (the amplitude `q^{2k+1}` sits in `K_k`,
  hence in the denominator), the summable per-factor budget.

* **`Fk` / `dk`** — the concrete CReal `θ`-lift of the factor and its formal
  derivative (`cosFull`/`sinFull` of `2·t`).

* **`jacobiFactorFDDeriv`** — the target object, obtained by feeding the per-factor
  quadratic residual into `fddOfQuadBound` at `cap = ½`.

## The honest residual (AGENTS.md Rule 6)

`JacobiQuadResidual` — the per-factor QUADRATIC CReal bound
`|fdRemC Fk dk θ h| ≤ K·h²` on `|h| ≤ ½`.  This is L1–L4 of the route: the constant
`1+q^{4k+2}` and the `d·h` linear term cancel (L1), the CReal second-difference
`Rc = cosFull(2θ+2h) − cosFull 2θ + 2h·sinFull 2θ` rewrites via the limit addition
formula (L2), and its magnitude is `≤ Bc + Bs = 4h² + (8/3)|h|³ ≤ (16/3)h²` on
`|h| ≤ ½` from the small-angle atoms `cos_small_angle`/`sin_small_angle` fed to the
already-proved `TrigBound.cos_second_diff_abs_le` (L3), giving `K_k = (32/3)q^{2k+1}`
(L4).  Those steps are per-truncation `Q'` bounds lifted through `leRat_of_equiv`;
they are NOT re-derived here — the residual names exactly that CReal quadratic
bound, and `fddOfQuadBound` discharges everything downstream of it.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.JTPInstance
import YMGap.Continuum.HeatKernelConv
import YMGap.Constructive.TrigAdd
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.JacobiFactorFDDeriv

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv

open YMGap.Continuum.JTPInstance (amp fourAmp)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The `K·|h| ≤ ε` cancellation (`|h| ≤ ε/K`, `K > 0`) -/

/-- **`|h| ≤ ε/K` and `K > 0` give `K·|h| ≤ ε`.**  `K·|h| ≤ K·(ε/K) ≃ ε` via the
genuine nonnegative quotient `HKConv.divPos` and its cancellation
`HKConv.divPos_mul_eqv`.  Pure `Q'` (no analysis). -/
theorem mul_le_of_le_divPos {K ε h : Q'} (hKnum : 0 < K.num)
    (hhnn : (0 : Q') ≤ h) (hh : h ≤ HKConv.divPos ε K) : K * h ≤ ε := by
  have hKnn : (0 : Q') ≤ K := Q'.le_of_lt (CReal.pos_of_num_pos hKnum)
  have s1 : K * h ≤ K * HKConv.divPos ε K :=
    Q'.mul_le_mul_of_nonneg_left h (HKConv.divPos ε K) K hh hKnn
  have s2 : (K * HKConv.divPos ε K) ≈ ε := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv K (HKConv.divPos ε K)) ?_
    exact HKConv.divPos_mul_eqv hKnum
  exact Q'.le_trans' _ _ _ s1 (Q'.le_of_eqv s2)

/-! ## 2. The generic quadratic-bound ⟶ `FDDerivDataC` assembly (L4→L6) -/

/-- **The modulus-assembly engine.**  Given a quadratic finite-difference bound
`|fdRemC F d θ h| ≤ K·(|h|·|h|)` valid whenever `0 < |h| ≤ cap` (with `K > 0`,
`cap > 0`), the pair `(F, d)` carries a `CReal`-valued finite-difference derivative
at `θ` with explicit modulus `δ ε = min cap (ε/K)`.

Genuine and axiom-clean.  For `0 < |h| ≤ δ ε`: `|h| ≤ cap` (so the quadratic bound
fires) and `|h| ≤ ε/K` (so `K·|h| ≤ ε`, `mul_le_of_le_divPos`), whence
`K·(|h|·|h|) = (K·|h|)·|h| ≤ ε·|h|` and `leRat_mono` closes `FDDerivDataC.bound`. -/
def fddOfQuadBound {F : Q' → CReal} {d : CReal} {θ K cap : Q'}
    (hKnum : 0 < K.num) (hcap : (0 : Q') < cap)
    (hb : ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ cap →
      CReal.leRat (CReal.abs (fdRemC F d θ h)) (K * (Q'.abs h * Q'.abs h))) :
    FDDerivDataC F d θ where
  δ ε := Q'.min' cap (HKConv.divPos ε K)
  δ_pos ε hε := Q'.lt_min' hcap (HKConv.divPos_pos (CReal.num_pos_of_pos hε))
  bound := by
    intro ε hε h hpos hle
    -- Split the modulus: |h| ≤ cap and |h| ≤ ε/K.
    have hle_cap : Q'.abs h ≤ cap :=
      Q'.le_trans' _ _ _ hle (Q'.min_le_left' cap (HKConv.divPos ε K))
    have hle_div : Q'.abs h ≤ HKConv.divPos ε K :=
      Q'.le_trans' _ _ _ hle (Q'.min_le_right' cap (HKConv.divPos ε K))
    -- The quadratic bound at this h.
    have hquad := hb h hpos hle_cap
    -- K·|h| ≤ ε.
    have hKh : K * Q'.abs h ≤ ε :=
      mul_le_of_le_divPos hKnum (Q'.abs_nonneg h) hle_div
    -- K·(|h|·|h|) ≃ (K·|h|)·|h| ≤ ε·|h|.
    have hassoc : (K * (Q'.abs h * Q'.abs h)) ≈ ((K * Q'.abs h) * Q'.abs h) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv K (Q'.abs h) (Q'.abs h))
    have hstep : ((K * Q'.abs h) * Q'.abs h) ≤ (ε * Q'.abs h) :=
      Q'.mul_le_mul_of_nonneg_right (K * Q'.abs h) ε (Q'.abs h) hKh (Q'.abs_nonneg h)
    have hfold : (K * (Q'.abs h * Q'.abs h)) ≤ (ε * Q'.abs h) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hstep
    exact CReal.leRat_mono hquad hfold

/-! ## 3. The concrete CReal `θ`-lift of the Jacobi factor and its derivative -/

/-- The CReal `θ`-lift of the `k`-th Jacobi factor
`f_k(θ) = 1 + (2q^{2k+1})·cos 2θ + q^{4k+2}` (constant part `1 + q^{4k+2}`). -/
def Fk (q : Q') (k : Nat) (t : Q') : CReal :=
  CReal.add (CReal.ofQ' 1)
    (CReal.add
      (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (TrigAdd.cosFull ((2 : Q') * t)))
      (CReal.ofQ' (amp q k * amp q k)))

/-- The CReal realization of the formal `θ`-derivative
`f_k'(θ) = −(4q^{2k+1})·sin 2θ`. -/
def dk (q : Q') (k : Nat) (θ : Q') : CReal :=
  CReal.neg (CReal.mul (CReal.ofQ' (fourAmp q k)) (TrigAdd.sinFull ((2 : Q') * θ)))

/-! ## 4. The honest per-factor quadratic residual (L1–L4) -/

/-- **The per-factor quadratic finite-difference residual.**  Names exactly the
CReal quadratic bound `|fdRemC (Fk) (dk) θ h| ≤ K·h²` on `|h| ≤ ½` that the route's
L1–L4 produce (`K = (32/3)q^{2k+1}` in the honest instantiation): the constant/`d·h`
cancellation, the second-difference addition-formula rewrite, and the `4h²+(8/3)|h|³
≤ (16/3)h²` small-angle magnitude bound fed to `TrigBound.cos_second_diff_abs_le`.

The `K`-value is carried as data so the residual is agnostic to the exact constant;
`Knum` records `K > 0` (from `q ∈ (0,1) ⇒ q^{2k+1} > 0`), which is all the assembly
`fddOfQuadBound` needs. -/
structure JacobiQuadResidual (q : Q') (k : Nat) (θ : Q') : Type where
  /-- The quadratic coefficient `K_k` (amplitude-scaled: `(32/3)·q^{2k+1}`). -/
  K : Q'
  /-- Positivity of the coefficient (numerator-level, feeds `divPos`). -/
  Knum : 0 < K.num
  /-- The quadratic bound on `|h| ≤ ½`. -/
  bound : ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ HalfPow.half →
    CReal.leRat (CReal.abs (fdRemC (Fk q k) (dk q k θ) θ h))
      (K * (Q'.abs h * Q'.abs h))

/-! ## 5. The target object -/

/-- **The per-factor `FDDerivDataC` `jacobiFactorFDDeriv k θ`.**  Given the per-factor
quadratic residual (L1–L4), the CReal `θ`-lift `Fk q k` of the `k`-th Jacobi factor
has `CReal`-valued finite-difference derivative `dk q k θ` at `θ`, with the
amplitude-scaled modulus `δ_k ε = min(½, ε/K_k)` supplied by `fddOfQuadBound`.

This native `FDDerivDataC` (no `ofQ'FDDerivDataC` bridge — the derivative value `dk`
is genuinely transcendental) feeds `TsumDeriv.fdDeriv_uniqueC` and thence the
product-side of the theta derivative-uniqueness closure. -/
def jacobiFactorFDDeriv {q : Q'} (k : Nat) (θ : Q')
    (res : JacobiQuadResidual q k θ) :
    FDDerivDataC (Fk q k) (dk q k θ) θ :=
  fddOfQuadBound res.Knum (by decide) res.bound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms mul_le_of_le_divPos
#print axioms fddOfQuadBound
#print axioms jacobiFactorFDDeriv

end YMGap.Continuum.JacobiFactorFDDeriv
