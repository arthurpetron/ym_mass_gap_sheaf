/-
# The sin-free x-derivative recast of `CoeffHalfIdentity` (Wall-2, Route A)

`HdconvReroute.CoeffHalfIdentity A` is the Θ-stripped scalar core `A ≈ (½)·S`,
with `S(x) = Σ_{n≥1} 2a^{2n-1}/(1 + 2a^{2n-1}x + a^{4n-2})` the log-derivative
sum (`HKConvGen.sConvCReal_general`, `approx N = HKConv.Spart a x N`).

`CoeffHalfIdentityClose.CoeffCloseResidual` reduced this to THREE `CReal` fields:
`packaging : A ≈ Pd`, `jacobiDeriv : Pd ≈ Sd`, and the trigonometric U-vs-T
`sinFold : Sd ≈ (½)·S`, carrying the `sin2θ = √(1−x²)` fold
`U_{n−1}(cos2θ)·sin2θ = sin2nθ`.

This module performs the **sin-free x-derivative recast**.  The `sin2θ` factor
appears identically on both sides of the fold and cancels; the sharp grading
`T'_m(x) = m·U_{m−1}(x)` is the proved polynomial identity
`ChebTFwdRatioClose.Lcoef x (m+1) = (m+1)·U_m(x)` — NO `sin`, no zero-crossing,
no U-vs-T grading question.  In the x-picture the finite content is a genuine
**real doubled-Leibniz product rule**, over the project's REAL rationals `Q'`,
with NO complex `z = e^{±2iθ}`.

## What is GENUINELY closed here (new, axiom-clean, fully real)

The heat-kernel partial product `RealTheta.factorProd a x N = ∏_{k<N}
factor(a^{2k+1}, x)` has each factor `factor(c, x) = 1 + 2c·x + c²`, whose
**x-derivative is the constant `2c = HKPos.two c`** (no `iz`, no `dz/dθ`).  Its
formal x-derivative by the discrete product rule, `factorProdDx`, satisfies the
genuine **finite log-derivative identity**

    factorProdDx a x N  ≈  factorProd a x N · Spart a x N,                    (LOGD)

where `Spart a x N = Σ_{k<N} 2a^{2k+1}/factor(a^{2k+1}, x)` is exactly the
`S`-partial-sum (`HKConv.Spart`, the `approx N` of `S`).  `(LOGD)` is a clean
product-rule induction: the new factor's x-derivative is `2c`, and the divPos
cancellation `sTerm_k · factor_k ≈ 2c_k` (`HKConv.divPos_mul_eqv`) rebrackets each
Leibniz half.  This is the sin-free replacement of `sinFold` — the real finite
doubled-Leibniz step.  Lifted to the `CReal` level in `factorProdDx_creal_equiv`
(rates never enter; only the per-`N` `Q'` identity does).

## The recast and the honest residual (AGENTS.md Rule 6 / Rule 8)

`XCoeffResidual` is the **2-field** recast of the 3-field `CoeffCloseResidual`:
`packaging : A ≈ Pd` and the single `interchange : Pd ≈ (½)·S`.  The middle
`jacobiDeriv` + `sinFold` collapse into `interchange` — as
`xResidual_of_coeffClose` proves (`interchange = jacobiDeriv.trans sinFold`).  The
finite algebra is re-expressed by `(LOGD)`; what remains in `interchange` is
EXACTLY the C¹ **double-limit interchange** `lim_h lim_N = lim_N lim_h`
(term-by-term x-differentiation of the convergent product) — the identical
irreducible leaf `DiffJTP` carries.  This module does NOT fake that: it lands the
real finite doubled-Leibniz identity honestly and names `interchange` as the sole
residual.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  `interchange` is a named `Type`-level `CReal.Equiv`,
never a `sorry`.
-/

import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.RealTheta
import YMGap.Continuum.HdconvReroute
import YMGap.Continuum.CoeffHalfIdentityClose
import YMGap.Continuum.ChebTFwdRatioClose
import YMGap.Continuum.ThetaLimit
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealMul
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.CoeffChebSineClose

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The sin-free grading `T'_m(x) = m·U_{m−1}(x)` (proved, not a fold)

The x-picture replacement of the trig sin-fold is the polynomial identity
`T'_m = m·U_{m−1}`, already in the repo as `ChebTFwdRatioClose.Lcoef`.  We record
it here — it is a definitional equality, carrying NO `sin`, no `√(1−x²)`, no
zero-crossing. -/

/-- **The sin-free Chebyshev grading.**  `Lcoef x (m+1) = (m+1)·U_m(x) = T'_{m+1}(x)`
(the derivative coefficient), verbatim from `ChebTFwdRatioClose.Lcoef`.  This is
the x-picture replacement of the U-vs-T sin-fold: a proved polynomial identity,
no trigonometry. -/
theorem chebT_deriv_grading (x : Q') (m : Nat) :
    ChebTFwdRatioClose.Lcoef x (m + 1)
      = Q'.ofNat (m + 1) * YMGap.Continuum.Cheb.U m x := rfl

/-! ## 2. The real x-derivative of the heat-kernel factor product

`factor(c, x) = 1 + 2c·x + c²` (`HKPos.factor`) has x-derivative the CONSTANT
`2c = HKPos.two c`.  The formal x-derivative of `factorProd a x N = ∏_{k<N}
factor(a^{2k+1}, x)` is defined by the discrete product rule (Leibniz):

    factorProdDx (N+1) = factorProdDx N · factor_N  +  factorProd N · (2·a^{2N+1}).

This is a genuine finite object (the exact formal derivative), NOT a residual. -/

/-- The formal x-derivative of `RealTheta.factorProd a x N`, by the discrete
product rule.  The new factor `factor(a^{2N+1}, x)` contributes its x-derivative
`HKPos.two (geoAmp a N) = 2·a^{2N+1}`. -/
def factorProdDx (a x : Q') : Nat → Q'
  | 0     => 0
  | N + 1 => factorProdDx a x N * HKPos.factor (HKPos.geoAmp a N) x
              + RealTheta.factorProd a x N * HKPos.two (HKPos.geoAmp a N)

@[simp] theorem factorProdDx_zero (a x : Q') : factorProdDx a x 0 = 0 := rfl

@[simp] theorem factorProdDx_succ (a x : Q') (N : Nat) :
    factorProdDx a x (N + 1)
      = factorProdDx a x N * HKPos.factor (HKPos.geoAmp a N) x
          + RealTheta.factorProd a x N * HKPos.two (HKPos.geoAmp a N) := rfl

/-! ## 3. The finite log-derivative identity `(LOGD)` (the real doubled-Leibniz)

`factorProdDx a x N ≈ factorProd a x N · Spart a x N`, by induction on `N`.  The
step separates `(Fp·f_N)·(Sp + s_N)` into its two Leibniz halves and rebrackets:
the `s_N` half uses the divPos cancellation `s_N·f_N ≈ 2·a^{2N+1}`
(`HKConv.divPos_mul_eqv`), the `Sp` half uses the induction hypothesis.  Pure
`Q'.eqv` ring algebra — NO `sin`, NO complex `z`, NO smallness. -/

/-- **`(LOGD)` — the finite real doubled-Leibniz / log-derivative identity.**
`factorProdDx a x N ≈ factorProd a x N · Spart a x N`.  This is the sin-free
x-picture replacement of the trigonometric U-vs-T fold: the x-derivative of the
finite heat-kernel product equals the product times the `S`-partial-sum, over the
REAL substrate `Q'` (no complex `z`, no q-series, no positivity). -/
theorem logDeriv_factorProd {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) :
    ∀ N, factorProdDx a x N ≈ RealTheta.factorProd a x N * HKConv.Spart a x N
  | 0 => by
      -- 0 ≈ 1 · 0  (factorProd 0 = 1, Spart 0 = 0)
      show factorProdDx a x 0 ≈ RealTheta.factorProd a x 0 * HKConv.Spart a x 0
      exact Q'.eqv_symm (Q'.one_mul_eqv (HKConv.Spart a x 0))
  | N + 1 => by
      have ih : factorProdDx a x N ≈ RealTheta.factorProd a x N * HKConv.Spart a x N :=
        logDeriv_factorProd ha0 ha1 hx N
      -- The divPos cancellation for the new factor:  s_N · f_N ≈ 2·a^{2N+1}.
      have hfact :
          HKConv.sTerm a x N * HKPos.factor (HKPos.geoAmp a N) x
            ≈ HKPos.two (HKPos.geoAmp a N) :=
        HKConv.divPos_mul_eqv (HKConv.factor_num_pos ha0 ha1 hx N)
      -- Leibniz half A (the `Sp` half):  (Fp·f_N)·Sp ≈ factorProdDx N · f_N.
      have hT1 :
          (RealTheta.factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
              * HKConv.Spart a x N
            ≈ factorProdDx a x N * HKPos.factor (HKPos.geoAmp a N) x := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (RealTheta.factorProd a x N)
            (HKPos.factor (HKPos.geoAmp a N) x) (HKConv.Spart a x N)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (RealTheta.factorProd a x N) _ _
            (Q'.mul_comm_eqv (HKPos.factor (HKPos.geoAmp a N) x) (HKConv.Spart a x N))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (RealTheta.factorProd a x N)
            (HKConv.Spart a x N) (HKPos.factor (HKPos.geoAmp a N) x))) ?_
        exact Q'.mul_eqv_congr_right _ _
          (HKPos.factor (HKPos.geoAmp a N) x) (Q'.eqv_symm ih)
      -- Leibniz half B (the `s_N` half):  (Fp·f_N)·s_N ≈ Fp · (2·a^{2N+1}).
      have hT2 :
          (RealTheta.factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
              * HKConv.sTerm a x N
            ≈ RealTheta.factorProd a x N * HKPos.two (HKPos.geoAmp a N) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (RealTheta.factorProd a x N)
            (HKPos.factor (HKPos.geoAmp a N) x) (HKConv.sTerm a x N)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (RealTheta.factorProd a x N) _ _
            (Q'.mul_comm_eqv (HKPos.factor (HKPos.geoAmp a N) x) (HKConv.sTerm a x N))) ?_
        exact Q'.mul_eqv_congr_left (RealTheta.factorProd a x N) _ _ hfact
      -- Assemble:  (Fp·f_N)·(Sp+s_N) ≈ (factorProdDx N · f_N) + (Fp · 2·a^{2N+1}) = LHS.
      have hmain :
          (RealTheta.factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
              * (HKConv.Spart a x N + HKConv.sTerm a x N)
            ≈ factorProdDx a x N * HKPos.factor (HKPos.geoAmp a N) x
                + RealTheta.factorProd a x N * HKPos.two (HKPos.geoAmp a N) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv (RealTheta.factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
            (HKConv.Spart a x N) (HKConv.sTerm a x N)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _
            ((RealTheta.factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
              * HKConv.sTerm a x N) hT1) ?_
        exact Q'.add_eqv_congr_left
          (factorProdDx a x N * HKPos.factor (HKPos.geoAmp a N) x) _ _ hT2
      -- Goal (defeq to the succ forms):  LHS ≈ (Fp·f_N)·(Sp+s_N).
      show factorProdDx a x N * HKPos.factor (HKPos.geoAmp a N) x
            + RealTheta.factorProd a x N * HKPos.two (HKPos.geoAmp a N)
          ≈ (RealTheta.factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
              * (HKConv.Spart a x N + HKConv.sTerm a x N)
      exact Q'.eqv_symm hmain

/-! ## 4. The `N → ∞` `CReal` lift of `(LOGD)`

Any two `CReal`s realising the product-derivative partials `factorProdDx` and the
product·partial-sum `factorProd · Spart` have equal limits.  Rates never enter —
only the per-`N` `Q'` identity `(LOGD)` does (mirrors
`CoeffHalfIdentityClose.qProdDeriv_creal_equiv`). -/

/-- **`(LOGD)` at the `CReal` level.**  If `Pd.approx N = factorProdDx a x N` and
`PS.approx N = factorProd a x N · Spart a x N` for all `N`, then `Equiv Pd PS`.
This is the unconditional `N → ∞` lift of the finite doubled-Leibniz identity. -/
theorem factorProdDx_creal_equiv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    {Pd PS : CReal}
    (hPd : ∀ N : Nat, Pd.approx N = factorProdDx a x N)
    (hPS : ∀ N : Nat, PS.approx N = RealTheta.factorProd a x N * HKConv.Spart a x N) :
    CReal.Equiv Pd PS := by
  refine CReal.Equiv_of_lifted_approx_equal ?_
  intro N
  have heq : Pd.approx N ≈ PS.approx N := by
    rw [hPd N, hPS N]; exact logDeriv_factorProd ha0 ha1 hx N
  exact ThetaLimit.Equiv_ofQ'_of_eqv heq

/-! ## 5. The sin-free recast of `CoeffCloseResidual` and its residual ledger

`XCoeffResidual` drops `sinFold` and collapses `jacobiDeriv` + `sinFold` into the
single `interchange` — the sole irreducible C¹ double-limit leaf.  The recast is
strictly a consolidation: `xResidual_of_coeffClose` produces it from the old
3-field bundle.  `coeffHalfIdentity_of_xResidual` closes `CoeffHalfIdentity` from
the 2-field recast by transitivity. -/

/-- **The sin-free (2-field) recast bundle for `CoeffHalfIdentity`.**  Drops the
trigonometric `sinFold`; the finite algebra is now carried by the real
doubled-Leibniz `(LOGD)`.  Two named `CReal` equivalences:

* `packaging : Equiv A Pd` — the driver / θ↔z packaging (`A` IS the x-derivative
  log-derivative `CReal`), NO complex `z` needed for any finite content.
* `interchange : Equiv Pd ((½)·S)` — the SINGLE irreducible residual: the C¹
  double-limit `lim_h lim_N = lim_N lim_h` (term-by-term x-differentiation of the
  convergent product).  This is the identical leaf `DiffJTP` carries. -/
structure XCoeffResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (A : CReal) : Type where
  /-- The x-derivative log-derivative `CReal`. -/
  Pd : CReal
  /-- Driver / θ↔z packaging: `A` IS the product-derivative `CReal`. -/
  packaging : CReal.Equiv A Pd
  /-- The single C¹ double-limit interchange residual (`= jacobiDeriv ∘ sinFold`). -/
  interchange : CReal.Equiv Pd
    (CReal.mul (CReal.ofQ' HalfPow.half) (HKConvGen.sConvCReal_general ha0 ha1 hx))

/-- **`CoeffHalfIdentity` from the sin-free recast (CLOSED given the 2-field
bundle).**  Transitivity `A ≈ Pd ≈ (½)·S`. -/
theorem coeffHalfIdentity_of_xResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (A : CReal)
    (R : XCoeffResidual ha0 ha1 hx hx1 A) :
    HdconvReroute.CoeffHalfIdentity ha0 ha1 hx hx1 A :=
  R.packaging.trans R.interchange

/-- **The recast subsumes the old bundle.**  From the 3-field
`CoeffHalfIdentityClose.CoeffCloseResidual`, the sin-free `XCoeffResidual` is
obtained by collapsing `jacobiDeriv ∘ sinFold` into the single `interchange`.
This makes precise that the Chebyshev-sine fold RE-EXPRESSES the finite algebra
(`jacobiDeriv`, `sinFold`) but leaves the single interchange leaf unchanged. -/
def xResidual_of_coeffClose {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (A : CReal)
    (R : CoeffHalfIdentityClose.CoeffCloseResidual ha0 ha1 hx hx1 A) :
    XCoeffResidual ha0 ha1 hx hx1 A where
  Pd := R.Pd
  packaging := R.packaging
  interchange := R.jacobiDeriv.trans R.sinFold

end YMGap.Continuum.CoeffChebSineClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CoeffChebSineClose.chebT_deriv_grading
#print axioms YMGap.Continuum.CoeffChebSineClose.factorProdDx_succ
#print axioms YMGap.Continuum.CoeffChebSineClose.logDeriv_factorProd
#print axioms YMGap.Continuum.CoeffChebSineClose.factorProdDx_creal_equiv
#print axioms YMGap.Continuum.CoeffChebSineClose.coeffHalfIdentity_of_xResidual
#print axioms YMGap.Continuum.CoeffChebSineClose.xResidual_of_coeffClose
