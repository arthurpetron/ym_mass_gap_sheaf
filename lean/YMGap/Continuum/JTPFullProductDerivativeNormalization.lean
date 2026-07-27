/-
# Full Jacobi-product derivative normalization

The differentiated Jacobi identity in `JTPIdentity` has a necessary factor
`1/2`:

    dSeries = (1/2) * Theta * S.

This module makes the corresponding finite-product normalization explicit.
The full Jacobi factor is

    g_k(x) = (1 - a^(2k+2)) * (1 + 2 a^(2k+1) x + a^(4k+2)).

Its formal x-derivative is

    g'_k = (1 - a^(2k+2)) * 2 a^(2k+1).

The discrete Leibniz derivative of the first `N` full factors is therefore

    (Ppart_N)' = Ppart_N * Spart_N.

Thus the full product derivative has the unhalved target
`Rproduct = Theta*S`.  The series truncation used by
`ThetaSeriesFDDeriv.chebTTrunc`,

    sum_{n < N} a^((n+1)^2) T_(n+1),

is the nonconstant *half* of theta, so its derivative has the halved target
`Rhalf`.  Any common-function derivative argument must first prove and use the
affine normalization

    Theta = 1 + 2 * chebTConv,

not identify `Theta` directly with `chebTConv`.

Everything below is finite algebra plus the standard limit-of-matched-
approximations lift.  It does not assume the missing Jacobi identity.

## Axiom gate

Only `[propext]` / `[propext, Quot.sound]`.  No `Classical`, no
`native_decide`, no `sorry`, and no custom axiom.
-/

import YMGap.Continuum.CoeffChebSineClose
import YMGap.Continuum.ThetaProdConvClose
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.JTPIdentity

namespace YMGap.Continuum.JTPFullProductDerivativeNormalization

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Per-factor and finite full-product derivatives -/

/-- The formal x-derivative of the full Jacobi factor `ThetaConv.gFac a x k`.
The Euler prefactor is independent of `x`; the heat factor has derivative
`2*a^(2k+1)`. -/
def gFacDx (a : Q') (k : Nat) : Q' :=
  (1 + (-(ThetaConv.uAmp a k))) * HKPos.two (HKPos.geoAmp a k)

/-- The exact finite Leibniz derivative of the full Jacobi partial product,
written through the generic finite-product derivative recursion. -/
def fullProdDx (a x : Q') (N : Nat) : Q' :=
  FiniteProductFDDeriv.prodDeriv
    (fun k t => ThetaConv.gFac a t k) (gFacDx a) x N

@[simp] theorem fullProdDx_zero (a x : Q') : fullProdDx a x 0 = 0 := rfl

@[simp] theorem fullProdDx_succ (a x : Q') (N : Nat) :
    fullProdDx a x (N + 1)
      = fullProdDx a x N * ThetaConv.gFac a x N
          + ThetaConv.Ppart a x N * gFacDx a N := by
  unfold fullProdDx
  rw [FiniteProductFDDeriv.prodDeriv_succ,
    ThetaProdConvClose.pre_gFac_eq_Ppart a x N]

/-! ## 2. The finite full-product logarithmic derivative identity -/

/-- The new full factor times its `S` summand cancels the heat-factor
denominator and leaves exactly the full factor derivative. -/
theorem gFac_mul_sTerm_eqv_gFacDx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (N : Nat) :
    ThetaConv.gFac a x N * HKConv.sTerm a x N ≈ gFacDx a N := by
  have hcancel :
      HKConv.sTerm a x N * HKPos.factor (HKPos.geoAmp a N) x
        ≈ HKPos.two (HKPos.geoAmp a N) :=
    HKConv.divPos_mul_eqv (HKConv.factor_num_pos ha0 ha1 hx N)
  show ((1 + (-(ThetaConv.uAmp a N))) * HKPos.factor (HKPos.geoAmp a N) x)
        * HKConv.sTerm a x N
      ≈ (1 + (-(ThetaConv.uAmp a N))) * HKPos.two (HKPos.geoAmp a N)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (1 + (-(ThetaConv.uAmp a N)))
      (HKPos.factor (HKPos.geoAmp a N) x) (HKConv.sTerm a x N)) ?_
  refine Q'.mul_eqv_congr_left (1 + (-(ThetaConv.uAmp a N))) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (HKPos.factor (HKPos.geoAmp a N) x)
      (HKConv.sTerm a x N)) ?_
  exact hcancel

/-- **Finite normalization theorem.**  The formal x-derivative of the first
`N` full Jacobi factors equals the full partial product times the `S` partial
sum:

`fullProdDx a x N ≈ Ppart a x N * Spart a x N`.

This is the unhalved product derivative. -/
theorem fullProdDx_eqv_Ppart_mul_Spart {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) :
    ∀ N : Nat,
      fullProdDx a x N ≈ ThetaConv.Ppart a x N * HKConv.Spart a x N
  | 0 => by
      show (0 : Q') ≈ (1 : Q') * (0 : Q')
      exact Q'.eqv_symm (Q'.mul_zero_eqv 1)
  | N + 1 => by
      have ih :
          fullProdDx a x N
            ≈ ThetaConv.Ppart a x N * HKConv.Spart a x N :=
        fullProdDx_eqv_Ppart_mul_Spart ha0 ha1 hx N
      have hnew :
          ThetaConv.gFac a x N * HKConv.sTerm a x N ≈ gFacDx a N :=
        gFac_mul_sTerm_eqv_gFacDx ha0 ha1 hx N
      have hT1 :
          (ThetaConv.Ppart a x N * ThetaConv.gFac a x N)
              * HKConv.Spart a x N
            ≈ fullProdDx a x N * ThetaConv.gFac a x N := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (ThetaConv.Ppart a x N)
            (ThetaConv.gFac a x N) (HKConv.Spart a x N)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (ThetaConv.Ppart a x N) _ _
            (Q'.mul_comm_eqv (ThetaConv.gFac a x N)
              (HKConv.Spart a x N))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (ThetaConv.Ppart a x N)
            (HKConv.Spart a x N) (ThetaConv.gFac a x N))) ?_
        exact Q'.mul_eqv_congr_right _ _ (ThetaConv.gFac a x N)
          (Q'.eqv_symm ih)
      have hT2 :
          (ThetaConv.Ppart a x N * ThetaConv.gFac a x N)
              * HKConv.sTerm a x N
            ≈ ThetaConv.Ppart a x N * gFacDx a N := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (ThetaConv.Ppart a x N)
            (ThetaConv.gFac a x N) (HKConv.sTerm a x N)) ?_
        exact Q'.mul_eqv_congr_left (ThetaConv.Ppart a x N) _ _ hnew
      have hmain :
          (ThetaConv.Ppart a x N * ThetaConv.gFac a x N)
              * (HKConv.Spart a x N + HKConv.sTerm a x N)
            ≈ fullProdDx a x N * ThetaConv.gFac a x N
                + ThetaConv.Ppart a x N * gFacDx a N := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_add_eqv
            (ThetaConv.Ppart a x N * ThetaConv.gFac a x N)
            (HKConv.Spart a x N) (HKConv.sTerm a x N)) ?_
        exact Q'.add_eqv_congr' hT1 hT2
      rw [fullProdDx_succ, ThetaConv.Ppart_succ, HKConv.Spart_succ]
      exact Q'.eqv_symm hmain

/-- The same finite derivative after separating the x-independent Euler
prefactor:

`fullProdDx_N ≈ eulerProd_N * factorProdDx_N`.

This pins the relation between the generic full-factor Leibniz recursion and
the already-proved sin-free doubled-factor derivative. -/
theorem fullProdDx_eqv_eulerProd_mul_factorProdDx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (N : Nat) :
    fullProdDx a x N
      ≈ RealTheta.eulerProd a N * CoeffChebSineClose.factorProdDx a x N := by
  refine Q'.eqv_trans _ _ _
    (fullProdDx_eqv_Ppart_mul_Spart ha0 ha1 hx N) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (HKConv.Spart a x N)
      (RealTheta.Ppart_eqv_prodRegroup a x N)) ?_
  show (RealTheta.eulerProd a N * RealTheta.factorProd a x N)
        * HKConv.Spart a x N
      ≈ RealTheta.eulerProd a N * CoeffChebSineClose.factorProdDx a x N
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (RealTheta.eulerProd a N)
      (RealTheta.factorProd a x N) (HKConv.Spart a x N)) ?_
  exact Q'.mul_eqv_congr_left (RealTheta.eulerProd a N) _ _
    (Q'.eqv_symm
      (CoeffChebSineClose.logDeriv_factorProd ha0 ha1 hx N))

/-! ## 3. CReal completion and the normalization fence -/

/-- Any constructive real whose approximations are the finite full-product
derivatives is equivalent to `Rproduct = Theta*S`, not directly to `Rhalf`.
This is an unconditional lift of the finite theorem; no convergence rate is
extracted from a proposition. -/
theorem fullProdDx_creal_equiv_Rproduct {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {D : CReal}
    (hD : ∀ N : Nat, D.approx N = fullProdDx a x N) :
    CReal.Equiv D (JTPIdentity.Rproduct ha0 ha1 hx hx1) := by
  refine CReal.Equiv_of_lifted_approx_equal ?_
  intro N
  apply ThetaLimit.Equiv_ofQ'_of_eqv
  rw [hD N]
  show fullProdDx a x N
      ≈ ThetaConv.Ppart a x N * HKConv.Spart a x N
  exact fullProdDx_eqv_Ppart_mul_Spart ha0 ha1 hx N

/-- A data-bearing canonical completion certificate for the finite full-product
derivatives.  Its value is `Rproduct`; `approxEqv` records that every one of its
approximations realizes the corresponding Leibniz derivative up to the `Q'`
setoid equality. -/
structure FullProductDerivativeCompletion {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : Type where
  value : CReal
  value_eqv_Rproduct :
    CReal.Equiv value (JTPIdentity.Rproduct ha0 ha1 hx hx1)
  approxEqv : ∀ N : Nat, value.approx N ≈ fullProdDx a x N

/-- The canonical full-product derivative completion, with value exactly
`Rproduct`. -/
def fullProductDerivativeCompletion {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    FullProductDerivativeCompletion ha0 ha1 hx hx1 where
  value := JTPIdentity.Rproduct ha0 ha1 hx hx1
  value_eqv_Rproduct := JTPIdentity.Equiv_refl _
  approxEqv := fun N =>
    Q'.eqv_symm (fullProdDx_eqv_Ppart_mul_Spart ha0 ha1 hx N)

end YMGap.Continuum.JTPFullProductDerivativeNormalization

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.JTPFullProductDerivativeNormalization.gFac_mul_sTerm_eqv_gFacDx
#print axioms YMGap.Continuum.JTPFullProductDerivativeNormalization.fullProdDx_eqv_Ppart_mul_Spart
#print axioms YMGap.Continuum.JTPFullProductDerivativeNormalization.fullProdDx_eqv_eulerProd_mul_factorProdDx
#print axioms YMGap.Continuum.JTPFullProductDerivativeNormalization.fullProdDx_creal_equiv_Rproduct
#print axioms YMGap.Continuum.JTPFullProductDerivativeNormalization.fullProductDerivativeCompletion
