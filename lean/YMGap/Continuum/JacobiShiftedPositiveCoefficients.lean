/-
# Actual finite Jacobi products and derivatives in the variable t=1+x

Each full factor has positive coefficients
  (1-q^(2k+2)) * [(1-q^(2k+1))^2, 2*q^(2k+1)].
The original product and Leibniz derivative recurrences therefore produce
nonnegative coefficient lists. Their evaluations are pinned to the EXISTING
Ppart and fullProdDx, with the correct inverse-nome/half normalization.

This supplies finite positive approximants for the original heat series.
It does not yet prove coefficient-L1 convergence through the interacting
Haar integral or identify a finite approximant with an original heat cutoff.
-/

import YMGap.Continuum.QPolyHaarPositiveSubstitution
import YMGap.Continuum.SU2PointwiseHeatStrictFloor

namespace YMGap.Continuum.JacobiShiftedPositiveCoefficients

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.SU2PointwiseHeatPositiveCompletion

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

def base (q : Q') (k : Nat) : Q' :=
  (1 + -(ThetaConv.uAmp q k)) * HKPos.factorLB (HKPos.geoAmp q k)

def factor (q : Q') (k : Nat) : QPoly.Poly := [base q k, gFacDx q k]

theorem base_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (k : Nat) :
    (0 : Q') < base q k := HKPos.q_mul_pos
  (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq0 hq1 k).2)
  (HKPos.factorLB_pos (HKPos.pow_succ_pos_lt_one hq0 hq1 (2 * k)).2)

theorem slope_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (k : Nat) :
    (0 : Q') < gFacDx q k := by
  have hc := HKPos.pow_pos hq0 (2 * k + 1)
  exact HKPos.q_mul_pos (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq0 hq1 k).2)
    (Q'.pos_of_lt_of_le hc (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hc)))

theorem factor_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (k : Nat) :
    nonnegCoeffs (factor q k) := by
  unfold factor nonnegCoeffs
  rw [nonnegCoeffsB, Bool.and_eq_true]
  refine ⟨decide_eq_true (Q'.le_of_lt (base_pos hq0 hq1 k)), ?_⟩
  rw [nonnegCoeffsB, Bool.and_eq_true]
  exact ⟨decide_eq_true (Q'.le_of_lt (slope_pos hq0 hq1 k)), rfl⟩

private def shiftedFactorLeft : PolyExpr :=
  let u : PolyExpr := .var 0
  let c : PolyExpr := .var 1
  let x : PolyExpr := .var 2
  .add (.mul (.add (.const 1) (.neg u)) (.mul (.add (.const 1) (.neg c)) (.add (.const 1) (.neg c))))
    (.mul (.mul (.add (.const 1) (.neg u)) (.add c c)) (.add (.const 1) x))
private def shiftedFactorRight : PolyExpr :=
  .mul (.add (.const 1) (.neg (.var 0)))
    (.add (.const 1) (.add (.mul (.add (.var 1) (.var 1)) (.var 2)) (.mul (.var 1) (.var 1))))

/-- Exact affine recoding, for every rational x, not only the unit interval. -/
theorem shifted_factor_eq (q x : Q') (k : Nat) :
    base q k + gFacDx q k * (1 + x) ≈ ThetaConv.gFac q x k := by
  have h := poly_identity_of_normal_eq shiftedFactorLeft shiftedFactorRight (by decide)
    (fun i => if i = 0 then ThetaConv.uAmp q k else if i = 1 then HKPos.geoAmp q k else x)
  simpa [shiftedFactorLeft, shiftedFactorRight, RingNormaliser.eval, base, gFacDx,
    ThetaConv.gFac, HKPos.factor, HKPos.factorLB, HKPos.two] using h

theorem eval_factor (q x : Q') (k : Nat) :
    QPoly.eval (factor q k) (1 + x) ≈ ThetaConv.gFac q x k := by
  have he : QPoly.eval (factor q k) (1 + x) ≈ base q k + gFacDx q k * (1 + x) := by
    change base q k + (1 + x) * (gFacDx q k + (1 + x) * 0) ≈ _
    apply Q'.add_eqv_congr_left
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) (QPoly.q_add_zero_eqv _)))
      (Q'.mul_comm_eqv _ _)
  exact Q'.eqv_trans _ _ _ he (shifted_factor_eq q x k)

def product (q : Q') : Nat → QPoly.Poly
  | 0 => [1]
  | N + 1 => pmul (product q N) (factor q N)

def derivative (q : Q') : Nat → QPoly.Poly
  | 0 => []
  | N + 1 => padd (pmul (derivative q N) (factor q N)) (pscale (gFacDx q N) (product q N))

theorem product_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    ∀ N, nonnegCoeffs (product q N)
  | 0 => by change nonnegCoeffs [1]; decide
  | N + 1 => nonnegCoeffs_pmul (product_nonnegative hq0 hq1 N) (factor_nonnegative hq0 hq1 N)

theorem derivative_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    ∀ N, nonnegCoeffs (derivative q N)
  | 0 => rfl
  | N + 1 => nonnegCoeffsB_padd _ _
      (nonnegCoeffs_pmul (derivative_nonnegative hq0 hq1 N) (factor_nonnegative hq0 hq1 N))
      (nonnegCoeffsB_pscale (Q'.le_of_lt (slope_pos hq0 hq1 N)) _ (product_nonnegative hq0 hq1 N))

theorem eval_product (q x : Q') : ∀ N,
    QPoly.eval (product q N) (1 + x) ≈ ThetaConv.Ppart q x N
  | 0 => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) (QPoly.q_add_zero_eqv _)
  | N + 1 => Q'.eqv_trans _ _ _ (eval_pmul _ _ _)
      (Cheb.mul_eqv_congr _ _ _ _ (eval_product q x N) (eval_factor q x N))

theorem eval_derivative (q x : Q') : ∀ N,
    QPoly.eval (derivative q N) (1 + x) ≈ fullProdDx q x N
  | 0 => Q'.eqv_refl 0
  | N + 1 => by
      rw [fullProdDx_succ]
      exact Q'.eqv_trans _ _ _ (eval_padd _ _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (eval_pmul _ _ _)
            (Cheb.mul_eqv_congr _ _ _ _ (eval_derivative q x N) (eval_factor q x N)))
          (Q'.eqv_trans _ _ _ (eval_pscale _ _ _)
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_product q x N)) (Q'.mul_comm_eqv _ _))))

/-- Correctly normalized finite Jacobi heat approximant; not a finite
original unweighted character cutoff. The inverse nome is explicit. -/
def heat (q : Q') (N : Nat) : QPoly.Poly := pscale (inverseNome q * HalfPow.half) (derivative q N)

theorem heat_nonnegative {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N : Nat) :
    nonnegCoeffs (heat q N) :=
  nonnegCoeffsB_pscale (Q'.mul_nonneg _ _ (inverseNome_nonnegative q) HalfPow.half_nonneg) _
    (derivative_nonnegative hq0 hq1 N)

theorem eval_heat (q x : Q') (N : Nat) :
    QPoly.eval (heat q N) (1 + x) ≈ inverseNome q * (HalfPow.half * fullProdDx q x N) :=
  Q'.eqv_trans _ _ _ (eval_pscale _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_derivative q x N)) (Q'.mul_assoc_eqv _ _ _))

/-- The finite positive approximant has the same positive floor at its
constant coefficient, uniformly in N>=1 at the supplied q. -/
theorem floor_le_heat_constant {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N : Nat) (hN : 1 ≤ N) : SU2PointwiseHeatStrictFloor.floor q ≤ QPoly.eval (heat q N) 0 := by
  have hprod := fullProdDx_eqv_Ppart_mul_Spart hq0 hq1 (by decide : (-(1 : Q')) ≤ -1) N
  have he : QPoly.eval (heat q N) 0
      ≈ inverseNome q * (JTPIdentity.Rhalf hq0 hq1 (by decide : (-(1 : Q')) ≤ -1)
        (by decide : (-(1 : Q')) ≤ 1)).approx N := by
    have h := eval_heat q (-1) N
    rw [show (1 : Q') + -1 = 0 by decide] at h
    exact Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hprod))
  have hbound := Q'.mul_le_mul_of_nonneg_left _ _ (inverseNome q)
    (SU2PointwiseHeatStrictFloor.nome_floor_le_Rhalf_approx hq0 hq1
      (by decide : (-(1 : Q')) ≤ -1) (by decide : (-(1 : Q')) ≤ 1) N hN)
    (inverseNome_nonnegative q)
  have hcancel : inverseNome q * (q * SU2PointwiseHeatStrictFloor.floor q)
      ≈ SU2PointwiseHeatStrictFloor.floor q :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inverseNome_mul_nome_eqv hq0))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
    (Q'.le_trans' _ _ _ hbound (Q'.ge_of_eqv he))

end YMGap.Continuum.JacobiShiftedPositiveCoefficients

#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.base
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.factor
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.base_pos
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.slope_pos
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.factor_nonnegative
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.shifted_factor_eq
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.eval_factor
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.product_nonnegative
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.derivative_nonnegative
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.eval_product
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.eval_derivative
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.heat
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.heat_nonnegative
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.eval_heat
#print axioms YMGap.Continuum.JacobiShiftedPositiveCoefficients.floor_le_heat_constant
