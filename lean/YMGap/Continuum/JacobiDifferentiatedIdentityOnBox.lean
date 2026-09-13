/-
# Differentiated Jacobi identity and the original completed SU(2) heat series

For every rational 0<q<1 and -1<=x<=1, the ORIGINAL dSeriesCReal equals
Rhalf=(1/2)*Theta*S. The proof compares the actual finite derivatives,
whose Gaussian q-binomial weights approach one with the computed derivative
modulus. No analytic identity premise, off-box totalizer, or interchange of
two limits is assumed. Both endpoints are included.

The existing exact nome/completion bridge then proves nonnegativity of the
original completed SU(2) pointwise heat series. This is NOT strict positivity,
a positive interacting-action floor, a stationary vacuum, a spectral gap,
or a continuum Yang--Mills construction.
-/

import YMGap.Continuum.FiniteJacobiDerivativeComparison
import YMGap.Continuum.SU2PointwiseHeatPositiveCompletion

namespace YMGap.Continuum.JacobiDifferentiatedIdentityOnBox

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteJacobiDerivativeComparison
open YMGap.Continuum.JTPFullProductDerivativeNormalization

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

/-- Correct half-normalization of the ACTUAL approximation error. -/
theorem Rhalf_sub_dSeries_approx {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    (JTPIdentity.Rhalf hq0 hq1 hxm1 hx1).approx N
      + -(JTPIdentity.dSeriesCReal hq0 hq1 hxm1 hx1).approx N
      ≈ HalfPow.half * (fullProdDx q x N + -((2 : Q') * JTPIdentity.dPartial q x N)) := by
  have hhalf : HalfPow.half * ((2 : Q') * JTPIdentity.dPartial q x N) ≈ JTPIdentity.dPartial q x N :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half * (2 : Q') ≈ (1 : Q')))
        (Q'.one_mul_eqv _))
  have hp : (JTPIdentity.Rproduct hq0 hq1 hxm1 hx1).approx N ≈ fullProdDx q x N :=
    Q'.eqv_symm (fullProdDx_eqv_Ppart_mul_Spart hq0 hq1 hxm1 N)
  calc (JTPIdentity.Rhalf hq0 hq1 hxm1 hx1).approx N
        + -(JTPIdentity.dSeriesCReal hq0 hq1 hxm1 hx1).approx N
      ≈ HalfPow.half * fullProdDx q x N + -(HalfPow.half * ((2 : Q') * JTPIdentity.dPartial q x N)) :=
        Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp)
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hhalf))
    _ ≈ HalfPow.half * (fullProdDx q x N + -((2 : Q') * JTPIdentity.dPartial q x N)) :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_neg_eqv _ _)))
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

/-- Explicit comparison modulus for the correctly normalized CReal objects. -/
theorem Rhalf_sub_dSeries_close {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : derivativeCutoff q ε ≤ N) :
    Q'.abs ((JTPIdentity.Rhalf hq0 hq1 hxm1 hx1).approx N
      + -(JTPIdentity.dSeriesCReal hq0 hq1 hxm1 hx1).approx N) ≤ ε := by
  have hm := ExpNeg.abs_mul_le HalfPow.half
    (fullProdDx q x N + -((2 : Q') * JTPIdentity.dPartial q x N))
  rw [ExpNeg.abs_of_nonneg HalfPow.half_nonneg] at hm
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Rhalf_sub_dSeries_approx hq0 hq1 hx1 hxm1 N)))
    (Q'.le_trans' _ _ _ hm (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (fullProdDx_sub_two_dPartial_close hq0 hq1 hx1 hxm1 hε N hN) HalfPow.half_nonneg)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : HalfPow.half ≤ (1 : Q')) (Q'.le_of_lt hε))
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))))

/-- The named differentiated JTP obligation is proved for all its rational
on-box parameters, with the unchanged original type and correct factor half. -/
theorem diffJTP {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxm1 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) :
    JTPIdentity.DiffJTP hq0 hq1 hxm1 hx1 := by
  apply CReal.Equiv.symm
  intro ε hε
  refine ⟨derivativeCutoff q ε, fun N hN => ?_⟩
  have h := Rhalf_sub_dSeries_close hq0 hq1 hx1 hxm1 hε N hN
  exact ⟨ExpNeg.le_add_of_abs_sub_le h, ExpNeg.le_add_of_abs_sub_le
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ExpNeg.abs_sub_comm _ _)) h)⟩

/-- Nonnegativity of the ORIGINAL differentiated heat-series completion. -/
theorem dSeriesCReal_geRat_zero {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxm1 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal hq0 hq1 hxm1 hx1) 0 :=
  JTPIdentity.Kt_geRat_zero_of_diff hq0 hq1 hxm1 hx1 (diffJTP hq0 hq1 hxm1 hx1)

/-- Nonnegativity of the EXISTING original SU(2) heat completion, using its
proved nome/offset bridge. This is not a strictly positive action floor. -/
theorem pointwiseHeatCReal_geRat_zero {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxm1 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) :
    ExpPos.geRat (SU2PointwiseHeatSpacingCompletion.pointwiseHeatCReal hq0 hq1 hxm1 hx1) 0 :=
  SU2PointwiseHeatPositiveCompletion.pointwiseHeatCReal_geRat_zero_of_diffJTP
    hq0 hq1 hxm1 hx1 (diffJTP hq0 hq1 hxm1 hx1)

end YMGap.Continuum.JacobiDifferentiatedIdentityOnBox

#print axioms YMGap.Continuum.JacobiDifferentiatedIdentityOnBox.Rhalf_sub_dSeries_approx
#print axioms YMGap.Continuum.JacobiDifferentiatedIdentityOnBox.Rhalf_sub_dSeries_close
#print axioms YMGap.Continuum.JacobiDifferentiatedIdentityOnBox.diffJTP
#print axioms YMGap.Continuum.JacobiDifferentiatedIdentityOnBox.dSeriesCReal_geRat_zero
#print axioms YMGap.Continuum.JacobiDifferentiatedIdentityOnBox.pointwiseHeatCReal_geRat_zero
