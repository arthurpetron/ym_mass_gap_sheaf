/-
`FusedRefinedSpectralBridge` — transports the refined Edgeworth defect to the
actual corrected fused Peter--Weyl eigenvalue.

The previous exact bridge compared `lamPW` with the one-parameter retune and
therefore exposed the genuinely linear `normEigShift`.  The refined retune is
useful only if its quadratic defect controls that same physical fused rate.
This file closes that algebraic transport, without assuming the missing local
CLT factorization:

  (1 - retEig2) - normEigShift2 <= 1 - lamPW.

Consequently any constructive `RefinedFactorization` immediately gives the
actual fused outgoing margin a quadratic erosion budget.  The remaining
front is exactly construction of that factorization from finite character
sums; it is neither hidden nor replaced here.
-/

import YMGap.Continuum.FusedSpectralCarrierBridge
import YMGap.Continuum.RefinedQuadraticClose

namespace YMGap.Continuum.FusedRefinedSpectralBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RefinedQuadraticClose
open YMGap.Continuum.VacNormEigShift

/-! ## 0. The explicit p=2 refined base is a genuine spectral base -/

/-- The exact p=2 Edgeworth coefficient `7/24` is nonnegative. -/
theorem refineCoeff_p2_nonneg :
    (0 : Q') <= refineCoeff 2 (by decide) := by decide

/-- The exact p=2 Edgeworth coefficient `7/24` does not exceed one. -/
theorem refineCoeff_p2_le_one :
    refineCoeff 2 (by decide) <= (1 : Q') := by decide

/-- On the complete physical window, the p=2 correction factor lies in
`[0,1]`.  Thus positivity of the refined retune is not part of the missing
Edgeworth input. -/
theorem corrFactor_refineCoeff_p2_mem {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) :
    ((0 : Q') <= corrFactor (refineCoeff 2 (by decide)) w) /\
      (corrFactor (refineCoeff 2 (by decide)) w <= (1 : Q')) := by
  let d := (1 : Q') - w
  let a := refineCoeff 2 (by decide)
  have hd0 : (0 : Q') <= d := Q'.sub_nonneg_of_le hw1
  have hd1 : d <= (1 : Q') := oneSub_le_one hw0
  have hsq : d * d <= (1 : Q') := by
    have hmul : d * d <= (1 : Q') * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg hd1 hd1 (by decide) hd0
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hprod0 : (0 : Q') <= a * (d * d) :=
    Q'.mul_nonneg _ _ refineCoeff_p2_nonneg
      (Q'.mul_nonneg _ _ hd0 hd0)
  have hprod1 : a * (d * d) <= (1 : Q') := by
    have hmul : a * (d * d) <= (1 : Q') * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg refineCoeff_p2_le_one hsq
        (by decide) (Q'.mul_nonneg _ _ hd0 hd0)
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  change ((0 : Q') <= (1 : Q') - a * (d * d)) /\
    ((1 : Q') - a * (d * d) <= (1 : Q'))
  exact ⟨Q'.sub_nonneg_of_le hprod1,
    YMGap.Continuum.BondMovingRetuneFix.oneSub_le_one hprod0⟩

/-- The full p=2 refined retune base lies in `[0,1]` on the physical window. -/
theorem renormW2_refineCoeff_p2_mem {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) :
    ((0 : Q') <= renormW2 2 (by decide) (refineCoeff 2 (by decide)) w) /\
      (renormW2 2 (by decide) (refineCoeff 2 (by decide)) w <= (1 : Q')) := by
  have hb0 : (0 : Q') <= renormWFix 2 (by decide) w :=
    renormWFix_nonneg hw0 2 (by decide)
  have hb1 : renormWFix 2 (by decide) w <= (1 : Q') :=
    renormWFix_le_one hw1 2 (by decide)
  have hc := corrFactor_refineCoeff_p2_mem hw0 hw1
  constructor
  · exact Q'.mul_nonneg _ _ hb0 hc.1
  · have hmul :
        renormWFix 2 (by decide) w *
            corrFactor (refineCoeff 2 (by decide)) w <=
          (1 : Q') * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg hb1 hc.2 (by decide) hc.1
    exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- Hence every refined p=2 eigenvalue is in `[0,1]`; the two range
fields formerly carried by `RefinedFactorization` are derivable at the exact
Edgeworth coefficient. -/
theorem retEig2_refineCoeff_p2_mem {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (s : Nat) :
    ((0 : Q') <= retEig2 2 (by decide) (refineCoeff 2 (by decide)) w s) /\
      (retEig2 2 (by decide) (refineCoeff 2 (by decide)) w s <= (1 : Q')) := by
  have hb := renormW2_refineCoeff_p2_mem hw0 hw1
  exact ⟨qpow_nonneg _ hb.1 _, qpow_le_one hb.1 hb.2 _⟩

/-! ## 1. Exact refined-defect comparison -/

/-- The corrected fused eigenvalue is bounded by the refined retuned
eigenvalue plus the *actual* refined vacuum-normalized defect. -/
theorem lamPW_refined_upper {w : Q'} (hw0 : (0 : Q') <= w)
    (hw1 : w <= (1 : Q')) (N k : Nat) (a : Q') :
    lamPW w N (k + 1) <=
      normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1) +
        retEig2 2 (by decide) a w (k + 1) := by
  have hlam := lamPW_eq_vacNorm_p2 hw0 hw1 N k
  have hdef :
      vacNorm N 2 (by decide) hw0 hw1 (k + 1) +
          -(retEig2 2 (by decide) a w (k + 1)) <=
        normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1) :=
    le_absQ _
  have hvac :
      vacNorm N 2 (by decide) hw0 hw1 (k + 1) <=
        normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1) +
          retEig2 2 (by decide) a w (k + 1) :=
    le_add_of_sub_le hdef
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hlam) hvac

/-- Exact additive-margin orientation of `lamPW_refined_upper`. -/
theorem fused_margin_after_refined_erosion {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (N k : Nat) (a : Q') :
    ((1 : Q') - retEig2 2 (by decide) a w (k + 1)) -
        normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1) <=
      (1 : Q') - lamPW w N (k + 1) := by
  let shift := normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1)
  let eig := retEig2 2 (by decide) a w (k + 1)
  have hup : lamPW w N (k + 1) <= shift + eig :=
    lamPW_refined_upper hw0 hw1 N k a
  have hneg : -(shift + eig) <= -(lamPW w N (k + 1)) := Q'.neg_le_neg hup
  have hadd : (1 : Q') + -(shift + eig) <=
      (1 : Q') + -(lamPW w N (k + 1)) :=
    Q'.add_le_add_left 1 _ _ hneg
  have hleft : (((1 : Q') - eig) - shift).eqv
      ((1 : Q') + -(shift + eig)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-eig) (-shift)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ _ (Q'.add_comm_eqv (-eig) (-shift))) ?_
    exact Q'.add_eqv_congr_left 1 _ _
      (Q'.eqv_symm (Q'.neg_add_eqv shift eig))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hadd

/-! ## 2. Quadratic erosion of the actual fused margin -/

/-- A supplied refined Edgeworth factorization now controls the corrected
fused spectral margin itself.  Along `1-w <= r`, the erosion is bounded by
`Cq*r^2`, uniformly in the cutoff and the excited channel. -/
theorem fused_margin_after_factorized_quadratic_erosion
    (N : Nat) {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (a : Q')
    (fac : RefinedFactorization N 2 (by decide) hw0 hw1 a)
    {r : Q'} (hr : (1 : Q') - w <= r) (k : Nat) :
    ((1 : Q') - retEig2 2 (by decide) a w (k + 1)) -
        fac.Cq * (r * r) <=
      (1 : Q') - lamPW w N (k + 1) := by
  have hshift :
      normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1) <=
        fac.Cq * (r * r) :=
    refined_route_summable N 2 (by decide) hw0 hw1 a fac hr (k + 1)
  have hneg : -(fac.Cq * (r * r)) <=
      -(normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1)) :=
    Q'.neg_le_neg hshift
  have hbudget :
      ((1 : Q') - retEig2 2 (by decide) a w (k + 1)) -
          fac.Cq * (r * r) <=
        ((1 : Q') - retEig2 2 (by decide) a w (k + 1)) -
          normEigShift2 N 2 (by decide) hw0 hw1 a (k + 1) :=
    Q'.add_le_add_left _ _ _ hneg
  exact Q'.le_trans' _ _ _ hbudget
    (fused_margin_after_refined_erosion hw0 hw1 N k a)

end YMGap.Continuum.FusedRefinedSpectralBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.refineCoeff_p2_nonneg
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.refineCoeff_p2_le_one
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.corrFactor_refineCoeff_p2_mem
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.renormW2_refineCoeff_p2_mem
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.retEig2_refineCoeff_p2_mem
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.lamPW_refined_upper
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.fused_margin_after_refined_erosion
#print axioms YMGap.Continuum.FusedRefinedSpectralBridge.fused_margin_after_factorized_quadratic_erosion
