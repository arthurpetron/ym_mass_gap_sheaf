/-
# Cutoff-independent rational precision for curvature transport

The finite weighted curvature cost is bounded BEFORE the approximation
tolerance is chosen. The explicit positive tolerance pays the value,
first-jet and second-jet discrepancy by the square of the supplied positive
original heat floor. The floor occurs in precision only, not in the cost.

This leaf is rational algebra/order. It does not construct the error jets,
the original floor, a Haar certificate or an interacting/OS/scaling bound.
-/

import YMGap.Continuum.JacobiHeatRadialProducedBound

namespace YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.JacobiHeatTransverseCurvature (transverseCap)
open YMGap.Continuum.JacobiHeatRadialProducedBound (radialCap)
open YMGap.Continuum.JacobiProductRadialSignedTail (radialTailPayment)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Uniform in the finite cutoff, at each fixed strict nome; weighted slack is one. -/
def curvatureCap (w : Q') : Q' :=
  transverseCap w + HKConvGen.geoTailBase 4 (w*w) 0 + 1

theorem curvatureCap_nonnegative {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ curvatureCap w :=
  Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (HKConvGen.geoTailBase_nonneg
        (Q'.zero_le_add _ _ (Q'.le_of_lt hw0) (Q'.le_of_lt hw0))
        (SumOfSquares.q_mul_self_nonneg w) 0)
      (HKConvGen.geoTailBase_nonneg (by decide : (0 : Q') ≤ 4)
        (SumOfSquares.q_mul_self_nonneg w) 0)) Q'.zero_le_one

/-- Numerator monotonicity of the literal geometric payment, without division cancellation. -/
theorem geoTailBase_numerator_mono {a b r : Q'} (hab : a ≤ b) :
    HKConvGen.geoTailBase a r 0 ≤ HKConvGen.geoTailBase b r 0 := by
  change (a*1)*HKConv.divPos 1 (1 + -r) ≤ (b*1)*HKConv.divPos 1 (1 + -r)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hab Q'.zero_le_one)
    (HKConv.divPos_nonneg Q'.zero_le_one)

theorem radialCap_le_curvatureCap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (N : Nat) :
    radialCap w N+1 ≤ curvatureCap w := by
  have hamp : HKPos.geoAmp w N ≤ (1 : Q') :=
    HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (m := 0) (n := 2*N+1) (Nat.zero_le _)
  have hnum : 4*HKPos.geoAmp w N ≤ (4 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hamp (by decide : (0 : Q') ≤ 4))
      (Q'.le_of_eqv (Q'.mul_one_eqv 4))
  exact Q'.add_le_add_right _ _ 1
    (Q'.add_le_add_left (transverseCap w) _ _ (geoTailBase_numerator_mono hnum))

/-- The actual finite tail is reduced before precision is chosen. Weighted
slack is one; the final original-prefix approximation adds another one. -/
def nearFlatCurvatureCap (w : Q') : Q' :=
  JacobiProductRadialNearFlatBound.nearFlatCap w + 2

theorem nearFlatCurvatureCap_nonnegative {w : Q'} (_hw0 : (0 : Q') < w) :
    (0 : Q') ≤ nearFlatCurvatureCap w :=
  Q'.zero_le_add _ _ (JacobiProductRadialNearFlatBound.nearFlatCap_nonnegative w)
    (by decide : (0 : Q') ≤ 2)

/-- Literal sufficient amplitude for a tail payment of at most one. -/
def nearFlatRadialThreshold (w : Q') : Q' :=
  Q'.mkPos 1 4 (by decide) * (1 + -(w*w))

private theorem nome_gap_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) : (0 : Q') < 1 + -(w*w) :=
  HKPos.one_sub_pos (HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1)

/-- Both guards are retained: the new tail threshold alone does not imply
the existing eighth-amplitude onset at every strict nome. -/
def nearFlatRadialOnset (w : Q') : Nat :=
  max (JacobiHeatRadialProducedBound.radialOnset w)
    (HKConvGen.powBaseCutoff w (nearFlatRadialThreshold w))

theorem nearFlatRadialOnset_small_factor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN : nearFlatRadialOnset w ≤ N) :
    HKPos.geoAmp w N ≤ JacobiProductRadialSignedTail.eighth :=
  JacobiHeatRadialProducedBound.radialOnset_small_factor hw0 hw1 N (by
    unfold nearFlatRadialOnset at hN
    omega)

/-- Produced bound on the literal signed-tail allowance, not a substituted
heat floor or an assumed cutoff-independent curvature estimate. -/
theorem nearFlatRadialOnset_tail_le_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN : nearFlatRadialOnset w ≤ N) : radialTailPayment w N ≤ 1 := by
  have hgap := nome_gap_positive hw0 hw1
  have hthreshold : (0 : Q') < nearFlatRadialThreshold w :=
    HKPos.q_mul_pos (by decide : (0 : Q') < Q'.mkPos 1 4 (by decide)) hgap
  have hcut : HKConvGen.powBaseCutoff w (nearFlatRadialThreshold w) ≤ N := by
    unfold nearFlatRadialOnset at hN
    omega
  have hamp : HKPos.geoAmp w N ≤ nearFlatRadialThreshold w :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
        (m := N) (n := 2*N+1) (by omega))
      (Q'.le_trans' _ _ _
        (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hcut)
        (HKConvGen.pow_base_le_cutoff hw0 hw1 hthreshold))
  have hpin : 4*nearFlatRadialThreshold w ≈ 1 + -(w*w) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv 4 (Q'.mkPos 1 4 (by decide)) (1 + -(w*w))))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 1 _
          (by decide : (4 : Q')*Q'.mkPos 1 4 (by decide) ≈ 1))
        (Q'.one_mul_eqv _))
  have hnum : 4*HKPos.geoAmp w N ≤ 1 + -(w*w) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 4 hamp (by decide)) (Q'.le_of_eqv hpin)
  change ((4*HKPos.geoAmp w N)*1)*HKConv.divPos 1 (1 + -(w*w)) ≤ 1
  have hinv : (0 : Q') ≤ HKConv.divPos 1 (1 + -(w*w)) :=
    HKConv.divPos_nonneg Q'.zero_le_one
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hnum) hinv)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hgap))))

theorem nearFlatRadialCap_le_curvatureCap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN : nearFlatRadialOnset w ≤ N) :
    JacobiHeatRadialProducedBound.nearFlatRadialCap w N+1 ≤ nearFlatCurvatureCap w :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ 1
      (Q'.add_le_add_left (JacobiProductRadialNearFlatBound.nearFlatCap w) _ _
        (nearFlatRadialOnset_tail_le_one hw0 hw1 N hN)))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.const 1)) (.const 1))
      (.add (.var 0) (.const 2)) (by decide)
      (fun _ => JacobiProductRadialNearFlatBound.nearFlatCap w)))

/-- Fixed error coefficient, selected before any finite cutoff. -/
def errorCoefficient (Cbar U0 U1 U2 : Q') : Q' :=
  Cbar*(2*U0+1)+4*U0+U2+4*U1+8

theorem errorCoefficient_nonnegative {Cbar U0 U1 U2 : Q'}
    (hCbar : (0 : Q') ≤ Cbar) (hU0 : (0 : Q') ≤ U0)
    (hU1 : (0 : Q') ≤ U1) (hU2 : (0 : Q') ≤ U2) :
    (0 : Q') ≤ errorCoefficient Cbar U0 U1 U2 :=
  Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ hCbar
            (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) hU0) Q'.zero_le_one))
          (Q'.mul_nonneg _ _ (by decide) hU0)) hU2)
      (Q'.mul_nonneg _ _ (by decide) hU1)) (by decide)

/-- Explicit positive error tolerance; no inverse floor appears. -/
def errorTolerance (m Cbar U0 U1 U2 : Q') : Q' :=
  HKConv.divPos (m*m) (errorCoefficient Cbar U0 U1 U2+1+m*m)

theorem errorTolerance_denominator_positive {m Cbar U0 U1 U2 : Q'}
    (hCbar : (0 : Q') ≤ Cbar) (hU0 : (0 : Q') ≤ U0)
    (hU1 : (0 : Q') ≤ U1) (hU2 : (0 : Q') ≤ U2) :
    (0 : Q') < errorCoefficient Cbar U0 U1 U2+1+m*m := by
  have hB := errorCoefficient_nonnegative hCbar hU0 hU1 hU2
  have h1 : (1 : Q') ≤ errorCoefficient Cbar U0 U1 U2+1 :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hB)
      (Q'.le_of_eqv (Q'.add_comm_eqv 1 _))
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ h1
      (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg m)))

theorem errorTolerance_positive {m Cbar U0 U1 U2 : Q'} (hm : (0 : Q') < m) :
    (0 : Q') < errorTolerance m Cbar U0 U1 U2 :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (HKPos.q_mul_pos hm hm))

theorem errorTolerance_le_one {m Cbar U0 U1 U2 : Q'}
    (hCbar : (0 : Q') ≤ Cbar) (hU0 : (0 : Q') ≤ U0)
    (hU1 : (0 : Q') ≤ U1) (hU2 : (0 : Q') ≤ U2) :
    errorTolerance m Cbar U0 U1 U2 ≤ (1 : Q') := by
  let B := errorCoefficient Cbar U0 U1 U2
  have hB := errorCoefficient_nonnegative hCbar hU0 hU1 hU2
  have hD := errorTolerance_denominator_positive (m := m) hCbar hU0 hU1 hU2
  apply HKConv.divPos_le_of_le (CReal.num_pos_of_pos hD)
  have h : m*m ≤ B+1+m*m :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (m*m) (B+1) (Q'.zero_le_add _ _ hB Q'.zero_le_one))
      (Q'.le_of_eqv (Q'.add_comm_eqv (m*m) (B+1)))
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (Q'.one_mul_eqv _))

theorem errorTolerance_budget {m Cbar U0 U1 U2 : Q'}
    (hCbar : (0 : Q') ≤ Cbar) (hU0 : (0 : Q') ≤ U0)
    (hU1 : (0 : Q') ≤ U1) (hU2 : (0 : Q') ≤ U2) :
    errorTolerance m Cbar U0 U1 U2 * errorCoefficient Cbar U0 U1 U2 ≤ m*m := by
  let B := errorCoefficient Cbar U0 U1 U2
  let D := B+1+m*m
  let eps := errorTolerance m Cbar U0 U1 U2
  have hD := errorTolerance_denominator_positive (m := m) hCbar hU0 hU1 hU2
  have hBD : B ≤ D :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg B 1 Q'.zero_le_one)
      (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg m))
  have heps : (0 : Q') ≤ eps := HKConv.divPos_nonneg (SumOfSquares.q_mul_self_nonneg m)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ eps hBD heps)
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD)))

/-- Exact association of the generic SOS curvature discrepancy cap. -/
def errorCap (C U0 U1 U2 a b c : Q') : Q' :=
  C*(2*(U0*a)+a*a) + ((U0*c+a*U2)+a*c) + (2*(U1*b)+b*b)

private def coefficientExpr (Cbar U0 U1 U2 : PolyExpr) : PolyExpr :=
  .add (.add (.add (.add (.mul Cbar (.add (.mul (.const 2) U0) (.const 1)))
    (.mul (.const 4) U0)) U2) (.mul (.const 4) U1)) (.const 8)

private def errorExpr (C U0 U1 U2 a b c : PolyExpr) : PolyExpr :=
  .add (.add (.mul C (.add (.mul (.const 2) (.mul U0 a)) (.mul a a)))
    (.add (.add (.mul U0 c) (.mul a U2)) (.mul a c)))
    (.add (.mul (.const 2) (.mul U1 b)) (.mul b b))

/-- The retained nonnegative factorization pays all quadratic error terms. -/
theorem errorCap_le_scaled {C Cbar U0 U1 U2 eps : Q'}
    (hCbar : (0 : Q') ≤ Cbar) (hU0 : (0 : Q') ≤ U0)
    (hC : C ≤ Cbar) (heps0 : (0 : Q') ≤ eps) (heps1 : eps ≤ (1 : Q')) :
    errorCap C U0 U1 U2 eps (2*eps) (4*eps) ≤
      eps*errorCoefficient Cbar U0 U1 U2 := by
  have hfirst : (0 : Q') ≤ (Cbar + -C)*(eps*(2*U0+eps)) :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hC)
      (Q'.mul_nonneg _ _ heps0
        (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) hU0) heps0))
  have hsecond : (0 : Q') ≤ (Cbar+8)*(eps*(1 + -eps)) :=
    Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ hCbar (by decide))
      (Q'.mul_nonneg _ _ heps0 (Q'.sub_nonneg_of_le heps1))
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ hfirst hsecond)
    (Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.var 5) (coefficientExpr (.var 1) (.var 2) (.var 3) (.var 4)))
        (.neg (errorExpr (.var 0) (.var 2) (.var 3) (.var 4)
          (.var 5) (.mul (.const 2) (.var 5)) (.mul (.const 4) (.var 5)))))
      (.add
        (.mul (.add (.var 1) (.neg (.var 0)))
          (.mul (.var 5) (.add (.mul (.const 2) (.var 2)) (.var 5))))
        (.mul (.add (.var 1) (.const 8))
          (.mul (.var 5) (.add (.const 1) (.neg (.var 5))))))
      (by decide) (fun
        | 0 => C
        | 1 => Cbar
        | 2 => U0
        | 3 => U1
        | 4 => U2
        | _ => eps)))

/-- Produced tolerance pays the exact generic discrepancy cap by m squared. -/
theorem error_budget {m C Cbar U0 U1 U2 : Q'} (hm : (0 : Q') < m)
    (hC0 : (0 : Q') ≤ C) (hCbar : (0 : Q') ≤ Cbar)
    (hC : C ≤ Cbar) (hU0 : (0 : Q') ≤ U0)
    (hU1 : (0 : Q') ≤ U1) (hU2 : (0 : Q') ≤ U2) :
    errorCap C U0 U1 U2 (errorTolerance m Cbar U0 U1 U2)
      (2*errorTolerance m Cbar U0 U1 U2) (4*errorTolerance m Cbar U0 U1 U2) ≤ m*m :=
  Q'.le_trans' _ _ _
    (errorCap_le_scaled hCbar hU0 hC
      (Q'.le_of_lt (errorTolerance_positive hm))
      (errorTolerance_le_one hCbar hU0 hU1 hU2))
    (errorTolerance_budget hCbar hU0 hU1 hU2)

end YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision

#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.curvatureCap
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.curvatureCap_nonnegative
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.geoTailBase_numerator_mono
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.radialCap_le_curvatureCap
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatCurvatureCap
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatCurvatureCap_nonnegative
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatRadialThreshold
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatRadialOnset
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatRadialOnset_small_factor
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatRadialOnset_tail_le_one
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.nearFlatRadialCap_le_curvatureCap
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorCoefficient
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorCoefficient_nonnegative
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorTolerance
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorTolerance_denominator_positive
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorTolerance_positive
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorTolerance_le_one
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorTolerance_budget
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorCap
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.errorCap_le_scaled
#print axioms YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision.error_budget
