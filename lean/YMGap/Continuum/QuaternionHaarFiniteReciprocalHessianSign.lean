/-
# Favorable finite reciprocal contribution to the weighted signed Hessian

For the ACTUAL finite reciprocal G_(k+1), J(A*G) is a nonnegative
polynomial multiplier of JA. This constructs F*G*JA*J(A*G) as a certificate
from the original upper window and certified F. Exact weighted Haar IBP
then retains the derivative of F while discarding only this favorable term.

The intended F is Vbar^2 times matched original conditional noise. No
lower-window inverse, Hessian sign, stationarity, source-norm/noise cap,
OS comparison or useful scaling estimate is supplied or assumed.
-/

import YMGap.Continuum.QuaternionHaarReciprocalAngularScore
import YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative
import YMGap.Continuum.QuaternionHaarUnitalReciprocalPrediction
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.ClusterCount

namespace YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (residual)
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse (residualCertificate)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative
open YMGap.Continuum.QuaternionHaarUnitalReciprocalPrediction (reciprocal_certificate)
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.ClusterCount (ofNat_nonneg)

local infix:50 " ≈ " => Q'.eqv

private theorem isolate {p q : RatPoly}
    (h : RatPolyCoeffEqv (polyAdd p q) polyZero) : RatPolyCoeffEqv p (polyNeg q) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (by decide)
    (fun | 0 => p | _ => q)).trans
      ((h.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))

private theorem negative_smul_negative (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul (-c) p)) (polySmul c p) :=
  (neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) (-c) p).trans
    (RatPolyCoeffEqv.smul_coefficient
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.neg (.var 0))) (.var 0)
        (by decide) (fun _ => c)) p))

/-- Exact finite multiplier derivative; even A=0 is allowed algebraically.
The residual and both rational scalar factors are explicit. -/
theorem reciprocal_multiplier_derivative_pin (i j : Nat) (A : RatPoly)
    (upper : Q') (hupper : (0 : Q') < upper) (k : Nat) :
    RatPolyCoeffEqv
      (angularDerivative i j (polyMul A (reciprocal A upper hupper (k+1))))
      (polySmul (Q'.ofNat (k+1)) (polySmul (scale upper hupper)
        (polyMul (residual (remainder A upper hupper) k) (angularDerivative i j A)))) := by
  let r := remainder A upper hupper
  let alpha := scale upper hupper
  have hn : RatPolyCoeffEqv (polyAdd polyOne r) (polySmul alpha A) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 1) (.add (.var 0) (.neg (.const 1)))) (.var 0)
      (by decide) (fun _ => polySmul alpha A)
  have hdr : RatPolyCoeffEqv (angularDerivative i j r)
      (polySmul alpha (angularDerivative i j A)) :=
    ((angularDerivative_add i j polyOne r).trans
      (((angularDerivative_one i j).add (RatPolyCoeffEqv.refl _)).trans
        (RatPolyCoeffEqv.zero_add _))).symm.trans
      ((angularDerivative_congr i j hn).trans (angularDerivative_smul i j alpha A))
  have hz : RatPolyCoeffEqv
      (polyAdd (angularDerivative i j (polyMul A (reciprocal A upper hupper (k+1))))
        (angularDerivative i j (residual r (k+1)))) polyZero :=
    (angularDerivative_add i j _ _).symm.trans
      ((angularDerivative_congr i j (reciprocal_cancellation A upper hupper (k+1))).trans
        (angularDerivative_one i j))
  exact (isolate hz).trans
    ((RatPolyCoeffEqv.neg (residual_angularDerivative_succ i j r k)).trans
      ((negative_smul_negative (Q'.ofNat (k+1)) _).trans
        (RatPolyCoeffEqv.smul (Q'.ofNat (k+1))
          ((hdr.mul_left _).trans (RatPolyCoeffEqv.polyMul_smul_right alpha _ _)))))

/-- The favorable term is an ACTUAL certificate, not a sign assumption.
Only the original positive upper endpoint is needed; no lower floor. -/
def finite_reciprocal_favorable_certificate {blocks block i j : Nat}
    (hb : block < blocks) (hi : i < 4) (hj : j < 4) {F A : RatPoly} {upper : Q'}
    (hupper : (0 : Q') < upper) (hA : SupportedQuaternionBlocks blocks A)
    (PF : Certificate blocks F)
    (U : Certificate blocks (polyAdd (cap upper) (polyNeg A))) (k : Nat) :
    let G := reciprocal A upper hupper (k+1)
    let dA := angularDerivative (4*block+i) (4*block+j) A
    Certificate blocks (polyMul (polyMul (polyMul F G) dA)
      (angularDerivative (4*block+i) (4*block+j) (polyMul A G))) := by
  dsimp only
  let G := reciprocal A upper hupper (k+1)
  let dA := angularDerivative (4*block+i) (4*block+j) A
  let E := residual (remainder A upper hupper) k
  have hdA := angularDerivative_supported_at (by omega : 4*block+i < 4*blocks)
    (by omega : 4*block+j < 4*blocks) hA
  let PG := reciprocal_certificate hA hupper U (k+1)
  let PE := residualCertificate (remainderNegative hupper U) k
  let Q := ((PF.mul PG).mul PE).mul (Certificate.square dA hdA)
  have h := (reciprocal_multiplier_derivative_pin (4*block+i) (4*block+j)
    A upper hupper k).mul_left (polyMul (polyMul F G) dA)
  have hmove : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul F G) dA)
        (polySmul (Q'.ofNat (k+1)) (polySmul (scale upper hupper) (polyMul E dA))))
      (polySmul (Q'.ofNat (k+1)) (polySmul (scale upper hupper)
        (polyMul (polyMul (polyMul F G) E) (polyMul dA dA)))) :=
    (RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
      (RatPolyCoeffEqv.smul _ ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 2)))
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 2)))
          (by decide) (fun | 0 => F | 1 => G | 2 => dA | _ => E)).smul (scale upper hupper))))
  exact Certificate.ofCoeff (h.trans hmove)
    ((Q.smul (scale upper hupper) (Q'.le_of_lt (scale_positive upper hupper))).smul
      (Q'.ofNat (k+1)) (ofNat_nonneg _))

private theorem derivative_four_factor_pin (i j : Nat) (F G A : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (polyMul (polyMul (polyMul F (polyMul G G)) A)
        (angularDerivative i j A)))
      (polyAdd
        (polyMul (polyMul F (polyMul G G))
          (polyAdd (polyMul A (angularDerivative i j (angularDerivative i j A)))
            (polyNeg (polyMul (angularDerivative i j A) (angularDerivative i j A)))))
        (polyAdd
          (polyMul (polyMul (polyMul A (polyMul G G)) (angularDerivative i j A))
            (angularDerivative i j F))
          (polyAdd
            (polyMul (polyMul (polyMul F G) (angularDerivative i j A))
              (angularDerivative i j (polyMul A G)))
            (polyMul (polyMul (polyMul F G) (angularDerivative i j A))
              (angularDerivative i j (polyMul A G)))))) := by
  let dA := angularDerivative i j A
  let dF := angularDerivative i j F
  let dG := angularDerivative i j G
  let ddA := angularDerivative i j dA
  have hfg := (angularDerivative_mul i j F (polyMul G G)).trans
    ((RatPolyCoeffEqv.refl _).add ((angularDerivative_mul i j G G).mul_left F))
  have hfga := (angularDerivative_mul i j (polyMul F (polyMul G G)) A).trans
    ((hfg.mul_right A).add (RatPolyCoeffEqv.refl _))
  have htotal := (angularDerivative_mul i j (polyMul (polyMul F (polyMul G G)) A) dA).trans
    ((hfga.mul_right dA).add (RatPolyCoeffEqv.refl _))
  have hring := coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.add
        (.mul (.add (.mul (.var 4) (.mul (.var 1) (.var 1)))
          (.mul (.var 0) (.add (.mul (.var 5) (.var 1)) (.mul (.var 1) (.var 5))))) (.var 2))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 3))) (.var 3))
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2)) (.var 6)))
    (.add
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 2) (.var 6)) (.neg (.mul (.var 3) (.var 3)))))
      (.add (.mul (.mul (.mul (.var 2) (.mul (.var 1) (.var 1))) (.var 3)) (.var 4))
        (.add
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3))
            (.add (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 5))))
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3))
            (.add (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 5)))))))
    (by decide) (fun | 0 => F | 1 => G | 2 => A | 3 => dA | 4 => dF | 5 => dG | _ => ddA)
  have hfav := (angularDerivative_mul i j A G).symm.mul_left (polyMul (polyMul F G) dA)
  exact htotal.trans (hring.trans
    ((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl _).add (hfav.add hfav))))

/-- Weighted IBP discards only the produced favorable finite reciprocal term.
JF remains signed and literal, including any original spatial/noise factors. -/
theorem finite_reciprocal_hessian_ibp_le {blocks block i j : Nat}
    (hb : block < blocks) (hi : i < 4) (hj : j < 4) {F A : RatPoly} {upper : Q'}
    (hupper : (0 : Q') < upper) (hA : SupportedQuaternionBlocks blocks A)
    (PF : Certificate blocks F)
    (U : Certificate blocks (polyAdd (cap upper) (polyNeg A))) (k : Nat) :
    let G := reciprocal A upper hupper (k+1)
    let J := angularDerivative (4*block+i) (4*block+j)
    quaternionHaar blocks (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (J (J A))) (polyNeg (polyMul (J A) (J A))))) ≤
    -quaternionHaar blocks (polyMul (polyMul (polyMul A (polyMul G G)) (J A)) (J F)) := by
  dsimp only
  let G := reciprocal A upper hupper (k+1)
  let dA := angularDerivative (4*block+i) (4*block+j) A
  let L := polyMul (polyMul F (polyMul G G))
    (polyAdd (polyMul A (angularDerivative (4*block+i) (4*block+j) dA))
      (polyNeg (polyMul dA dA)))
  let M := polyMul (polyMul (polyMul A (polyMul G G)) dA)
    (angularDerivative (4*block+i) (4*block+j) F)
  let B := polyMul (polyMul (polyMul F G) dA)
    (angularDerivative (4*block+i) (4*block+j) (polyMul A G))
  have hn : (0 : Q') ≤ quaternionHaar blocks B :=
    (finite_reciprocal_favorable_certificate hb hi hj hupper hA PF U k).haar_nonnegative
  have htotal := derivative_four_factor_pin (4*block+i) (4*block+j) F G A
  have hzero : quaternionHaar blocks L +
      (quaternionHaar blocks M+(quaternionHaar blocks B+quaternionHaar blocks B)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff htotal)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks L _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks M _)
              (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_append blocks B B)))))))
      (quaternionHaar_angularDerivative_at hb hi hj _)
  have hpay : quaternionHaar blocks B+quaternionHaar blocks B ≈
      -quaternionHaar blocks M + -quaternionHaar blocks L := by
    refine Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.var 2) (.var 2))
        (.add (.add (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 2))))
          (.neg (.var 1))) (.neg (.var 0)))
        (by decide) (fun
          | 0 => quaternionHaar blocks L
          | 1 => quaternionHaar blocks M
          | _ => quaternionHaar blocks B)) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hzero (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq (.add (.add (.const 0) (.var 0)) (.var 1))
        (.add (.var 0) (.var 1)) (by decide)
        (fun | 0 => -quaternionHaar blocks M | _ => -quaternionHaar blocks L))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ hn hn) (Q'.le_of_eqv hpay))

end YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign

#print axioms YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign.reciprocal_multiplier_derivative_pin
#print axioms YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign.finite_reciprocal_favorable_certificate
#print axioms YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign.finite_reciprocal_hessian_ibp_le
