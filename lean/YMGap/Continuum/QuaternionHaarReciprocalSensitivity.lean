/-
# Degree-uniform sensitivity of the actual finite reciprocal

For x=-R, h=1+R and S_k=corrector R k, construct J_0=0 and
J_(k+1)=S_k+x*J_k. Then D S_k=-J_k*D R and F_k=h^2*J_k.
The exact complement 1-F_(k+1)=x^k*(x+(k+1)*h) constructs
0<=F_k<=1 whenever x and h have actual Haar certificates.

For R=sigma*A-1 and G_k=sigma*S_k this gives the literal polynomial
slope sigma^2*J_k, D G_k=-slope*D A, and a certificate for
1-(A^2*slope)^2. There is no lower-window constant or degree-dependent
loss. No limiting inverse or relative filtered-variance estimate is claimed.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.QuaternionHaarReciprocalSensitivity

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
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarAngularCarrier

/-- The derivative row of the existing finite geometric corrector. -/
def sensitivityRow (R : RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | k+1 => polyAdd (corrector R k) (polyMul (polyNeg R) (sensitivityRow R k))

/-- Cleared sensitivity multiplier, on the original shared carrier. -/
def sensitivity (R : RatPoly) (k : Nat) : RatPoly :=
  polyMul (polyMul (polyAdd polyOne R) (polyAdd polyOne R)) (sensitivityRow R k)

private theorem derivative_zero (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans (RatPolyCoeffEqv.zero_smul _))

/-- Exact derivative of the existing corrector, with no degree bound. -/
theorem corrector_angularDerivative (i j : Nat) (R : RatPoly) : ∀ k : Nat,
    RatPolyCoeffEqv (angularDerivative i j (corrector R k))
      (polyNeg (polyMul (sensitivityRow R k) (angularDerivative i j R)))
  | 0 => (derivative_zero i j).trans
      ((RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left _)).symm)
  | k+1 => by
      let dR := angularDerivative i j R
      have hprod := (angularDerivative_mul i j (polyNeg R) (corrector R k)).trans
        (((angularDerivative_neg i j R).mul_right _).add
          ((corrector_angularDerivative i j R k).mul_left (polyNeg R)))
      have hr : RatPolyCoeffEqv
          (polyAdd (polyMul (polyNeg dR) (corrector R k))
            (polyMul (polyNeg R) (polyNeg (polyMul (sensitivityRow R k) dR))))
          (polyNeg (polyMul (sensitivityRow R (k+1)) dR)) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.neg (.var 0)) (.var 1))
            (.mul (.neg (.var 2)) (.neg (.mul (.var 3) (.var 0)))))
          (.neg (.mul (.add (.var 1) (.mul (.neg (.var 2)) (.var 3))) (.var 0)))
          (by decide)
          (fun
            | 0 => dR
            | 1 => corrector R k
            | 2 => R
            | _ => sensitivityRow R k)
      exact (angularDerivative_add i j polyOne _).trans
        (((angularDerivative_one i j).add hprod).trans
          ((RatPolyCoeffEqv.zero_add _).trans hr))

private theorem sensitivity_zero (R : RatPoly) :
    RatPolyCoeffEqv (sensitivity R 0) polyZero := RatPolyCoeffEqv.mul_zero_right _

/-- The exact positive complement, including k=0 (F_1=0).
The power is the ORIGINAL residual, not an evaluation-only replacement. -/
theorem sensitivity_complement_succ (R : RatPoly) : ∀ k : Nat,
    RatPolyCoeffEqv (polyAdd polyOne (polyNeg (sensitivity R (k+1))))
      (polyMul (residual R k)
        (polyAdd (polyNeg R) (polySmul (Q'.ofNat (k+1)) (polyAdd polyOne R)))) := by
  have hsum : ∀ k : Nat,
      RatPolyCoeffEqv
        (polyAdd (sensitivity R (k+1))
          (polyMul (residual R k)
            (polyAdd (polyNeg R) (polySmul (Q'.ofNat (k+1)) (polyAdd polyOne R)))))
        polyOne := by
    intro k
    induction k with
    | zero =>
        have h : RatPolyCoeffEqv (sensitivity R 1) polyZero :=
          ((RatPolyCoeffEqv.refl _).mul
            (((RatPolyCoeffEqv.refl polyZero).add
              (RatPolyCoeffEqv.mul_zero_right _)).trans (RatPolyCoeffEqv.add_zero polyZero)))
            |>.trans (RatPolyCoeffEqv.mul_zero_right _)
        exact (h.add
          ((RatPolyCoeffEqv.one_mul _).trans
            (((RatPolyCoeffEqv.refl _).add
              ((RatPolyCoeffEqv.smul_coefficient (by decide) _).trans
                (RatPolyCoeffEqv.one_smul _))).trans
              (coeffEvalExpr_eqv_of_normalize_eq
                (.add (.neg (.var 0)) (.add (.const 1) (.var 0))) (.const 1)
                (by decide) (fun _ => R))))).trans (RatPolyCoeffEqv.zero_add _)
    | succ k ih =>
        let h := polyAdd polyOne R
        let x := polyNeg R
        let e := residual R k
        let f := sensitivity R (k+1)
        let s := corrector R (k+1)
        let c := Q'.ofNat (k+1)
        have hc : Q'.eqv (Q'.ofNat (k+2)) (c+1) := Q'.ofNat_add_eqv (k+1) 1
        have hcast : RatPolyCoeffEqv
            (polyAdd (sensitivity R (k+2))
              (polyMul (residual R (k+1))
                (polyAdd x (polySmul (Q'.ofNat (k+2)) h))))
            (polyAdd (sensitivity R (k+2))
              (polyMul (residual R (k+1)) (polyAdd x (polySmul (c+1) h)))) :=
          (RatPolyCoeffEqv.refl _).add
            (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_coefficient hc h)).mul_left _)
        have halg : RatPolyCoeffEqv
            (polyAdd (sensitivity R (k+2))
              (polyMul (residual R (k+1)) (polyAdd x (polySmul (c+1) h))))
            (polyAdd
              (polyMul h (polyAdd (polyMul h s) (residual R (k+1))))
              (polyMul x (polyAdd f (polyMul e (polyAdd x (polySmul c h)))))) := by
          -- Expose only the one-step row and residual recurrences.
          change RatPolyCoeffEqv
            (polyAdd (polyMul (polyMul h h)
              (polyAdd s (polyMul x (sensitivityRow R (k+1)))))
              (polyMul (polyMul x e) (polyAdd x (polySmul (c+1) h)))) _
          have hc1 : RatPolyCoeffEqv (cap (c+1)) (polyAdd (cap c) polyOne) :=
            (cap_add c 1).symm.trans
              ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul polyOne))
          have hcH : RatPolyCoeffEqv (polySmul (c+1) h)
              (polyMul (polyAdd (cap c) polyOne) h) :=
            (cap_mul_left (c+1) h).symm.trans (hc1.mul_right h)
          have hn := coeffEvalExpr_eqv_of_normalize_eq
            (.add (.mul (.mul (.var 0) (.var 0))
              (.add (.var 1) (.mul (.var 2) (.var 3))))
              (.mul (.mul (.var 2) (.var 4))
                (.add (.var 2) (.mul (.add (.var 5) (.const 1)) (.var 0)))))
            (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 1))
              (.mul (.var 2) (.var 4))))
              (.mul (.var 2) (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
                (.mul (.var 4) (.add (.var 2) (.mul (.var 5) (.var 0)))))))
            (by decide)
            (fun
              | 0 => h
              | 1 => s
              | 2 => x
              | 3 => sensitivityRow R (k+1)
              | 4 => e
              | _ => cap c)
          exact ((RatPolyCoeffEqv.refl _).add
            (((RatPolyCoeffEqv.refl x).add hcH).mul_left (polyMul x e))).trans
            (hn.trans ((RatPolyCoeffEqv.refl _).add
              (((RatPolyCoeffEqv.refl f).add
                (((RatPolyCoeffEqv.refl x).add (cap_mul_left c h)).mul_left e)).mul_left x)))
        exact hcast.trans (halg.trans
          ((((cancellation R (k+1)).mul_left h).add (ih.mul_left x)).trans
            (((RatPolyCoeffEqv.mul_one h).add (RatPolyCoeffEqv.mul_one x)).trans
              (coeffEvalExpr_eqv_of_normalize_eq
                (.add (.add (.const 1) (.var 0)) (.neg (.var 0))) (.const 1)
                (by decide) (fun _ => R)))))
  intro k
  let f := sensitivity R (k+1)
  let c := polyMul (residual R k)
    (polyAdd (polyNeg R) (polySmul (Q'.ofNat (k+1)) (polyAdd polyOne R)))
  exact ((hsum k).symm.add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide)
        (fun
          | 0 => f
          | _ => c))

private def correctorCertificate {blocks : Nat} {R : RatPoly}
    (X : Certificate blocks (polyNeg R)) :
    (k : Nat) → Certificate blocks (corrector R k)
  | 0 => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | k+1 => (Certificate.one blocks).add (X.mul (correctorCertificate X k))

private def rowCertificate {blocks : Nat} {R : RatPoly}
    (X : Certificate blocks (polyNeg R)) :
    (k : Nat) → Certificate blocks (sensitivityRow R k)
  | 0 => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | k+1 => (correctorCertificate X k).add (X.mul (rowCertificate X k))

/-- Actual positivity of the finite multiplier; no strict lower floor. -/
def sensitivityCertificate {blocks : Nat} {R : RatPoly}
    (X : Certificate blocks (polyNeg R))
    (H : Certificate blocks (polyAdd polyOne R)) (k : Nat) :
    Certificate blocks (sensitivity R k) := (H.mul H).mul (rowCertificate X k)

/-- Constructed unit complement, valid even when A vanishes on the carrier. -/
def sensitivityComplementCertificate {blocks : Nat} {R : RatPoly}
    (X : Certificate blocks (polyNeg R))
    (H : Certificate blocks (polyAdd polyOne R)) :
    (k : Nat) → Certificate blocks (polyAdd polyOne (polyNeg (sensitivity R k)))
  | 0 => Certificate.ofCoeff
      (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (sensitivity_zero R))).trans
        (RatPolyCoeffEqv.add_zero _)) (Certificate.one blocks)
  | k+1 => Certificate.ofCoeff (sensitivity_complement_succ R k)
      ((residualCertificate X k).mul (X.add (H.smul (Q'.ofNat (k+1)) (by
        rw [Q'.zero_le_iff_num_nonneg]
        exact Int.natCast_nonneg (k+1)))))

/-- The actual polynomial slope of the existing reciprocal. -/
def reciprocalSlope (A : RatPoly) (u : Q') (hu : (0 : Q') < u) (k : Nat) : RatPoly :=
  polySmul (scale u hu * scale u hu) (sensitivityRow (remainder A u hu) k)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem row_supported {blocks : Nat} {R : RatPoly}
    (hR : SupportedQuaternionBlocks blocks R) : ∀ k : Nat,
    SupportedQuaternionBlocks blocks (sensitivityRow R k)
  | 0 => fun _ ht => False.elim (List.not_mem_nil ht)
  | k+1 => supported_add (corrector_supported hR k)
      (supported_polyMul (support_neg hR) (row_supported hR k))

/-- The slope retains every original variable and spectator. -/
theorem reciprocalSlope_supported {blocks : Nat} {A : RatPoly}
    (hA : SupportedQuaternionBlocks blocks A)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    SupportedQuaternionBlocks blocks (reciprocalSlope A u hu k) := by
  intro term ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact row_supported (remainder_supported hA u hu) k s hs

private theorem remainder_normalized (A : RatPoly) (u : Q') (hu : (0 : Q') < u) :
    RatPolyCoeffEqv (polyAdd polyOne (remainder A u hu)) (polySmul (scale u hu) A) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.const 1) (.add (.var 0) (.neg (.const 1)))) (.var 0)
    (by decide) (fun _ => polySmul (scale u hu) A)

/-- The reciprocal multiplier is bounded even without a strictly positive
lower window. This is a finite polynomial statement, not an inverse at A=0. -/
def reciprocalMultiplierSquareCertificate {blocks : Nat} {A : RatPoly}
    {u : Q'} (hu : (0 : Q') < u) (P : Certificate blocks A)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A))) (k : Nat) :
    Certificate blocks (polyAdd polyOne (polyNeg (polyMul
      (polyMul A (reciprocal A u hu k)) (polyMul A (reciprocal A u hu k))))) := by
  let R := remainder A u hu
  let f := polyMul A (reciprocal A u hu k)
  let e := residual R k
  have X := remainderNegative hu U
  have H : Certificate blocks (polyAdd polyOne R) :=
    Certificate.ofCoeff (remainder_normalized A u hu)
      (P.smul (scale u hu) (Q'.le_of_lt (scale_positive u hu)))
  have hf : RatPolyCoeffEqv f
      (polyMul (polyAdd polyOne R) (corrector R k)) :=
    (RatPolyCoeffEqv.polyMul_smul_right (scale u hu) A (corrector R k)).trans
      ((RatPolyCoeffEqv.polyMul_smul_left (scale u hu) A (corrector R k)).symm.trans
        ((remainder_normalized A u hu).symm.mul_right (corrector R k)))
  have F : Certificate blocks f := Certificate.ofCoeff hf (H.mul (correctorCertificate X k))
  have hc : RatPolyCoeffEqv (polyAdd polyOne (polyNeg f)) e :=
    (((reciprocal_cancellation A u hu k).symm).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun | 0 => f | _ => e))
  have C := Certificate.ofCoeff hc (residualCertificate X k)
  exact Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
      (by decide) (fun _ => f))
    (C.mul ((Certificate.one blocks).add F))

/-- Formal derivative of the literal finite reciprocal, with an explicit slope. -/
theorem reciprocal_angularDerivative (i j : Nat) (A : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (angularDerivative i j (reciprocal A u hu k))
      (polyNeg (polyMul (reciprocalSlope A u hu k) (angularDerivative i j A))) := by
  let a := scale u hu
  let R := remainder A u hu
  let J := sensitivityRow R k
  let dA := angularDerivative i j A
  have hR : RatPolyCoeffEqv (angularDerivative i j R) (polySmul a dA) :=
    ((angularDerivative_add i j polyOne R).trans
      (((angularDerivative_one i j).add (RatPolyCoeffEqv.refl _)).trans
        (RatPolyCoeffEqv.zero_add _))).symm.trans
      ((angularDerivative_congr i j (remainder_normalized A u hu)).trans
        (angularDerivative_smul i j a A))
  have hd := (angularDerivative_smul i j a (corrector R k)).trans
    (((corrector_angularDerivative i j R k).trans
      (RatPolyCoeffEqv.neg (hR.mul_left J))).smul a)
  have hr : RatPolyCoeffEqv
      (polySmul a (polyNeg (polyMul J (polySmul a dA))))
      (polyNeg (polyMul (polySmul (a*a) J) dA)) := by
    have hl : RatPolyCoeffEqv
        (polySmul a (polyNeg (polyMul J (polySmul a dA))))
        (polyMul (cap a) (polyNeg (polyMul J (polyMul (cap a) dA)))) :=
      (cap_mul_left a _).symm.trans
        ((RatPolyCoeffEqv.neg ((cap_mul_left a dA).symm.mul_left J)).mul_left (cap a))
    have hn := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.neg (.mul (.var 1) (.mul (.var 0) (.var 2)))))
      (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2)))
      (by decide)
      (fun
        | 0 => cap a
        | 1 => J
        | _ => dA)
    have hh : RatPolyCoeffEqv (polyMul (polyMul (cap a) (cap a)) J)
        (polySmul (a*a) J) :=
      ((cap_mul a a).mul_right J).trans (cap_mul_left (a*a) J)
    exact hl.trans (hn.trans (RatPolyCoeffEqv.neg (hh.mul_right dA)))
  exact hd.trans hr

/-- Exact coefficient pin to the certified dimensionless multiplier. -/
theorem reciprocalSlope_multiplier_pin (A : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (polyMul (polyMul A A) (reciprocalSlope A u hu k))
      (sensitivity (remainder A u hu) k) := by
  let a := scale u hu
  let R := remainder A u hu
  let J := sensitivityRow R k
  have h := (remainder_normalized A u hu).mul (remainder_normalized A u hu)
  have hl : RatPolyCoeffEqv (polyMul (polyMul A A) (polySmul (a*a) J))
      (polyMul (polyMul A A) (polyMul (polyMul (cap a) (cap a)) J)) :=
    ((cap_mul_left (a*a) J).symm.trans ((cap_mul a a).symm.mul_right J)).mul_left _
  exact hl.trans ((coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
    (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.var 2))
    (by decide)
    (fun
      | 0 => A
      | 1 => cap a
      | _ => J)).trans
    ((((cap_mul_left a A).mul (cap_mul_left a A)).mul_right J).trans
      (h.symm.mul_right J)))

/-- The degree-uniform square certificate needs only 0<=A<=u, not ell<=A. -/
def reciprocalSensitivitySquareCertificate {blocks : Nat} {A : RatPoly}
    {u : Q'} (hu : (0 : Q') < u) (P : Certificate blocks A)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A))) (k : Nat) :
    Certificate blocks (polyAdd polyOne (polyNeg (polyMul
      (polyMul (polyMul A A) (reciprocalSlope A u hu k))
      (polyMul (polyMul A A) (reciprocalSlope A u hu k))))) := by
  let R := remainder A u hu
  let F := sensitivity R k
  have X := remainderNegative hu U
  have H : Certificate blocks (polyAdd polyOne R) :=
    Certificate.ofCoeff (remainder_normalized A u hu)
      (P.smul (scale u hu) (Q'.le_of_lt (scale_positive u hu)))
  have FC := sensitivityCertificate X H k
  have CC := sensitivityComplementCertificate X H k
  have hs : RatPolyCoeffEqv (polyAdd polyOne (polyNeg (polyMul F F)))
      (polyMul (polyAdd polyOne (polyNeg F)) (polyAdd polyOne F)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
      (by decide) (fun _ => F)
  exact Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
      ((reciprocalSlope_multiplier_pin A u hu k).mul
        (reciprocalSlope_multiplier_pin A u hu k)))).trans hs)
    (CC.mul ((Certificate.one blocks).add FC))

end YMGap.Continuum.QuaternionHaarReciprocalSensitivity

#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.sensitivityRow
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.sensitivity
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.corrector_angularDerivative
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.sensitivity_complement_succ
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.sensitivityCertificate
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.sensitivityComplementCertificate
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.reciprocalSlope
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.reciprocalSlope_supported
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.reciprocalMultiplierSquareCertificate
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.reciprocal_angularDerivative
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.reciprocalSlope_multiplier_pin
#print axioms YMGap.Continuum.QuaternionHaarReciprocalSensitivity.reciprocalSensitivitySquareCertificate
