/-
# Finite algebra for relative polynomial interval certificates

Every operation below transports or combines original-Haar positive-cone
certificates. No analytic relative derivative estimate is introduced here.
-/

import YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

namespace YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace RelativeInterval

/-- Transport the base polynomial without changing the signed numerator. -/
def baseOfCoeff {blocks : Nat} {base newBase p : RatPoly} {c : Q'}
    (h : RatPolyCoeffEqv newBase base)
    (P : RelativeInterval blocks base p c) :
    RelativeInterval blocks newBase p c where
  lower := Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl (cap c)).mul h).add (RatPolyCoeffEqv.refl p)) P.lower
  upper := Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl (cap c)).mul h).add (RatPolyCoeffEqv.refl _)) P.upper

private def halveDouble {blocks : Nat} {p q : RatPoly}
    (h : RatPolyCoeffEqv (polyAdd p p) q) (Q : Certificate blocks q) :
    Certificate blocks p := by
  have he : RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p :=
    (RatPolyCoeffEqv.smul_add _ _ _).trans
      ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
        ((RatPolyCoeffEqv.smul_coefficient (by decide) p).trans
          (RatPolyCoeffEqv.one_smul p)))
  exact Certificate.ofCoeff he.symm
    ((Certificate.ofCoeff h Q).smul HalfPow.half HalfPow.half_nonneg)

/-- Relative intervals multiply without assuming either numerator has a sign.
The two endpoint certificates are half-sums of signed products. -/
def mul {blocks : Nat} {a b p q : RatPoly} {c d : Q'}
    (P : RelativeInterval blocks a p c)
    (Q : RelativeInterval blocks b q d) :
    RelativeInterval blocks (polyMul a b) (polyMul p q) (c*d) := by
  let C := cap c
  let D := cap d
  let L := polyAdd (polyMul (cap (c*d)) (polyMul a b)) (polyMul p q)
  let U := polyAdd (polyMul (cap (c*d)) (polyMul a b))
    (polyNeg (polyMul p q))
  have hc : RatPolyCoeffEqv (cap (c*d)) (polyMul C D) :=
    (cap_mul c d).symm
  have hl : RatPolyCoeffEqv (polyAdd L L)
      (polyAdd (polyMul (polyAdd (polyMul C a) p)
        (polyAdd (polyMul D b) q))
        (polyMul (polyAdd (polyMul C a) (polyNeg p))
          (polyAdd (polyMul D b) (polyNeg q)))) := by
    apply (((hc.mul_right (polyMul a b)).add (RatPolyCoeffEqv.refl _)).add
      ((hc.mul_right (polyMul a b)).add (RatPolyCoeffEqv.refl _))).trans
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.var 4) (.var 5)))
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.var 4) (.var 5))))
      (.add
        (.mul (.add (.mul (.var 0) (.var 2)) (.var 4))
          (.add (.mul (.var 1) (.var 3)) (.var 5)))
        (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.var 4)))
          (.add (.mul (.var 1) (.var 3)) (.neg (.var 5)))))
      (by decide) (fun | 0 => C | 1 => D | 2 => a | 3 => b | 4 => p | _ => q)
  have hu : RatPolyCoeffEqv (polyAdd U U)
      (polyAdd (polyMul (polyAdd (polyMul C a) p)
        (polyAdd (polyMul D b) (polyNeg q)))
        (polyMul (polyAdd (polyMul C a) (polyNeg p))
          (polyAdd (polyMul D b) q))) := by
    apply (((hc.mul_right (polyMul a b)).add (RatPolyCoeffEqv.refl _)).add
      ((hc.mul_right (polyMul a b)).add (RatPolyCoeffEqv.refl _))).trans
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.neg (.mul (.var 4) (.var 5))))
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.neg (.mul (.var 4) (.var 5)))))
      (.add
        (.mul (.add (.mul (.var 0) (.var 2)) (.var 4))
          (.add (.mul (.var 1) (.var 3)) (.neg (.var 5))))
        (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.var 4)))
          (.add (.mul (.var 1) (.var 3)) (.var 5))))
      (by decide) (fun | 0 => C | 1 => D | 2 => a | 3 => b | 4 => p | _ => q)
  exact ⟨halveDouble hl (P.lower.mul Q.lower |>.add (P.upper.mul Q.upper)),
    halveDouble hu (P.lower.mul Q.upper |>.add (P.upper.mul Q.lower))⟩

/-- Add both bases and both numerators at a common relative cap. -/
def sumBases {blocks : Nat} {a b p q : RatPoly} {c : Q'}
    (P : RelativeInterval blocks a p c)
    (Q : RelativeInterval blocks b q c) :
    RelativeInterval blocks (polyAdd a b) (polyAdd p q) c := by
  constructor
  · exact Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
          (.add (.var 3) (.var 4)))
        (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
          (.add (.mul (.var 0) (.var 2)) (.var 4)))
        (by decide) (fun | 0 => cap c | 1 => a | 2 => b | 3 => p | _ => q))
      (P.lower.add Q.lower)
  · exact Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
          (.neg (.add (.var 3) (.var 4))))
        (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 3)))
          (.add (.mul (.var 0) (.var 2)) (.neg (.var 4))))
        (by decide) (fun | 0 => cap c | 1 => a | 2 => b | 3 => p | _ => q))
      (P.upper.add Q.upper)

/-- A nonnegative scalar scales the base and numerator together, leaving
the relative cap unchanged. -/
def smulBoth {blocks : Nat} {base p : RatPoly} {c : Q'}
    (P : RelativeInterval blocks base p c) (r : Q') (hr : (0 : Q') ≤ r) :
    RelativeInterval blocks (polySmul r base) (polySmul r p) c := by
  have hbase : RatPolyCoeffEqv (polySmul r base) (polyMul (cap r) base) :=
    (cap_mul_left r base).symm
  have hp : RatPolyCoeffEqv (polySmul r p) (polyMul (cap r) p) :=
    (cap_mul_left r p).symm
  have hplus : RatPolyCoeffEqv
      (polyAdd (polyMul (cap c) (polySmul r base)) (polySmul r p))
      (polyMul (cap r) (polyAdd (polyMul (cap c) base) p)) := by
    exact (((RatPolyCoeffEqv.refl _).mul hbase).add hp).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => cap c | 1 => cap r | 2 => base | _ => p))
  have hminus : RatPolyCoeffEqv
      (polyAdd (polyMul (cap c) (polySmul r base)) (polyNeg (polySmul r p)))
      (polyMul (cap r) (polyAdd (polyMul (cap c) base) (polyNeg p))) := by
    exact (((RatPolyCoeffEqv.refl _).mul hbase).add (RatPolyCoeffEqv.neg hp)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.neg (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))))
        (by decide) (fun | 0 => cap c | 1 => cap r | 2 => base | _ => p))
  have R : Certificate blocks (cap r) :=
    Certificate.ofCoeff (RatPolyCoeffEqv.refl _) (Certificate.constant blocks r hr)
  exact ⟨Certificate.ofCoeff hplus (R.mul P.lower),
    Certificate.ofCoeff hminus (R.mul P.upper)⟩

/-- Widen a relative cap using a certificate of the common base. -/
def weaken {blocks : Nat} {base p : RatPoly} {c d : Q'}
    (P : RelativeInterval blocks base p c)
    (hbase : Certificate blocks base) (hcd : c ≤ d) :
    RelativeInterval blocks base p d := by
  let delta := d + -c
  have hd : (0 : Q') ≤ delta := Q'.sub_nonneg_of_le hcd
  have hdiff : Certificate blocks (polyMul (cap delta) base) :=
    (Certificate.constant blocks delta hd).mul hbase
  have hcap : RatPolyCoeffEqv (cap d) (polyAdd (cap c) (cap delta)) := by
    have he : Q'.eqv (c+delta) d := by
      unfold delta
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
        (.var 1) (by decide) (fun | 0 => c | _ => d)
    exact (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm he) polyOne).trans
      (cap_add c delta).symm
  constructor
  · exact Certificate.ofCoeff
      (((hcap.mul_right base).add (RatPolyCoeffEqv.refl p)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
          (.add (.add (.mul (.var 0) (.var 2)) (.var 3))
            (.mul (.var 1) (.var 2)))
          (by decide) (fun | 0 => cap c | 1 => cap delta | 2 => base | _ => p)))
      (P.lower.add hdiff)
  · exact Certificate.ofCoeff
      (((hcap.mul_right base).add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 3)))
          (.add (.add (.mul (.var 0) (.var 2)) (.neg (.var 3)))
            (.mul (.var 1) (.var 2)))
          (by decide) (fun | 0 => cap c | 1 => cap delta | 2 => base | _ => p)))
      (P.upper.add hdiff)

/-- The base itself has the exact relative cap one. -/
def self {blocks : Nat} {base : RatPoly}
    (hbase : Certificate blocks base) :
    RelativeInterval blocks base base 1 := by
  have h1 : RatPolyCoeffEqv (polyMul (cap 1) base) base :=
    ((RatPolyCoeffEqv.one_smul polyOne).mul_right base).trans
      (RatPolyCoeffEqv.one_mul base)
  constructor
  · exact Certificate.ofCoeff
      (h1.add (RatPolyCoeffEqv.refl base)) (hbase.add hbase)
  · exact Certificate.ofCoeff
      ((h1.add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.var 0) (.neg (.var 0)))
          (.const 0) (by decide) (fun _ => base)))
      (Certificate.constant blocks 0 (Q'.le_refl' _))

end RelativeInterval

end YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.baseOfCoeff
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.mul
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.sumBases
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.smulBoth
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.weaken
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.self
