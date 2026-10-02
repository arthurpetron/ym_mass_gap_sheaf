/-
# A constructed cap-four interval for the literal unit-word chord

The unit assumptions are arbitrary-insertion Haar equalities. The upper
endpoint is the four-square norm of p+q, using the exact parallelogram
identity; the lower endpoint is four plus the norm of p-q. No pointwise
substitution or path-length bound is used.
-/

import YMGap.Continuum.QuaternionHaarChordalDifference
import YMGap.Continuum.QuaternionHaarPolynomialInterval

namespace YMGap.Continuum.QuaternionHaarChordalInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarWordDifference (difference difference_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPolynomialInterval

private def sumQuaternion (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar q.scalar, polyAdd p.iPart q.iPart,
    polyAdd p.jPart q.jPart, polyAdd p.kPart q.kPart⟩

private def sum_supported {n : Nat} {p q : PolyQuaternion}
    (hp : Supported n p) (hq : Supported n q) : Supported n (sumQuaternion p q) :=
  ⟨supported_add hp.scalar hq.scalar, supported_add hp.iPart hq.iPart,
    supported_add hp.jPart hq.jPart, supported_add hp.kPart hq.kPart⟩

private def normCertificate {n : Nat} (p : PolyQuaternion) (hp : Supported n p) :
    Certificate n (polyQuaternionNorm p) :=
  (Certificate.square p.scalar hp.scalar).add
    ((Certificate.square p.iPart hp.iPart).add
      ((Certificate.square p.jPart hp.jPart).add (Certificate.square p.kPart hp.kPart)))

private def normSupport {n : Nat} (p : PolyQuaternion) (hp : Supported n p) :
    SupportedQuaternionBlocks n (polyQuaternionNorm p) :=
  supported_add (supported_polyMul hp.scalar hp.scalar)
    (supported_add (supported_polyMul hp.iPart hp.iPart)
      (supported_add (supported_polyMul hp.jPart hp.jPart) (supported_polyMul hp.kPart hp.kPart)))

private def env (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar
  | 1 => p.iPart
  | 2 => p.jPart
  | 3 => p.kPart
  | 4 => q.scalar
  | 5 => q.iPart
  | 6 => q.jPart
  | _ => q.kPart

private def sumExpr : PolyQuaternionExpr :=
  ⟨.add (.var 0) (.var 4), .add (.var 1) (.var 5),
    .add (.var 2) (.var 6), .add (.var 3) (.var 7)⟩

private def deltaExpr : PolyQuaternionExpr :=
  ⟨.add (.var 0) (.neg (.var 4)), .add (.var 1) (.neg (.var 5)),
    .add (.var 2) (.neg (.var 6)), .add (.var 3) (.neg (.var 7))⟩

private theorem upper_pin {n : Nat} {p q : PolyQuaternion}
    (hp : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (hq : HaarCarrierEqv n (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv n
      (polyAdd (cap 4) (polyNeg (polyQuaternionNorm (difference p q))))
      (polyQuaternionNorm (sumQuaternion p q)) := by
  let r := polyQuaternionNorm (difference p q)
  have hfirst : RatPolyCoeffEqv (polyAdd (cap 4) (polyNeg r))
      (polyAdd (polyMul (cap 2) polyOne)
        (polyAdd (polyMul (cap 2) polyOne) (polyNeg r))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.add (.const 4) (.neg (.var 0)))
      (.add (.mul (.const 2) (.const 1))
        (.add (.mul (.const 2) (.const 1)) (.neg (.var 0))))
      (by decide) (fun _ => r)
  have hunit := HaarCarrierEqv.add
    (HaarCarrierEqv.mul_left (cap 2) (HaarCarrierEqv.symm hp))
    (HaarCarrierEqv.add
      (HaarCarrierEqv.mul_left (cap 2) (HaarCarrierEqv.symm hq))
      (HaarCarrierEqv.refl n (polyNeg r)))
  have hlast : RatPolyCoeffEqv
      (polyAdd (polyMul (cap 2) (polyQuaternionNorm p))
        (polyAdd (polyMul (cap 2) (polyQuaternionNorm q)) (polyNeg r)))
      (polyQuaternionNorm (sumQuaternion p q)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.const 2) (PolyQuaternionExpr.norm (.coordinate 0)))
        (.add (.mul (.const 2) (PolyQuaternionExpr.norm (.coordinate 4)))
          (.neg (PolyQuaternionExpr.norm deltaExpr))))
      (PolyQuaternionExpr.norm sumExpr) (by decide) (env p q)
  exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier hfirst)
    (HaarCarrierEqv.trans hunit (RatPolyCoeffEqv.haarCarrier hlast))

/-- Exact Type-valued cap-four interval for the ENTIRE supported unit words. -/
def chord_interval {n : Nat} {p q : PolyQuaternion}
    (hp : Supported n p) (hq : Supported n q)
    (hp1 : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (hq1 : HaarCarrierEqv n (polyQuaternionNorm q) polyOne) :
    Interval n (polyQuaternionNorm (difference p q)) 4 :=
  ⟨normSupport _ (difference_supported hp hq), by decide,
    Certificate.transport (upper_pin hp1 hq1) (normCertificate _ (sum_supported hp hq)),
    (Certificate.constant n 4 (by decide)).add (normCertificate _ (difference_supported hp hq))⟩

#print axioms chord_interval

end YMGap.Continuum.QuaternionHaarChordalInterval
