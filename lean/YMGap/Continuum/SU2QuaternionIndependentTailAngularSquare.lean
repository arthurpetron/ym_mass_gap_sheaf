/-
# A selected fundamental angular square with an independent quaternion tail

This is finite eight-variable algebra.  The tail quaternion may depend on
every block except the selected one; its Haar-unit norm is an explicit
arbitrary-insertion hypothesis.  The intermediate identity retains both
quaternion norms.  No heat eigenvalue, source, or scaling estimate enters.
-/

import YMGap.Continuum.SU2QuaternionAngularCoordinate
import YMGap.Continuum.SU2QuaternionAngularSquareLocality
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

namespace YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularCoordinate
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)

private def environment (block : Nat) (p : PolyQuaternion) : Nat → RatPoly
  | 0 => polyVar (4*block)
  | 1 => polyVar (4*block+1)
  | 2 => polyVar (4*block+2)
  | 3 => polyVar (4*block+3)
  | 4 => p.scalar
  | 5 => p.iPart
  | 6 => p.jPart
  | 7 => p.kPart
  | _ => polyZero

private def signedExpr : Nat → PolyExpr
  | 0 => .var 4
  | 1 => .neg (.var 5)
  | 2 => .neg (.var 6)
  | 3 => .neg (.var 7)
  | _ => .const 0

private def linearExpr : PolyExpr :=
  .add (.mul (.var 0) (signedExpr 0))
    (.add (.mul (.var 1) (signedExpr 1))
      (.add (.mul (.var 2) (signedExpr 2))
        (.mul (.var 3) (signedExpr 3))))

private def linearForm (block : Nat) (p : PolyQuaternion) : RatPoly :=
  coeffEvalExpr (environment block p) linearExpr

private def deltaExpr (u v k : Nat) : PolyExpr :=
  .add (if v = k then .var u else .const 0)
    (.neg (if u = k then .var v else .const 0))

private def termExpr (u v k : Nat) : PolyExpr :=
  .mul (deltaExpr u v k) (signedExpr k)

private def derivativeExpr (u v : Nat) : PolyExpr :=
  .add (termExpr u v 0)
    (.add (termExpr u v 1)
      (.add (termExpr u v 2) (termExpr u v 3)))

private def planeExpr (u v : Nat) : PolyExpr :=
  .add (.mul (.var u) (signedExpr v))
    (.neg (.mul (.var v) (signedExpr u)))

private def rotatedExpr (u v : Nat) : PolyExpr :=
  .mul (.const 2) (planeExpr u v)

private def radiusExpr : PolyExpr :=
  .add (.mul (.var 0) (.var 0))
    (.add (.mul (.var 1) (.var 1))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))

private def tailNormExpr : PolyExpr :=
  .add (.mul (.var 4) (.var 4))
    (.add (.mul (.var 5) (.var 5))
      (.add (.mul (.var 6) (.var 6)) (.mul (.var 7) (.var 7))))

private def sixSquareExpr : PolyExpr :=
  .add (.mul (rotatedExpr 0 1) (rotatedExpr 0 1))
    (.add (.mul (rotatedExpr 0 2) (rotatedExpr 0 2))
      (.add (.mul (rotatedExpr 0 3) (rotatedExpr 0 3))
        (.add (.mul (rotatedExpr 1 2) (rotatedExpr 1 2))
          (.add (.mul (rotatedExpr 1 3) (rotatedExpr 1 3))
            (.mul (rotatedExpr 2 3) (rotatedExpr 2 3))))))

private def normDifferenceExpr : PolyExpr :=
  .add (.mul (.const 4) (.mul radiusExpr tailNormExpr))
    (.neg (.mul (.mul (.const 2) linearExpr)
      (.mul (.const 2) linearExpr)))

private theorem coefficient_independent {block k : Nat} (p : PolyQuaternion)
    (hd : HasPolyQuaternionBlockDegree block 0 p) (hk : k < 4) :
    QuaternionBlockIndependent block
      (coeffEvalExpr (environment block p) (signedExpr k)) := by
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact degree_zero_independent hd.scalar
  · exact quaternionBlockIndependent_polyNeg (degree_zero_independent hd.iPart)
  · exact quaternionBlockIndependent_polyNeg (degree_zero_independent hd.jPart)
  · exact quaternionBlockIndependent_polyNeg (degree_zero_independent hd.kPart)

private theorem delta_carrier {blocks block u v k : Nat} (hb : block < blocks)
    (hu : u < 4) (hv : v < 4) (hk : k < 4) (p : PolyQuaternion) :
    HaarCarrierEqv blocks
      (angularDerivative (4*block+u) (4*block+v) (polyVar (4*block+k)))
      (coeffEvalExpr (environment block p) (deltaExpr u v k)) := by
  have hc := angular_coordinate_carrier (i := 4*block+u) (j := 4*block+v)
    (k := 4*block+k) (by omega : 4*block+k < 4*blocks)
  have hu' : (4*block+u = 4*block+k) ↔ u=k := Nat.add_left_cancel_iff
  have hv' : (4*block+v = 4*block+k) ↔ v=k := Nat.add_left_cancel_iff
  have hleft : RatPolyCoeffEqv
      (if 4*block+v=4*block+k then polyVar (4*block+u) else polyZero)
      (coeffEvalExpr (environment block p)
        (if v=k then .var u else .const 0)) := by
    by_cases h : v=k
    · simp only [if_pos h, if_pos (hv'.mpr h), coeffEvalExpr]
      have huCases : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
      rcases huCases with rfl | rfl | rfl | rfl <;> exact RatPolyCoeffEqv.refl _
    · simp only [if_neg h, if_neg (fun e => h (hv'.mp e)), coeffEvalExpr]
      exact (RatPolyCoeffEqv.zero_smul polyOne).symm
  have hright : RatPolyCoeffEqv
      (if 4*block+u=4*block+k then polyVar (4*block+v) else polyZero)
      (coeffEvalExpr (environment block p)
        (if u=k then .var v else .const 0)) := by
    by_cases h : u=k
    · simp only [if_pos h, if_pos (hu'.mpr h), coeffEvalExpr]
      have hvCases : v=0 ∨ v=1 ∨ v=2 ∨ v=3 := by omega
      rcases hvCases with rfl | rfl | rfl | rfl <;> exact RatPolyCoeffEqv.refl _
    · simp only [if_neg h, if_neg (fun e => h (hu'.mp e)), coeffEvalExpr]
      exact (RatPolyCoeffEqv.zero_smul polyOne).symm
  exact hc.trans (RatPolyCoeffEqv.haarCarrier
    (hleft.add ((neg_smul _).symm.trans (RatPolyCoeffEqv.neg hright))))

private theorem term_derivative {blocks block u v k : Nat} (hb : block < blocks)
    (hu : u < 4) (hv : v < 4) (hk : k < 4) (p : PolyQuaternion)
    (hd : HasPolyQuaternionBlockDegree block 0 p) :
    HaarCarrierEqv blocks
      (angularDerivative (4*block+u) (4*block+v)
        (polyMul (polyVar (4*block+k))
          (coeffEvalExpr (environment block p) (signedExpr k))))
      (coeffEvalExpr (environment block p) (termExpr u v k)) := by
  let c := coeffEvalExpr (environment block p) (signedExpr k)
  have hz := angularDerivative_blockIndependent_zero hu hv
    (coefficient_independent p hd hk)
  have h := angularDerivative_mul (4*block+u) (4*block+v)
    (polyVar (4*block+k)) c
  have hzero : HaarCarrierEqv blocks
      (polyMul (polyVar (4*block+k))
        (angularDerivative (4*block+u) (4*block+v) c)) polyZero :=
    RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl _).mul hz).trans
        (RatPolyCoeffEqv.mul_zero_right _))
  exact (RatPolyCoeffEqv.haarCarrier h).trans
    ((HaarCarrierEqv.add
      (HaarCarrierEqv.mul_right c (delta_carrier hb hu hv hk p))
      hzero).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _)))

private theorem linear_derivative {blocks block u v : Nat} (hb : block < blocks)
    (hu : u < 4) (hv : v < 4) (p : PolyQuaternion)
    (hd : HasPolyQuaternionBlockDegree block 0 p)
    (hnormal : normalize (derivativeExpr u v) = normalize (planeExpr u v)) :
    HaarCarrierEqv blocks
      (angularDerivative (4*block+u) (4*block+v) (linearForm block p))
      (coeffEvalExpr (environment block p) (planeExpr u v)) := by
  have h0 := term_derivative hb hu hv (by decide : 0<4) p hd
  have h1 := term_derivative hb hu hv (by decide : 1<4) p hd
  have h2 := term_derivative hb hu hv (by decide : 2<4) p hd
  have h3 := term_derivative hb hu hv (by decide : 3<4) p hd
  let i := 4*block+u
  let j := 4*block+v
  let t0 := polyMul (polyVar (4*block+0))
    (coeffEvalExpr (environment block p) (signedExpr 0))
  let t1 := polyMul (polyVar (4*block+1))
    (coeffEvalExpr (environment block p) (signedExpr 1))
  let t2 := polyMul (polyVar (4*block+2))
    (coeffEvalExpr (environment block p) (signedExpr 2))
  let t3 := polyMul (polyVar (4*block+3))
    (coeffEvalExpr (environment block p) (signedExpr 3))
  have hsum : HaarCarrierEqv blocks
      (angularDerivative i j (polyAdd t0 (polyAdd t1 (polyAdd t2 t3))))
      (polyAdd (angularDerivative i j t0)
        (polyAdd (angularDerivative i j t1)
          (polyAdd (angularDerivative i j t2) (angularDerivative i j t3)))) := by
    apply RatPolyCoeffEqv.haarCarrier
    exact (angularDerivative_add i j t0 (polyAdd t1 (polyAdd t2 t3))).trans
      ((RatPolyCoeffEqv.refl _).add
        ((angularDerivative_add i j t1 (polyAdd t2 t3)).trans
          ((RatPolyCoeffEqv.refl _).add (angularDerivative_add i j t2 t3))))
  exact hsum.trans ((HaarCarrierEqv.add h0
    (HaarCarrierEqv.add h1 (HaarCarrierEqv.add h2 h3))).trans
    (RatPolyCoeffEqv.haarCarrier
      (coeffEvalExpr_eqv_of_normalize_eq _ _ hnormal (environment block p))))

private theorem fundamental_as_linear (block : Nat) (p : PolyQuaternion) :
    RatPolyCoeffEqv
      (characterPolynomial
        (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1)
      (polySmul 2 (linearForm block p)) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 4))
      (.neg (.add (.mul (.var 1) (.var 5))
        (.add (.mul (.var 2) (.var 6)) (.mul (.var 3) (.var 7))))))
    linearExpr (by decide) (environment block p)
  simpa only [characterPolynomial, linearForm, PolyQuaternion.mul,
    PolyQuaternion.coordinateVariable, coeffEvalExpr, environment] using h.smul 2

private theorem fundamental_derivative {blocks block u v : Nat} (hb : block < blocks)
    (hu : u < 4) (hv : v < 4) (p : PolyQuaternion)
    (hd : HasPolyQuaternionBlockDegree block 0 p)
    (hnormal : normalize (derivativeExpr u v) = normalize (planeExpr u v)) :
    let f := characterPolynomial
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1
    HaarCarrierEqv blocks (blockAngularDerivative block u v f)
      (coeffEvalExpr (environment block p) (rotatedExpr u v)) := by
  dsimp only
  let L := linearForm block p
  have hf := angularDerivative_congr (4*block+u) (4*block+v)
    (fundamental_as_linear block p)
  have hs := angularDerivative_smul (4*block+u) (4*block+v) 2 L
  have hp := linear_derivative hb hu hv p hd hnormal
  exact (RatPolyCoeffEqv.haarCarrier (hf.trans hs)).trans
    ((HaarCarrierEqv.smul 2 hp).trans
      (RatPolyCoeffEqv.haarCarrier
        (cap_mul_left 2 (coeffEvalExpr (environment block p) (planeExpr u v))).symm))

private theorem fundamental_six {blocks block : Nat} (hb : block < blocks)
    (p : PolyQuaternion) (hd : HasPolyQuaternionBlockDegree block 0 p) :
    let f := characterPolynomial
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare block f)
      (coeffEvalExpr (environment block p) sixSquareExpr) := by
  dsimp only
  have h01 := fundamental_derivative hb (by decide : 0<4) (by decide : 1<4)
    p hd (by decide)
  have h02 := fundamental_derivative hb (by decide : 0<4) (by decide : 2<4)
    p hd (by decide)
  have h03 := fundamental_derivative hb (by decide : 0<4) (by decide : 3<4)
    p hd (by decide)
  have h12 := fundamental_derivative hb (by decide : 1<4) (by decide : 2<4)
    p hd (by decide)
  have h13 := fundamental_derivative hb (by decide : 1<4) (by decide : 3<4)
    p hd (by decide)
  have h23 := fundamental_derivative hb (by decide : 2<4) (by decide : 3<4)
    p hd (by decide)
  unfold blockAngularSquare six sixSquareExpr
  exact HaarCarrierEqv.add (HaarCarrierEqv.mul h01 h01)
    (HaarCarrierEqv.add (HaarCarrierEqv.mul h02 h02)
      (HaarCarrierEqv.add (HaarCarrierEqv.mul h03 h03)
        (HaarCarrierEqv.add (HaarCarrierEqv.mul h12 h12)
          (HaarCarrierEqv.add (HaarCarrierEqv.mul h13 h13)
            (HaarCarrierEqv.mul h23 h23)))))

/-- Retained norm identity before applying either unit-radius law. -/
theorem linear_angularSquare_norm {blocks block : Nat} (hb : block < blocks)
    (p : PolyQuaternion) (hd : HasPolyQuaternionBlockDegree block 0 p) :
    let f := characterPolynomial
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare block f)
      (polyAdd (polySmul 4
        (polyMul (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
          (polyQuaternionNorm p))) (polyNeg (polyMul f f))) := by
  dsimp only
  let ρ := environment block p
  let f := characterPolynomial
    (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1
  have hpoly := coeffEvalExpr_eqv_of_normalize_eq sixSquareExpr normDifferenceExpr
    (by decide) ρ
  have hradius : RatPolyCoeffEqv (coeffEvalExpr ρ radiusExpr)
      (polyQuaternionNorm (PolyQuaternion.coordinateVariable block)) := by
    exact RatPolyCoeffEqv.refl _
  have htail : RatPolyCoeffEqv (coeffEvalExpr ρ tailNormExpr)
      (polyQuaternionNorm p) := by
    exact RatPolyCoeffEqv.refl _
  have hf : RatPolyCoeffEqv (coeffEvalExpr ρ (.mul (.const 2) linearExpr)) f :=
    (cap_mul_left 2 (linearForm block p)).trans
      (fundamental_as_linear block p).symm
  have hright : RatPolyCoeffEqv (coeffEvalExpr ρ normDifferenceExpr)
      (polyAdd (polySmul 4
        (polyMul (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
          (polyQuaternionNorm p))) (polyNeg (polyMul f f))) :=
    ((cap_mul_left 4 _).add (RatPolyCoeffEqv.refl _)).trans
      ((RatPolyCoeffEqv.smul 4 (hradius.mul htail)).add
        (RatPolyCoeffEqv.neg (hf.mul hf)))
  exact (fundamental_six hb p hd).trans
    ((RatPolyCoeffEqv.haarCarrier hpoly).trans
      (RatPolyCoeffEqv.haarCarrier hright))

/-- A block-independent Haar-unit quaternion tail gives the literal
fundamental angular square, with EVERY polynomial insertion retained. -/
theorem fundamental_angularSquare {blocks block : Nat} (hb : block < blocks)
    (p : PolyQuaternion) (hd : HasPolyQuaternionBlockDegree block 0 p)
    (hn : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    let f := characterPolynomial
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable block) p).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare block f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  dsimp only
  have hx := haarNorm_coordinate hb
  have hunit : HaarCarrierEqv blocks
      (polySmul 4
        (polyMul (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
          (polyQuaternionNorm p))) (cap 4) :=
    (HaarCarrierEqv.smul 4 (HaarCarrierEqv.mul hx hn)).trans
      (RatPolyCoeffEqv.haarCarrier
        (RatPolyCoeffEqv.smul 4 (RatPolyCoeffEqv.mul_one polyOne)))
  exact (linear_angularSquare_norm hb p hd).trans
    (HaarCarrierEqv.add hunit (HaarCarrierEqv.refl blocks _))

#print axioms linear_angularSquare_norm
#print axioms fundamental_angularSquare

end YMGap.Continuum.SU2QuaternionIndependentTailAngularSquare
