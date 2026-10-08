/-
# Produced curvature of the literal finite heat in actual paired directions

The actual Horner chain rule and relative-scalar second jet identify the
paired derivatives BEFORE the curvature certificate is assembled. Radial
curvature plus the heat log-discriminant times the actual two-square
complement produces the original paired-direction certificate. There is
no division by 1-X^2, no inverse heat floor in the cost, and no supplied
curvature or coordinate-cone hypothesis.

Scope: the finite WEIGHTED Jacobi heat on original blocks zero and one,
separately in each of the three existing plus-paired directions. Full
frozen-direction tensorization, original unweighted-prefix transport and
interacting conditional/OS/scaling estimates remain separate joins.
-/

import YMGap.Continuum.QPolyHaarAngularChain
import YMGap.Continuum.SU2QuaternionPairedScalarSquare
import YMGap.Continuum.JacobiHeatLogConcavity
import YMGap.Continuum.JacobiHeatRadialSubstitutionPin

namespace YMGap.Continuum.SU2QuaternionPairedJacobiCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets
open YMGap.Continuum.SU2QuaternionPairedScalarSquare
open YMGap.Continuum.QPolyHaarAngularChain
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.JacobiShiftedPositiveCoefficients (heat)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.JacobiHeatRadialProducedBound (radialCap)
open YMGap.Continuum.JacobiProductRadialSignedTail (eighth)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem paired_shift (i : Fin 3) (X : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (polyAdd polyOne X)) (pairedDerivative i X) := by
  have h (a b : Nat) : RatPolyCoeffEqv
      (angularDerivative a b (polyAdd polyOne X)) (angularDerivative a b X) :=
    (angularDerivative_add a b polyOne X).trans
      (((angularDerivative_one a b).add (.refl _)).trans (RatPolyCoeffEqv.zero_add _))
  rcases direction_cases i with rfl | rfl | rfl
  · exact (h 0 1).add (h 2 3)
  · exact (h 0 2).add (RatPolyCoeffEqv.neg (h 1 3))
  · exact (h 0 3).add (h 1 2)

/-- Literal normalized finite heat on the SAME original relative scalar. -/
def pairedHeat (w : Q') (N : Nat) : RatPoly :=
  subst (polyAdd polyOne relativeScalar) (heat w N)

/-- Its actual first paired derivative, before Haar transport. -/
theorem pairedHeat_first_pin (w : Q') (N : Nat) (i : Fin 3) :
    RatPolyCoeffEqv (pairedDerivative i (pairedHeat w N))
      (polyMul (subst (polyAdd polyOne relativeScalar) (pderiv (heat w N)))
        (pairedDerivative i relativeScalar)) :=
  (paired_subst i _ _).trans ((RatPolyCoeffEqv.refl _).mul (paired_shift i relativeScalar))

/-- Actual second paired derivative, retaining the proved -X scalar jet
under arbitrary ORIGINAL insertions. No heat or positivity guard is used. -/
theorem pairedHeat_second_pin {blocks : Nat} (hb : 1 < blocks)
    (w : Q') (N : Nat) (i : Fin 3) :
    HaarCarrierEqv blocks (pairedDerivative i (pairedDerivative i (pairedHeat w N)))
      (polyAdd
        (polyMul (subst (polyAdd polyOne relativeScalar) (pderiv (pderiv (heat w N))))
          (polyMul (pairedDerivative i relativeScalar) (pairedDerivative i relativeScalar)))
        (polyNeg (polyMul relativeScalar
          (subst (polyAdd polyOne relativeScalar) (pderiv (heat w N)))))) := by
  let hx := subst (polyAdd polyOne relativeScalar) (pderiv (heat w N))
  have hs := paired_shift i relativeScalar
  have hsecond := (RatPolyCoeffEqv.haarCarrier (paired_congr i hs)).trans
    (relativeScalar_second_jet hb i)
  refine (RatPolyCoeffEqv.haarCarrier (paired_subst_second i _ _)).trans ?_
  refine (HaarCarrierEqv.add
    (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).mul (hs.mul hs)))
    (hsecond.mul_left hx)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 1) (.var 0)))
      (by decide) (fun | 0 => hx | _ => relativeScalar)))

/-- Actual paired curvature numerator, not an assigned formal jet. -/
def pairedCurvature (w C : Q') (N : Nat) (i : Fin 3) : RatPoly :=
  let h := pairedHeat w N
  let dh := pairedDerivative i h
  let ddh := pairedDerivative i dh
  polyAdd (polyMul (cap C) (polyMul h h))
    (polyAdd (polyMul h ddh) (polyNeg (polyMul dh dh)))

/-- Constructed local paired-direction curvature on the literal finite
heat. Positive slack is paid in C; the heat floor is not a budget multiplier.
The certificate still permits only certified positive/square insertions. -/
def paired_curvature_certificate {blocks : Nat} {w delta : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) (i : Fin 3) :
    Certificate blocks (pairedCurvature w (radialCap w N+delta) N i) := by
  let X := relativeScalar
  let h := pairedHeat w N
  let hx := subst (polyAdd polyOne X) (pderiv (heat w N))
  let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w N)))
  let d := pairedDerivative i X
  let C := radialCap w N+delta
  let R := JacobiHeatRadialHaarCertificate.radialCertificate hw0 hw1
    (relativeScalarSquare hb) N hN1 hsmall hdelta
  let R' := Certificate.ofCoeff
    (JacobiHeatRadialSubstitutionPin.radial_substitution_pin X w C N).symm R
  let B := JacobiHeatLogConcavity.heat_logConcavity_certificate hw0 hw1
    (QuaternionHaarSharpCharacterInterval.unitSquareInterval (relativeScalarSquare hb)) N
  let G := complementSquare hb i
  have hp := pairedHeat_first_pin w N i
  have hs := pairedHeat_second_pin hb w N i
  have hjet : HaarCarrierEqv blocks (pairedCurvature w C N i)
      (polyAdd (polyMul (cap C) (polyMul h h))
        (polyAdd
          (polyMul h (polyAdd (polyMul hxx (polyMul d d)) (polyNeg (polyMul X hx))))
          (polyNeg (polyMul (polyMul hx d) (polyMul hx d))))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _)
      (HaarCarrierEqv.add (hs.mul_left h)
        (HaarCarrierEqv.neg (RatPolyCoeffEqv.haarCarrier (hp.mul hp))))
  apply Certificate.transport hjet
  exact Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 1)
          (.add (.mul (.var 3) (.mul (.var 4) (.var 4)))
            (.neg (.mul (.var 5) (.var 2)))))
          (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 2) (.var 4))))))
      (.add
        (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.add
            (.mul (.add (.const 1) (.neg (.mul (.var 5) (.var 5))))
              (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 2)))))
            (.neg (.mul (.var 5) (.mul (.var 1) (.var 2))))))
        (.mul (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
          (.add (.add (.const 1) (.neg (.mul (.var 5) (.var 5))))
            (.neg (.mul (.var 4) (.var 4))))))
      (by decide) (fun | 0 => cap C | 1 => h | 2 => hx | 3 => hxx | 4 => d | _ => X))
    (R'.add (B.mul G))

end YMGap.Continuum.SU2QuaternionPairedJacobiCurvature

#print axioms YMGap.Continuum.SU2QuaternionPairedJacobiCurvature.pairedHeat
#print axioms YMGap.Continuum.SU2QuaternionPairedJacobiCurvature.pairedHeat_first_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedJacobiCurvature.pairedHeat_second_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedJacobiCurvature.pairedCurvature
#print axioms YMGap.Continuum.SU2QuaternionPairedJacobiCurvature.paired_curvature_certificate
