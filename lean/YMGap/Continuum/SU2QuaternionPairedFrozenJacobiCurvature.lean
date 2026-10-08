/-
# Produced full frozen-direction curvature of the literal finite heat

The coefficients may be arbitrary supported polynomials. All NINE actual
ordered mixed jets are computed before the coefficients are multiplied.
The existing scalar Hessian pin and the literal cross-product square
complement turn the radial and log-discriminant witnesses into the full
frozen quadratic-form certificate, with no dimension penalty in the cost.

Frozen means coefficients are NOT differentiated: this is not the square
of a variable-coefficient vector field. Scope remains weighted finite heat
on original blocks zero/one. Full original-prefix matrix transport,
arbitrary-block recoding, interacting conditional and OS/scaling/physical
joins remain separate obligations.
-/

import YMGap.Continuum.QPolyHaarFrozenChain
import YMGap.Continuum.SU2QuaternionPairedJacobiCurvature

namespace YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection (relativeScalar)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (frozenSecondJet frozenScalarSecondJet_pin)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeScalarSquare)
open YMGap.Continuum.SU2QuaternionPairedFrozenComplement
open YMGap.Continuum.QPolyHaarFrozenChain
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.JacobiShiftedPositiveCoefficients (heat)
open YMGap.Continuum.SU2QuaternionPairedJacobiCurvature (pairedHeat)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.JacobiHeatRadialProducedBound (radialCap nearFlatRadialCap)
open YMGap.Continuum.JacobiProductRadialSignedTail (eighth)

theorem frozenHeat_first_pin (w : Q') (N : Nat) (u : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (frozenFirstJet u (pairedHeat w N))
      (polyMul (subst (polyAdd polyOne relativeScalar) (pderiv (heat w N)))
        (frozenFirstJet u relativeScalar)) :=
  (frozen_subst_first u _ _).trans
    ((RatPolyCoeffEqv.refl _).mul (frozen_one_add_first u relativeScalar))

theorem frozenHeat_second_pin {blocks : Nat} (hb : 1 < blocks)
    (w : Q') (N : Nat) (u : Fin 3 → RatPoly) :
    HaarCarrierEqv blocks (frozenSecondJet u (pairedHeat w N))
      (polyAdd
        (polyMul (subst (polyAdd polyOne relativeScalar) (pderiv (pderiv (heat w N))))
          (polyMul (frozenFirstJet u relativeScalar) (frozenFirstJet u relativeScalar)))
        (polyNeg (polyMul (subst (polyAdd polyOne relativeScalar) (pderiv (heat w N)))
          (polyMul (threeSquare u) relativeScalar)))) := by
  have hfirst := frozen_one_add_first u relativeScalar
  have hsecond := (RatPolyCoeffEqv.haarCarrier (frozen_one_add_second u relativeScalar)).trans
    (frozenScalarSecondJet_pin hb u)
  refine (RatPolyCoeffEqv.haarCarrier (frozen_subst_second u _ _)).trans ?_
  refine (HaarCarrierEqv.add
    (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).mul (hfirst.mul hfirst)))
    (hsecond.mul_left _)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1))) (by decide) (fun
        | 0 => subst (polyAdd polyOne relativeScalar) (pderiv (heat w N))
        | _ => polyMul (threeSquare u) relativeScalar)))

def frozenCurvature (w C : Q') (N : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  let h := pairedHeat w N
  polyAdd (polyMul (cap C) (polyMul (threeSquare u) (polyMul h h)))
    (polyAdd (polyMul h (frozenSecondJet u h))
      (polyNeg (polyMul (frozenFirstJet u h) (frozenFirstJet u h))))

private def frozen_curvature_of_radial_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (C : Q') (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (radial : Certificate blocks (subst relativeScalar
      (JacobiHeatRadialHaarCertificate.radialPolynomial w N C))) :
    Certificate blocks (frozenCurvature w C N u) := by
  let X := relativeScalar
  let h := pairedHeat w N
  let hx := subst (polyAdd polyOne X) (pderiv (heat w N))
  let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w N)))
  let d := frozenFirstJet u X
  let R := threeSquare u
  let radial' := Certificate.ofCoeff
    (JacobiHeatRadialSubstitutionPin.radial_substitution_pin X w C N).symm radial
  let direction : Certificate blocks R :=
    (Certificate.square (u 0) (hu 0)).add
      ((Certificate.square (u 1) (hu 1)).add (Certificate.square (u 2) (hu 2)))
  let discriminant := JacobiHeatLogConcavity.heat_logConcavity_certificate hw0 hw1
    (QuaternionHaarSharpCharacterInterval.unitSquareInterval (relativeScalarSquare hb)) N
  let complement := frozen_complement_certificate hb u hu
  have hp := frozenHeat_first_pin w N u
  have hs := frozenHeat_second_pin hb w N u
  have hjet : HaarCarrierEqv blocks (frozenCurvature w C N u)
      (polyAdd (polyMul (cap C) (polyMul R (polyMul h h)))
        (polyAdd
          (polyMul h (polyAdd (polyMul hxx (polyMul d d))
            (polyNeg (polyMul hx (polyMul R X)))))
          (polyNeg (polyMul (polyMul hx d) (polyMul hx d))))) :=
    HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _)
      (HaarCarrierEqv.add (hs.mul_left h)
        (HaarCarrierEqv.neg (RatPolyCoeffEqv.haarCarrier (hp.mul hp))))
  apply Certificate.transport hjet
  exact Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 6) (.mul (.var 1) (.var 1))))
        (.add
          (.mul (.var 1) (.add (.mul (.var 3) (.mul (.var 4) (.var 4)))
            (.neg (.mul (.var 2) (.mul (.var 6) (.var 5))))))
          (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 2) (.var 4))))))
      (.add
        (.mul (.var 6)
          (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
            (.add
              (.mul (.add (.const 1) (.neg (.mul (.var 5) (.var 5))))
                (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 2)))))
              (.neg (.mul (.var 5) (.mul (.var 1) (.var 2)))))))
        (.mul
          (.add (.mul (.var 6) (.add (.const 1) (.neg (.mul (.var 5) (.var 5)))))
            (.neg (.mul (.var 4) (.var 4))))
          (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 1) (.var 3))))))
      (by decide) (fun
        | 0 => cap C | 1 => h | 2 => hx | 3 => hxx
        | 4 => d | 5 => X | _ => R))
    ((direction.mul radial').add (complement.mul discriminant))

/-- Full frozen quadratic form at the SAME radial cost. Neither unit
direction, strict nonzero direction nor supplied curvature is required. -/
def frozen_curvature_certificate {blocks : Nat} {w delta : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (frozenCurvature w (radialCap w N+delta) N u) :=
  frozen_curvature_of_radial_certificate hb hw0 hw1 N (radialCap w N+delta) u hu
    (JacobiHeatRadialHaarCertificate.radialCertificate hw0 hw1
      (relativeScalarSquare hb) N hN1 hsmall hdelta)

/-- Sharper full frozen certificate from the PRODUCED whole-interval radial
certificate, retaining the actual finite-tail allowance and the same guards.
No interacting marginal curvature or source-weighted payment is asserted. -/
def frozen_curvature_nearFlat_certificate {blocks : Nat} {w delta : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN1 : 1 ≤ N) (hsmall : HKPos.geoAmp w N ≤ eighth)
    (hdelta : (0 : Q') < delta) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (frozenCurvature w (nearFlatRadialCap w N+delta) N u) :=
  frozen_curvature_of_radial_certificate hb hw0 hw1 N (nearFlatRadialCap w N+delta) u hu
    (JacobiHeatRadialHaarCertificate.nearFlatRadialCertificate hw0 hw1
      (relativeScalarSquare hb) N hN1 hsmall hdelta)

end YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature

#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature.frozenHeat_first_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature.frozenHeat_second_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature.frozen_curvature_certificate
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature.frozen_curvature_of_radial_certificate
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature.frozen_curvature_nearFlat_certificate
