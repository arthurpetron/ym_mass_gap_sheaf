/-
# Thermodynamic limit of ordinary lower plaquette covariance

The existing thermodynamic moment theorem applies to every finite product in
the lower plaquette algebra.  Applying it to `e`, `f`, and `e*f` constructs
the limit of the ordinary connected covariance without invoking reflection.
The finite sequence is also pinned to the existing full-action face-set
covariance on every odd slab.

This is a fixed-nome thermodynamic limit for two fixed lower expressions.  It
does not identify a moving observable family with this sequence, construct a
continuum measure or Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

namespace YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance

set_option autoImplicit false
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay (expressionMean)
open YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The ordinary connected covariance of two fixed lower expressions on the
odd slab at `margin`. -/
def lowerCovarianceSequence {base : Nat}
    (e f : PlaquetteExpression base) (margin : Nat) : CReal :=
  CReal.sub (meanSequence (.mul e f) margin)
    (CReal.mul (meanSequence e margin) (meanSequence f margin))

/-- The thermodynamic ordinary connected covariance built from the three
already-constructed thermodynamic moments. -/
def lowerCovarianceLimit {base : Nat}
    (e f : PlaquetteExpression base) : CReal :=
  CReal.sub (meanLimit (.mul e f))
    (CReal.mul (meanLimit e) (meanLimit f))

def lowerCovarianceLimitCauchy {base : Nat}
    (e f : PlaquetteExpression base) :
    QCauchy (lowerCovarianceLimit e f).approx :=
  scalarAddCauchy _ _ (meanLimitCauchy (.mul e f))
    (scalarNegCauchy _
      (scalarMulCauchy _ _ (meanLimitCauchy e) (meanLimitCauchy f)))

/-- The ordinary lower covariance sequence converges because its mixed and
one-point moments converge. -/
theorem lowerCovariance_converges {base : Nat}
    (e f : PlaquetteExpression base) :
    ConvergesTo (lowerCovarianceSequence e f) (lowerCovarianceLimit e f) :=
  convergesTo_add (meanLimit_converges (.mul e f))
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        (meanLimit_converges e) (meanLimit_converges f)))

/-- Any other limit of the same ordinary covariance sequence is equivalent to
the constructed mixed-moment limit. -/
theorem lowerCovarianceLimit_unique {base : Nat}
    (e f : PlaquetteExpression base) (candidate : CReal)
    (hcandidate : ConvergesTo (lowerCovarianceSequence e f) candidate) :
    Equiv candidate (lowerCovarianceLimit e f) :=
  Equiv_of_limit_of_equal (fun _ => Equiv.refl _)
    hcandidate (lowerCovariance_converges e f)

/-- At every margin the sequence is the existing cutoff-removed covariance
under the full original action on the corresponding odd slab. -/
theorem lowerCovarianceSequence_faceSet {base : Nat}
    (e f : PlaquetteExpression base) (margin : Nat) :
    Equiv (lowerCovarianceSequence e f margin)
      (covariance nome nome_pos nome_lt_one (centralExtent (base + margin))
        (slabPhysicalFaceEdges (centralExtent (base + margin)))
        (fun _ hid => hid)
        (shiftedExpression margin e) (shiftedExpression margin f)) := by
  simpa only [lowerCovarianceSequence, meanSequence, expressionMean,
    BF4ExactSlabTwoProbeCovariance.covariance, shiftedExpression, evaluate] using
    (full_covariance_pin nome nome_pos nome_lt_one (base + margin)
      (shiftedExpression margin e) (shiftedExpression margin f)).symm

/-- The literal full-action face-set covariance therefore converges to the
same constructed ordinary lower covariance limit. -/
theorem fullLowerCovariance_converges {base : Nat}
    (e f : PlaquetteExpression base) :
    ConvergesTo
      (fun margin =>
        covariance nome nome_pos nome_lt_one (centralExtent (base + margin))
          (slabPhysicalFaceEdges (centralExtent (base + margin)))
          (fun _ hid => hid)
          (shiftedExpression margin e) (shiftedExpression margin f))
      (lowerCovarianceLimit e f) :=
  TrigAddCReal.convergesTo_congr_seq
    (fun margin => lowerCovarianceSequence_faceSet e f margin)
    (lowerCovariance_converges e f)

end YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.lowerCovarianceSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.lowerCovarianceLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.lowerCovarianceLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.lowerCovariance_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.lowerCovarianceLimit_unique
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.lowerCovarianceSequence_faceSet
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance.fullLowerCovariance_converges
