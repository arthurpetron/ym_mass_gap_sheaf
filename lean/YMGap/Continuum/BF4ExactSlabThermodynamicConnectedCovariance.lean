/-
# The SAME original connected reflected covariance in thermodynamic volume

The limit subtracts the product of the two already-constructed lower means
from the original thermodynamic reflected form. It is proved to be the
limit of the actual finite-slab connected covariances, hence also of the
already-proved centered completed pairings at each volume.

The returned real has computed representative Cauchy data. Symmetry,
positive diagonal and sharp Cauchy--Schwarz pass to the limit. This is not
a temporal-decay estimate or an identification with a thermodynamic
physical transfer operator, which has not been constructed here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm

namespace YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit (meanLimit meanLimitCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

def covarianceSequence {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) : CReal :=
  BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance nome nome_pos nome_lt_one
    (enlarge margin e) (enlarge margin f)

def covarianceLimit {base : Nat} (e f : PlaquetteExpression base) : CReal :=
  CReal.sub (formLimit e f) (CReal.mul (meanLimit e) (meanLimit f))

def covarianceLimitCauchy {base : Nat} (e f : PlaquetteExpression base) :
    QCauchy (covarianceLimit e f).approx :=
  scalarAddCauchy _ _ (formLimitCauchy e f)
    (scalarNegCauchy _ (scalarMulCauchy _ _ (meanLimitCauchy e) (meanLimitCauchy f)))

theorem covarianceSequence_pin {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) :
    Equiv (covarianceSequence e f margin)
      (CReal.sub (formSequence e f margin)
        (CReal.mul
          (BF4ExactSlabPlaquetteConnectedCovariance.mean nome nome_pos nome_lt_one (enlarge margin e))
          (BF4ExactSlabPlaquetteConnectedCovariance.mean nome nome_pos nome_lt_one (enlarge margin f)))) :=
  Pivot2.add_congr
    (BF4ExactSlabPlaquetteReflectedForm.form_reflected nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f)).symm (Equiv.refl _)

theorem covariance_converges {base : Nat} (e f : PlaquetteExpression base) :
    ConvergesTo (covarianceSequence e f) (covarianceLimit e f) :=
  TrigAddCReal.convergesTo_congr_seq (fun margin => (covarianceSequence_pin e f margin).symm)
    (convergesTo_add (form_converges e f)
      (TrigAddCReal.convergesTo_neg
        (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
          (lowerMeanSequence_converges e) (lowerMeanSequence_converges f))))

/-- At every volume, this is the SAME previously constructed centered pairing. -/
theorem covarianceSequence_centeredPairing {base : Nat} (e f : PlaquetteExpression base) (margin : Nat) :
    BF4ExactSlabPlaquetteCompletedInner.completedInner nome nome_pos nome_lt_one
      (BF4ExactSlabPlaquetteCenteredDensity.centeredExpression nome nome_pos nome_lt_one (enlarge margin e)).val
      (BF4ExactSlabPlaquetteCenteredDensity.centeredExpression nome nome_pos nome_lt_one (enlarge margin f)).val =
      Quotient.mk crealSetoid (covarianceSequence e f margin) :=
  BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_pairing nome nome_pos nome_lt_one
    (enlarge margin e) (enlarge margin f)

theorem covariance_symm {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (covarianceLimit e f) (covarianceLimit f e) :=
  Equiv_of_limit_of_equal
    (fun margin => BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_symm nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f)) (covariance_converges e f) (covariance_converges f e)

theorem covariance_nonnegative {base : Nat} (e : PlaquetteExpression base) :
    leEv czero (covarianceLimit e e) :=
  leEv_of_convergesTo_le (convergesTo_const _) (covariance_converges e e)
    (fun margin => BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_nonnegative nome nome_pos nome_lt_one
      (enlarge margin e))

theorem covariance_cauchySchwarz {base : Nat} (e f : PlaquetteExpression base) :
    leEv (CReal.mul (covarianceLimit e f) (covarianceLimit e f))
      (CReal.mul (covarianceLimit e e) (covarianceLimit f f)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (covariance_converges e f) (covariance_converges e f))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (covariance_converges e e) (covariance_converges f f))
    (fun margin => BF4ExactSlabPlaquetteConnectedCovariance.connectedCovariance_cauchySchwarz nome nome_pos nome_lt_one
      (enlarge margin e) (enlarge margin f))

end YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covarianceSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covarianceLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covarianceLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covarianceSequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covariance_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covarianceSequence_centeredPairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covariance_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covariance_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance.covariance_cauchySchwarz
