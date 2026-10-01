/-
# Scalar compatibility of the original signed physical Cayley action

The constructed reciprocal acts componentwise on the SAME completed complex
bond carrier.  Its identification with the existing full complex scalar
action gives commutation with every signed Cayley time.  The rational
imaginary rotation, additive inverse, and difference are recorded for the
negative-real tangent consumer.  No time derivative or analytic estimate is
assumed here.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
  (realScalar)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_smul signedAction_add_state)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale imagScale_smul cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_sub bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedZero_add completedAdd_zero completedNeg_add completedSmul_zero)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (completedSub_zero)
open YMGap.Continuum.SignedRealTimeData
  (SignedTimeValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "G" => signedAction hw0 hw1
local notation "Neg" => cneg hw0 hw1
local notation "I" => imagScale hw0 hw1

/-- The original complex scalar with zero imaginary part is literally the
componentwise real scalar used by the normalized positive-real tangent.
The supplied Cauchy witness remains present in both components. -/
theorem fullSmul_realScalar (s : CReal) (cs : QCauchy s.approx) (x : H) :
    S s (ofQ' 0) cs (rationalCauchy 0) x = realScalar hw0 hw1 s cs x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [BF4WilsonAllNomeComplexBondOSTime.smul,realScalar,
      bondValue_sub,bondValue_realSmul,completedRealSmul_ofQ',completedSmul_zero]
    exact completedSub_zero hw0 hw1 _
  · apply bondValue_injective hw0 hw1
    simp only [BF4WilsonAllNomeComplexBondOSTime.smul,realScalar,
      bondValue_add,bondValue_realSmul,completedRealSmul_ofQ',completedSmul_zero]
    exact completedZero_add hw0 hw1 _

/-- Every actual signed Cayley action commutes with the SAME constructive
componentwise real scalar, including the time's computed reciprocal. -/
theorem signedAction_realScalar (t : SignedTimeValue)
    (s : CReal) (cs : QCauchy s.approx) (x : H) :
    G t (realScalar hw0 hw1 s cs x) =
      realScalar hw0 hw1 s cs (G t x) := by
  calc
    G t (realScalar hw0 hw1 s cs x) =
        G t (S s (ofQ' 0) cs (rationalCauchy 0) x) :=
      congrArg (G t) (fullSmul_realScalar hw0 hw1 s cs x).symm
    _ = S s (ofQ' 0) cs (rationalCauchy 0) (G t x) :=
      signedAction_smul hw0 hw1 t s (ofQ' 0) cs (rationalCauchy 0) x
    _ = realScalar hw0 hw1 s cs (G t x) :=
      fullSmul_realScalar hw0 hw1 s cs (G t x)

/-- Rational imaginary rotation commutes with the actual signed action. -/
theorem signedAction_imagScale (t : SignedTimeValue) (q : Q') (x : H) :
    G t (I q x) = I q (G t x) := by
  calc
    G t (I q x) =
        G t (S (ofQ' 0) (ofQ' q) (rationalCauchy 0) (rationalCauchy q) x) :=
      congrArg (G t) (imagScale_smul hw0 hw1 q x)
    _ = S (ofQ' 0) (ofQ' q) (rationalCauchy 0) (rationalCauchy q) (G t x) :=
      signedAction_smul hw0 hw1 t (ofQ' 0) (ofQ' q)
        (rationalCauchy 0) (rationalCauchy q) x
    _ = I q (G t x) := (imagScale_smul hw0 hw1 q (G t x)).symm

private theorem cneg_fullSmul (x : H) :
    Neg x = S (ofQ' (-1)) (ofQ' 0)
      (rationalCauchy (-1)) (rationalCauchy 0) x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg,
      BF4WilsonAllNomeComplexBondOSTime.smul,bondValue_negate,bondValue_sub,
      bondValue_realSmul,completedRealSmul_ofQ',completedSmul_zero]
    change BF4WilsonAllNomeLinear.completedNeg hw0 hw1 (bondValue hw0 hw1 x.1) =
      BF4WilsonAllNomeLinear.completedAdd hw0 hw1
        (BF4WilsonAllNomeLinear.completedNeg hw0 hw1 (bondValue hw0 hw1 x.1))
        (BF4WilsonAllNomeLinear.completedNeg hw0 hw1
          (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width))
    have hz : BF4WilsonAllNomeLinear.completedNeg hw0 hw1
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) =
        BF4WilsonAllNomeLinear.completedZero hw0 hw1 width := by
      have h := completedNeg_add hw0 hw1
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width)
      rw [completedAdd_zero] at h
      exact h
    rw [hz,completedAdd_zero]
  · apply bondValue_injective hw0 hw1
    simp only [BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.cneg,
      BF4WilsonAllNomeComplexBondOSTime.smul,bondValue_negate,bondValue_add,
      bondValue_realSmul,completedRealSmul_ofQ',completedSmul_zero]
    exact (completedZero_add hw0 hw1 _).symm

/-- The signed action respects the actual componentwise additive inverse. -/
theorem signedAction_cneg (t : SignedTimeValue) (x : H) :
    G t (Neg x) = Neg (G t x) := by
  rw [cneg_fullSmul,cneg_fullSmul]
  exact signedAction_smul hw0 hw1 t (ofQ' (-1)) (ofQ' 0)
    (rationalCauchy (-1)) (rationalCauchy 0) x

/-- The signed action transports the ORIGINAL physical difference. -/
theorem signedAction_diff (t : SignedTimeValue) (x y : H) :
    G t (diff hw0 hw1 x y) =
      diff hw0 hw1 (G t x) (G t y) := by
  unfold diff
  rw [signedAction_add_state,signedAction_cneg]

#print axioms fullSmul_realScalar
#print axioms signedAction_realScalar
#print axioms signedAction_imagScale
#print axioms signedAction_cneg
#print axioms signedAction_diff

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedScalarCommutation
