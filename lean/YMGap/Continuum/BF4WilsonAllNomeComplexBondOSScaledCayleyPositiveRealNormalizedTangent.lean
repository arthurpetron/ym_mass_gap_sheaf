/-
# The actual original positive-real difference quotient

The supplied positive time computes its reciprocal and its Cauchy modulus.
Scaling the already proved original graph error by that reciprocal cancels
the time square exactly.  The normalized residual is pinned to the ACTUAL
original difference quotient minus its SAME graph slope, with phase -2i.

This is fixed-nome/fixed-width numerical-time differentiation on supplied
original graph Points.  It is not physical clock/spacing calibration, a
negative-real derivative, Wick analytic continuation or a continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealTangent
import YMGap.Continuum.PositiveTimeReciprocalData
import YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
import YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff
import YMGap.Continuum.SymbolTypedParsevalClose

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.PositiveTimeReciprocalData
  (reciprocalReal reciprocalRealCauchy reciprocal_product)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealTangent
  (realOutputTerm realError realTangentRadius realTangentRadius_positive real_tangent_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency (imagScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (add_right_cancel neg_add add_neg)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_realSmul bondValue_smul bondValue_add bondValue_negate bondValue_sub)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (completedRealSmul rationalCauchy completedRealSmul_congr
    completedRealSmul_ofQ' completedRealSmul_one)
open YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
  (completedRealSmul_add completedRealSmul_mul completedInner_realSmul_diagonal)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "RH" => BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
  (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "R" => BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1
local notation "RS" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "RN" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Componentwise REAL scaling on the SAME physical completion, with explicit
scalar Cauchy data retained in both coordinates. -/
def realScalar (s : CReal) (cs : QCauchy s.approx) (x : H) : H :=
  (R s cs x.1,R s cs x.2)

private theorem bond_real_add (s : CReal) (cs : QCauchy s.approx) (x y : RH) :
    R s cs (RA x y) = RA (R s cs x) (R s cs y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_realSmul,bondValue_add]
  exact completedRealSmul_add hw0 hw1 s cs _ _

private theorem bond_real_rational (s : CReal) (cs : QCauchy s.approx)
    (q : Q') (x : RH) : R s cs (RS q x) = RS q (R s cs x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_realSmul,bondValue_smul]
  have hleft := completedRealSmul_mul hw0 hw1 s (ofQ' q) cs (rationalCauchy q)
    (bondValue hw0 hw1 x)
  have hright := completedRealSmul_mul hw0 hw1 (ofQ' q) s (rationalCauchy q) cs
    (bondValue hw0 hw1 x)
  rw [completedRealSmul_ofQ'] at hleft hright
  exact hleft.trans ((completedRealSmul_congr hw0 hw1 _ _ _ _
    (CRealAlg.cmul_comm s (ofQ' q)) _).trans hright.symm)

private theorem bond_real_neg (s : CReal) (cs : QCauchy s.approx) (x : RH) :
    R s cs (RN x) = RN (R s cs x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_realSmul,bondValue_negate]
  have h := congrArg (bondValue hw0 hw1) (bond_real_rational hw0 hw1 s cs (-1) x)
  simp only [bondValue_realSmul,bondValue_smul] at h
  exact h

private theorem realScalar_add (s : CReal) (cs : QCauchy s.approx) (x y : H) :
    realScalar hw0 hw1 s cs (A x y) =
      A (realScalar hw0 hw1 s cs x) (realScalar hw0 hw1 s cs y) :=
  Prod.ext (bond_real_add hw0 hw1 s cs x.1 y.1)
    (bond_real_add hw0 hw1 s cs x.2 y.2)

private theorem realScalar_imag (s : CReal) (cs : QCauchy s.approx)
    (q : Q') (x : H) :
    realScalar hw0 hw1 s cs (imagScale hw0 hw1 q x) =
      imagScale hw0 hw1 q (realScalar hw0 hw1 s cs x) :=
  Prod.ext ((bond_real_neg hw0 hw1 s cs _).trans
    (congrArg RN (bond_real_rational hw0 hw1 s cs q x.2)))
    (bond_real_rational hw0 hw1 s cs q x.1)

private theorem rc_mul_assoc (a b c : RC) :
    RCmul (RCmul a b) c = RCmul a (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun alpha beta gamma => Quotient.sound (CRealAlg.cmul_assoc alpha beta gamma)

private theorem rc_mul_add (a b c : RC) :
    RCmul a (RCadd b c) = RCadd (RCmul a b) (RCmul a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun alpha beta gamma => Quotient.sound (CReal.mul_add alpha beta gamma)

/-- The original physical squared norm scales by the exact scalar square. -/
theorem normSq_realScalar (s : CReal) (cs : QCauchy s.approx) (x : H) :
    N (realScalar hw0 hw1 s cs x) =
      RCmul (RCmul (Quotient.mk crealSetoid s) (Quotient.mk crealSetoid s)) (N x) := by
  change RCadd (bondCompletedInner hw0 hw1 (R s cs x.1) (R s cs x.1))
    (bondCompletedInner hw0 hw1 (R s cs x.2) (R s cs x.2)) =
    RCmul (RCmul (Quotient.mk crealSetoid s) (Quotient.mk crealSetoid s))
      (RCadd (bondCompletedInner hw0 hw1 x.1 x.1) (bondCompletedInner hw0 hw1 x.2 x.2))
  simp only [bondValue_inner,bondValue_realSmul,completedInner_realSmul_diagonal]
  rw [rc_mul_add,rc_mul_assoc,rc_mul_assoc]

private theorem reciprocal_bond_cancel (D : PositiveTime) (x : RH) :
    R (reciprocalReal D) (reciprocalRealCauchy D) (R D.real D.cauchy x) = x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_realSmul,bondValue_realSmul,completedRealSmul_mul]
  have h := Equiv.trans (CRealAlg.cmul_comm (reciprocalReal D) D.real)
    (reciprocal_product D)
  exact (completedRealSmul_congr hw0 hw1 _ cone
    (scalarMulCauchy (reciprocalReal D) D.real (reciprocalRealCauchy D) D.cauchy)
    (rationalCauchy 1) h _).trans (completedRealSmul_one hw0 hw1 _ _)

private theorem reciprocal_output_cancel (p : P) (D : PositiveTime) :
    realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
      (realOutputTerm hw0 hw1 p D) = output hw0 hw1 (ofPoint hw0 hw1 p) := by
  apply Prod.ext
  · exact reciprocal_bond_cancel hw0 hw1 D (output hw0 hw1 (ofPoint hw0 hw1 p)).1
  · exact reciprocal_bond_cancel hw0 hw1 D (output hw0 hw1 (ofPoint hw0 hw1 p)).2

private theorem cneg_cneg (x : H) : cneg hw0 hw1 (cneg hw0 hw1 x) = x := by
  apply add_right_cancel hw0 hw1 _ _ (cneg hw0 hw1 x)
  rw [neg_add,add_neg]

/-- Actual increment scaled by the supplied time's constructed reciprocal. -/
def differenceQuotient (p : P) (D : PositiveTime) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (diff hw0 hw1 (positiveAction hw0 hw1 D (input hw0 hw1 (ofPoint hw0 hw1 p)))
      (input hw0 hw1 (ofPoint hw0 hw1 p)))

/-- Normalized original error, not an auxiliary or surrogate quadratic form. -/
def normalizedResidual (p : P) (D : PositiveTime) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (realError hw0 hw1 p D)

/-- Exact -2i graph slope of the ACTUAL original difference quotient. -/
theorem quotient_error_pin (p : P) (D : PositiveTime) :
    diff hw0 hw1 (differenceQuotient hw0 hw1 p D)
      (cneg hw0 hw1 (imagScale hw0 hw1 2 (output hw0 hw1 (ofPoint hw0 hw1 p)))) =
      normalizedResidual hw0 hw1 p D := by
  unfold normalizedResidual realError
  rw [realScalar_add,realScalar_imag,reciprocal_output_cancel]
  unfold diff
  rw [cneg_cneg]
  rfl

private theorem reciprocal_square_cancel (D : PositiveTime) (e : Q') :
    RCmul (RCmul (Quotient.mk crealSetoid (reciprocalReal D))
      (Quotient.mk crealSetoid (reciprocalReal D)))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat e)) = rat e := by
  let r := reciprocalReal D
  have hpoly : RCmul (RCmul (Quotient.mk crealSetoid r) (Quotient.mk crealSetoid r))
      (RCmul (RCmul (Quotient.mk crealSetoid D.real) (Quotient.mk crealSetoid D.real)) (rat e)) =
      RCmul (RCmul (RCmul (Quotient.mk crealSetoid D.real) (Quotient.mk crealSetoid r))
        (RCmul (Quotient.mk crealSetoid D.real) (Quotient.mk crealSetoid r))) (rat e) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
        (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.var 2))
        (by decide) (fun | 0 => r.approx n | 1 => D.real.approx n | _ => e)))
  have hpin : RCmul (Quotient.mk crealSetoid D.real) (Quotient.mk crealSetoid r) = rat 1 :=
    Quotient.sound (reciprocal_product D)
  change RCmul (RCmul (Quotient.mk crealSetoid r) (Quotient.mk crealSetoid r))
    (RCmul (RCmul (Quotient.mk crealSetoid D.real) (Quotient.mk crealSetoid D.real)) (rat e)) = rat e
  rw [hpoly,hpin]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e (Q'.one_mul_eqv 1))
      (Q'.one_mul_eqv e)))

/-- Every sufficiently small supplied positive real time controls the actual
normalized graph error with the UNCHANGED source-computed radius. -/
theorem normalized_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (D : PositiveTime)
    (ht : RCle (realValue (timeValue D)) (rat (realTangentRadius hw0 hw1 p e he))) :
    RCle (N (normalizedResidual hw0 hw1 p D)) (rat e) := by
  have hsq := SymbolTypedParsevalClose.RCmul_self_nonneg
    (Quotient.mk crealSetoid (reciprocalReal D))
  have h := RCmul_mono_nonneg_left hsq (real_tangent_bound hw0 hw1 p e he D ht)
  rw [reciprocal_square_cancel] at h
  unfold normalizedResidual
  rw [normSq_realScalar]
  exact h

/-- A computed radius, its positivity, and the original right-real tangent
law as Type data; no modulus is selected from a quotient class. -/
def normalizedTangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat r) →
        RCle (N (diff hw0 hw1 (differenceQuotient hw0 hw1 p D)
          (cneg hw0 hw1 (imagScale hw0 hw1 2 (output hw0 hw1 (ofPoint hw0 hw1 p)))))) (rat e)) :=
  ⟨realTangentRadius hw0 hw1 p e he,realTangentRadius_positive hw0 hw1 p e he,
    fun D ht => by rw [quotient_error_pin]; exact normalized_bound hw0 hw1 p e he D ht⟩

#print axioms realScalar
#print axioms normSq_realScalar
#print axioms differenceQuotient
#print axioms normalizedResidual
#print axioms quotient_error_pin
#print axioms normalized_bound
#print axioms normalizedTangentCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
