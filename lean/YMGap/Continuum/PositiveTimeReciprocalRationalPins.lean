/-
# Rational pins for the constructed positive-time reciprocal

For a supplied constant rational time, the ORIGINAL positive-time reciprocal
stream is constant at the literal rational reciprocal.  The resulting CReal
equivalence transports the already constructed reciprocal real scalar to
ordinary rational scaling on the SAME physical bond completion.  These are
numerical and fixed-carrier pins, not physical clock calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.PositiveTimeReciprocalRationalPins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData
  (rational rational_sample)
open YMGap.Continuum.PositiveTimeReciprocalData
  (reciprocalTerm reciprocalReal reciprocalRealCauchy reciprocalReal_approx)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
  (realScalar)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (realScale)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_realSmul bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_congr completedRealSmul_ofQ')

/-- On the actual constant rational time, every raw reciprocal sample is the
same literal rational reciprocal. -/
theorem reciprocalTerm_rational (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    reciprocalTerm (rational t ht) n = Q'.recipPos t ht := by
  rfl

/-- Regularization does not change the constant reciprocal stream. -/
theorem reciprocal_approx_rational (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    (reciprocalReal (rational t ht)).approx n = Q'.recipPos t ht := by
  rw [reciprocalReal_approx]
  exact reciprocalTerm_rational t ht _

/-- The computed positive-time reciprocal is the ordinary rational
reciprocal when the supplied time itself is rational. -/
theorem reciprocal_rational (t : Q') (ht : (0 : Q') < t) :
    CReal.Equiv (reciprocalReal (rational t ht))
      (CReal.ofQ' (Q'.recipPos t ht)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  rw [reciprocal_approx_rational,CReal.ofQ'_approx]
  exact Q'.eqv_refl _

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1
local notation "S" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1

private theorem bond_reciprocal_rational (t : Q') (ht : (0 : Q') < t)
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    R (reciprocalReal (rational t ht))
        (reciprocalRealCauchy (rational t ht)) x =
      S (Q'.recipPos t ht) x := by
  apply bondValue_injective hw0 hw1
  calc
    bondValue hw0 hw1
        (R (reciprocalReal (rational t ht))
          (reciprocalRealCauchy (rational t ht)) x) =
        BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
          (reciprocalReal (rational t ht))
          (reciprocalRealCauchy (rational t ht)) (bondValue hw0 hw1 x) :=
      bondValue_realSmul hw0 hw1 _ _ x
    _ = BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
          (CReal.ofQ' (Q'.recipPos t ht))
          (rationalCauchy (Q'.recipPos t ht)) (bondValue hw0 hw1 x) :=
      completedRealSmul_congr hw0 hw1 _ _ _ _ (reciprocal_rational t ht) _
    _ = BF4WilsonAllNomeLinear.completedSmul hw0 hw1
          (Q'.recipPos t ht) (bondValue hw0 hw1 x) :=
      completedRealSmul_ofQ' hw0 hw1 _ _ _
    _ = bondValue hw0 hw1 (S (Q'.recipPos t ht) x) :=
      (bondValue_smul hw0 hw1 _ x).symm

/-- The SAME constructed reciprocal scalar used by the real tangent becomes
the existing rational scaling of both original physical coordinates. -/
theorem realScalar_reciprocal_rational (t : Q') (ht : (0 : Q') < t) (x : H) :
    realScalar hw0 hw1 (reciprocalReal (rational t ht))
        (reciprocalRealCauchy (rational t ht)) x =
      realScale hw0 hw1 (Q'.recipPos t ht) x :=
  Prod.ext
    (bond_reciprocal_rational hw0 hw1 t ht x.1)
    (bond_reciprocal_rational hw0 hw1 t ht x.2)

#print axioms reciprocalTerm_rational
#print axioms reciprocal_approx_rational
#print axioms reciprocal_rational
#print axioms realScalar_reciprocal_rational

end YMGap.Continuum.PositiveTimeReciprocalRationalPins
