/-
# Supplied-real tangents and the SAME original generator-domain converse

Both signed difference quotients use the constructed reciprocal of the SAME
supplied positive time. Original represented graph Points compute one radius
for both directions. Constant rational times recover the actual rational
quotient exactly, so the existing resolvent converse constructs the ORIGINAL
domain with both input and output pins.

This is fixed-nome/fixed-width numerical-time differentiation. No sign of an
arbitrary real is decided; no representative or modulus is selected from a
quotient domain. The forward producer takes a supplied original Point, not an
arbitrary domain class. Physical clock, changing-spacing control and the
continuum Clay problem remain open.
-/

import YMGap.Continuum.PositiveTimeReciprocalRationalPins
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeRealTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGeneratorConverse

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRealTangentData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime rational)
open YMGap.Continuum.PositiveTimeReciprocalData (reciprocalReal reciprocalRealCauchy)
open YMGap.Continuum.PositiveTimeReciprocalRationalPins
  (realScalar_reciprocal_rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (positiveAction positiveAction_rational)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime (signedAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealNormalizedTangent
  (realScalar differenceQuotient normalizedResidual quotient_error_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeRealTangent
  (negativeClock negativeDifferenceQuotient negativeResidual twoSidedTangentCertificate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData
  (slope rightQuotient RightTangent)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (bondValue_smul bondValue_negate)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws (completedSmul_mul completedSmul_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "Dist" => distance hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "S" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The actual positive-real quotient on an arbitrary ORIGINAL physical input. -/
def realRightQuotient (D : PositiveTime) (u : H) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (diff hw0 hw1 (positiveAction hw0 hw1 D u) u)

/-- Reversing the numerator implements division by SIGNED time -D.real. -/
def realLeftQuotient (D : PositiveTime) (u : H) : H :=
  realScalar hw0 hw1 (reciprocalReal D) (reciprocalRealCauchy D)
    (diff hw0 hw1 u (signedAction hw0 hw1 (negativeClock D) u))

/-- Constant rational time recovers the SAME rational quotient, not an
approximation or a surrogate action. -/
theorem realRightQuotient_rational (t : Q') (ht : (0 : Q') < t) (u : H) :
    realRightQuotient hw0 hw1 (rational t ht) u = rightQuotient hw0 hw1 t ht u := by
  unfold realRightQuotient
  rw [realScalar_reciprocal_rational,positiveAction_rational]
  rfl

/-- The rational and real tangent statements use the identical -2i phase. -/
theorem slope_pin (v : H) : slope hw0 hw1 v = cneg hw0 hw1 (imagScale hw0 hw1 2 v) := by
  apply Prod.ext
  · change Neg (S (-2) v.2) = Neg (Neg (S 2 v.2))
    apply bondValue_injective hw0 hw1
    simp only [bondValue_negate,bondValue_smul]
    change completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 (-2) (bondValue hw0 hw1 v.2)) =
      completedSmul hw0 hw1 (-1)
        (completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 2 (bondValue hw0 hw1 v.2)))
    rw [completedSmul_mul,completedSmul_mul,completedSmul_mul]
    exact completedSmul_congr hw0 hw1
      (by decide : Q'.eqv (-1*(-2)) ((-1*(-1))*2)) _
  · change S (-2) v.1 = Neg (S 2 v.1)
    apply bondValue_injective hw0 hw1
    simp only [bondValue_negate,bondValue_smul]
    change completedSmul hw0 hw1 (-2) (bondValue hw0 hw1 v.1) =
      completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 2 (bondValue hw0 hw1 v.1))
    rw [completedSmul_mul]
    exact completedSmul_congr hw0 hw1 (by decide : Q'.eqv (-2) (-1*2)) _

/-- Witnessed two-sided differentiability on supplied positive times. This
defines the actual quantitative tangent property, not a new analytic YM
hypothesis: the represented original graph producer below inhabits it. -/
structure RealTangent (u v : H) : Type where
  radius : (e : Q') → (0 : Q') < e → Q'
  positive : ∀ e he, (0 : Q') < radius e he
  bound : ∀ e he (D : PositiveTime),
    RCle (realValue (timeValue D)) (rat (radius e he)) →
      (RCle (Dist (realRightQuotient hw0 hw1 D u) (slope hw0 hw1 v)) (rat e)) ×'
      (RCle (Dist (realLeftQuotient hw0 hw1 D u) (slope hw0 hw1 v)) (rat e))

/-- The supplied ORIGINAL graph Point computes one radius and BOTH actual
signed quotient laws. No data are chosen from its domain quotient. -/
def ofPointRealTangent (p : P) :
    RealTangent hw0 hw1 (In (ofPoint hw0 hw1 p)) (Out (ofPoint hw0 hw1 p)) where
  radius := fun e he => (twoSidedTangentCertificate hw0 hw1 p e he).1
  positive := fun e he => (twoSidedTangentCertificate hw0 hw1 p e he).2.1
  bound := by
    intro e he D ht
    have hb := (twoSidedTangentCertificate hw0 hw1 p e he).2.2 D ht
    constructor
    · rw [distance_eq_norm_difference,slope_pin]
      change RCle (N (diff hw0 hw1 (differenceQuotient hw0 hw1 p D)
        (cneg hw0 hw1 (imagScale hw0 hw1 2 (Out (ofPoint hw0 hw1 p)))))) (rat e)
      rw [quotient_error_pin]
      exact hb.1
    · rw [distance_eq_norm_difference,slope_pin]
      exact hb.2

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

/-- Restriction to rational increments retains the entire supplied radius.
The exact quotient pin, rather than a density argument, supplies the join. -/
def toRightTangent (u v : H) (T : RealTangent hw0 hw1 u v) :
    RightTangent hw0 hw1 u v where
  radius := T.radius
  positive := T.positive
  bound := by
    intro e he t ht htr
    have h := (T.bound e he (rational t ht) (rat_le htr)).1
    rwa [realRightQuotient_rational] at h

/-- Uniqueness concerns the SAME physical graph output and exact phase. -/
theorem RealTangent.unique {u v z : H}
    (T : RealTangent hw0 hw1 u v) (U : RealTangent hw0 hw1 u z) : v = z :=
  RightTangent.unique hw0 hw1 (toRightTangent hw0 hw1 u v T)
    (toRightTangent hw0 hw1 u z U)

/-- A supplied actual real tangent computes the ORIGINAL maximal-domain
witness, with BOTH original input and output pins. The witness is the existing
unit-resolvent reconstruction; no new domain or estimate is assumed. -/
def ofRealTangent (u v : H) (T : RealTangent hw0 hw1 u v) :
    Σ' d : Domain hw0 hw1 (width := width), (In d = u) ×' (Out d = v) :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyGeneratorConverse.ofRightTangent
    hw0 hw1 u v (toRightTangent hw0 hw1 u v T)

#print axioms realRightQuotient
#print axioms realLeftQuotient
#print axioms realRightQuotient_rational
#print axioms slope_pin
#print axioms RealTangent
#print axioms ofPointRealTangent
#print axioms toRightTangent
#print axioms RealTangent.unique
#print axioms ofRealTangent

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRealTangentData
