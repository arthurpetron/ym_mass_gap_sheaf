/-
# Reciprocal of a supplied positive real time

The existing positive-time datum supplies both a rational floor and a
Type-level Cauchy modulus.  Shifting to its certified positive samples gives
an actual reciprocal stream, an explicit modulus for its CReal representative,
and a product pin to the SAME supplied time.  This is numerical time data for
normalizing the original fixed-carrier tangent estimate, not a physical clock
or a mass/spacing calibration.
-/

import YMGap.Continuum.PositiveRealDyadicTimeData
import YMGap.Continuum.PositiveRationalCauchyReciprocal
import YMGap.Continuum.BoundedRationalCauchyProduct
import YMGap.Constructive.CRealLimitClose
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.PositiveTimeReciprocalData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime sample sample_lower)

/-- The actual positive samples retain the supplied modulus, not a modulus
extracted from the legacy propositional CReal field. -/
def sampleCauchy (D : PositiveTime) : QCauchy (sample D) where
  M := D.cauchy.M
  bound := by
    intro epsilon he p q hp hq
    exact D.cauchy.bound epsilon he (D.start+p) (D.start+q)
      (Nat.le_trans hp (Nat.le_add_left _ _))
      (Nat.le_trans hq (Nat.le_add_left _ _))

theorem sample_floor (D : PositiveTime) (n : Nat) : D.floor ≤ sample D n :=
  sample_lower D n

/-- The shifted stream converges to the ORIGINAL supplied time, not a newly
selected real.  The proof uses only the already supplied Cauchy modulus. -/
theorem sample_converges (D : PositiveTime) :
    ConvergesTo (fun n => ofQ' (sample D n)) D.real := by
  intro epsilon he
  refine ⟨D.cauchy.M epsilon,fun N hN => ⟨D.cauchy.M epsilon,fun n hn => ?_⟩⟩
  exact D.cauchy.bound epsilon he (D.start+N) n
    (Nat.le_trans hN (Nat.le_add_left _ _)) hn

/-- The regularized CReal limit of the same shifted positive samples. -/
def sampleLimit (D : PositiveTime) : CReal :=
  ofQ'CauchySeq (sample D) (sampleCauchy D)

theorem sampleLimit_equiv (D : PositiveTime) : Equiv (sampleLimit D) D.real := by
  apply Equiv_of_ofQ'_limit_close
    (convergesTo_ofQ'CauchySeq (sample D) (sampleCauchy D))
    (sample_converges D)
  intro epsilon he
  exact ⟨0,fun n _ =>
    ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he),
      Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩⟩

/-- Raw positive rational reciprocal with its original sample index. -/
def reciprocalTerm (D : PositiveTime) (n : Nat) : Q' :=
  PositiveRationalCauchyReciprocal.term D.floor D.floor_positive
    (sample_floor D) n

/-- Computed modulus for the raw reciprocal stream. -/
def reciprocalStreamCauchy (D : PositiveTime) : QCauchy (reciprocalTerm D) :=
  PositiveRationalCauchyReciprocal.reciprocalCauchy
    (sampleCauchy D) D.floor D.floor_positive (sample_floor D)

/-- The actual reciprocal of the supplied positive real time. -/
def reciprocalReal (D : PositiveTime) : CReal :=
  PositiveRationalCauchyReciprocal.value
    (sampleCauchy D) D.floor D.floor_positive (sample_floor D)

/-- Type-level modulus for the approximants of the reciprocal CReal itself. -/
def reciprocalRealCauchy (D : PositiveTime) : QCauchy (reciprocalReal D).approx :=
  BoundedRationalCauchyProduct.representativeCauchy
    (reciprocalTerm D) (reciprocalStreamCauchy D)

theorem reciprocalReal_approx (D : PositiveTime) (n : Nat) :
    (reciprocalReal D).approx n =
      reciprocalTerm D (QMhat (reciprocalTerm D) (reciprocalStreamCauchy D) n) := rfl

/-- This reciprocal cancels the SAME original `D.real`; the shifted sample
limit is eliminated by its proved pin before the product is used. -/
theorem reciprocal_product (D : PositiveTime) :
    Equiv (CReal.mul D.real (reciprocalReal D)) CReal.cone := by
  have hshift : Equiv D.real (sampleLimit D) :=
    Equiv.symm (sampleLimit_equiv D)
  exact Equiv.trans (CReal.mul_congr_left hshift)
    (PositiveRationalCauchyReciprocal.mul_value
      (sampleCauchy D) D.floor D.floor_positive (sample_floor D))

#print axioms sampleCauchy
#print axioms sample_floor
#print axioms sample_converges
#print axioms sampleLimit
#print axioms sampleLimit_equiv
#print axioms reciprocalTerm
#print axioms reciprocalStreamCauchy
#print axioms reciprocalReal
#print axioms reciprocalRealCauchy
#print axioms reciprocalReal_approx
#print axioms reciprocal_product

end YMGap.Continuum.PositiveTimeReciprocalData
