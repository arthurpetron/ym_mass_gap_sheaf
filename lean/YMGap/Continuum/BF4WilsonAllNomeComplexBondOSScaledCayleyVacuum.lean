/-
# The constructed Cayley action fixes the original Wilson vacuum

The unit source supplies an actual sector derivative-graph point.  Its input
is the original complex physical vacuum and its output is zero.  The finite
Cayley shifts, represented dyadic products, positive-real limits, and signed
action therefore fix that SAME vacuum.  This is fixed-nome/fixed-width
stationarity, not a locality, cyclicity, physical-clock, or continuum claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
import YMGap.Continuum.BF4WilsonAllNomeUnitProjection
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows value value_injective value_zero ofRows rowsOfState
    ofRows_rowsOfState distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain Point input output ofPoint value_input_ofPoint value_output_ofPoint vacuum value_vacuum)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows productLimit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (positiveAction positiveAction_ofRows timeRows_pin timeSequence timeLimitRows sample_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse
  (inverseRealAction positiveRealAction_inverse_left)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_ofPair pairAction)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection (unitCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "Ω" => vacuum hw0 hw1 (width := width)
local notation "Z" => BF4WilsonAllNomeComplexBondOSCompletion.zero hw0 hw1 (width := width)
local notation "RZ" => BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The original unit Cauchy source, with its original time-range witness;
the imaginary graph coordinate is the already constructed zero point. -/
def vacuumPoint : Point hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 (unitCauchy hw0 hw1),
   BF4WilsonAllNomeComplexSectorDerivative.zeroDomain hw0 hw1)

theorem vacuumPoint_input :
    input hw0 hw1 (ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))) = Ω := by
  apply value_injective hw0 hw1
  rw [value_input_ofPoint,value_vacuum]
  change (BF4WilsonAllNomeCompletedTime.completedTime hw0 hw1 1
      (BF4WilsonAllNomeCompletedInner.unitState hw0 hw1 width),
      BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) =
    (BF4WilsonAllNomeCompletedInner.unitState hw0 hw1 width,
      BF4WilsonAllNomeLinear.completedZero hw0 hw1 width)
  exact Prod.ext (BF4WilsonAllNomeCompletedTime.completedUnit_fixed hw0 hw1 1) rfl

theorem vacuumPoint_output :
    output hw0 hw1 (ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))) = Z := by
  apply value_injective hw0 hw1
  rw [value_output_ofPoint,value_zero]
  change (BF4WilsonAllNomeDyadicDerivative.derivativeAction hw0 hw1
      (BF4WilsonAllNomeCompletedInner.unitState hw0 hw1 width),
      BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) =
    (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width,
      BF4WilsonAllNomeLinear.completedZero hw0 hw1 width)
  exact Prod.ext (BF4WilsonAllNomeDerivativeCore.derivativeAction_unit_zero hw0 hw1) rfl

private theorem realScale_zero (t : Q') :
    BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t RZ = RZ := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSLinear.bondValue_smul,
    BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  calc
    BF4WilsonAllNomeLinear.completedSmul hw0 hw1 t
        (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) =
        BF4WilsonAllNomeLinear.completedSmul hw0 hw1 t
          (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 0
            (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width)) :=
      congrArg (BF4WilsonAllNomeLinear.completedSmul hw0 hw1 t)
        (BF4WilsonAllNomeLinearLaws.completedSmul_zero hw0 hw1 _).symm
    _ = BF4WilsonAllNomeLinear.completedSmul hw0 hw1 (t*0)
          (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) :=
      BF4WilsonAllNomeLinearLaws.completedSmul_mul hw0 hw1 t 0 _
    _ = BF4WilsonAllNomeLinear.completedSmul hw0 hw1 0
          (BF4WilsonAllNomeLinear.completedZero hw0 hw1 width) :=
      BF4WilsonAllNomeLinearLaws.completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv t) _
    _ = BF4WilsonAllNomeLinear.completedZero hw0 hw1 width :=
      BF4WilsonAllNomeLinearLaws.completedSmul_zero hw0 hw1 _

private theorem realAdd_zero (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x RZ = x := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSLinear.bondValue_add,
    BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact BF4WilsonAllNomeLinearLaws.completedAdd_zero hw0 hw1 _

private theorem realZero_add (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.add hw0 hw1 RZ x = x := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSLinear.bondValue_add,
    BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact BF4WilsonAllNomeLinearLaws.completedZero_add hw0 hw1 _

private theorem realSub_zero (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1 (width := width)) :
    BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x RZ = x := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [BF4WilsonAllNomeBondOSLinear.bondValue_sub,
    BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact BF4WilsonAllNomeRowPairingLimit.completedSub_zero hw0 hw1 _

/-- Both actual scaled shifts of the supplied vacuum graph point are Ω. -/
theorem vacuumPoint_shifts (t : Q') :
    BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plus hw0 hw1 t
      (ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))) = Ω ∧
    BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.minus hw0 hw1 t
      (ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))) = Ω := by
  let d := ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))
  have hi := vacuumPoint_input hw0 hw1 (width := width)
  have ho := vacuumPoint_output hw0 hw1 (width := width)
  change input hw0 hw1 d = Ω at hi
  change output hw0 hw1 d = Z at ho
  have hI1 := congrArg Prod.fst hi
  have hI2 := congrArg Prod.snd hi
  have hO1 := congrArg Prod.fst ho
  have hO2 := congrArg Prod.snd ho
  change BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.1 = Ω.1 at hI1
  change BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.2 = RZ at hI2
  change BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.1 = RZ at hO1
  change BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.2 = RZ at hO2
  constructor
  · change (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.1)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.2)),
      BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.2)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.1))) = Ω
    apply Prod.ext
    · change BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.1)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.2)) = Ω.1
      rw [hI1,hO2,realScale_zero,realSub_zero]
    · change BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.2)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.1)) = Ω.2
      rw [hI2,hO1,realScale_zero,realZero_add]
      rfl
  · change (BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.1)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.2)),
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.2)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.1))) = Ω
    apply Prod.ext
    · change BF4WilsonAllNomeBondOSLinear.add hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.1)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.2)) = Ω.1
      rw [hI1,hO2,realScale_zero,realAdd_zero]
    · change BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1 d.2)
        (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 t
          (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1 d.1)) = Ω.2
      rw [hI2,hO1,realScale_zero,realSub_zero]
      rfl

theorem cayley_vacuum (t : Q') (ht : (0 : Q') < t) :
    BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 t ht Ω = Ω := by
  let d := ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))
  have hs := vacuumPoint_shifts hw0 hw1 (width := width) t
  have hp : BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plus hw0 hw1 t d = Ω := hs.1
  have hm : BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.minus hw0 hw1 t d = Ω := hs.2
  have hpre : BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plusDomain hw0 hw1 t ht Ω = d := by
    rw [← hp]
    exact BF4WilsonAllNomeComplexBondOSScaledCayley.plus_left hw0 hw1 t ht d
  unfold BF4WilsonAllNomeComplexBondOSScaledCayley.cayley
  rw [hpre]
  exact hm

theorem iterate_vacuum (t : Q') (ht : (0 : Q') < t) : ∀ n : Nat,
    iterate hw0 hw1 t ht Ω n = Ω := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate,ih,cayley_vacuum hw0 hw1 t ht]

/-- Original represented rows of the unit graph input; no quotient choice. -/
def vacuumRows : Rows hw0 hw1 (width := width) :=
  rowsOfState hw0 hw1
    (BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1
      (vacuumPoint hw0 hw1 (width := width)))

theorem vacuumRows_pin : ofRows hw0 hw1 (vacuumRows hw0 hw1 (width := width)) = Ω := by
  apply value_injective hw0 hw1
  rw [vacuumRows,ofRows_rowsOfState,
    BF4WilsonAllNomeComplexBondOSCompletion.value_ofState]
  exact (value_input_ofPoint hw0 hw1 (vacuumPoint hw0 hw1 (width := width))).symm.trans
    (congrArg (value hw0 hw1) (vacuumPoint_input hw0 hw1 (width := width)))

private theorem zero_distance_le_rat (x : H) (e : Q') (he : (0 : Q') < e) :
    RCle (distance hw0 hw1 x x) (rat e) := by
  rw [BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.distance_self]
  change RCle (rat (0 : Q')) (rat e)
  intro q hq
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ (Q'.le_of_lt he)
    (Q'.add_le_self_of_nonneg e q (Q'.le_of_lt hq))⟩

theorem limitMap_vacuum (t : Q') (ht : (0 : Q') < t) :
    limitMap hw0 hw1 t ht Ω = Ω := by
  let X := vacuumRows hw0 hw1 (width := width)
  have hX : ofRows hw0 hw1 X = Ω := vacuumRows_pin hw0 hw1 (width := width)
  rw [← hX,limitMap_ofRows]
  apply productLimit_unique hw0 hw1 X X t ht (fun _ => 0)
  intro e he n _
  change RCle (distance hw0 hw1
    (productValue hw0 hw1 X t ht n) (ofRows hw0 hw1 X)) (rat e)
  rw [show productValue hw0 hw1 X t ht n = Ω from by
    unfold productValue
    rw [hX]
    exact iterate_vacuum hw0 hw1 (step t n) (step_pos t ht n) (2^n),hX]
  exact zero_distance_le_rat hw0 hw1 Ω e he

theorem positiveAction_vacuum (time : PositiveRealDyadicTimeData.PositiveTime) :
    positiveAction hw0 hw1 time Ω = Ω := by
  let X := vacuumRows hw0 hw1 (width := width)
  have hX : ofRows hw0 hw1 X = Ω := vacuumRows_pin hw0 hw1 (width := width)
  rw [← hX,positiveAction_ofRows]
  apply BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.rows_limit_unique hw0 hw1
    (timeSequence hw0 hw1 time X) X (fun _ => 0)
  intro e he n _
  change RCle (distance hw0 hw1 (ofRows hw0 hw1 (BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime.timeRows
    hw0 hw1 time X n)) (ofRows hw0 hw1 X)) (rat e)
  simp only [timeRows_pin,hX,limitMap_vacuum]
  exact zero_distance_le_rat hw0 hw1 Ω e he

theorem positiveRealAction_vacuum (time : BF4ExactSlabThermodynamicPositiveTimePins.PositiveTimeValue) :
    positiveRealAction hw0 hw1 time Ω = Ω := by
  refine Quotient.inductionOn time ?_
  intro s
  change positiveRealAction hw0 hw1
    (BF4ExactSlabThermodynamicPositiveTimePins.timeValue s) Ω = Ω
  rw [positiveRealAction_pin]
  exact positiveAction_vacuum hw0 hw1 s

theorem inverseRealAction_vacuum
    (time : BF4ExactSlabThermodynamicPositiveTimePins.PositiveTimeValue) :
    inverseRealAction hw0 hw1 time Ω = Ω := by
  have h := positiveRealAction_inverse_left hw0 hw1 time Ω
  rw [positiveRealAction_vacuum hw0 hw1 time] at h
  exact h

/-- The constructed signed action fixes the SAME original complex vacuum. -/
theorem signedAction_vacuum (time : SignedRealTimeData.SignedTimeValue) :
    signedAction hw0 hw1 time Ω = Ω := by
  refine Quotient.inductionOn time ?_
  intro pair
  change positiveRealAction hw0 hw1 pair.1
      (inverseRealAction hw0 hw1 pair.2 Ω) = Ω
  rw [inverseRealAction_vacuum,positiveRealAction_vacuum]

/-- Vacuum expectation of any original physical vector is stationary.  This
does not assert a translated observable algebra or buffered locality. -/
theorem signedAction_vacuum_pairing (time : SignedRealTimeData.SignedTimeValue) (x : H) :
    BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1 Ω (signedAction hw0 hw1 time x) =
      BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1 Ω x := by
  calc
    BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1 Ω (signedAction hw0 hw1 time x) =
        BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1
          (signedAction hw0 hw1 time Ω) (signedAction hw0 hw1 time x) :=
      congrArg (fun y => BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1 y
        (signedAction hw0 hw1 time x)) (signedAction_vacuum hw0 hw1 time).symm
    _ = BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1 Ω x :=
      BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction_pairing_preserved
        hw0 hw1 time Ω x

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum

#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.vacuumPoint
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.vacuumPoint_input
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.vacuumPoint_output
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.vacuumPoint_shifts
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.cayley_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.iterate_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.vacuumRows
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.vacuumRows_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.limitMap_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.positiveAction_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.positiveRealAction_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.inverseRealAction_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.signedAction_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.signedAction_vacuum_pairing
