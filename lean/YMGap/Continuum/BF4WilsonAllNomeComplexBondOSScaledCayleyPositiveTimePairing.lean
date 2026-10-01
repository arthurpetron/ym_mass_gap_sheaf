/-
# Hermitian pairing of the constructed positive-time Cayley action

Every rational sample preserves the full original complex Wilson-bond
pairing.  The represented-row pairing limit transports both its real sum
and its imaginary cross difference to the constructed positive-time limit.
This is fixed nome and width, without physical-time calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGraphNorm

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (RepresentedCauchy rowPoint limit)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (constantRows constantRows_point limit_constantRows)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
  (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows rowState value
    value_ofRows value_ofState inner inner_value distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (timeSequence timeRows timeRows_pin timeLimitRows positiveAction positiveAction_ofRows
    sample_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
  (sum_pairing_limits_eq limitMap_pairing_preserved)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime sample)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "I" => inner hw0 hw1

private def realRows (C : CauchySequence hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.representedRows hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.realSequence hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.sectorSequence hw0 hw1 C))

private def imagRows (C : CauchySequence hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.representedRows hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.imagSequence hw0 hw1
      (BF4WilsonAllNomeComplexBondOSCompletion.sectorSequence hw0 hw1 C))

private theorem realRows_point (C : CauchySequence hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (realRows hw0 hw1 C) n =
      (value hw0 hw1 (ofRows hw0 hw1 (C.seq n))).1 := by
  rw [realRows,BF4WilsonAllNomeTimeSector.representedRows_point,value_ofRows]
  rfl

private theorem imagRows_point (C : CauchySequence hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (imagRows hw0 hw1 C) n =
      (value hw0 hw1 (ofRows hw0 hw1 (C.seq n))).2 := by
  rw [imagRows,BF4WilsonAllNomeTimeSector.representedRows_point,value_ofRows]
  rfl

private theorem realRows_limit (C : CauchySequence hw0 hw1 (width := width)) :
    limit hw0 hw1 (realRows hw0 hw1 C) =
      (value hw0 hw1 (ofRows hw0 hw1
        (BF4WilsonAllNomeComplexBondOSCompletion.limitRows hw0 hw1 C))).1 := by
  rw [realRows,BF4WilsonAllNomeComplexBondOSCompletion.limitRows,
    BF4WilsonAllNomeComplexBondOSCompletion.ofRows_rowsOfState,value_ofState]
  rfl

private theorem imagRows_limit (C : CauchySequence hw0 hw1 (width := width)) :
    limit hw0 hw1 (imagRows hw0 hw1 C) =
      (value hw0 hw1 (ofRows hw0 hw1
        (BF4WilsonAllNomeComplexBondOSCompletion.limitRows hw0 hw1 C))).2 := by
  rw [imagRows,BF4WilsonAllNomeComplexBondOSCompletion.limitRows,
    BF4WilsonAllNomeComplexBondOSCompletion.ofRows_rowsOfState,value_ofState]
  rfl

private def constantReal (X : Rows hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  constantRows hw0 hw1
    (representative hw0 hw1 (rowState hw0 hw1 X).1.range)

private def constantImag (X : Rows hw0 hw1 (width := width)) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  constantRows hw0 hw1
    (representative hw0 hw1 (rowState hw0 hw1 X).2.range)

private theorem constantReal_point (X : Rows hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (constantReal hw0 hw1 X) n =
      (value hw0 hw1 (ofRows hw0 hw1 X)).1 := by
  rw [constantReal,constantRows_point,representative_pin,value_ofRows]
  rfl

private theorem constantImag_point (X : Rows hw0 hw1 (width := width)) (n : Nat) :
    rowPoint hw0 hw1 (constantImag hw0 hw1 X) n =
      (value hw0 hw1 (ofRows hw0 hw1 X)).2 := by
  rw [constantImag,constantRows_point,representative_pin,value_ofRows]
  rfl

private theorem constantReal_limit (X : Rows hw0 hw1 (width := width)) :
    limit hw0 hw1 (constantReal hw0 hw1 X) =
      (value hw0 hw1 (ofRows hw0 hw1 X)).1 := by
  rw [constantReal,limit_constantRows,representative_pin,value_ofRows]
  rfl

private theorem constantImag_limit (X : Rows hw0 hw1 (width := width)) :
    limit hw0 hw1 (constantImag hw0 hw1 X) =
      (value hw0 hw1 (ofRows hw0 hw1 X)).2 := by
  rw [constantImag,limit_constantRows,representative_pin,value_ofRows]
  rfl

private theorem cross_add_of_sub_eq (a b c d : RC)
    (h : RCsub a b = RCsub c d) : RCadd a d = RCadd c b := by
  have left : RCadd (RCsub a b) (RCadd b d) = RCadd a d := by
    refine Quotient.inductionOn₃ a b d ?_
    intro A C D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.var 2)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => D.approx n)))
  have right : RCadd (RCsub c d) (RCadd b d) = RCadd c b := by
    refine Quotient.inductionOn₃ c d b ?_
    intro C D A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.var 1)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => C.approx n | 1 => D.approx n | _ => A.approx n)))
  calc
    RCadd a d = RCadd (RCsub a b) (RCadd b d) := left.symm
    _ = RCadd (RCsub c d) (RCadd b d) := congrArg (fun z => RCadd z (RCadd b d)) h
    _ = RCadd c b := right

private theorem sub_eq_of_cross_add (a b c d : RC)
    (h : RCadd a d = RCadd c b) : RCsub a b = RCsub c d := by
  have left : RCsub (RCadd a d) (RCadd b d) = RCsub a b := by
    refine Quotient.inductionOn₃ a b d ?_
    intro A C D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 2))))
        (.add (.var 0) (.neg (.var 1)))
        (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => D.approx n)))
  have right : RCsub (RCadd c b) (RCadd b d) = RCsub c d := by
    refine Quotient.inductionOn₃ c b d ?_
    intro C A D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 1) (.var 2))))
        (.add (.var 0) (.neg (.var 2)))
        (by decide) (fun | 0 => C.approx n | 1 => A.approx n | _ => D.approx n)))
  calc
    RCsub a b = RCsub (RCadd a d) (RCadd b d) := left.symm
    _ = RCsub (RCadd c b) (RCadd b d) := congrArg (fun z => RCsub z (RCadd b d)) h
    _ = RCsub c d := right

/-- The same numerical sample acts on both sources; its FULL Hermitian
pairing is the original one, including the imaginary cross terms. -/
theorem positiveAction_pairing_rows (time : PositiveTime)
    (X Y : Rows hw0 hw1 (width := width)) :
    I (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X))
      (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y)) =
    I (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y) := by
  let CX := timeSequence hw0 hw1 time X
  let CY := timeSequence hw0 hw1 time Y
  have hstage (n : Nat) :
      I (ofRows hw0 hw1 (CX.seq n)) (ofRows hw0 hw1 (CY.seq n)) =
        I (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y) := by
    change I (ofRows hw0 hw1 (timeRows hw0 hw1 time X n))
      (ofRows hw0 hw1 (timeRows hw0 hw1 time Y n)) = _
    rw [timeRows_pin,timeRows_pin]
    exact limitMap_pairing_preserved hw0 hw1
      (sample time n) (sample_positive time n) (ofRows hw0 hw1 X) (ofRows hw0 hw1 Y)
  apply Prod.ext
  · rw [inner_value,inner_value]
    change RCadd
      (B (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X))).1
        (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y))).1)
      (B (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X))).2
        (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y))).2) = _
    have h := sum_pairing_limits_eq hw0 hw1
        (realRows hw0 hw1 CX) (realRows hw0 hw1 CY)
        (imagRows hw0 hw1 CX) (imagRows hw0 hw1 CY)
        (constantReal hw0 hw1 X) (constantReal hw0 hw1 Y)
        (constantImag hw0 hw1 X) (constantImag hw0 hw1 Y) (fun n => by
          rw [realRows_point,realRows_point,imagRows_point,imagRows_point,
            constantReal_point,constantReal_point,
            constantImag_point,constantImag_point]
          have hf := congrArg Prod.fst (hstage n)
          simpa only [inner_value,BF4WilsonAllNomeComplexification.inner] using hf)
    rw [realRows_limit,realRows_limit,imagRows_limit,imagRows_limit,
      constantReal_limit,constantReal_limit,constantImag_limit,constantImag_limit] at h
    exact h
  · rw [inner_value,inner_value]
    change RCsub
      (B (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X))).1
        (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y))).2)
      (B (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X))).2
        (value hw0 hw1 (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y))).1) = _
    have h := sum_pairing_limits_eq hw0 hw1
        (realRows hw0 hw1 CX) (imagRows hw0 hw1 CY)
        (constantImag hw0 hw1 X) (constantReal hw0 hw1 Y)
        (constantReal hw0 hw1 X) (constantImag hw0 hw1 Y)
        (imagRows hw0 hw1 CX) (realRows hw0 hw1 CY) (fun n => by
          rw [realRows_point,imagRows_point,constantImag_point,constantReal_point,
            constantReal_point,constantImag_point,imagRows_point,realRows_point]
          apply cross_add_of_sub_eq
          have hf := congrArg Prod.snd (hstage n)
          simpa only [inner_value,BF4WilsonAllNomeComplexification.inner] using hf)
    rw [realRows_limit,imagRows_limit,constantImag_limit,constantReal_limit,
      constantReal_limit,constantImag_limit,imagRows_limit,realRows_limit] at h
    exact sub_eq_of_cross_add _ _ _ _ h

/-- Full Hermitian preservation on every ORIGINAL completed bond class. -/
theorem positiveAction_pairing_preserved (time : PositiveTime) (x y : H) :
    I (positiveAction hw0 hw1 time x) (positiveAction hw0 hw1 time y) = I x y := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  refine Quotient.inductionOn₂ x₁ x₂ ?_
  intro X₁ X₂
  refine Quotient.inductionOn₂ y₁ y₂ ?_
  intro Y₁ Y₂
  change I (positiveAction hw0 hw1 time (ofRows hw0 hw1 (X₁,X₂)))
    (positiveAction hw0 hw1 time (ofRows hw0 hw1 (Y₁,Y₂))) =
    I (ofRows hw0 hw1 (X₁,X₂)) (ofRows hw0 hw1 (Y₁,Y₂))
  rw [positiveAction_ofRows,positiveAction_ofRows]
  exact positiveAction_pairing_rows hw0 hw1 time (X₁,X₂) (Y₁,Y₂)

/-- The quotient time value acts on the same physical Hermitian carrier. -/
theorem positiveRealAction_pairing_preserved (time : PositiveTimeValue) (x y : H) :
    I (positiveRealAction hw0 hw1 time x)
      (positiveRealAction hw0 hw1 time y) = I x y := by
  refine Quotient.inductionOn time ?_
  intro t
  exact positiveAction_pairing_preserved hw0 hw1 t x y

theorem positiveAction_distance (time : PositiveTime) (x y : H) :
    distance hw0 hw1 (positiveAction hw0 hw1 time x)
      (positiveAction hw0 hw1 time y) = distance hw0 hw1 x y := by
  rw [BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing,
    BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing,
    positiveAction_pairing_preserved,positiveAction_pairing_preserved,
    positiveAction_pairing_preserved,positiveAction_pairing_preserved]

theorem positiveRealAction_distance (time : PositiveTimeValue) (x y : H) :
    distance hw0 hw1 (positiveRealAction hw0 hw1 time x)
      (positiveRealAction hw0 hw1 time y) = distance hw0 hw1 x y := by
  rw [BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing,
    BF4WilsonAllNomeComplexBondOSGraphNorm.distance_pairing,
    positiveRealAction_pairing_preserved,positiveRealAction_pairing_preserved,
    positiveRealAction_pairing_preserved,positiveRealAction_pairing_preserved]

theorem positiveAction_injective (time : PositiveTime) {x y : H}
    (h : positiveAction hw0 hw1 time x = positiveAction hw0 hw1 time y) : x = y := by
  apply BF4WilsonAllNomeComplexBondOSCayley.eq_of_pairings hw0 hw1
  intro z
  calc
    I x z = I (positiveAction hw0 hw1 time x) (positiveAction hw0 hw1 time z) :=
      (positiveAction_pairing_preserved hw0 hw1 time x z).symm
    _ = I (positiveAction hw0 hw1 time y) (positiveAction hw0 hw1 time z) :=
      congrArg (fun u => I u (positiveAction hw0 hw1 time z)) h
    _ = I y z := positiveAction_pairing_preserved hw0 hw1 time y z

theorem positiveRealAction_injective (time : PositiveTimeValue) {x y : H}
    (h : positiveRealAction hw0 hw1 time x = positiveRealAction hw0 hw1 time y) : x = y := by
  apply BF4WilsonAllNomeComplexBondOSCayley.eq_of_pairings hw0 hw1
  intro z
  calc
    I x z = I (positiveRealAction hw0 hw1 time x) (positiveRealAction hw0 hw1 time z) :=
      (positiveRealAction_pairing_preserved hw0 hw1 time x z).symm
    _ = I (positiveRealAction hw0 hw1 time y) (positiveRealAction hw0 hw1 time z) :=
      congrArg (fun u => I u (positiveRealAction hw0 hw1 time z)) h
    _ = I y z := positiveRealAction_pairing_preserved hw0 hw1 time y z

#print axioms positiveAction_pairing_rows
#print axioms positiveAction_pairing_preserved
#print axioms positiveRealAction_pairing_preserved
#print axioms positiveAction_distance
#print axioms positiveRealAction_distance
#print axioms positiveAction_injective
#print axioms positiveRealAction_injective

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
