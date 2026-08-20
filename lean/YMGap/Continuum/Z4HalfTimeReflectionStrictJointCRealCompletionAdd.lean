/-
# Addition on the completed strict-cylinder OS carrier

The strict-cylinder direct-limit completion previously carried only its
squared metric and the nonexpansive Euclidean-time semigroup.  This module
constructs the first genuinely linear operation on that same completed
carrier.

Staged vectors are added after canonical transport to their maximum source
base.  The difference of two such sums is semantically the sum of the two
endpoint differences.  The established quadratic triangle bound therefore
makes staged addition binary quadratic-Lipschitz.  The generic constructive
completion machinery then descends it without choosing representatives.

This is only the additive entry point.  Zero, negation, rational scaling, the
completed bilinear form, and linear self-adjointness of time translation are
separate obligations.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-! ## 1. The fixed-base addition estimate -/

/-- The difference of two presentation sums represents the sum of the two
endpoint differences. -/
theorem strictJointCylinderDifference_add_equivalent
    {base : Nat}
    (left left' right right' : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference
        (left.add right) (left'.add right'))
      ((strictJointCylinderDifference left left').add
        (strictJointCylinderDifference right right')) := by
  intro radius support
  have houter := strictJointCylinderDifference_coefficient_code
    (left.add right) (left'.add right') radius support
  have hleftAdd := StrictJointCylinderVector.add_coefficient_code
    left right radius support
  have hrightAdd := StrictJointCylinderVector.add_coefficient_code
    left' right' radius support
  have hleftDiff := strictJointCylinderDifference_coefficient_code
    left left' radius support
  have hrightDiff := strictJointCylinderDifference_coefficient_code
    right right' radius support
  have htargetAdd := StrictJointCylinderVector.add_coefficient_code
    (strictJointCylinderDifference left left')
    (strictJointCylinderDifference right right') radius support
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleftAdd (Q'.neg_eqv_congr _ _ hrightAdd)) ?_
  let a := left.coefficient
    (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
      radius base left.roots support)
  let b := right.coefficient
    (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
      radius base right.roots support)
  let c := left'.coefficient
    (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
      radius base left'.roots support)
  let d := right'.coefficient
    (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
      radius base right'.roots support)
  have halgebra : ((a + b) + (-(c + d))) ≈
      ((a + (-c)) + (b + (-d))) := by
    ring_qeqv
  refine Q'.eqv_trans _ _ _ halgebra ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm hleftDiff) (Q'.eqv_symm hrightDiff))
    (Q'.eqv_symm htargetAdd)

/-- Addition is quadratic-Lipschitz for the fixed-base strict OS distance. -/
theorem strictJointCylinderReflectionDistSq_add_le
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat}
    (left left' right right' : StrictJointCylinderVector base) :
    CReal.leEv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (left.add right) (left'.add right'))
      (CReal.add
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle left left')
          (strictJointCylinderReflectionDistSq hcoupling hle left left'))
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle right right')
          (strictJointCylinderReflectionDistSq hcoupling hle right right'))) := by
  have hpresentation := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle
    (strictJointCylinderDifference_add_equivalent left left' right right')
  exact CReal.leEv_trans (CReal.leEv_of_equiv hpresentation)
    (reflectionQuadratic_add_le hcoupling hle
      (strictJointCylinderDifference left left')
      (strictJointCylinderDifference right right'))

/-! ## 2. Addition on staged direct-limit presentations -/

/-- Addition of staged vectors after canonical transport to the maximum of
their two source bases. -/
def strictJointCylinderStageAdd
    (left right : StrictJointCylinderStage) : StrictJointCylinderStage :=
  let outer := max left.base right.base
  ⟨outer,
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_left left.base right.base) left.vector).add
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_right left.base right.base) right.vector)⟩

private theorem boxTransportStrictJointCylinderVector_add_of_le
    {base outer : Nat} (hbase : base <= outer)
    (left right : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hbase (left.add right) =
      (boxTransportStrictJointCylinderVector hbase left).add
        (boxTransportStrictJointCylinderVector hbase right) := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_add padding left right

/-- Transporting a staged sum to any larger common base gives the sum of the
separately transported endpoints. -/
theorem strictJointCylinderStage_add_transport
    (left right : StrictJointCylinderStage)
    {outer : Nat} (hleft : left.base <= outer)
    (hright : right.base <= outer) :
    boxTransportStrictJointCylinderVector
        (Nat.max_le.mpr ⟨hleft, hright⟩)
        (strictJointCylinderStageAdd left right).vector =
      (boxTransportStrictJointCylinderVector hleft left.vector).add
        (boxTransportStrictJointCylinderVector hright right.vector) := by
  unfold strictJointCylinderStageAdd
  rw [boxTransportStrictJointCylinderVector_add_of_le]
  congr 1
  · exact boxTransportStrictJointCylinderVector_trans
      (Nat.le_max_left left.base right.base)
      (Nat.max_le.mpr ⟨hleft, hright⟩) left.vector
  · exact boxTransportStrictJointCylinderVector_trans
      (Nat.le_max_right left.base right.base)
      (Nat.max_le.mpr ⟨hleft, hright⟩) right.vector

private theorem double_add_equiv {left right : CReal}
    (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.add left left) (CReal.add right right) :=
  CReal.Equiv.trans (CReal.add_congr_left h) (CReal.add_congr_right h)

/-- Staged addition has the binary quadratic-Lipschitz estimate required by
the choice-free completion. -/
theorem strictJointCylinderStage_add_quadraticLipschitz
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left left' right right' : StrictJointCylinderStage) :
    CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageAdd left right)
        (strictJointCylinderStageAdd left' right'))
      (CReal.add
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle left left')
          (strictJointCylinderStageReflectionDistSq hcoupling hle left left'))
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle right right')
          (strictJointCylinderStageReflectionDistSq hcoupling hle right right'))) := by
  let leftBase := max left.base right.base
  let rightBase := max left'.base right'.base
  let outer := max leftBase rightBase
  have hsumLeft : (strictJointCylinderStageAdd left right).base <= outer :=
    Nat.le_max_left _ _
  have hsumRight : (strictJointCylinderStageAdd left' right').base <= outer :=
    Nat.le_max_right _ _
  have hleft : left.base <= outer := Nat.le_trans
    (Nat.le_max_left _ _) hsumLeft
  have hright : right.base <= outer := Nat.le_trans
    (Nat.le_max_right _ _) hsumLeft
  have hleft' : left'.base <= outer := Nat.le_trans
    (Nat.le_max_left _ _) hsumRight
  have hright' : right'.base <= outer := Nat.le_trans
    (Nat.le_max_right _ _) hsumRight
  have hsum := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle (strictJointCylinderStageAdd left right)
      (strictJointCylinderStageAdd left' right') hsumLeft hsumRight
  have hleftDist := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left left' hleft hleft'
  have hrightDist := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle right right' hright hright'
  have hbound := strictJointCylinderReflectionDistSq_add_le hcoupling hle
    (boxTransportStrictJointCylinderVector hleft left.vector)
    (boxTransportStrictJointCylinderVector hleft' left'.vector)
    (boxTransportStrictJointCylinderVector hright right.vector)
    (boxTransportStrictJointCylinderVector hright' right'.vector)
  rw [← strictJointCylinderStage_add_transport left right hleft hright,
    ← strictJointCylinderStage_add_transport left' right' hleft' hright'] at hbound
  have hrightSide : CReal.Equiv
      (CReal.add
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle
            (boxTransportStrictJointCylinderVector hleft left.vector)
            (boxTransportStrictJointCylinderVector hleft' left'.vector))
          (strictJointCylinderReflectionDistSq hcoupling hle
            (boxTransportStrictJointCylinderVector hleft left.vector)
            (boxTransportStrictJointCylinderVector hleft' left'.vector)))
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle
            (boxTransportStrictJointCylinderVector hright right.vector)
            (boxTransportStrictJointCylinderVector hright' right'.vector))
          (strictJointCylinderReflectionDistSq hcoupling hle
            (boxTransportStrictJointCylinderVector hright right.vector)
            (boxTransportStrictJointCylinderVector hright' right'.vector))))
      (CReal.add
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle left left')
          (strictJointCylinderStageReflectionDistSq hcoupling hle left left'))
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle right right')
          (strictJointCylinderStageReflectionDistSq hcoupling hle right right'))) :=
    CReal.Equiv.trans
      (CReal.add_congr_left (double_add_equiv hleftDist))
      (CReal.add_congr_right (double_add_equiv hrightDist))
  exact (CReal.leEv_congr hsum hrightSide).mp hbound

/-! ## 3. Addition on the completed strict OS carrier -/

def strictJointCylinderStageAddQuadraticLipschitz
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).BinaryQuadraticLipschitz where
  toFun := strictJointCylinderStageAdd
  contraction := strictJointCylinderStage_add_quadraticLipschitz
    hcoupling hle

/-- Addition on the completed, base-independent strict OS carrier. -/
def strictJointCylinderCompletedAdd
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle ->
        StrictJointCylinderOSCompletion hcoupling hle :=
  (strictJointCylinderStageAddQuadraticLipschitz
    hcoupling hle).completionMap

#print axioms strictJointCylinderDifference_add_equivalent
#print axioms strictJointCylinderReflectionDistSq_add_le
#print axioms strictJointCylinderStage_add_transport
#print axioms strictJointCylinderStage_add_quadraticLipschitz
#print axioms strictJointCylinderStageAddQuadraticLipschitz
#print axioms strictJointCylinderCompletedAdd

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
