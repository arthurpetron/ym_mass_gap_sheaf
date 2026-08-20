/-
# Additive laws on the completed strict-cylinder OS carrier

The preceding modules constructed addition, zero, and negation on the same
choice-free `CReal` completion.  Here the presentation algebra is related to
the OS radical strongly enough to prove all completed additive-group laws:
left/right zero, additive inverse, commutativity, and associativity.  The
rational scalar laws are supplied in a later layer; this file therefore does
not install a bundled module instance.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
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
               Q'.mkPos_num, Q'.mkPos_den, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-! ## 1. Semantic presentation laws -/

theorem strictJointCylinderVector_add_zeroLike_equivalent
    {base : Nat} (vector zeroLike : StrictJointCylinderVector base)
    (hzero : ∀ bits, zeroLike.coefficient bits ≈ 0) :
    StrictJointCylinderVectorEquivalent (vector.add zeroLike) vector := by
  intro radius support
  have hadd := StrictJointCylinderVector.add_coefficient_code
    vector zeroLike radius support
  refine Q'.eqv_trans _ _ _ hadd ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (hzero (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
        radius base zeroLike.roots support))) ?_
  exact QPoly.q_add_zero_eqv _

theorem strictJointCylinderVector_zeroLike_add_equivalent
    {base : Nat} (zeroLike vector : StrictJointCylinderVector base)
    (hzero : ∀ bits, zeroLike.coefficient bits ≈ 0) :
    StrictJointCylinderVectorEquivalent (zeroLike.add vector) vector := by
  intro radius support
  have hadd := StrictJointCylinderVector.add_coefficient_code
    zeroLike vector radius support
  refine Q'.eqv_trans _ _ _ hadd ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (hzero (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
        radius base zeroLike.roots support))) ?_
  exact QPoly.q_zero_add_eqv _

theorem strictJointCylinderVector_add_comm_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent (left.add right) (right.add left) := by
  intro radius support
  have hleft := StrictJointCylinderVector.add_coefficient_code
    left right radius support
  have hright := StrictJointCylinderVector.add_coefficient_code
    right left radius support
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.eqv_symm hright))

theorem strictJointCylinderVector_add_assoc_equivalent
    {base : Nat}
    (first second third : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      ((first.add second).add third)
      (first.add (second.add third)) := by
  intro radius support
  have hleftOuter := StrictJointCylinderVector.add_coefficient_code
    (first.add second) third radius support
  have hleftInner := StrictJointCylinderVector.add_coefficient_code
    first second radius support
  have hrightOuter := StrictJointCylinderVector.add_coefficient_code
    first (second.add third) radius support
  have hrightInner := StrictJointCylinderVector.add_coefficient_code
    second third radius support
  refine Q'.eqv_trans _ _ _ hleftOuter ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hleftInner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hrightInner)) ?_
  exact Q'.eqv_symm hrightOuter

theorem strictJointCylinderVector_neg_add_self_zeroLike_equivalent
    {base : Nat} (vector zeroLike : StrictJointCylinderVector base)
    (hzero : ∀ bits, zeroLike.coefficient bits ≈ 0) :
    StrictJointCylinderVectorEquivalent
      ((vector.smul (-1)).add vector) zeroLike := by
  intro radius support
  have hadd := StrictJointCylinderVector.add_coefficient_code
    (vector.smul (-1)) vector radius support
  refine Q'.eqv_trans _ _ _ hadd ?_
  change
    ((-1 : Q') * vector.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base vector.roots support)) +
      vector.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base vector.roots support) ≈
    zeroLike.coefficient
      (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
        radius base zeroLike.roots support)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm
      (hzero (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
        radius base zeroLike.roots support)))
  let value := vector.coefficient
    (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
      radius base vector.roots support)
  have hnegOne : ((-1 : Q') * value) ≈ (-value) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 value)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv value))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ value hnegOne)
    (Q'.neg_add_self_eqv value)

/-! ## 2. Null versions on staged vectors -/

/-- Semantic equality after transport to one common base implies zero staged
OS distance. -/
theorem strictJointCylinderStage_dist_zero_of_common_equivalent
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {left right : StrictJointCylinderStage} {outer : Nat}
    (hleft : left.base <= outer) (hright : right.base <= outer)
    (hequivalent : StrictJointCylinderVectorEquivalent
      (boxTransportStrictJointCylinderVector hleft left.vector)
      (boxTransportStrictJointCylinderVector hright right.vector)) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right)
      CReal.czero := by
  have hcommon := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  have hreplace := strictJointCylinderReflectionDistSq_equiv_of_equivalent
    hcoupling hle hequivalent
      (strictJointCylinderVectorEquivalent_refl
        (boxTransportStrictJointCylinderVector hright right.vector))
  have hrefl := strictJointCylinderReflectionDistSq_refl hcoupling hle
    (boxTransportStrictJointCylinderVector hright right.vector)
  exact CReal.Equiv.trans (CReal.Equiv.symm hcommon)
    (CReal.Equiv.trans hreplace hrefl)

theorem strictJointCylinderStage_add_zero_right_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageAdd stage strictJointCylinderStageZero) stage)
      CReal.czero := by
  have hsum :
      (strictJointCylinderStageAdd stage strictJointCylinderStageZero).base <=
        stage.base := by
    simp [strictJointCylinderStageAdd, strictJointCylinderStageZero]
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    hcoupling hle hsum (Nat.le_refl _)
  have htransport :
      boxTransportStrictJointCylinderVector hsum
          (strictJointCylinderStageAdd stage strictJointCylinderStageZero).vector =
        (boxTransportStrictJointCylinderVector (Nat.le_refl _) stage.vector).add
          (boxTransportStrictJointCylinderVector (Nat.zero_le _)
            strictJointCylinderStageZero.vector) := by
    exact strictJointCylinderStage_add_transport stage strictJointCylinderStageZero
      (Nat.le_refl _) (Nat.zero_le _)
  rw [htransport]
  rw [boxTransportStrictJointCylinderVector_refl]
  apply strictJointCylinderVector_add_zeroLike_equivalent
  intro bits
  exact Q'.eqv_refl 0

theorem strictJointCylinderStage_add_zero_left_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageAdd strictJointCylinderStageZero stage) stage)
      CReal.czero := by
  have hsum :
      (strictJointCylinderStageAdd strictJointCylinderStageZero stage).base <=
        stage.base := by
    simp [strictJointCylinderStageAdd, strictJointCylinderStageZero]
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    hcoupling hle hsum (Nat.le_refl _)
  have htransport :
      boxTransportStrictJointCylinderVector hsum
          (strictJointCylinderStageAdd strictJointCylinderStageZero stage).vector =
        (boxTransportStrictJointCylinderVector (Nat.zero_le _)
          strictJointCylinderStageZero.vector).add
        (boxTransportStrictJointCylinderVector (Nat.le_refl _) stage.vector) := by
    exact strictJointCylinderStage_add_transport strictJointCylinderStageZero stage
      (Nat.zero_le _) (Nat.le_refl _)
  rw [htransport]
  rw [boxTransportStrictJointCylinderVector_refl]
  apply strictJointCylinderVector_zeroLike_add_equivalent
  intro bits
  exact Q'.eqv_refl 0

theorem strictJointCylinderStage_neg_add_self_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageAdd (strictJointCylinderStageNeg stage) stage)
        strictJointCylinderStageZero)
      CReal.czero := by
  have hsum :
      (strictJointCylinderStageAdd (strictJointCylinderStageNeg stage) stage).base <=
        stage.base := by
    simp [strictJointCylinderStageAdd, strictJointCylinderStageNeg]
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    hcoupling hle hsum (Nat.zero_le _)
  have htransport :
      boxTransportStrictJointCylinderVector hsum
          (strictJointCylinderStageAdd
            (strictJointCylinderStageNeg stage) stage).vector =
        (boxTransportStrictJointCylinderVector (Nat.le_refl _)
          (strictJointCylinderStageNeg stage).vector).add
        (boxTransportStrictJointCylinderVector (Nat.le_refl _) stage.vector) := by
    exact strictJointCylinderStage_add_transport
      (strictJointCylinderStageNeg stage) stage (Nat.le_refl _) (Nat.le_refl _)
  rw [htransport]
  rw [boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVector_refl]
  apply strictJointCylinderVector_neg_add_self_zeroLike_equivalent
  intro bits
  exact Q'.eqv_refl 0

theorem strictJointCylinderStage_add_comm_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageAdd left right)
        (strictJointCylinderStageAdd right left))
      CReal.czero := by
  let outer := max left.base right.base
  have hforward : (strictJointCylinderStageAdd left right).base <= outer :=
    Nat.le_refl _
  have hbackward : (strictJointCylinderStageAdd right left).base <= outer := by
    simpa [strictJointCylinderStageAdd, Nat.max_comm]
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    hcoupling hle hforward hbackward
  have htransportForward :
      boxTransportStrictJointCylinderVector hforward
          (strictJointCylinderStageAdd left right).vector =
        (boxTransportStrictJointCylinderVector
          (Nat.le_max_left _ _) left.vector).add
        (boxTransportStrictJointCylinderVector
          (Nat.le_max_right _ _) right.vector) := by
    exact strictJointCylinderStage_add_transport left right
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have htransportBackward :
      boxTransportStrictJointCylinderVector hbackward
          (strictJointCylinderStageAdd right left).vector =
        (boxTransportStrictJointCylinderVector
          (Nat.le_max_right _ _) right.vector).add
        (boxTransportStrictJointCylinderVector
          (Nat.le_max_left _ _) left.vector) := by
    exact strictJointCylinderStage_add_transport right left
      (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  rw [htransportForward, htransportBackward]
  exact strictJointCylinderVector_add_comm_equivalent _ _

theorem strictJointCylinderStage_add_assoc_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second third : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageAdd
          (strictJointCylinderStageAdd first second) third)
        (strictJointCylinderStageAdd first
          (strictJointCylinderStageAdd second third)))
      CReal.czero := by
  let outer := max first.base (max second.base third.base)
  have hfirst : first.base <= outer := Nat.le_max_left _ _
  have hsecond : second.base <= outer := Nat.le_trans
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hthird : third.base <= outer := Nat.le_trans
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hfirstSecond :
      (strictJointCylinderStageAdd first second).base <= outer :=
    Nat.max_le.mpr ⟨hfirst, hsecond⟩
  have hsecondThird :
      (strictJointCylinderStageAdd second third).base <= outer :=
    Nat.max_le.mpr ⟨hsecond, hthird⟩
  have hleft :
      (strictJointCylinderStageAdd
        (strictJointCylinderStageAdd first second) third).base <= outer :=
    Nat.max_le.mpr ⟨hfirstSecond, hthird⟩
  have hright :
      (strictJointCylinderStageAdd first
        (strictJointCylinderStageAdd second third)).base <= outer :=
    Nat.max_le.mpr ⟨hfirst, hsecondThird⟩
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    hcoupling hle hleft hright
  have hleftOuter :
      boxTransportStrictJointCylinderVector hleft
          (strictJointCylinderStageAdd
            (strictJointCylinderStageAdd first second) third).vector =
        (boxTransportStrictJointCylinderVector hfirstSecond
          (strictJointCylinderStageAdd first second).vector).add
        (boxTransportStrictJointCylinderVector hthird third.vector) := by
    exact strictJointCylinderStage_add_transport
      (strictJointCylinderStageAdd first second) third hfirstSecond hthird
  have hleftInner :
      boxTransportStrictJointCylinderVector hfirstSecond
          (strictJointCylinderStageAdd first second).vector =
        (boxTransportStrictJointCylinderVector hfirst first.vector).add
        (boxTransportStrictJointCylinderVector hsecond second.vector) := by
    exact strictJointCylinderStage_add_transport first second hfirst hsecond
  have hrightOuter :
      boxTransportStrictJointCylinderVector hright
          (strictJointCylinderStageAdd first
            (strictJointCylinderStageAdd second third)).vector =
        (boxTransportStrictJointCylinderVector hfirst first.vector).add
        (boxTransportStrictJointCylinderVector hsecondThird
          (strictJointCylinderStageAdd second third).vector) := by
    exact strictJointCylinderStage_add_transport first
      (strictJointCylinderStageAdd second third) hfirst hsecondThird
  have hrightInner :
      boxTransportStrictJointCylinderVector hsecondThird
          (strictJointCylinderStageAdd second third).vector =
        (boxTransportStrictJointCylinderVector hsecond second.vector).add
        (boxTransportStrictJointCylinderVector hthird third.vector) := by
    exact strictJointCylinderStage_add_transport second third hsecond hthird
  rw [hleftOuter, hleftInner, hrightOuter, hrightInner]
  exact strictJointCylinderVector_add_assoc_equivalent _ _ _

/-! ## 3. Laws on all completion points -/

private def closeOfPointwiseNull
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy}
    (h : ∀ n,
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).Null
        (X.seq n) (Y.seq n)) :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close X Y :=
  SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull h

theorem strictJointCylinderCompletedAdd_zero_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedAdd hcoupling hle vector
        (strictJointCylinderCompletedZero hcoupling hle) = vector := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull hcoupling hle
    (fun n => strictJointCylinderStage_add_zero_right_null
      hcoupling hle (X.seq n))⟩

theorem strictJointCylinderCompletedAdd_zero_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedZero hcoupling hle) vector = vector := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull hcoupling hle
    (fun n => strictJointCylinderStage_add_zero_left_null
      hcoupling hle (X.seq n))⟩

theorem strictJointCylinderCompletedNeg_add_self
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedNeg hcoupling hle vector) vector =
      strictJointCylinderCompletedZero hcoupling hle := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull hcoupling hle
    (fun n => strictJointCylinderStage_neg_add_self_null
      hcoupling hle (X.seq n))⟩

theorem strictJointCylinderCompletedAdd_comm
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedAdd hcoupling hle left right =
      strictJointCylinderCompletedAdd hcoupling hle right left := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull hcoupling hle
    (fun n => strictJointCylinderStage_add_comm_null
      hcoupling hle (X.seq n) (Y.seq n))⟩

theorem strictJointCylinderCompletedAdd_assoc
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second third : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedAdd hcoupling hle first second) third =
      strictJointCylinderCompletedAdd hcoupling hle first
        (strictJointCylinderCompletedAdd hcoupling hle second third) := by
  refine Quotient.inductionOn first (fun X => ?_)
  refine Quotient.inductionOn second (fun Y => ?_)
  refine Quotient.inductionOn third (fun Z => ?_)
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull hcoupling hle
    (fun n => strictJointCylinderStage_add_assoc_null
      hcoupling hle (X.seq n) (Y.seq n) (Z.seq n))⟩

#print axioms strictJointCylinderVector_add_zeroLike_equivalent
#print axioms strictJointCylinderVector_zeroLike_add_equivalent
#print axioms strictJointCylinderVector_add_comm_equivalent
#print axioms strictJointCylinderVector_add_assoc_equivalent
#print axioms strictJointCylinderVector_neg_add_self_zeroLike_equivalent
#print axioms strictJointCylinderStage_dist_zero_of_common_equivalent
#print axioms strictJointCylinderStage_add_zero_right_null
#print axioms strictJointCylinderStage_add_zero_left_null
#print axioms strictJointCylinderStage_neg_add_self_null
#print axioms strictJointCylinderStage_add_comm_null
#print axioms strictJointCylinderStage_add_assoc_null
#print axioms strictJointCylinderCompletedAdd_zero_right
#print axioms strictJointCylinderCompletedAdd_zero_left
#print axioms strictJointCylinderCompletedNeg_add_self
#print axioms strictJointCylinderCompletedAdd_comm
#print axioms strictJointCylinderCompletedAdd_assoc

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveLaws
