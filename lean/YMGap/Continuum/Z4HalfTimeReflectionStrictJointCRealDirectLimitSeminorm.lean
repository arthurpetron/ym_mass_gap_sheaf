/-
# The strict-cylinder squared distance on staged direct-limit carriers

The algebraic direct limit identifies base transports by quotient equality.
For constructive completion it is more convenient to retain the staged
carrier and let the OS radical identify those transports.  This module defines
the squared distance by moving each pair to its canonical maximum base, proves
independence from any larger common base, and places every direct-limit
transport equivalence in the metric radical.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Squared OS distance is invariant under simultaneous canonical transport to
an arbitrary larger base. -/
theorem boxTransportStrictJointCylinderVector_reflectionDistSq_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base outer : Nat} (hbase : base <= outer)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (boxTransportStrictJointCylinderVector hbase left)
        (boxTransportStrictJointCylinderVector hbase right))
      (strictJointCylinderReflectionDistSq hcoupling hle left right) := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  unfold strictJointCylinderReflectionDistSq strictJointCylinderDifference
  rw [← boxTransportStrictJointCylinderVector_smul,
    ← boxTransportStrictJointCylinderVector_add]
  exact boxTransportStrictJointCylinderVector_reflectionQuadratic_equiv
    hcoupling hle padding (left.add (right.smul (-1)))

/-- Pairwise squared distance on the quotient-free staged direct carrier. -/
def strictJointCylinderStageReflectionDistSq
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) : CReal :=
  strictJointCylinderReflectionDistSq hcoupling hle
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_left left.base right.base) left.vector)
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_right left.base right.base) right.vector)

/-- Computing the staged distance in any common larger box gives the same
constructive real. -/
theorem strictJointCylinderStageReflectionDistSq_at_common
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage)
    {outer : Nat} (hleft : left.base <= outer)
    (hright : right.base <= outer) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (boxTransportStrictJointCylinderVector hleft left.vector)
        (boxTransportStrictJointCylinderVector hright right.vector))
      (strictJointCylinderStageReflectionDistSq
        hcoupling hle left right) := by
  have hmax : max left.base right.base <= outer :=
    Nat.max_le.mpr ⟨hleft, hright⟩
  have hleftTrans := boxTransportStrictJointCylinderVector_trans
    (Nat.le_max_left left.base right.base) hmax left.vector
  have hrightTrans := boxTransportStrictJointCylinderVector_trans
    (Nat.le_max_right left.base right.base) hmax right.vector
  change CReal.Equiv
    (strictJointCylinderReflectionDistSq hcoupling hle
      (boxTransportStrictJointCylinderVector hleft left.vector)
      (boxTransportStrictJointCylinderVector hright right.vector))
    (strictJointCylinderReflectionDistSq hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_left left.base right.base) left.vector)
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_right left.base right.base) right.vector))
  rw [← hleftTrans, ← hrightTrans]
  exact boxTransportStrictJointCylinderVector_reflectionDistSq_equiv
    hcoupling hle hmax
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_left left.base right.base) left.vector)
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_right left.base right.base) right.vector)

/-- Literal direct-limit equivalence is contained in the OS metric radical. -/
theorem strictJointCylinderStageEquivalent_reflectionDistSq_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {left right : StrictJointCylinderStage}
    (h : StrictJointCylinderStageEquivalent left right) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right)
      CReal.czero := by
  rcases h with ⟨outer, hleft, hright, heq⟩
  have hcommon := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  apply CReal.Equiv.trans (CReal.Equiv.symm hcommon)
  rw [heq]
  exact strictJointCylinderReflectionDistSq_refl hcoupling hle _

theorem strictJointCylinderStageReflectionDistSq_refl
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle stage stage)
      CReal.czero := by
  have hcommon := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle stage stage (Nat.le_refl _) (Nat.le_refl _)
  apply CReal.Equiv.trans (CReal.Equiv.symm hcommon)
  rw [boxTransportStrictJointCylinderVector_refl]
  exact strictJointCylinderReflectionDistSq_refl hcoupling hle _

theorem strictJointCylinderStageReflectionDistSq_symm
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right)
      (strictJointCylinderStageReflectionDistSq hcoupling hle right left) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hforward := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  have hbackward := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle right left hright hleft
  exact CReal.Equiv.trans (CReal.Equiv.symm hforward)
    (CReal.Equiv.trans
      (strictJointCylinderReflectionDistSq_symm hcoupling hle _ _)
      hbackward)

theorem strictJointCylinderStageReflectionDistSq_nonneg
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.leEv CReal.czero
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right) :=
  strictJointCylinderReflectionDistSq_nonneg hcoupling hle _ _

private theorem double_add_equiv {left right : CReal}
    (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.add left left) (CReal.add right right) :=
  CReal.Equiv.trans (CReal.add_congr_left h) (CReal.add_congr_right h)

theorem strictJointCylinderStageReflectionDistSq_triangle
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (x y z : StrictJointCylinderStage) :
    CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle x z)
      (CReal.add
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle x y)
          (strictJointCylinderStageReflectionDistSq hcoupling hle x y))
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle y z)
          (strictJointCylinderStageReflectionDistSq hcoupling hle y z))) := by
  let outer := max x.base (max y.base z.base)
  have hx : x.base <= outer := Nat.le_max_left _ _
  have hy : y.base <= outer := Nat.le_trans
    (Nat.le_max_left y.base z.base) (Nat.le_max_right _ _)
  have hz : z.base <= outer := Nat.le_trans
    (Nat.le_max_right y.base z.base) (Nat.le_max_right _ _)
  let X := boxTransportStrictJointCylinderVector hx x.vector
  let Y := boxTransportStrictJointCylinderVector hy y.vector
  let Z := boxTransportStrictJointCylinderVector hz z.vector
  have hxy := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle x y hx hy
  have hxz := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle x z hx hz
  have hyz := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle y z hy hz
  have hright : CReal.Equiv
      (CReal.add
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle X Y)
          (strictJointCylinderReflectionDistSq hcoupling hle X Y))
        (CReal.add
          (strictJointCylinderReflectionDistSq hcoupling hle Y Z)
          (strictJointCylinderReflectionDistSq hcoupling hle Y Z)))
      (CReal.add
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle x y)
          (strictJointCylinderStageReflectionDistSq hcoupling hle x y))
        (CReal.add
          (strictJointCylinderStageReflectionDistSq hcoupling hle y z)
          (strictJointCylinderStageReflectionDistSq hcoupling hle y z))) :=
    CReal.Equiv.trans
      (CReal.add_congr_left (double_add_equiv hxy))
      (CReal.add_congr_right (double_add_equiv hyz))
  exact (CReal.leEv_congr hxz hright).mp
    (strictJointCylinderReflectionDistSq_triangle
      hcoupling hle X Y Z)

theorem strictJointCylinderStageReflectionDistSq_null_congr
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {x x' y y' : StrictJointCylinderStage}
    (hxNull : CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle x x')
      CReal.czero)
    (hyNull : CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle y y')
      CReal.czero) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle x y)
      (strictJointCylinderStageReflectionDistSq hcoupling hle x' y') := by
  let outer := max x.base (max x'.base (max y.base y'.base))
  have hx : x.base <= outer := Nat.le_max_left _ _
  have hxp : x'.base <= outer := Nat.le_trans
    (Nat.le_max_left x'.base (max y.base y'.base))
    (Nat.le_max_right _ _)
  have hy : y.base <= outer := Nat.le_trans
    (Nat.le_trans (Nat.le_max_left y.base y'.base)
      (Nat.le_max_right x'.base (max y.base y'.base)))
    (Nat.le_max_right _ _)
  have hyp : y'.base <= outer := Nat.le_trans
    (Nat.le_trans (Nat.le_max_right y.base y'.base)
      (Nat.le_max_right x'.base (max y.base y'.base)))
    (Nat.le_max_right _ _)
  let X := boxTransportStrictJointCylinderVector hx x.vector
  let X' := boxTransportStrictJointCylinderVector hxp x'.vector
  let Y := boxTransportStrictJointCylinderVector hy y.vector
  let Y' := boxTransportStrictJointCylinderVector hyp y'.vector
  have hxxp := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle x x' hx hxp
  have hyyp := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle y y' hy hyp
  have hxy := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle x y hx hy
  have hxpy := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle x' y' hxp hyp
  have hXNull : CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle X X')
      CReal.czero := CReal.Equiv.trans hxxp hxNull
  have hYNull : CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle Y Y')
      CReal.czero := CReal.Equiv.trans hyyp hyNull
  exact CReal.Equiv.trans (CReal.Equiv.symm hxy)
    (CReal.Equiv.trans
      (strictJointCylinderReflectionDistSq_null_congr
        hcoupling hle hXNull hYNull)
      hxpy)

/-- The fully discharged squared seminorm on the base-independent staged
carrier.  Its radical contains every literal direct-limit transport relation. -/
def strictJointCylinderStageSquaredSeminorm
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) : SquaredSeminorm where
  Carrier := StrictJointCylinderStage
  distSq := strictJointCylinderStageReflectionDistSq hcoupling hle
  distSq_refl := strictJointCylinderStageReflectionDistSq_refl hcoupling hle
  distSq_symm := strictJointCylinderStageReflectionDistSq_symm hcoupling hle
  distSq_nonneg := strictJointCylinderStageReflectionDistSq_nonneg hcoupling hle
  distSq_triangle :=
    strictJointCylinderStageReflectionDistSq_triangle hcoupling hle
  null_congr := strictJointCylinderStageReflectionDistSq_null_congr hcoupling hle

/-- The staged time action is nonexpansive for the base-independent squared
distance. -/
theorem strictJointCylinderStage_timeTranslate_nonexpansive
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (left right : StrictJointCylinderStage) :
    CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (left.timeTranslate shift) (right.timeTranslate shift))
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  let L := boxTransportStrictJointCylinderVector hleft left.vector
  let R := boxTransportStrictJointCylinderVector hright right.vector
  have htarget := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle (left.timeTranslate shift) (right.timeTranslate shift)
      (Nat.add_le_add_right hleft shift)
      (Nat.add_le_add_right hright shift)
  have hsource := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  have hcontract := timeTranslatedStrictJointReflectionDistSq_leEv_source
    hcoupling hle L R shift
  rw [timeTranslate_boxTransportStrictJointCylinderVector hleft,
    timeTranslate_boxTransportStrictJointCylinderVector hright] at hcontract
  exact (CReal.leEv_congr htarget hsource).mp hcontract

def strictJointCylinderStageTimeTranslateNonexpansive
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (shift : Nat) :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).Nonexpansive where
  toFun := StrictJointCylinderStage.timeTranslate shift
  contraction := strictJointCylinderStage_timeTranslate_nonexpansive
    hcoupling hle shift

/-- The staged action satisfies the semigroup laws modulo exactly the radical
used by the constructive completion. -/
def strictJointCylinderStageNonexpansiveSemigroup
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).NonexpansiveSemigroup where
  op := strictJointCylinderStageTimeTranslateNonexpansive hcoupling hle
  zero_law := by
    intro stage
    exact strictJointCylinderStageEquivalent_reflectionDistSq_zero
      hcoupling hle (strictJointCylinderStage_timeTranslate_zero stage)
  add_law := by
    intro first second stage
    rw [Nat.add_comm first second]
    exact strictJointCylinderStageEquivalent_reflectionDistSq_zero
      hcoupling hle
      (strictJointCylinderStage_timeTranslate_add second first stage)

/-- The completed strict OS carrier built from all finite bases at once. -/
def StrictJointCylinderOSCompletion
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) : Type :=
  (strictJointCylinderStageSquaredSeminorm hcoupling hle).Completion

/-- The actual time-semigroup operator on the completed strict OS carrier. -/
def strictJointCylinderCompletedTimeTranslate
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (shift : Nat) :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle :=
  ((strictJointCylinderStageNonexpansiveSemigroup hcoupling hle).op shift).completionMap

theorem strictJointCylinderCompletedTimeTranslate_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle 0 vector = vector :=
  (strictJointCylinderStageNonexpansiveSemigroup
    hcoupling hle).completionMap_zero vector

theorem strictJointCylinderCompletedTimeTranslate_add
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle
        (first + second) vector =
      strictJointCylinderCompletedTimeTranslate hcoupling hle first
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle second vector) :=
  (strictJointCylinderStageNonexpansiveSemigroup
    hcoupling hle).completionMap_add first second vector

/-- Canonical base transports have the same dense vector in the completed
carrier, so the algebraic direct-limit relation is genuinely respected. -/
theorem strictJointCylinderCompletion_embed_eq_of_stageEquivalent
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {left right : StrictJointCylinderStage}
    (h : StrictJointCylinderStageEquivalent left right) :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep left =
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep right :=
  (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep_eq_of_null
    (strictJointCylinderStageEquivalent_reflectionDistSq_zero
      hcoupling hle h)

#print axioms boxTransportStrictJointCylinderVector_reflectionDistSq_equiv
#print axioms strictJointCylinderStageReflectionDistSq_at_common
#print axioms strictJointCylinderStageEquivalent_reflectionDistSq_zero
#print axioms strictJointCylinderStageReflectionDistSq_triangle
#print axioms strictJointCylinderStageReflectionDistSq_null_congr
#print axioms strictJointCylinderStageSquaredSeminorm
#print axioms strictJointCylinderStage_timeTranslate_nonexpansive
#print axioms strictJointCylinderStageNonexpansiveSemigroup
#print axioms strictJointCylinderCompletedTimeTranslate_zero
#print axioms strictJointCylinderCompletedTimeTranslate_add
#print axioms strictJointCylinderCompletion_embed_eq_of_stageEquivalent

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
