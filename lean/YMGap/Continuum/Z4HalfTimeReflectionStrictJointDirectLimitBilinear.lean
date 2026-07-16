/-
# The strict reflection form on the algebraic base direct limit

The limiting strict reflection form is only representation-invariant up to
constructive-real equivalence.  Its natural codomain on the algebraic direct
limit is therefore `CReal.RC`.  This module evaluates a staged pair in its
maximum common base, proves independence from every larger common box and from
both direct-limit representatives, and descends the pairing by quotient lift.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

theorem boxTransportStrictJointCylinderVector_reflectionBilinear_equiv_of_le
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base outer : Nat} (hbase : base <= outer)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector hbase left)
        (boxTransportStrictJointCylinderVector hbase right))
      (strictJointCylinderReflectionBilinear hcoupling hle left right) := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_reflectionBilinear_equiv
    hcoupling hle padding left right

/-- The strict reflection pairing of staged vectors, evaluated in their
canonical maximum common box. -/
def strictJointCylinderStageReflectionBilinear
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_left left.base right.base) left.vector)
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_right left.base right.base) right.vector)

theorem strictJointCylinderStageReflectionBilinear_at_common
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage)
    {outer : Nat} (hleft : left.base <= outer)
    (hright : right.base <= outer) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector hleft left.vector)
        (boxTransportStrictJointCylinderVector hright right.vector))
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right) := by
  have hmax : max left.base right.base <= outer :=
    Nat.max_le.mpr ⟨hleft, hright⟩
  have hleftTrans := boxTransportStrictJointCylinderVector_trans
    (Nat.le_max_left left.base right.base) hmax left.vector
  have hrightTrans := boxTransportStrictJointCylinderVector_trans
    (Nat.le_max_right left.base right.base) hmax right.vector
  change CReal.Equiv
    (strictJointCylinderReflectionBilinear hcoupling hle
      (boxTransportStrictJointCylinderVector hleft left.vector)
      (boxTransportStrictJointCylinderVector hright right.vector))
    (strictJointCylinderReflectionBilinear hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_left left.base right.base) left.vector)
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_right left.base right.base) right.vector))
  rw [← hleftTrans, ← hrightTrans]
  exact boxTransportStrictJointCylinderVector_reflectionBilinear_equiv_of_le
    hcoupling hle hmax
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_left left.base right.base) left.vector)
      (boxTransportStrictJointCylinderVector
        (Nat.le_max_right left.base right.base) right.vector)

/-- Both staged arguments may be replaced by algebraically direct-limit
equivalent representatives. -/
theorem strictJointCylinderStageReflectionBilinear_congr
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {left left' right right' : StrictJointCylinderStage}
    (hleftEq : StrictJointCylinderStageEquivalent left left')
    (hrightEq : StrictJointCylinderStageEquivalent right right') :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle left right)
      (strictJointCylinderStageReflectionBilinear hcoupling hle left' right') := by
  rcases hleftEq with ⟨leftCommon, hleft, hleft', heqLeft⟩
  rcases hrightEq with ⟨rightCommon, hright, hright', heqRight⟩
  let outer := max leftCommon rightCommon
  have hleftCommonOuter : leftCommon <= outer := Nat.le_max_left _ _
  have hrightCommonOuter : rightCommon <= outer := Nat.le_max_right _ _
  have hL : left.base <= outer := Nat.le_trans hleft hleftCommonOuter
  have hLp : left'.base <= outer := Nat.le_trans hleft' hleftCommonOuter
  have hR : right.base <= outer := Nat.le_trans hright hrightCommonOuter
  have hRp : right'.base <= outer := Nat.le_trans hright' hrightCommonOuter
  have heqL :
      boxTransportStrictJointCylinderVector hL left.vector =
        boxTransportStrictJointCylinderVector hLp left'.vector := by
    calc
      boxTransportStrictJointCylinderVector hL left.vector =
          boxTransportStrictJointCylinderVector hleftCommonOuter
            (boxTransportStrictJointCylinderVector hleft left.vector) :=
        (boxTransportStrictJointCylinderVector_trans
          hleft hleftCommonOuter left.vector).symm
      _ = boxTransportStrictJointCylinderVector hleftCommonOuter
            (boxTransportStrictJointCylinderVector hleft' left'.vector) :=
        congrArg (boxTransportStrictJointCylinderVector hleftCommonOuter) heqLeft
      _ = boxTransportStrictJointCylinderVector hLp left'.vector :=
        boxTransportStrictJointCylinderVector_trans
          hleft' hleftCommonOuter left'.vector
  have heqR :
      boxTransportStrictJointCylinderVector hR right.vector =
        boxTransportStrictJointCylinderVector hRp right'.vector := by
    calc
      boxTransportStrictJointCylinderVector hR right.vector =
          boxTransportStrictJointCylinderVector hrightCommonOuter
            (boxTransportStrictJointCylinderVector hright right.vector) :=
        (boxTransportStrictJointCylinderVector_trans
          hright hrightCommonOuter right.vector).symm
      _ = boxTransportStrictJointCylinderVector hrightCommonOuter
            (boxTransportStrictJointCylinderVector hright' right'.vector) :=
        congrArg (boxTransportStrictJointCylinderVector hrightCommonOuter) heqRight
      _ = boxTransportStrictJointCylinderVector hRp right'.vector :=
        boxTransportStrictJointCylinderVector_trans
          hright' hrightCommonOuter right'.vector
  have hfirst := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left right hL hR
  have hsecond := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left' right' hLp hRp
  apply CReal.Equiv.trans (CReal.Equiv.symm hfirst)
  rw [heqL, heqR]
  exact hsecond

/-- The `RC`-valued reflection pairing on the algebraic direct limit. -/
def StrictJointCylinderDirectLimit.reflectionBilinear
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderDirectLimit -> StrictJointCylinderDirectLimit -> CReal.RC :=
  Quotient.lift₂
    (fun left right => Quotient.mk CReal.crealSetoid
      (strictJointCylinderStageReflectionBilinear hcoupling hle left right))
    (fun _ _ _ _ hleft hright => Quotient.sound
      (strictJointCylinderStageReflectionBilinear_congr
        hcoupling hle hleft hright))

@[simp] theorem strictJointCylinderDirectLimit_reflectionBilinear_embed
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        (StrictJointCylinderDirectLimit.embed left)
        (StrictJointCylinderDirectLimit.embed right) =
      Quotient.mk CReal.crealSetoid
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left right) := rfl

#print axioms boxTransportStrictJointCylinderVector_reflectionBilinear_equiv_of_le
#print axioms strictJointCylinderStageReflectionBilinear_at_common
#print axioms strictJointCylinderStageReflectionBilinear_congr
#print axioms StrictJointCylinderDirectLimit.reflectionBilinear

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
