/-
# Linear operations on the completed physical bond sources

Each operation constructs its original time-range witness before quotienting.
The exact original-vector pins supply the derivative and resolvent consumers
on this SAME bond completion. No representative is chosen from a quotient,
and no original time-zero multiplier is restricted to the sector.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSTime
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completedRealSmul)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State stateSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion Rows rowSetoid toSectorRep fromSector toSector_fromSector
    close_iff_limit_eq)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue sectorValue bondValue_injective)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "Sector" => State hw0 hw1 (width := width)
local notation "Class" => Quotient.mk (rowSetoid hw0 hw1 (width := width))

/-- The existing inverse completion map consumes actual range data. -/
def ofState (x : Sector) : H :=
  fromSector hw0 hw1 (Quotient.mk (stateSetoid hw0 hw1) x)

theorem bondValue_ofState (x : Sector) :
    bondValue hw0 hw1 (ofState hw0 hw1 x) = x.val := by
  unfold ofState bondValue
  rw [toSector_fromSector]
  rfl

theorem ofState_congr {x y : Sector} (h : x.val = y.val) :
    ofState hw0 hw1 x = ofState hw0 hw1 y := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_ofState, bondValue_ofState, h]

def zero : H := ofState hw0 hw1 (BF4WilsonAllNomeTimeSector.zero hw0 hw1)

theorem bondValue_zero :
    bondValue hw0 hw1 (zero hw0 hw1 (width := width)) =
      completedZero hw0 hw1 width := bondValue_ofState hw0 hw1 _

def add : H → H → H :=
  Quotient.lift₂
    (fun X Y => ofState hw0 hw1 (BF4WilsonAllNomeTimeSector.add hw0 hw1
      (toSectorRep hw0 hw1 X) (toSectorRep hw0 hw1 Y)))
    (fun _ _ _ _ h k => by
      apply ofState_congr hw0 hw1
      dsimp only [BF4WilsonAllNomeTimeSector.add]
      rw [(close_iff_limit_eq hw0 hw1 _ _).mp h,
        (close_iff_limit_eq hw0 hw1 _ _).mp k])

theorem bondValue_add (x y : H) :
    bondValue hw0 hw1 (add hw0 hw1 x y) =
      completedAdd hw0 hw1 (bondValue hw0 hw1 x) (bondValue hw0 hw1 y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact bondValue_ofState hw0 hw1 _

def negate : H → H :=
  Quotient.lift
    (fun X => ofState hw0 hw1
      (BF4WilsonAllNomeTimeSector.negate hw0 hw1 (toSectorRep hw0 hw1 X)))
    (fun _ _ h => by
      apply ofState_congr hw0 hw1
      dsimp only [BF4WilsonAllNomeTimeSector.negate]
      rw [(close_iff_limit_eq hw0 hw1 _ _).mp h])

theorem bondValue_negate (x : H) :
    bondValue hw0 hw1 (negate hw0 hw1 x) =
      completedNeg hw0 hw1 (bondValue hw0 hw1 x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact bondValue_ofState hw0 hw1 _

def sub (x y : H) : H := add hw0 hw1 x (negate hw0 hw1 y)

theorem bondValue_sub (x y : H) :
    bondValue hw0 hw1 (sub hw0 hw1 x y) =
      completedSub hw0 hw1 (bondValue hw0 hw1 x) (bondValue hw0 hw1 y) := by
  unfold sub
  rw [bondValue_add, bondValue_negate]
  rfl

private def rationalState (c : Q') (x : Sector) : Sector where
  val := completedSmul hw0 hw1 c x.val
  range := BF4WilsonAllNomeTimeRangeLinear.rationalSmul hw0 hw1 c x.range

def smul (c : Q') : H → H :=
  Quotient.lift
    (fun X => ofState hw0 hw1 (rationalState hw0 hw1 c (toSectorRep hw0 hw1 X)))
    (fun _ _ h => by
      apply ofState_congr hw0 hw1
      dsimp only [rationalState]
      rw [(close_iff_limit_eq hw0 hw1 _ _).mp h])

theorem bondValue_smul (c : Q') (x : H) :
    bondValue hw0 hw1 (smul hw0 hw1 c x) =
      completedSmul hw0 hw1 c (bondValue hw0 hw1 x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact bondValue_ofState hw0 hw1 _

/-- Real scalars retain the supplied constructive Cauchy modulus. -/
def realSmul (s : CReal) (cs : QCauchy s.approx) : H → H :=
  Quotient.lift
    (fun X => ofState hw0 hw1
      (BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 s cs (toSectorRep hw0 hw1 X)))
    (fun _ _ h => by
      apply ofState_congr hw0 hw1
      dsimp only [BF4WilsonAllNomeTimeSector.realSmul]
      rw [(close_iff_limit_eq hw0 hw1 _ _).mp h])

theorem bondValue_realSmul (s : CReal) (cs : QCauchy s.approx) (x : H) :
    bondValue hw0 hw1 (realSmul hw0 hw1 s cs x) =
      completedRealSmul hw0 hw1 s cs (bondValue hw0 hw1 x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact bondValue_ofState hw0 hw1 _

#print axioms ofState
#print axioms bondValue_ofState
#print axioms ofState_congr
#print axioms bondValue_zero
#print axioms bondValue_add
#print axioms bondValue_negate
#print axioms bondValue_sub
#print axioms bondValue_smul
#print axioms bondValue_realSmul

end YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
