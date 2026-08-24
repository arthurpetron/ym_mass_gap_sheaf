/-
# Cofinal non-vacuum escape ceiling for the all-spin vacuum star

The exact row split reduces a uniform spin-ray return floor to one quantitative
statement: at every sufficiently large cutoff, all non-vacuum target mass in
each admitted excited spin row is bounded by one fixed nonnegative multiple of
that row's vacuum joint entry.

This module states that missing estimate as honest Type-level data and compiles
it into the previously defined cofinal return-floor and ray-capacity
certificates.  The compiler is lossless apart from the exact transformation
`C |-> 1 / (1 + C)`.  No inhabitant of the escape-ceiling datum is supplied.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass
import YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor

/-! ## 1. The exact named analytic datum -/

/-- A cutoff-independent ceiling on the ratio of all non-vacuum escape mass
to the vacuum joint entry, uniformly over the admitted all-spin ray.  This
structure is intentionally uninhabited in this module. -/
structure FixedNomeCofinalSpinCubeEscapeRatioCeiling
    {w : Q'} (hw : (0 : Q') < w) : Type where
  ceiling : Q'
  ceiling_nonnegative : (0 : Q') ≤ ceiling
  start : Nat
  escape_le : ∀ K, start ≤ K →
    ∀ offset, (hoffset : offset < K) →
      centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset ≤
        ceiling *
          centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K offset) 0

namespace FixedNomeCofinalSpinCubeEscapeRatioCeiling

/-! ## 2. Pointwise and finite-minimum return floors -/

def returnFloor {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw) : Q' :=
  spinCubeEscapeReturnFloor family.ceiling family.ceiling_nonnegative

theorem returnFloor_pos {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw) :
    (0 : Q') < family.returnFloor :=
  spinCubeEscapeReturnFloor_pos
    family.ceiling family.ceiling_nonnegative

theorem returnFloor_le_one {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw) :
    family.returnFloor ≤ 1 :=
  spinCubeEscapeReturnFloor_le_one
    family.ceiling family.ceiling_nonnegative

theorem returnFloor_le_return
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw)
    {K : Nat} (hK : family.start ≤ K)
    {offset : Nat} (hoffset : offset < K) :
    family.returnFloor ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset :=
  spinCubeEscapeReturnFloor_le_return_of_escape_le
    hw hoffset family.ceiling family.ceiling_nonnegative
    (family.escape_le K hK offset hoffset)

private theorem le_listPositiveMinOne_of_forall_local
    {State : Type} (value : State → Q') (candidate : Q') :
    ∀ states : List State,
      candidate ≤ 1 →
      (∀ state, state ∈ states → candidate ≤ value state) →
      candidate ≤ listPositiveMinOne value states
  | [], hunit, _hall => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact le_listPositiveMinOne_of_forall_local
          value candidate rest hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))

theorem returnFloor_le_finiteReturnFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw)
    (K : Nat) (hK : family.start ≤ K) :
    family.returnFloor ≤
      centralLowerExcitedSpinCubeReturnFloor hw K := by
  unfold centralLowerExcitedSpinCubeReturnFloor
  apply le_listPositiveMinOne_of_forall_local
  · exact family.returnFloor_le_one
  · intro offset hoffsetMem
    have hoffset : offset < K := List.mem_range.mp hoffsetMem
    simpa [centralLowerExcitedSpinCubeReturnCandidate, hoffset] using
      family.returnFloor_le_return hK hoffset

/-! ## 3. Lossless compilation to the existing cofinal capacity frontier -/

def toCofinalRayReturnFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw) :
    FixedNomeCofinalSpinCubeRayReturnFloor hw where
  floor := family.returnFloor
  floor_pos := family.returnFloor_pos
  start := family.start
  floor_le := fun K hK => family.returnFloor_le_finiteReturnFloor K hK

def finiteRayCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K :=
  family.toCofinalRayReturnFloor.finiteCapacityAt K hK

def toCofinalRayCapacity
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw) :
    FixedNomeCofinalSpinCubeRayCapacity hw :=
  family.toCofinalRayReturnFloor.toCofinalRayCapacity

end FixedNomeCofinalSpinCubeEscapeRatioCeiling

end YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling.FixedNomeCofinalSpinCubeEscapeRatioCeiling.returnFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling.FixedNomeCofinalSpinCubeEscapeRatioCeiling.returnFloor_le_return
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling.FixedNomeCofinalSpinCubeEscapeRatioCeiling.returnFloor_le_finiteReturnFloor
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling.FixedNomeCofinalSpinCubeEscapeRatioCeiling.toCofinalRayReturnFloor
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling.FixedNomeCofinalSpinCubeEscapeRatioCeiling.finiteRayCapacityAt
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling.FixedNomeCofinalSpinCubeEscapeRatioCeiling.toCofinalRayCapacity
