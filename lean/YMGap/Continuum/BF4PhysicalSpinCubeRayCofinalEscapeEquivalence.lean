/-
# Equivalence of the cofinal return-floor and escape-ceiling frontiers

A fixed escape-ratio ceiling already compiles to a positive cofinal return
floor.  Conversely, a positive cofinal return floor bounds the non-vacuum
escape by the reciprocal of that floor times the vacuum joint entry.  Thus
the two named frontiers are equivalent up to explicit constructive rational
recodings; the escape formulation does not hide an easier analytic premise.

Neither frontier datum is inhabited here.  No full-sector, completed,
thermodynamic, continuum, or Clay conclusion is asserted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling

namespace YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeCeiling
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayEscapeMass
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes

local infix:50 " ≈ " => Q'.eqv

namespace ReturnFloorCompiler

/-! ## 1. A cofinal return floor gives a cofinal escape ceiling -/

def escapeCeiling {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) : Q' :=
  Q'.recipPos family.floor family.floor_pos

theorem escapeCeiling_pos {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) :
    (0 : Q') < escapeCeiling family :=
  Q'.recipPos_pos family.floor family.floor_pos

theorem escape_le_ceiling_mul_vacuumJoint
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw)
    {K : Nat} (hK : family.start ≤ K)
    {offset : Nat} (hoffset : offset < K) :
    centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset ≤
      escapeCeiling family *
        centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) 0 := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let joint := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 index 0
  let escape := centralLowerExcitedSpinCubeNonVacuumEscapeMass hw K offset
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 index
  let returnProbability :=
    centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset
  have hfloorReturn : family.floor ≤ returnProbability :=
    Q'.le_trans' _ _ _ (family.floor_le K hK)
      (centralLowerExcitedSpinCubeReturnFloor_le hw hoffset)
  have hweight0 : (0 : Q') ≤ weight :=
    Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
  have hscaled : family.floor * weight ≤ returnProbability * weight :=
    Q'.mul_le_mul_of_nonneg_right
      family.floor returnProbability weight hfloorReturn hweight0
  have hreturnWeight : returnProbability * weight ≈ joint :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv returnProbability weight)
      (centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
        hw hoffset)
  have hfloorWeight : family.floor * weight ≤ joint :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hreturnWeight)
  have hescapeWeight : escape ≤ weight :=
    centralLowerExcitedSpinCubeNonVacuumEscapeMass_le_weight hw hoffset
  have hfloor0 : (0 : Q') ≤ family.floor :=
    Q'.le_of_lt family.floor_pos
  have hfloorEscape : family.floor * escape ≤ joint :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        escape weight family.floor hescapeWeight hfloor0)
      hfloorWeight
  have hescapeDiv :
      escape ≤ Q'.divPos joint family.floor family.floor_pos := by
    apply Q'.le_divPos_of_mul_le joint family.floor family.floor_pos
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv escape family.floor))
      hfloorEscape
  exact Q'.le_trans' _ _ _ hescapeDiv
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv joint (escapeCeiling family)))

def toCofinalEscapeRatioCeiling
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) :
    FixedNomeCofinalSpinCubeEscapeRatioCeiling hw where
  ceiling := escapeCeiling family
  ceiling_nonnegative := Q'.le_of_lt (escapeCeiling_pos family)
  start := family.start
  escape_le := fun _K hK _offset hoffset =>
    escape_le_ceiling_mul_vacuumJoint family hK hoffset

end ReturnFloorCompiler

/-! ## 2. Type-level equivalence of the named frontier data -/

def returnFloorToEscapeCeilingToReturnFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeRayReturnFloor hw) :
    FixedNomeCofinalSpinCubeRayReturnFloor hw :=
  (ReturnFloorCompiler.toCofinalEscapeRatioCeiling family).toCofinalRayReturnFloor

def escapeCeilingToReturnFloorToEscapeCeiling
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeEscapeRatioCeiling hw) :
    FixedNomeCofinalSpinCubeEscapeRatioCeiling hw :=
  ReturnFloorCompiler.toCofinalEscapeRatioCeiling
    family.toCofinalRayReturnFloor

end YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence.ReturnFloorCompiler.escapeCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence.ReturnFloorCompiler.escape_le_ceiling_mul_vacuumJoint
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence.ReturnFloorCompiler.toCofinalEscapeRatioCeiling
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence.returnFloorToEscapeCeilingToReturnFloor
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalEscapeEquivalence.escapeCeilingToReturnFloorToEscapeCeiling
