/-
# Split cutoff-two new-shell mass into a controlled tail and component mergers

The stationary mass outside the embedded cutoff-two vacuum component has two
causally different sources.  A later vacuum-sector state may lie outside the
entire cutoff-two positive carrier, or it may already be a positive
cutoff-two state belonging to another component and only later join the
vacuum component.  The first contribution is controlled by the existing
corrected-slab cutoff increment; the second is a genuine component-merger
mass.

This module defines the two disjoint index lists, proves their exact mass
decomposition, and bounds the outside-positive-carrier contribution by the
existing stationary source tail.  It does not bound component-merger mass,
inhabit the cofinal edge-floor payment, construct a thermodynamic/continuum
limit, or prove the Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment
import YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two disjoint parts of the new block -/

def cutoffTwoNewStateOutsidePositiveCarrierB
    (later index : Nat) : Bool :=
  centralPhysicalPositiveSourceOutsideB
    cutoffTwoHalfCoupling (by decide) 2 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 index)

def cutoffTwoNewOutsidePositiveIndices (later : Nat) : List Nat :=
  (cutoffTwoEdgeLoadNewStates later).filter
    (cutoffTwoNewStateOutsidePositiveCarrierB later)

def cutoffTwoNewComponentMergerIndices (later : Nat) : List Nat :=
  (cutoffTwoEdgeLoadNewStates later).filter
    (fun index => !(cutoffTwoNewStateOutsidePositiveCarrierB later index))

def cutoffTwoNewOutsidePositiveMass (later : Nat) : Q' :=
  finiteWeightedMass
    (cutoffTwoNewOutsidePositiveIndices later)
    (cutoffTwoEdgeLoadWeight later)

def cutoffTwoNewComponentMergerMass (later : Nat) : Q' :=
  finiteWeightedMass
    (cutoffTwoNewComponentMergerIndices later)
    (cutoffTwoEdgeLoadWeight later)

theorem cutoffTwoNewMass_eqv_outside_add_componentMerger
    (later : Nat) :
    cutoffTwoNewMass later ≈
      cutoffTwoNewOutsidePositiveMass later +
        cutoffTwoNewComponentMergerMass later := by
  unfold cutoffTwoNewMass cutoffTwoNewOutsidePositiveMass
    cutoffTwoNewComponentMergerMass cutoffTwoNewOutsidePositiveIndices
    cutoffTwoNewComponentMergerIndices finiteWeightedMass
    cutoffTwoEdgeLoadWeight cutoffTwoEdgeLoadNewStates
  exact listQSum_filter_partition _ _ _

theorem cutoffTwoNewOutsidePositiveMass_nonnegative (later : Nat) :
    (0 : Q') ≤ cutoffTwoNewOutsidePositiveMass later := by
  unfold cutoffTwoNewOutsidePositiveMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _hindex
  exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _

theorem cutoffTwoNewComponentMergerMass_nonnegative (later : Nat) :
    (0 : Q') ≤ cutoffTwoNewComponentMergerMass later := by
  unfold cutoffTwoNewComponentMergerMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _hindex
  exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _

/-! ## 2. The outside-positive part embeds in the global stationary tail -/

private def cutoffTwoFullOutsidePositiveIndices (later : Nat) : List Nat :=
  (List.range
    (centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) later 0)).filter
    (cutoffTwoNewStateOutsidePositiveCarrierB later)

private theorem cutoffTwoNewOutsidePositiveIndices_nodup (later : Nat) :
    (cutoffTwoNewOutsidePositiveIndices later).Nodup := by
  unfold cutoffTwoNewOutsidePositiveIndices cutoffTwoEdgeLoadNewStates
  exact List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorNewBlockIndices_nodup
      cutoffTwoHalfCoupling (by decide) 2 later 0)

private theorem cutoffTwoNewOutsidePositiveIndices_mem_fullOutside
    {later index : Nat}
    (hindex : index ∈ cutoffTwoNewOutsidePositiveIndices later) :
    index ∈ cutoffTwoFullOutsidePositiveIndices later := by
  have hparts := List.mem_filter.mp hindex
  have hnew := hparts.1
  have hsector :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hnew).1
  have hlt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) later 0 hsector
  unfold cutoffTwoFullOutsidePositiveIndices
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hlt, hparts.2⟩

theorem cutoffTwoNewOutsidePositiveMass_le_fullOutsideIndexedMass
    (later : Nat) :
    cutoffTwoNewOutsidePositiveMass later ≤
      listQSum
        (cutoffTwoEdgeLoadWeight later)
        (cutoffTwoFullOutsidePositiveIndices later) := by
  unfold cutoffTwoNewOutsidePositiveMass finiteWeightedMass
  apply listQSum_le_of_injective
    (cutoffTwoNewOutsidePositiveIndices later)
    (cutoffTwoFullOutsidePositiveIndices later)
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadWeight later)
    (fun index => index)
  · exact cutoffTwoNewOutsidePositiveIndices_nodup later
  · intro index hindex
    exact cutoffTwoNewOutsidePositiveIndices_mem_fullOutside hindex
  · intro left _hleft right _hright heq
    exact heq
  · intro index _hindex
    exact Q'.le_refl' _
  · intro index _hindex
    exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _

theorem cutoffTwoFullOutsideIndexedMass_eqv_stationarySourceTail
    (later : Nat) :
    listQSum
        (cutoffTwoEdgeLoadWeight later)
        (cutoffTwoFullOutsidePositiveIndices later) ≈
      centralPhysicalRowMarginalOutsideBase
        cutoffTwoHalfCoupling (by decide) later 0 2 := by
  let states := centralPositiveHalfStates
    cutoffTwoHalfCoupling (by decide) later 0
  let stateAt := finiteListStateAt states zeroEdgeLabelling
  let row := centralPhysicalRowMarginal
    cutoffTwoHalfCoupling (by decide) later 0
  let test := centralPhysicalPositiveSourceOutsideB
    cutoffTwoHalfCoupling (by decide) 2 0
  let indexedTest : Nat → Bool := fun index => test (stateAt index)
  unfold cutoffTwoFullOutsidePositiveIndices
    cutoffTwoNewStateOutsidePositiveCarrierB
    cutoffTwoEdgeLoadWeight centralPhysicalFiniteWeight
    centralPhysicalFiniteStateAt centralPhysicalFiniteCarrierSize
  change listQSum (fun index => row (stateAt index))
      ((List.range states.length).filter indexedTest) ≈
    centralPhysicalRowMarginalOutsideBase
      cutoffTwoHalfCoupling (by decide) later 0 2
  refine Q'.eqv_trans _
    (listQSum
      (finiteMaskedValue indexedTest (fun index => row (stateAt index)))
      (List.range states.length)) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_finiteMaskedValue_eqv_filter
        indexedTest (fun index => row (stateAt index))
        (List.range states.length))
  refine Q'.eqv_trans _
    (listQSum
      (fun index => finiteMaskedValue test row (stateAt index))
      (List.range states.length)) _ ?_ ?_
  · apply listQSum_congr
    intro index
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum (finiteMaskedValue test row) states) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum
        states zeroEdgeLabelling (finiteMaskedValue test row))
  refine Q'.eqv_trans _
    (listQSum row (states.filter test)) _ ?_ ?_
  · exact listQSum_finiteMaskedValue_eqv_filter test row states
  · exact Q'.eqv_refl _

theorem cutoffTwoNewOutsidePositiveMass_le_stationarySourceTail
    (later : Nat) :
    cutoffTwoNewOutsidePositiveMass later ≤
      centralPhysicalRowMarginalOutsideBase
        cutoffTwoHalfCoupling (by decide) later 0 2 :=
  Q'.le_trans' _ _ _
    (cutoffTwoNewOutsidePositiveMass_le_fullOutsideIndexedMass later)
    (Q'.le_of_eqv
      (cutoffTwoFullOutsideIndexedMass_eqv_stationarySourceTail later))

/-! ## 3. Corrected-slab control leaves only component-merger mass -/

theorem cutoffTwoNewOutsidePositiveMass_le_increment
    {later : Nat} (hcutoff : 2 ≤ later) :
    cutoffTwoNewOutsidePositiveMass later ≤
      slabParametricKCutoffIncrement
        cutoffTwoHalfCoupling 2 later (centralExtent 0) :=
  Q'.le_trans' _ _ _
    (cutoffTwoNewOutsidePositiveMass_le_stationarySourceTail later)
    (centralPhysicalRowMarginalOutsideBase_le_increment
      (w := cutoffTwoHalfCoupling) (half := 0) (by decide) hcutoff)

theorem cutoffTwoNewMass_le_increment_add_componentMerger
    {later : Nat} (hcutoff : 2 ≤ later) :
    cutoffTwoNewMass later ≤
      slabParametricKCutoffIncrement
          cutoffTwoHalfCoupling 2 later (centralExtent 0) +
        cutoffTwoNewComponentMergerMass later := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoNewMass_eqv_outside_add_componentMerger later)) ?_
  exact Q'.add_le_add_right _ _ _
    (cutoffTwoNewOutsidePositiveMass_le_increment hcutoff)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewMass_eqv_outside_add_componentMerger
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewOutsidePositiveMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewComponentMergerMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewOutsidePositiveMass_le_fullOutsideIndexedMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoFullOutsideIndexedMass_eqv_stationarySourceTail
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewOutsidePositiveMass_le_stationarySourceTail
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewOutsidePositiveMass_le_increment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.cutoffTwoNewMass_le_increment_add_componentMerger
