/-
# Generic moving-base split of physical vacuum-sector new mass

For arbitrary `base <= later`, the later vacuum component outside the
embedded base component has two stationary-mass sources.  A state may be
outside the entire positive base carrier, or it may already be positive at the
base cutoff in another connected component and join the vacuum component only
later.

This file defines those two exact lists and masses, proves their partition of
generic new-block mass, and bounds the outside-positive contribution by the
local corrected-slab cutoff increment from `base` to `later`.  Only the
component-merger mass remains as an explicit moving-base residual.

No merger-mass ceiling, capacity comparison, cofinal schedule,
thermodynamic/continuum construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth
import YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic new mass and its two semantic parts -/

def centralPhysicalFiniteVacuumSectorNewMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half)
    (centralPhysicalFiniteWeight w hw later half)

def centralPhysicalFiniteNewStateOutsideBasePositiveB
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half index : Nat) : Bool :=
  centralPhysicalPositiveSourceOutsideB w hw base half
    (centralPhysicalFiniteStateAt w hw later half index)

def centralPhysicalFiniteNewOutsideBasePositiveIndices
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half).filter
    (centralPhysicalFiniteNewStateOutsideBasePositiveB
      w hw base later half)

def centralPhysicalFiniteNewComponentMergerIndices
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half).filter
    (fun index =>
      !(centralPhysicalFiniteNewStateOutsideBasePositiveB
        w hw base later half index))

def centralPhysicalFiniteNewOutsideBasePositiveMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteNewOutsideBasePositiveIndices
      w hw base later half)
    (centralPhysicalFiniteWeight w hw later half)

def centralPhysicalFiniteNewComponentMergerMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteNewComponentMergerIndices
      w hw base later half)
    (centralPhysicalFiniteWeight w hw later half)

theorem centralPhysicalFiniteVacuumSectorNewMass_eqv_outside_add_merger
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteVacuumSectorNewMass
        w hw base later half ≈
      centralPhysicalFiniteNewOutsideBasePositiveMass
          w hw base later half +
        centralPhysicalFiniteNewComponentMergerMass
          w hw base later half := by
  unfold centralPhysicalFiniteVacuumSectorNewMass
    centralPhysicalFiniteNewOutsideBasePositiveMass
    centralPhysicalFiniteNewComponentMergerMass
    centralPhysicalFiniteNewOutsideBasePositiveIndices
    centralPhysicalFiniteNewComponentMergerIndices finiteWeightedMass
  exact listQSum_filter_partition _ _ _

theorem centralPhysicalFiniteNewOutsideBasePositiveMass_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteNewOutsideBasePositiveMass
      w hw base later half := by
  unfold centralPhysicalFiniteNewOutsideBasePositiveMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _
  unfold centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative hw later half _

theorem centralPhysicalFiniteNewComponentMergerMass_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteNewComponentMergerMass
      w hw base later half := by
  unfold centralPhysicalFiniteNewComponentMergerMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _
  unfold centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative hw later half _

/-! ## 2. Exact state semantics of the merger residual -/

theorem mem_centralPhysicalFiniteNewComponentMergerIndices_iff
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat} :
    index ∈ centralPhysicalFiniteNewComponentMergerIndices
        w hw base later half ↔
      index ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half ∧
        labelWithinB base (centralLowerFaceIds half)
            (centralPhysicalFiniteStateAt w hw later half index) = true ∧
          (0 : Q') < centralPhysicalRowMarginal w hw base half
            (centralPhysicalFiniteStateAt w hw later half index) := by
  constructor
  · intro hmerger
    have hparts := List.mem_filter.mp hmerger
    have houtsideFalse :
        centralPhysicalFiniteNewStateOutsideBasePositiveB
          w hw base later half index = false := by
      cases houtside :
          centralPhysicalFiniteNewStateOutsideBasePositiveB
            w hw base later half index with
      | false => rfl
      | true =>
          rw [houtside] at hparts
          exact False.elim
            ((by decide : (false : Bool) ≠ true) hparts.2)
    unfold centralPhysicalFiniteNewStateOutsideBasePositiveB
      centralPhysicalPositiveSourceOutsideB at houtsideFalse
    cases hand :
        (labelWithinB base (centralLowerFaceIds half)
            (centralPhysicalFiniteStateAt w hw later half index) &&
          decide ((0 : Q') < centralPhysicalRowMarginal w hw base half
            (centralPhysicalFiniteStateAt w hw later half index))) with
    | false =>
        rw [hand] at houtsideFalse
        exact False.elim
          ((by decide : (true : Bool) ≠ false) houtsideFalse)
    | true =>
        have hinside := Bool.and_eq_true_iff.mp hand
        exact ⟨hparts.1, hinside.1,
          (decide_eq_true_eq.mp hinside.2)⟩
  · rintro ⟨hnew, hwithin, hrow⟩
    apply List.mem_filter.mpr
    refine ⟨hnew, ?_⟩
    have hdecision : decide ((0 : Q') <
        centralPhysicalRowMarginal w hw base half
          (centralPhysicalFiniteStateAt w hw later half index)) = true :=
      decide_eq_true hrow
    unfold centralPhysicalFiniteNewStateOutsideBasePositiveB
      centralPhysicalPositiveSourceOutsideB
    simp only [hwithin, hdecision, Bool.true_and, Bool.not_true,
      Bool.not_false]

/-! ## 3. The outside-positive part embeds in the global stationary tail -/

private def centralPhysicalFiniteFullOutsideBasePositiveIndices
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : List Nat :=
  (List.range (centralPhysicalFiniteCarrierSize w hw later half)).filter
    (centralPhysicalFiniteNewStateOutsideBasePositiveB
      w hw base later half)

private theorem centralPhysicalFiniteNewOutsideBasePositiveIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (centralPhysicalFiniteNewOutsideBasePositiveIndices
      w hw base later half).Nodup := by
  unfold centralPhysicalFiniteNewOutsideBasePositiveIndices
  exact List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorNewBlockIndices_nodup
      w hw base later half)

private theorem centralPhysicalFiniteNewOutsideBasePositiveIndices_mem_full
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hindex : index ∈ centralPhysicalFiniteNewOutsideBasePositiveIndices
      w hw base later half) :
    index ∈ centralPhysicalFiniteFullOutsideBasePositiveIndices
      w hw base later half := by
  have hparts := List.mem_filter.mp hindex
  have hsector :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp
      hparts.1).1
  have hlt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw later half hsector
  unfold centralPhysicalFiniteFullOutsideBasePositiveIndices
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hlt, hparts.2⟩

theorem centralPhysicalFiniteNewOutsideBasePositiveMass_le_fullIndexedMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteNewOutsideBasePositiveMass
        w hw base later half ≤
      listQSum (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteFullOutsideBasePositiveIndices
          w hw base later half) := by
  unfold centralPhysicalFiniteNewOutsideBasePositiveMass finiteWeightedMass
  apply listQSum_le_of_injective
    (centralPhysicalFiniteNewOutsideBasePositiveIndices
      w hw base later half)
    (centralPhysicalFiniteFullOutsideBasePositiveIndices
      w hw base later half)
    (centralPhysicalFiniteWeight w hw later half)
    (centralPhysicalFiniteWeight w hw later half)
    (fun index => index)
  · exact centralPhysicalFiniteNewOutsideBasePositiveIndices_nodup
      w hw base later half
  · intro index hindex
    exact centralPhysicalFiniteNewOutsideBasePositiveIndices_mem_full hindex
  · intro _ _ _ _ heq
    exact heq
  · intro _ _
    exact Q'.le_refl' _
  · intro index _
    unfold centralPhysicalFiniteWeight
    exact centralPhysicalRowMarginal_nonnegative hw later half _

theorem centralPhysicalFiniteFullOutsideBasePositiveIndexedMass_eqv_tail
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    listQSum (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteFullOutsideBasePositiveIndices
          w hw base later half) ≈
      centralPhysicalRowMarginalOutsideBase
        w hw later half base := by
  let states := centralPositiveHalfStates w hw later half
  let stateAt := finiteListStateAt states zeroEdgeLabelling
  let row := centralPhysicalRowMarginal w hw later half
  let test := centralPhysicalPositiveSourceOutsideB w hw base half
  let indexedTest : Nat → Bool := fun index => test (stateAt index)
  unfold centralPhysicalFiniteFullOutsideBasePositiveIndices
    centralPhysicalFiniteNewStateOutsideBasePositiveB
    centralPhysicalFiniteWeight centralPhysicalFiniteStateAt
    centralPhysicalFiniteCarrierSize
  change listQSum (fun index => row (stateAt index))
      ((List.range states.length).filter indexedTest) ≈
    centralPhysicalRowMarginalOutsideBase w hw later half base
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

theorem centralPhysicalFiniteNewOutsideBasePositiveMass_le_tail
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteNewOutsideBasePositiveMass
        w hw base later half ≤
      centralPhysicalRowMarginalOutsideBase
        w hw later half base :=
  Q'.le_trans' _ _ _
    (centralPhysicalFiniteNewOutsideBasePositiveMass_le_fullIndexedMass
      w hw base later half)
    (Q'.le_of_eqv
      (centralPhysicalFiniteFullOutsideBasePositiveIndexedMass_eqv_tail
        w hw base later half))

/-! ## 4. Moving-base corrected-slab control leaves only merger mass -/

theorem centralPhysicalFiniteNewOutsideBasePositiveMass_le_increment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later) :
    centralPhysicalFiniteNewOutsideBasePositiveMass
        w hw base later half ≤
      slabParametricKCutoffIncrement
        w base later (centralExtent half) :=
  Q'.le_trans' _ _ _
    (centralPhysicalFiniteNewOutsideBasePositiveMass_le_tail
      w hw base later half)
    (centralPhysicalRowMarginalOutsideBase_le_increment hw hcutoff)

theorem centralPhysicalFiniteVacuumSectorNewMass_le_increment_add_merger
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later) :
    centralPhysicalFiniteVacuumSectorNewMass
        w hw base later half ≤
      slabParametricKCutoffIncrement
          w base later (centralExtent half) +
        centralPhysicalFiniteNewComponentMergerMass
          w hw base later half := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorNewMass_eqv_outside_add_merger
        w hw base later half)) ?_
  exact Q'.add_le_add_right _ _ _
    (centralPhysicalFiniteNewOutsideBasePositiveMass_le_increment hcutoff)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteVacuumSectorNewMass_eqv_outside_add_merger
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteNewOutsideBasePositiveMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteNewComponentMergerMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.mem_centralPhysicalFiniteNewComponentMergerIndices_iff
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteNewOutsideBasePositiveMass_le_fullIndexedMass
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteFullOutsideBasePositiveIndexedMass_eqv_tail
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteNewOutsideBasePositiveMass_le_increment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteVacuumSectorNewMass_le_increment_add_merger
