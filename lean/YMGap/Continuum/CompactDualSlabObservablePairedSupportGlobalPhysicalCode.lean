/-
# One aggregate physical-value code for the observable support

After the whole connected support has been encoded once, its decoded order
gives a common coordinate chart.  This module writes the left and right
twice-spin values at every decoded plaquette, producing two coordinates per
support site but only the actual total physical l1 mass.

For the canonical peeling trace of mass `M`, the support has at most `M`
sites and the paired value word has l1 mass at most `M`.  The asymmetric
weak-composition compiler therefore places it in one exact `8^M` carrier.
This is the physical-label factor of the global aggregate entropy budget.

No injectivity of the complete source code or auxiliary reconstruction is
asserted here.  Those require the remaining source-to-terminal locality and
auxiliary aggregate bridges.

Constructive contract: finite decoded lists and explicit natural-number
sums only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode
import YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPairedWeakCompositionCode
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. The shape decoder supplies a common support order -/

/-- Decode the global shape word from its fixed target plaquette. -/
def slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) : List Z4Plaq :=
  decode z4Chain (slabPlaquetteAt D.extent targetFaceId)
    (slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
      D rootFaceId targetFaceId htarget pair hpair massBudget)

theorem slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_sameSupport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    sameSupport (L := z4Chain.toLattice)
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId)
      (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
        D rootFaceId targetFaceId htarget pair hpair massBudget) :=
  slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_decode
    D rootFaceId targetFaceId htarget pair hpair massBudget

theorem slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
      D rootFaceId targetFaceId htarget pair hpair massBudget).Nodup := by
  unfold slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
  exact decode_nodup z4Chain _ _

/-- Every decoded coordinate is a literal corrected-slab plaquette. -/
theorem slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_boundary
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈
      slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
        D rootFaceId targetFaceId htarget pair hpair massBudget) :
    plaquette ∈ boundaryCompleteSlabPlaquettes D.extent := by
  have horiginal :=
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_sameSupport
      D rootFaceId targetFaceId htarget pair hpair massBudget).2
        plaquette hplaquette
  let faceId := slabObservableTwoReplicaPairTargetSupportFaceValue
    D pair targetFaceId plaquette
  have hface := slabObservableTwoReplicaPairTargetSupportFaceValue_mem
    D rootFaceId targetFaceId htarget pair hpair plaquette
  have hprojection :=
    slabObservableTwoReplicaPairTargetSupportFaceValue_projection
      D pair targetFaceId plaquette horiginal
  rw [← hprojection]
  apply slabPlaquetteAt_mem
  exact
    slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
      D rootFaceId targetFaceId htarget pair hpair faceId hface

/-! ## 2. Recover physical face identifiers and write both values -/

/-- The decoded support order, transported back to literal slab face ids. -/
def slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) : List Nat :=
  (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
    D rootFaceId targetFaceId htarget pair hpair massBudget).map
      (slabFaceIdOfPlaquette D.extent)

theorem slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    (slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
      D rootFaceId targetFaceId htarget pair hpair massBudget).Nodup := by
  unfold slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
  apply nodup_map_of_injOn (slabFaceIdOfPlaquette D.extent)
  · exact
      slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_nodup
        D rootFaceId targetFaceId htarget pair hpair massBudget
  · intro left hleft right hright heq
    have hleftBoundary :=
      slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_boundary
        D rootFaceId targetFaceId htarget pair hpair massBudget left hleft
    have hrightBoundary :=
      slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_boundary
        D rootFaceId targetFaceId htarget pair hpair massBudget right hright
    have hplaquette := congrArg (slabPlaquetteAt D.extent) heq
    rw [slabPlaquetteAt_faceIdOfPlaquette hleftBoundary,
      slabPlaquetteAt_faceIdOfPlaquette hrightBoundary] at hplaquette
    exact hplaquette

theorem slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_subset_component
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) (faceId : Nat)
    (hfaceId : faceId ∈
      slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
        D rootFaceId targetFaceId htarget pair hpair massBudget) :
    faceId ∈ slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId := by
  unfold slabObservableTwoReplicaPairTargetSupportGlobalFaceIds at hfaceId
  obtain ⟨plaquette, hplaquette, hfaceIdEq⟩ := List.mem_map.mp hfaceId
  have horiginal :=
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_sameSupport
      D rootFaceId targetFaceId htarget pair hpair massBudget).2
        plaquette hplaquette
  let sourceFaceId := slabObservableTwoReplicaPairTargetSupportFaceValue
    D pair targetFaceId plaquette
  have hsource := slabObservableTwoReplicaPairTargetSupportFaceValue_mem
    D rootFaceId targetFaceId htarget pair hpair plaquette
  have hprojection :=
    slabObservableTwoReplicaPairTargetSupportFaceValue_projection
      D pair targetFaceId plaquette horiginal
  have hsourcePhysical :=
    slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
      D rootFaceId targetFaceId htarget pair hpair sourceFaceId hsource
  have hinverse : slabFaceIdOfPlaquette D.extent plaquette = sourceFaceId := by
    rw [← hprojection]
    exact slabFaceIdOfPlaquette_slabPlaquetteAt hsourcePhysical
  rw [← hfaceIdEq, hinverse]
  exact hsource

/-- Left then right physical twice-spin values at every decoded support site. -/
def slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) : List Nat :=
  (slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
    D rootFaceId targetFaceId htarget pair hpair massBudget).flatMap
      fun faceId => [pair.1.1.1 faceId, pair.2.1.1 faceId]

private theorem pairValueWord_length
    (left right : Nat → Nat) : ∀ faceIds : List Nat,
    (faceIds.flatMap fun faceId => [left faceId, right faceId]).length =
      2 * faceIds.length
  | [] => rfl
  | _ :: tail => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil]
      rw [pairValueWord_length left right tail]
      omega

private theorem pairValueWord_l1
    (left right : Nat → Nat) : ∀ faceIds : List Nat,
    natListSum
        (faceIds.flatMap fun faceId => [left faceId, right faceId]) =
      listNatWeight (fun faceId => left faceId + right faceId) faceIds
  | [] => rfl
  | _ :: tail => by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append,
        natListSum, listNatWeight]
      rw [pairValueWord_l1 left right tail]
      omega

/-! ## 3. The canonical trace mass pays both coordinate and l1 budgets -/

theorem slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_length_le_traceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
        D rootFaceId targetFaceId htarget pair hpair massBudget).length ≤
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget pair hpair).2 := by
  have hsameLength := sameSupport_length_eq_of_nodup
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_sameSupport
      D rootFaceId targetFaceId htarget pair hpair massBudget)
    (slabObservableTwoReplicaPairTargetSupportPlaquettes_nodup
      D pair targetFaceId)
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_nodup
      D rootFaceId targetFaceId htarget pair hpair massBudget)
  have hsupportMass :
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
          D pair targetFaceId).length ≤
        slabObservableTwoReplicaPairTargetSupportMass
          D pair targetFaceId :=
    Nat.le_trans
      (slabObservableTwoReplicaPairTargetSupportPlaquettes_length_le_component
        D pair targetFaceId)
      (slabObservableTwoReplicaPairTargetSupportComponent_length_le_mass
        D rootFaceId targetFaceId htarget pair hpair)
  have hcomponentTrace :=
    slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
      D
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId)
      (rootComponent_nodup
        (slabSupportFaceAdjacentB D.extent)
        (slabTwoReplicaSupportFaceVertices D.extent
          pair.1.1.1 pair.2.1.1)
        targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)
  calc
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
        D rootFaceId targetFaceId htarget pair hpair massBudget).length =
        (slabObservableTwoReplicaPairTargetSupportPlaquettes
          D pair targetFaceId).length := hsameLength.symm
    _ ≤ listNatWeight
          (fun faceId => pair.1.1.1 faceId + pair.2.1.1 faceId)
          (slabTwoReplicaTargetSupportComponent D.extent
            pair.1.1.1 pair.2.1.1 targetFaceId) := by
      simpa only [slabObservableTwoReplicaPairTargetSupportMass] using
        hsupportMass
    _ ≤ slabAcceptedPairedPeelTraceMass
          (slabObservablePairTargetSupportCanonicalPeeling
            D rootFaceId targetFaceId htarget pair hpair).2 := by
      simpa only [slabObservablePairTargetSupportCanonicalPeeling,
        slabObservableTwoReplicaPairToAcceptedState,
        slabObservablePositiveSourceEntryToAccepted] using hcomponentTrace

theorem slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_length_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    (slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
        D rootFaceId targetFaceId htarget pair hpair massBudget).length ≤
      2 * slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget pair hpair).2 := by
  unfold slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
  rw [pairValueWord_length]
  unfold slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
  rw [List.length_map]
  exact Nat.mul_le_mul_left 2
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_length_le_traceMass
      D rootFaceId targetFaceId htarget pair hpair massBudget)

theorem slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_l1_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    natListSum
        (slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget pair hpair massBudget) ≤
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget pair hpair).2 := by
  unfold slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
  rw [pairValueWord_l1]
  have hsubset := listNatWeight_le_of_nodup_mem
    (fun faceId => pair.1.1.1 faceId + pair.2.1.1 faceId)
    (slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
      D rootFaceId targetFaceId htarget pair hpair massBudget)
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)
    (slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_nodup
      D rootFaceId targetFaceId htarget pair hpair massBudget)
    (slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_subset_component
      D rootFaceId targetFaceId htarget pair hpair massBudget)
  have hcomponentTrace :=
    slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
      D
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId)
      (rootComponent_nodup
        (slabSupportFaceAdjacentB D.extent)
        (slabTwoReplicaSupportFaceVertices D.extent
          pair.1.1.1 pair.2.1.1)
        targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)
  unfold slabObservablePairTargetSupportCanonicalPeeling
  exact Nat.le_trans hsubset hcomponentTrace

/-! ## 4. The exact `8^M` physical carrier -/

def slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) : List Nat :=
  let traceMass := slabAcceptedPairedPeelTraceMass
    (slabObservablePairTargetSupportCanonicalPeeling
      D rootFaceId targetFaceId htarget pair hpair).2
  asymmetricWeakCompositionBinaryCode (2 * traceMass) traceMass
    (slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
      D rootFaceId targetFaceId htarget pair hpair massBudget)

theorem slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    let traceMass := slabAcceptedPairedPeelTraceMass
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget pair hpair).2
    slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
        D rootFaceId targetFaceId htarget pair hpair massBudget ∈
      pairedPhysicalValueCarrier traceMass := by
  dsimp only
  apply asymmetricWeakCompositionBinaryCode_mem_pairedCarrier
  · exact
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_length_le
        D rootFaceId targetFaceId htarget pair hpair massBudget
  · exact
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_l1_le
        D rootFaceId targetFaceId htarget pair hpair massBudget

theorem slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode_eq_values
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (htraceMass :
      slabAcceptedPairedPeelTraceMass
          (slabObservablePairTargetSupportCanonicalPeeling
            D rootFaceId targetFaceId htarget left hleft).2 =
        slabAcceptedPairedPeelTraceMass
          (slabObservablePairTargetSupportCanonicalPeeling
            D rootFaceId targetFaceId htarget right hright).2)
    (hcode :
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode
          D rootFaceId targetFaceId htarget right hright massBudget) :
    slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
        D rootFaceId targetFaceId htarget left hleft massBudget =
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
        D rootFaceId targetFaceId htarget right hright massBudget := by
  unfold slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode at hcode
  rw [htraceMass] at hcode
  exact asymmetricWeakCompositionBinaryCode_injective _ _ _ _ hcode

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode.slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_sameSupport
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode.slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode.slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_length_le_traceMass
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode.slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_l1_le
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode.slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode.slabObservableTwoReplicaPairTargetSupportGlobalPhysicalCode_eq_values
