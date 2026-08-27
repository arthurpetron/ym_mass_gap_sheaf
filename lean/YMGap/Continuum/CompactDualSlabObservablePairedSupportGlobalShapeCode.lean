/-
# One global shape code for an observable paired-support component

The connected paired-support residue already supplies one finite Z4 lattice
animal rooted at the target plaquette.  Rather than paying for an animal at
every later peel, this module applies the generic rooted-animal compiler once
to that whole component.

For any common mass budget `M` dominating the support size, the resulting
word has length `2 * M` in the 25-symbol descend/backtrack alphabet and hence
lies in a carrier of exact size `625^M`.  Decoding recovers the entire support;
therefore equal words at the common target root force equal support sets.

No weight estimate or label reconstruction is asserted here.  This is the
global geometric factor for the later aggregate source-to-terminal code.

Constructive contract: the animal and all paths are Type-valued data, and the
code is an explicit finite list; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
import YMGap.Continuum.FiniteRootedAnimalTourCode

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The observable support as rooted animal data -/

/-- The whole target-rooted union-support component of an observable source
pair, packaged for the generic constructive animal compiler. -/
def slabObservableTwoReplicaPairTargetSupportRootedAnimal
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    RootedConnectedAnimal z4Chain where
  root := slabPlaquetteAt D.extent targetFaceId
  support := slabObservableTwoReplicaPairTargetSupportPlaquettes
    D pair targetFaceId
  root_mem :=
    slabObservableTwoReplicaPairTargetPlaquette_mem_targetSupport
      D rootFaceId targetFaceId htarget pair hpair
  support_nodup :=
    slabObservableTwoReplicaPairTargetSupportPlaquettes_nodup
      D pair targetFaceId
  connected :=
    slabObservableTwoReplicaPairTargetSupportPlaquettes_connected
      D rootFaceId targetFaceId htarget pair hpair

theorem slabObservableTwoReplicaPairTargetSupportRootedAnimal_root
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget pair hpair).root =
        slabPlaquetteAt D.extent targetFaceId :=
  rfl

theorem slabObservableTwoReplicaPairTargetSupportRootedAnimal_support
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget pair hpair).support =
        slabObservableTwoReplicaPairTargetSupportPlaquettes
          D pair targetFaceId :=
  rfl

/-! ## 2. One common-budget word for the whole support -/

/-- The globally padded shape word of the complete connected support. -/
def slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) : List (Fin (z4Chain.D + 1)) :=
  rootedAnimalPaddedTourCode
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget pair hpair)
    massBudget

theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_length
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hsupport :
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length ≤ massBudget) :
    (slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
      D rootFaceId targetFaceId htarget pair hpair massBudget).length =
        2 * massBudget := by
  exact rootedAnimalPaddedTourCode_length
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget pair hpair)
    massBudget hsupport

theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hsupport :
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length ≤ massBudget) :
    slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
        D rootFaceId targetFaceId htarget pair hpair massBudget ∈
      rootedAnimalPaddedTourCarrier z4Chain massBudget := by
  exact rootedAnimalPaddedTourCode_mem_carrier
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget pair hpair)
    massBudget hsupport

theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_decode
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat) :
    sameSupport (L := z4Chain.toLattice)
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId)
      (YMGap.Continuum.BddLatticeAnimal.decode z4Chain
        (slabPlaquetteAt D.extent targetFaceId)
        (slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget pair hpair massBudget)) := by
  exact rootedAnimalPaddedTourCode_decode_sameSupport
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget pair hpair)
    massBudget

/-! ## 3. Faithfulness and the exact global carrier -/

/-- At the common target root, an equal global word determines an equal
geometric support set. -/
theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_sameSupport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hcode :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget) :
    sameSupport (L := z4Chain.toLattice)
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D left targetFaceId)
      (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D right targetFaceId) := by
  exact rootedAnimalPaddedTourCode_eq_sameSupport
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget left hleft)
    (slabObservableTwoReplicaPairTargetSupportRootedAnimal
      D rootFaceId targetFaceId htarget right hright)
    massBudget rfl hcode

theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCarrier_length
    (massBudget : Nat) :
    (rootedAnimalPaddedTourCarrier z4Chain massBudget).length =
      625 ^ massBudget :=
  z4RootedAnimalPaddedTourCarrier_length massBudget

/-! ## 4. The complete pair mass is already a valid budget -/

theorem slabObservableTwoReplicaPairTargetSupport_length_le_totalPhysicalMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId).length ≤
      slabObservableTwoReplicaPairTotalPhysicalMass D pair :=
  Nat.le_trans
    (slabObservableTwoReplicaPairTargetSupportPlaquettes_length_le_component
      D pair targetFaceId)
    (Nat.le_trans
      (slabObservableTwoReplicaPairTargetSupportComponent_length_le_mass
        D rootFaceId targetFaceId htarget pair hpair)
      (slabObservableTwoReplicaPairTargetSupportMass_le_total
        D rootFaceId targetFaceId htarget pair hpair))

theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_mem_totalMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
        D rootFaceId targetFaceId htarget pair hpair
        (slabObservableTwoReplicaPairTotalPhysicalMass D pair) ∈
      rootedAnimalPaddedTourCarrier z4Chain
        (slabObservableTwoReplicaPairTotalPhysicalMass D pair) := by
  exact slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_mem
    D rootFaceId targetFaceId htarget pair hpair
    (slabObservableTwoReplicaPairTotalPhysicalMass D pair)
    (slabObservableTwoReplicaPairTargetSupport_length_le_totalPhysicalMass
      D rootFaceId targetFaceId htarget pair hpair)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode.slabObservableTwoReplicaPairTargetSupportRootedAnimal
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode.slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode.slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_sameSupport
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode.slabObservableTwoReplicaPairTargetSupportGlobalShapeCarrier_length
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode.slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_mem_totalMass
