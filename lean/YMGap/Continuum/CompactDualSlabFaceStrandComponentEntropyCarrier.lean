/-
# The complete finite component-code carrier and its arithmetic diagnostic

The preceding inverse decoders isolate four finite words for a rooted complete-
slab strand component: geometric shape, physical multiplicities, auxiliary-row
presence, and flattened auxiliary values.  This module packages those words,
enumerates their Cartesian carrier, and proves its exact cardinality.

The result is also a decisive diagnostic.  The unweighted carrier base is

  625 * 4 * 16 * 4^12 = 671088640000,

which is larger than the proved per-copy heat-payment denominator 32000000.
Thus raw counting of every auxiliary natural word cannot close the component
Peierls estimate.  A successful continuation must retain the SU2 weights while
summing auxiliary labels instead of paying their entire unweighted code count.

Constructive contract: finite Cartesian lists, literal inverse-code fields,
and decidable rational arithmetic only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryDropDecoder
import YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentEntropyCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowKeyCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Package and enumerate the four code words -/

/-- The complete component-relative word package. -/
structure ComponentEntropyCode : Type where
  shape : List (Fin (z4Chain.D + 1))
  physicalMultiplicity : List Nat
  auxiliaryRowPresence : List Nat
  auxiliaryValues : List Nat
deriving DecidableEq

/-- Cartesian product of four word carriers. -/
def componentEntropyCarrierFrom
    (shapes : List (List (Fin (z4Chain.D + 1))))
    (physicalMultiplicities auxiliaryRowPresences auxiliaryValues :
      List (List Nat)) : List ComponentEntropyCode :=
  shapes.flatMap fun shape =>
    physicalMultiplicities.flatMap fun physicalMultiplicity =>
      auxiliaryRowPresences.flatMap fun auxiliaryRowPresence =>
        auxiliaryValues.map fun values =>
          { shape := shape
            physicalMultiplicity := physicalMultiplicity
            auxiliaryRowPresence := auxiliaryRowPresence
            auxiliaryValues := values }

/-- The Cartesian enumerator has the product cardinality. -/
theorem componentEntropyCarrierFrom_length
    (shapes : List (List (Fin (z4Chain.D + 1))))
    (physicalMultiplicities auxiliaryRowPresences auxiliaryValues :
      List (List Nat)) :
    (componentEntropyCarrierFrom shapes physicalMultiplicities
      auxiliaryRowPresences auxiliaryValues).length =
      shapes.length * (physicalMultiplicities.length *
        (auxiliaryRowPresences.length * auxiliaryValues.length)) := by
  unfold componentEntropyCarrierFrom
  have hvalues : forall shape physicalMultiplicity auxiliaryRowPresence,
      (auxiliaryValues.map fun values =>
        { shape := shape
          physicalMultiplicity := physicalMultiplicity
          auxiliaryRowPresence := auxiliaryRowPresence
          auxiliaryValues := values : ComponentEntropyCode }).length =
        auxiliaryValues.length := by
    intro _ _ _
    exact List.length_map _
  have hpresence : forall shape physicalMultiplicity,
      (auxiliaryRowPresences.flatMap fun auxiliaryRowPresence =>
        auxiliaryValues.map fun values =>
          { shape := shape
            physicalMultiplicity := physicalMultiplicity
            auxiliaryRowPresence := auxiliaryRowPresence
            auxiliaryValues := values : ComponentEntropyCode }).length =
        auxiliaryRowPresences.length * auxiliaryValues.length := by
    intro shape physicalMultiplicity
    exact length_flatMap_const _ _ _
      (fun auxiliaryRowPresence _ =>
        hvalues shape physicalMultiplicity auxiliaryRowPresence)
  have hphysical : forall shape,
      (physicalMultiplicities.flatMap fun physicalMultiplicity =>
        auxiliaryRowPresences.flatMap fun auxiliaryRowPresence =>
          auxiliaryValues.map fun values =>
            { shape := shape
              physicalMultiplicity := physicalMultiplicity
              auxiliaryRowPresence := auxiliaryRowPresence
              auxiliaryValues := values : ComponentEntropyCode }).length =
        physicalMultiplicities.length *
          (auxiliaryRowPresences.length * auxiliaryValues.length) := by
    intro shape
    exact length_flatMap_const _ _ _
      (fun physicalMultiplicity _ => hpresence shape physicalMultiplicity)
  exact length_flatMap_const _ _ _ (fun shape _ => hphysical shape)

/-- The four carriers specialized to one common peel size. -/
def componentEntropyCarrier (peelSize : Nat) : List ComponentEntropyCode :=
  componentEntropyCarrierFrom
    (componentPlaquettePaddedTourCarrier peelSize)
    (allSeqs 2 (2 * peelSize))
    (allSeqs 2 (4 * peelSize))
    (allSeqs 2 (2 * (12 * peelSize)))

/-- Package the four production words of one rooted complete-slab component. -/
def componentEntropyCode
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : ComponentEntropyCode where
  shape := componentPlaquettePaddedTourCode seed
  physicalMultiplicity :=
    componentDecodedPhysicalMultiplicityBinaryCode seed
  auxiliaryRowPresence := componentAuxiliaryRowPresenceCode seed
  auxiliaryValues :=
    SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode seed

/-- Every production word package lies in the carrier indexed only by peel
size. -/
theorem componentEntropyCode_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentEntropyCode seed ∈ componentEntropyCarrier
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentEntropyCarrier componentEntropyCarrierFrom
    componentEntropyCode
  apply List.mem_flatMap.mpr
  refine ⟨componentPlaquettePaddedTourCode seed,
    componentPlaquettePaddedTourCode_mem_carrier seed, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨componentDecodedPhysicalMultiplicityBinaryCode seed,
    componentDecodedPhysicalMultiplicityBinaryCode_mem_carrier seed, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨componentAuxiliaryRowPresenceCode seed,
    componentAuxiliaryRowPresenceCode_mem_carrier seed, ?_⟩
  apply List.mem_map.mpr
  exact ⟨SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode seed,
    SlabFusionWitnessFaceStrandSeed.sparseAuxiliaryValueBinaryCode_mem_carrier
      seed, rfl⟩

/-! ## 2. Exact cardinality and the unweighted no-go -/

/-- The explicit unweighted base of the complete four-factor carrier. -/
def componentEntropyBase : Nat := 625 * 4 * 16 * (4 ^ 12)

theorem componentEntropyBase_eq :
    componentEntropyBase = 671088640000 := by
  rfl

/-- The complete carrier has exact size `componentEntropyBase^peelSize`. -/
theorem componentEntropyCarrier_length (peelSize : Nat) :
    (componentEntropyCarrier peelSize).length =
      componentEntropyBase ^ peelSize := by
  unfold componentEntropyCarrier
  rw [componentEntropyCarrierFrom_length,
    componentPlaquettePaddedTourCarrier_length,
    componentDecodedPhysicalMultiplicityCarrier_length,
    componentAuxiliaryRowPresenceCarrier_length]
  have hauxiliary :
      (allSeqs 2 (2 * (12 * peelSize))).length =
        (4 ^ 12) ^ peelSize := by
    rw [weakCompositionBinaryCarrier_length,
      two_pow_two_mul_eq_four_pow, Nat.pow_mul]
  rw [hauxiliary]
  unfold componentEntropyBase
  rw [← Nat.mul_pow, ← Nat.mul_pow, ← Nat.mul_pow]

/-- The unweighted entropy base multiplied by the proved one-copy heat factor. -/
def componentEntropyAnchorRatio : Q' :=
  Q'.ofNat componentEntropyBase * anchorFaceCoefficient

/-- Exact simplification of the unweighted ratio. -/
theorem componentEntropyAnchorRatio_eqv :
    componentEntropyAnchorRatio ≈ Q'.mkPos 524288 25 (by decide) := by
  decide

/-- Raw counting of all four code words overwhelms rather than contracts the
proved heat payment. -/
theorem one_lt_componentEntropyAnchorRatio :
    (1 : Q') < componentEntropyAnchorRatio := by
  decide

/-! ## 3. What equality of complete codes actually reconstructs -/

/-- Equal complete codes at a common literal root recover both the physical
drop function and the literal sparse auxiliary table. -/
theorem componentEntropyCode_eq_dropData_eq
    {K extent : Nat} {physical : SlabLabelling}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        rightAssignment hrightAssignment)
    (hroot : left.root.faceId = right.root.faceId)
    (hcode : componentEntropyCode left = componentEntropyCode right) :
    (forall faceId,
      slabFaceStrandSelectionCount left.selected faceId =
        slabFaceStrandSelectionCount right.selected faceId) ∧
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode left).auxiliaryWords =
        (SlabFusionWitnessFaceStrandSeed.sparseDropCode right).auxiliaryWords := by
  have hshape := congrArg ComponentEntropyCode.shape hcode
  have hphysical := congrArg ComponentEntropyCode.physicalMultiplicity hcode
  have hpresence := congrArg ComponentEntropyCode.auxiliaryRowPresence hcode
  have hvalues := congrArg ComponentEntropyCode.auxiliaryValues hcode
  constructor
  · intro faceId
    exact componentProductionCodes_eq_physicalDrop_eq
      left right hroot hshape hphysical faceId
  · exact componentProductionCodes_eq_auxiliaryWords_eq
      left right hroot hshape hpresence hvalues

/-! ## 4. Generic finite injection consequence -/

/-- Any duplicate-free finite family that injects through the complete code
into one peel-size carrier has the advertised cardinality bound.  Supplying
such a family and discharging injectivity against a common lowered target are
separate geometric/measure-theoretic steps. -/
theorem componentEntropyCountBound {A : Type}
    (items : List A) (encode : A -> ComponentEntropyCode) (peelSize : Nat)
    (hitems : items.Nodup)
    (hmem : forall item, item ∈ items ->
      encode item ∈ componentEntropyCarrier peelSize)
    (hinjective : forall left, left ∈ items -> forall right, right ∈ items ->
      encode left = encode right -> left = right) :
    items.length <= componentEntropyBase ^ peelSize := by
  have hencodedNodup :=
    nodup_map_of_injOn encode items hitems hinjective
  have hsubset : forall code, code ∈ items.map encode ->
      code ∈ componentEntropyCarrier peelSize := by
    intro code hcode
    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hcode
    exact hmem item hitem
  have hbound := nodup_subset_length_le
    (items.map encode) (componentEntropyCarrier peelSize)
    hencodedNodup hsubset
  rw [List.length_map, componentEntropyCarrier_length] at hbound
  exact hbound

#print axioms ComponentEntropyCode
#print axioms componentEntropyCarrierFrom
#print axioms componentEntropyCarrierFrom_length
#print axioms componentEntropyCarrier
#print axioms componentEntropyCode
#print axioms componentEntropyCode_mem_carrier
#print axioms componentEntropyBase
#print axioms componentEntropyBase_eq
#print axioms componentEntropyCarrier_length
#print axioms componentEntropyAnchorRatio
#print axioms componentEntropyAnchorRatio_eqv
#print axioms one_lt_componentEntropyAnchorRatio
#print axioms componentEntropyCode_eq_dropData_eq
#print axioms componentEntropyCountBound

end YMGap.Continuum.CompactDualSlabFaceStrandComponentEntropyCarrier
