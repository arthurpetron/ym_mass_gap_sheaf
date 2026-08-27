/-
# A volume-free three-factor adaptive component carrier

The rooted shape word and physical-multiplicity word decode a total physical
drop function.  Summing that function around every complete-slab link defines
the auxiliary `(mass,width)` specifications without retaining a production
seed.  We filter the finite multiplicity carrier by the decidable condition
that its decoded physical mass is at most the common peel budget.  Every
production word passes this filter exactly.

For each admitted structural pair, the adaptive auxiliary carrier has size at
most `4096^peelSize`.  Combining this with the existing `625^peelSize` shape
and `4^peelSize` physical carriers gives the strict three-factor base

  625 * 4 * 4096 = 10240000.

Against the proved one-copy anchor factor `1/32000000`, the arithmetic ratio is
exactly `8/25 < 1`.  This is a carrier and arithmetic theorem, not yet the
injectivity theorem for a fixed lowered-target inverse family.

Constructive contract: finite filters, finite Cartesian products, and exact
natural/rational arithmetic only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder
import YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Seed-independent decoded adaptive specifications -/

/-- Total decoded physical mass on the corrected-slab physical face list. -/
def componentAdaptiveDecodedPhysicalMass
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (multiplicityCode : List Nat) : Nat :=
  natListSum ((slabPhysicalFaceEdges extent).map
    (componentPhysicalDropDecode extent rootFaceId shapeCode multiplicityCode))

/-- The structural words are admitted at budget `peelSize` exactly when their
decoded physical mass is no larger than that budget. -/
def componentAdaptiveMultiplicityAdmissibleB
    (extent rootFaceId peelSize : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (multiplicityCode : List Nat) : Bool :=
  decide (componentAdaptiveDecodedPhysicalMass extent rootFaceId
    shapeCode multiplicityCode <= peelSize)

/-- Decode one `(mass,width)` specification for every complete-slab link. -/
def componentAdaptiveSpecificationsDecode
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (multiplicityCode : List Nat) : List (Nat × Nat) :=
  (boundaryCompleteSlabLinks extent).map fun link =>
    (natListSum ((slabIncidentPlaqIds extent link).map
      (componentPhysicalDropDecode extent rootFaceId
        shapeCode multiplicityCode)),
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length).length)

private theorem adaptiveAuxiliaryMass_map_eq_natListSumLocal
    (mass width : SlabLink -> Nat) : forall links : List SlabLink,
    adaptiveAuxiliaryMass
        (links.map fun link => (mass link, width link)) =
      natListSum (links.map mass)
  | [] => rfl
  | _ :: links => by
      simp only [List.map_cons, adaptiveAuxiliaryMass, natListSum]
      rw [adaptiveAuxiliaryMass_map_eq_natListSumLocal mass width links]

/-- The decoded specification mass is four times its decoded physical mass. -/
theorem componentAdaptiveSpecificationsDecode_mass
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (multiplicityCode : List Nat) :
    adaptiveAuxiliaryMass
        (componentAdaptiveSpecificationsDecode extent rootFaceId
          shapeCode multiplicityCode) =
      4 * componentAdaptiveDecodedPhysicalMass extent rootFaceId
        shapeCode multiplicityCode := by
  unfold componentAdaptiveSpecificationsDecode
    componentAdaptiveDecodedPhysicalMass
  rw [adaptiveAuxiliaryMass_map_eq_natListSumLocal]
  exact slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum
    extent (componentPhysicalDropDecode extent rootFaceId
      shapeCode multiplicityCode)

/-- Every decoded specification has one of the at most three canonical used
auxiliary coordinates. -/
theorem componentAdaptiveSpecificationsDecode_width_le_three
    (extent rootFaceId : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1)))
    (multiplicityCode : List Nat)
    (specification : Nat × Nat)
    (hspecification : specification ∈
      componentAdaptiveSpecificationsDecode extent rootFaceId
        shapeCode multiplicityCode) :
    specification.2 <= 3 := by
  unfold componentAdaptiveSpecificationsDecode at hspecification
  obtain ⟨link, _, rfl⟩ := List.mem_map.mp hspecification
  exact canonicalUsedAuxiliaryCoordinates_length_le_three
    (slabIncidentPlaqIds_length_le_six extent link)

/-- Production structural words decode the exact physical peel mass. -/
theorem componentAdaptiveDecodedPhysicalMass_code
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentAdaptiveDecodedPhysicalMass extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentDecodedPhysicalMultiplicityBinaryCode seed) =
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentAdaptiveDecodedPhysicalMass
  calc
    natListSum ((slabPhysicalFaceEdges extent).map
          (componentPhysicalDropDecode extent seed.root.faceId
            (componentPlaquettePaddedTourCode seed)
            (componentDecodedPhysicalMultiplicityBinaryCode seed))) =
        natListSum ((slabPhysicalFaceEdges extent).map
          (slabFaceStrandSelectionCount seed.selected)) := by
      apply natListSum_map_congr
      intro faceId hfaceId
      exact componentPhysicalDropDecode_code seed faceId
    _ = (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length :=
      (SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1
        seed).symm

/-- Production structural words decode the exact adaptive specification list. -/
theorem componentAdaptiveSpecificationsDecode_code
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentAdaptiveSpecificationsDecode extent seed.root.faceId
        (componentPlaquettePaddedTourCode seed)
        (componentDecodedPhysicalMultiplicityBinaryCode seed) =
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications seed := by
  unfold componentAdaptiveSpecificationsDecode
    SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
  apply List.map_congr_left
  intro link hlink
  apply Prod.ext
  · unfold SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass
    apply natListSum_map_congr
    intro faceId hfaceId
    exact componentPhysicalDropDecode_code seed faceId
  · rfl

/-! ## 2. The dependent three-factor carrier -/

/-- Shape, physical multiplicity, and full adaptive auxiliary rows. -/
structure ComponentAdaptiveEntropyCode : Type where
  shape : List (Fin (z4Chain.D + 1))
  physicalMultiplicity : List Nat
  auxiliaryRows : List (List Nat)
deriving DecidableEq

/-- The admitted physical word carrier for one decoded rooted shape. -/
def componentAdaptivePhysicalCarrier
    (extent rootFaceId peelSize : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1))) : List (List Nat) :=
  (allSeqs 2 (2 * peelSize)).filter fun multiplicityCode =>
    componentAdaptiveMultiplicityAdmissibleB extent rootFaceId peelSize
      shapeCode multiplicityCode

/-- The dependent Cartesian carrier: the auxiliary radix list is decoded from
the preceding structural words. -/
def componentAdaptiveEntropyCarrier
    (extent rootFaceId peelSize : Nat) : List ComponentAdaptiveEntropyCode :=
  (componentPlaquettePaddedTourCarrier peelSize).flatMap fun shapeCode =>
    (componentAdaptivePhysicalCarrier extent rootFaceId peelSize shapeCode).flatMap
      fun multiplicityCode =>
        (adaptiveAuxiliaryCarrier
          (componentAdaptiveSpecificationsDecode extent rootFaceId
            shapeCode multiplicityCode)).map fun rows =>
              { shape := shapeCode
                physicalMultiplicity := multiplicityCode
                auxiliaryRows := rows }

/-- Package the three production words. -/
def componentAdaptiveEntropyCode
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : ComponentAdaptiveEntropyCode where
  shape := componentPlaquettePaddedTourCode seed
  physicalMultiplicity := componentDecodedPhysicalMultiplicityBinaryCode seed
  auxiliaryRows := SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows seed

/-- Every production code belongs to the dependent carrier at its literal
root and peel size. -/
theorem componentAdaptiveEntropyCode_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    componentAdaptiveEntropyCode seed ∈
      componentAdaptiveEntropyCarrier extent seed.root.faceId
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold componentAdaptiveEntropyCarrier componentAdaptiveEntropyCode
  apply List.mem_flatMap.mpr
  refine ⟨componentPlaquettePaddedTourCode seed,
    componentPlaquettePaddedTourCode_mem_carrier seed, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨componentDecodedPhysicalMultiplicityBinaryCode seed, ?_, ?_⟩
  · unfold componentAdaptivePhysicalCarrier
    apply List.mem_filter.mpr
    refine ⟨componentDecodedPhysicalMultiplicityBinaryCode_mem_carrier seed,
      ?_⟩
    unfold componentAdaptiveMultiplicityAdmissibleB
    simp only [decide_eq_true_eq]
    rw [componentAdaptiveDecodedPhysicalMass_code seed]
    exact Nat.le_refl _
  · apply List.mem_map.mpr
    refine ⟨SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows seed, ?_, rfl⟩
    rw [componentAdaptiveSpecificationsDecode_code seed]
    exact SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows_mem_carrier seed

/-! ## 3. Uniform carrier cardinality -/

private theorem length_flatMap_leLocal {A B : Type}
    (block : A -> List B) (bound : Nat) : forall items : List A,
    (forall item, item ∈ items -> (block item).length <= bound) ->
      (items.flatMap block).length <= items.length * bound
  | [], _ => by simp
  | item :: items, hbound => by
      have hhead := hbound item List.mem_cons_self
      have htail := length_flatMap_leLocal block bound items
        (fun next hnext => hbound next (List.mem_cons_of_mem item hnext))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- Filtering for decoded mass never enlarges the physical word carrier. -/
theorem componentAdaptivePhysicalCarrier_length_le
    (extent rootFaceId peelSize : Nat)
    (shapeCode : List (Fin (z4Chain.D + 1))) :
    (componentAdaptivePhysicalCarrier extent rootFaceId peelSize
        shapeCode).length <= 4 ^ peelSize := by
  calc
    (componentAdaptivePhysicalCarrier extent rootFaceId peelSize
        shapeCode).length <= (allSeqs 2 (2 * peelSize)).length := by
      unfold componentAdaptivePhysicalCarrier
      exact List.length_filter_le _ _
    _ = 4 ^ peelSize :=
      componentDecodedPhysicalMultiplicityCarrier_length peelSize

/-- Every admitted decoded structural pair has an auxiliary carrier bounded
by `4096^peelSize`. -/
theorem componentAdaptiveDecodedAuxiliaryCarrier_length_le
    {extent rootFaceId peelSize : Nat}
    {shapeCode : List (Fin (z4Chain.D + 1))}
    {multiplicityCode : List Nat}
    (hadmissible : componentAdaptiveMultiplicityAdmissibleB
      extent rootFaceId peelSize shapeCode multiplicityCode = true) :
    (adaptiveAuxiliaryCarrier
        (componentAdaptiveSpecificationsDecode extent rootFaceId
          shapeCode multiplicityCode)).length <=
      4096 ^ peelSize := by
  apply adaptiveAuxiliaryCarrier_length_le_4096_pow
  · exact componentAdaptiveSpecificationsDecode_width_le_three
      extent rootFaceId shapeCode multiplicityCode
  · rw [componentAdaptiveSpecificationsDecode_mass]
    have hmass : componentAdaptiveDecodedPhysicalMass extent rootFaceId
        shapeCode multiplicityCode <= peelSize := by
      unfold componentAdaptiveMultiplicityAdmissibleB at hadmissible
      exact of_decide_eq_true hadmissible
    exact Nat.mul_le_mul_left 4 hmass

/-- The strict three-factor entropy base. -/
def componentAdaptiveEntropyBase : Nat := 625 * 4 * 4096

theorem componentAdaptiveEntropyBase_eq :
    componentAdaptiveEntropyBase = 10240000 := by
  rfl

/-- The complete dependent carrier has the desired volume-free exponential
upper bound. -/
theorem componentAdaptiveEntropyCarrier_length_le
    (extent rootFaceId peelSize : Nat) :
    (componentAdaptiveEntropyCarrier extent rootFaceId peelSize).length <=
      componentAdaptiveEntropyBase ^ peelSize := by
  let shapes := componentPlaquettePaddedTourCarrier peelSize
  let physicals := fun shapeCode =>
    componentAdaptivePhysicalCarrier extent rootFaceId peelSize shapeCode
  let auxiliary := fun shapeCode multiplicityCode =>
    adaptiveAuxiliaryCarrier
      (componentAdaptiveSpecificationsDecode extent rootFaceId
        shapeCode multiplicityCode)
  have hphysicalBranch : forall shapeCode, shapeCode ∈ shapes ->
      ((physicals shapeCode).flatMap fun multiplicityCode =>
        (auxiliary shapeCode multiplicityCode).map fun rows =>
          { shape := shapeCode
            physicalMultiplicity := multiplicityCode
            auxiliaryRows := rows : ComponentAdaptiveEntropyCode }).length <=
        4 ^ peelSize * 4096 ^ peelSize := by
    intro shapeCode hshapeCode
    have hflat := length_flatMap_leLocal
      (fun multiplicityCode =>
        (auxiliary shapeCode multiplicityCode).map fun rows =>
          { shape := shapeCode
            physicalMultiplicity := multiplicityCode
            auxiliaryRows := rows : ComponentAdaptiveEntropyCode })
      (4096 ^ peelSize) (physicals shapeCode) (by
        intro multiplicityCode hmultiplicityCode
        rw [List.length_map]
        apply componentAdaptiveDecodedAuxiliaryCarrier_length_le
        exact (List.mem_filter.mp hmultiplicityCode).2)
    exact Nat.le_trans hflat
      (Nat.mul_le_mul_right (4096 ^ peelSize)
        (componentAdaptivePhysicalCarrier_length_le
          extent rootFaceId peelSize shapeCode))
  have hshapeFlat := length_flatMap_leLocal
    (fun shapeCode =>
      ((physicals shapeCode).flatMap fun multiplicityCode =>
        (auxiliary shapeCode multiplicityCode).map fun rows =>
          { shape := shapeCode
            physicalMultiplicity := multiplicityCode
            auxiliaryRows := rows : ComponentAdaptiveEntropyCode }))
    (4 ^ peelSize * 4096 ^ peelSize) shapes hphysicalBranch
  unfold componentAdaptiveEntropyCarrier
  change (shapes.flatMap fun shapeCode =>
      ((physicals shapeCode).flatMap fun multiplicityCode =>
        (auxiliary shapeCode multiplicityCode).map fun rows =>
          { shape := shapeCode
            physicalMultiplicity := multiplicityCode
            auxiliaryRows := rows : ComponentAdaptiveEntropyCode })).length <=
    componentAdaptiveEntropyBase ^ peelSize
  calc
    (shapes.flatMap fun shapeCode =>
        ((physicals shapeCode).flatMap fun multiplicityCode =>
          (auxiliary shapeCode multiplicityCode).map fun rows =>
            { shape := shapeCode
              physicalMultiplicity := multiplicityCode
              auxiliaryRows := rows : ComponentAdaptiveEntropyCode })).length <=
        shapes.length * (4 ^ peelSize * 4096 ^ peelSize) := hshapeFlat
    _ = 625 ^ peelSize * (4 ^ peelSize * 4096 ^ peelSize) := by
      unfold shapes
      rw [componentPlaquettePaddedTourCarrier_length]
    _ = componentAdaptiveEntropyBase ^ peelSize := by
      unfold componentAdaptiveEntropyBase
      rw [← Nat.mul_pow, ← Nat.mul_pow]

/-! ## 4. Exact strict arithmetic reserve -/

/-- Adaptive entropy multiplied by the proved one-copy anchor factor. -/
def componentAdaptiveEntropyAnchorRatio : Q' :=
  Q'.ofNat componentAdaptiveEntropyBase * anchorFaceCoefficient

theorem componentAdaptiveEntropyAnchorRatio_eqv :
    componentAdaptiveEntropyAnchorRatio ≈
      Q'.mkPos 8 25 (by decide) := by
  decide

theorem componentAdaptiveEntropyAnchorRatio_lt_one :
    componentAdaptiveEntropyAnchorRatio < (1 : Q') := by
  decide

#print axioms componentAdaptiveDecodedPhysicalMass
#print axioms componentAdaptiveMultiplicityAdmissibleB
#print axioms componentAdaptiveSpecificationsDecode
#print axioms componentAdaptiveSpecificationsDecode_mass
#print axioms componentAdaptiveSpecificationsDecode_width_le_three
#print axioms componentAdaptiveDecodedPhysicalMass_code
#print axioms componentAdaptiveSpecificationsDecode_code
#print axioms ComponentAdaptiveEntropyCode
#print axioms componentAdaptivePhysicalCarrier
#print axioms componentAdaptiveEntropyCarrier
#print axioms componentAdaptiveEntropyCode
#print axioms componentAdaptiveEntropyCode_mem_carrier
#print axioms componentAdaptivePhysicalCarrier_length_le
#print axioms componentAdaptiveDecodedAuxiliaryCarrier_length_le
#print axioms componentAdaptiveEntropyBase
#print axioms componentAdaptiveEntropyBase_eq
#print axioms componentAdaptiveEntropyCarrier_length_le
#print axioms componentAdaptiveEntropyAnchorRatio
#print axioms componentAdaptiveEntropyAnchorRatio_eqv
#print axioms componentAdaptiveEntropyAnchorRatio_lt_one

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
