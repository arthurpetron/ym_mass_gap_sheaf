/-
# Exact-component occurrence cannot fill overlapping multi-true fibres

The volume-six three-cube construction proves a genuine positive `001`
physical cell.  It also exposes a structural limitation of using *whole
canonical component occurrence* as all three block coordinates.  Distinct
canonical polymers in one corrected gas family are link-separated.  Hence
two roots whose geometric supports share a production link can never occur
simultaneously as distinct components.

We prove the corresponding physical pattern mass exactly zero and rule out
the all-eight-positive `ThreeBlockPatternMatch` premise.  The constructive
pivot is therefore to sub-support/face queries inside a larger connected
component, rather than three exact overlapping-component occurrence events.
-/

import YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
import YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder

namespace YMGap.Continuum.Z4OverlappingCanonicalRootOccurrenceFence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPhysicalCubeLeakage
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeBareCouplingShift
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Link-overlapping canonical roots are mutually exclusive -/

theorem compatibleFamily_not_contains_linkOverlappingRoots
    {n : Nat} {left right : List Nat} {family : List (List Nat)}
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : left ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n left right)
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    ¬ (left ∈ family ∧ right ∈ family) := by
  rintro ⟨hleftFamily, hrightFamily⟩
  obtain ⟨leftFace, hleftFace, rightFace, hrightFace,
      link, hlinkLeft, hlinkRight⟩ := hoverlap
  obtain ⟨leftId, hleftId, hleftEq⟩ :=
    List.mem_map.mp hleftFace
  obtain ⟨rightId, hrightId, hrightEq⟩ :=
    List.mem_map.mp hrightFace
  have hleftPhysical : leftId ∈ physicalFaceEdges n :=
    mem_of_mem_sublists (physicalFaceEdges n) left
      (canonicalSurfacePolymer_mem_faceSupports hleftCanonical)
      leftId hleftId
  have hrightPhysical : rightId ∈ physicalFaceEdges n :=
    mem_of_mem_sublists (physicalFaceEdges n) right
      (canonicalSurfacePolymer_mem_faceSupports hrightCanonical)
      rightId hrightId
  have hadjacent : z4Chain.toLattice.Adjacent
      (boxPlaquetteAt n leftId) (boxPlaquetteAt n rightId) := by
    refine { link := link, on_p := ?_, on_q := ?_ }
    · change z4Boundary (boxPlaquetteAt n leftId) link = true
      unfold z4Boundary
      apply decide_eq_true
      rw [hleftEq]
      exact hlinkLeft
    · change z4Boundary (boxPlaquetteAt n rightId) link = true
      unfold z4Boundary
      apply decide_eq_true
      rw [hrightEq]
      exact hlinkRight
  have hadjacentTrue :
      faceLinkAdjacentB n leftId rightId = true :=
    faceLinkAdjacentB_true_of_actualAdjacent
      hleftPhysical hrightPhysical hadjacent
  have hadjacentFalse :
      faceLinkAdjacentB n leftId rightId = false :=
    (compatibleAmbientFamily_invariants hfamily).2
      left hleftFamily right hrightFamily hne
      leftId hleftId rightId hrightId
  rw [hadjacentTrue] at hadjacentFalse
  cases hadjacentFalse

theorem physical_linkOverlappingRootOccurrences_not_both
    {n : Nat} {left right : List Nat}
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : left ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n left right)
    (physical : EdgeLabelling) :
    ¬ (physicalRootOccurrenceEvent n left physical = true ∧
      physicalRootOccurrenceEvent n right physical = true) := by
  rintro ⟨hleftEvent, hrightEvent⟩
  have hleftFamily : left ∈ physicalCanonicalAmbientFamily n physical := by
    unfold physicalRootOccurrenceEvent cutoffOneLiftedFamilyEvent
      familyContainsPolymerB at hleftEvent
    exact of_decide_eq_true hleftEvent
  have hrightFamily : right ∈ physicalCanonicalAmbientFamily n physical := by
    unfold physicalRootOccurrenceEvent cutoffOneLiftedFamilyEvent
      familyContainsPolymerB at hrightEvent
    exact of_decide_eq_true hrightEvent
  exact compatibleFamily_not_contains_linkOverlappingRoots
    hleftCanonical hrightCanonical hne hoverlap
    (physicalCanonicalAmbientFamily_mem_compatible n physical)
    ⟨hleftFamily, hrightFamily⟩

/-! ## 2. The three coarse axis roots overlap pairwise as well -/

theorem axisCoarseFace_mem_geometricRoot
    (offset : AxisOffset)
    (hoffset : offset = zeroAxisOffset ∨
      offset = xAxisOffset ∨ offset = yAxisOffset)
    (face : CubeFaceIndex) :
    axisShiftPlaquette offset (cubeFace face) ∈
      geometricPolymer 6 (axisCoarseRoot offset) := by
  apply (axisCoarseRoot_sameSupport offset hoffset).2
  unfold axisCubeSurface
  exact List.mem_map.mpr
    ⟨cubeFace face, cubeFace_mem_unitCubeSurface face, rfl⟩

theorem coarseXAxisYAxis_shareProductionLink :
    CanonicalRootsShareProductionLink 6
      (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset) := by
  let leftFace : Z4Plaq :=
    axisShiftPlaquette xAxisOffset (cubeFace .leftYZ)
  let rightFace : Z4Plaq :=
    axisShiftPlaquette yAxisOffset (cubeFace .frontXZ)
  let sharedLink : Z4Link := ((1, 1, 0, 0), .x2)
  refine ⟨leftFace, ?_, rightFace, ?_, sharedLink, ?_, ?_⟩
  · exact axisCoarseFace_mem_geometricRoot xAxisOffset
      (Or.inr (Or.inl rfl)) .leftYZ
  · exact axisCoarseFace_mem_geometricRoot yAxisOffset
      (Or.inr (Or.inr rfl)) .frontXZ
  · simp [leftFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      xAxisOffset, cubeFace, dirsOf, addE, edgesOf]
  · simp [rightFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      yAxisOffset, cubeFace, dirsOf, addE, edgesOf]

theorem coarseXAxisZero_shareProductionLink :
    CanonicalRootsShareProductionLink 6
      (axisCoarseRoot xAxisOffset) (axisCoarseRoot zeroAxisOffset) := by
  let leftFace : Z4Plaq :=
    axisShiftPlaquette xAxisOffset (cubeFace .leftYZ)
  let rightFace : Z4Plaq :=
    axisShiftPlaquette zeroAxisOffset (cubeFace .rightYZ)
  let sharedLink : Z4Link := ((1, 0, 0, 0), .x1)
  refine ⟨leftFace, ?_, rightFace, ?_, sharedLink, ?_, ?_⟩
  · exact axisCoarseFace_mem_geometricRoot xAxisOffset
      (Or.inr (Or.inl rfl)) .leftYZ
  · exact axisCoarseFace_mem_geometricRoot zeroAxisOffset
      (Or.inl rfl) .rightYZ
  · simp [leftFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      xAxisOffset, cubeFace, dirsOf, addE, edgesOf]
  · simp [rightFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      zeroAxisOffset, cubeFace, dirsOf, addE, edgesOf]

theorem coarseYAxisZero_shareProductionLink :
    CanonicalRootsShareProductionLink 6
      (axisCoarseRoot yAxisOffset) (axisCoarseRoot zeroAxisOffset) := by
  let leftFace : Z4Plaq :=
    axisShiftPlaquette yAxisOffset (cubeFace .frontXZ)
  let rightFace : Z4Plaq :=
    axisShiftPlaquette zeroAxisOffset (cubeFace .backXZ)
  let sharedLink : Z4Link := ((0, 1, 0, 0), .x0)
  refine ⟨leftFace, ?_, rightFace, ?_, sharedLink, ?_, ?_⟩
  · exact axisCoarseFace_mem_geometricRoot yAxisOffset
      (Or.inr (Or.inr rfl)) .frontXZ
  · exact axisCoarseFace_mem_geometricRoot zeroAxisOffset
      (Or.inl rfl) .backXZ
  · simp [leftFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      yAxisOffset, cubeFace, dirsOf, addE, edgesOf]
  · simp [rightFace, sharedLink, axisShiftPlaquette, axisShiftVertex,
      zeroAxisOffset, cubeFace, dirsOf, addE, edgesOf]

theorem xOuterCoarseFace_not_mem_y :
    xOuterCoarseFace ∉ axisCubeSurface yAxisOffset := by
  simp [xOuterCoarseFace, axisCubeSurface, unitCubeSurface,
    axisShiftPlaquette, axisShiftVertex, xAxisOffset, yAxisOffset,
    cubeFace]

private theorem local_roots_ne_of_geometric_witness
    {left right : List Nat} {leftSupport rightSupport : List Z4Plaq}
    (hleft : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 left) leftSupport)
    (hright : sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 6 right) rightSupport)
    (face : Z4Plaq) (hface : face ∈ leftSupport)
    (hnot : face ∉ rightSupport) : left ≠ right := by
  intro heq
  have hdecoded := hleft.2 face hface
  rw [heq] at hdecoded
  exact hnot (hright.1 face hdecoded)

theorem coarseXAxisRoot_ne_yAxisRoot :
    axisCoarseRoot xAxisOffset ≠ axisCoarseRoot yAxisOffset :=
  local_roots_ne_of_geometric_witness
    (axisCoarseRoot_sameSupport xAxisOffset (Or.inr (Or.inl rfl)))
    (axisCoarseRoot_sameSupport yAxisOffset (Or.inr (Or.inr rfl)))
    xOuterCoarseFace xOuterCoarseFace_mem_x
    xOuterCoarseFace_not_mem_y

private theorem local_dyadicOrigin_not_mem_of_parent_not_mem
    {plaquette : Z4Plaq} {support : List Z4Plaq}
    (hnot : plaquette ∉ support) :
    dyadicCell plaquette .origin ∉ dyadicSupportCells support := by
  intro hcell
  obtain ⟨source, hsource, hlocal⟩ :=
    (mem_dyadicSupportCells_iff support _).mp hcell
  unfold dyadicPlaquetteCells at hlocal
  obtain ⟨index, _, heq⟩ := List.mem_map.mp hlocal
  have hparents : plaquette = source :=
    (dyadicCell_injective heq.symm).1
  exact hnot (hparents.symm ▸ hsource)

theorem fineXAxisRoot_ne_yAxisRoot :
    axisFineRoot xAxisOffset ≠ axisFineRoot yAxisOffset := by
  apply local_roots_ne_of_geometric_witness
    (axisFineRoot_sameSupport xAxisOffset (Or.inr (Or.inl rfl)))
    (axisFineRoot_sameSupport yAxisOffset (Or.inr (Or.inr rfl)))
    (dyadicCell xOuterCoarseFace .origin)
  · unfold axisFineCubeSurface
    exact (mem_dyadicSupportCells_iff _ _).mpr
      ⟨xOuterCoarseFace, xOuterCoarseFace_mem_x,
        dyadicCell_mem_cells _ _⟩
  · unfold axisFineCubeSurface
    exact local_dyadicOrigin_not_mem_of_parent_not_mem
      xOuterCoarseFace_not_mem_y

/-! ## 3. Every multi-true cell has exact mass zero -/

theorem normalizedPhysical_linkOverlappingPattern_ne
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : left ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n left right)
    (sharedBit : Bool) (physical : EdgeLabelling) :
    threeBlockPattern
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right)) physical ≠
      (true, sharedBit, true) := by
  intro hpattern
  rw [normalizedPhysicalThreeRootPattern_eq] at hpattern
  have hleftEvent : physicalRootOccurrenceEvent n left physical = true :=
    congrArg Prod.fst hpattern
  have hrightEvent : physicalRootOccurrenceEvent n right physical = true :=
    congrArg (fun pattern : Bool × Bool × Bool => pattern.2.2) hpattern
  exact physical_linkOverlappingRootOccurrences_not_both
    hleftCanonical hrightCanonical hne hoverlap physical
    ⟨hleftEvent, hrightEvent⟩

theorem normalizedPhysical_linkOverlappingPatternMass_eqv_zero
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : left ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n left right)
    (sharedBit : Bool) :
    threeBlockPatternMass
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right))
        (true, sharedBit, true) ≈ 0 := by
  unfold threeBlockPatternMass
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q'))
      (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
        (left, shared, right)).states) _ ?_ ?_
  · apply listQSum_congr_on
    intro physical _
    rw [if_neg (normalizedPhysical_linkOverlappingPattern_ne
      coupling hcoupling cutoff n left shared right
      hleftCanonical hrightCanonical hne hoverlap sharedBit physical)]
    exact Q'.eqv_refl 0
  · exact listQSum_zero _

theorem normalizedPhysical_leftSharedOverlappingPattern_ne
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hsharedCanonical : shared ∈ canonicalSurfacePolymers n)
    (hne : left ≠ shared)
    (hoverlap : CanonicalRootsShareProductionLink n left shared)
    (rightBit : Bool) (physical : EdgeLabelling) :
    threeBlockPattern
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right)) physical ≠
      (true, true, rightBit) := by
  intro hpattern
  rw [normalizedPhysicalThreeRootPattern_eq] at hpattern
  have hleftEvent : physicalRootOccurrenceEvent n left physical = true :=
    congrArg Prod.fst hpattern
  have hsharedEvent : physicalRootOccurrenceEvent n shared physical = true :=
    congrArg (fun pattern : Bool × Bool × Bool => pattern.2.1) hpattern
  exact physical_linkOverlappingRootOccurrences_not_both
    hleftCanonical hsharedCanonical hne hoverlap physical
    ⟨hleftEvent, hsharedEvent⟩

theorem normalizedPhysical_leftSharedOverlappingPatternMass_eqv_zero
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hsharedCanonical : shared ∈ canonicalSurfacePolymers n)
    (hne : left ≠ shared)
    (hoverlap : CanonicalRootsShareProductionLink n left shared)
    (rightBit : Bool) :
    threeBlockPatternMass
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right))
        (true, true, rightBit) ≈ 0 := by
  unfold threeBlockPatternMass
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q'))
      (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
        (left, shared, right)).states) _ ?_ ?_
  · apply listQSum_congr_on
    intro physical _
    rw [if_neg (normalizedPhysical_leftSharedOverlappingPattern_ne
      coupling hcoupling cutoff n left shared right
      hleftCanonical hsharedCanonical hne hoverlap rightBit physical)]
    exact Q'.eqv_refl 0
  · exact listQSum_zero _

theorem normalizedPhysical_sharedRightOverlappingPattern_ne
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hsharedCanonical : shared ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : shared ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n shared right)
    (leftBit : Bool) (physical : EdgeLabelling) :
    threeBlockPattern
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right)) physical ≠
      (leftBit, true, true) := by
  intro hpattern
  rw [normalizedPhysicalThreeRootPattern_eq] at hpattern
  have hsharedEvent : physicalRootOccurrenceEvent n shared physical = true :=
    congrArg (fun pattern : Bool × Bool × Bool => pattern.2.1) hpattern
  have hrightEvent : physicalRootOccurrenceEvent n right physical = true :=
    congrArg (fun pattern : Bool × Bool × Bool => pattern.2.2) hpattern
  exact physical_linkOverlappingRootOccurrences_not_both
    hsharedCanonical hrightCanonical hne hoverlap physical
    ⟨hsharedEvent, hrightEvent⟩

theorem normalizedPhysical_sharedRightOverlappingPatternMass_eqv_zero
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hsharedCanonical : shared ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : shared ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n shared right)
    (leftBit : Bool) :
    threeBlockPatternMass
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right))
        (leftBit, true, true) ≈ 0 := by
  unfold threeBlockPatternMass
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => (0 : Q'))
      (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
        (left, shared, right)).states) _ ?_ ?_
  · apply listQSum_congr_on
    intro physical _
    rw [if_neg (normalizedPhysical_sharedRightOverlappingPattern_ne
      coupling hcoupling cutoff n left shared right
      hsharedCanonical hrightCanonical hne hoverlap leftBit physical)]
    exact Q'.eqv_refl 0
  · exact listQSum_zero _

def ExactComponentOneHotPattern (pattern : ThreeBlockPattern) : Prop :=
  pattern = (false, false, false) ∨
    pattern = (true, false, false) ∨
    pattern = (false, true, false) ∨
    pattern = (false, false, true)

theorem normalizedPhysical_threePairOverlapping_pattern_oneHot
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hsharedCanonical : shared ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hleftSharedNe : left ≠ shared)
    (hleftRightNe : left ≠ right)
    (hsharedRightNe : shared ≠ right)
    (hleftSharedOverlap : CanonicalRootsShareProductionLink n left shared)
    (hleftRightOverlap : CanonicalRootsShareProductionLink n left right)
    (hsharedRightOverlap : CanonicalRootsShareProductionLink n shared right)
    (physical : EdgeLabelling) :
    ExactComponentOneHotPattern
      (threeBlockPattern
        (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
          (left, shared, right)) physical) := by
  rw [normalizedPhysicalThreeRootPattern_eq]
  unfold physicalRootTripleLeftEvent physicalRootTripleSharedEvent
    physicalRootTripleRightEvent physicalRootTripleLeft
    physicalRootTripleShared physicalRootTripleRight
  generalize hleftEvent :
    physicalRootOccurrenceEvent n left physical = leftBit
  generalize hsharedEvent :
    physicalRootOccurrenceEvent n shared physical = sharedBit
  generalize hrightEvent :
    physicalRootOccurrenceEvent n right physical = rightBit
  cases leftBit <;> cases sharedBit <;> cases rightBit
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exfalso
    exact physical_linkOverlappingRootOccurrences_not_both
      hsharedCanonical hrightCanonical hsharedRightNe
      hsharedRightOverlap physical ⟨hsharedEvent, hrightEvent⟩
  · exact Or.inr (Or.inl rfl)
  · exfalso
    exact physical_linkOverlappingRootOccurrences_not_both
      hleftCanonical hrightCanonical hleftRightNe
      hleftRightOverlap physical ⟨hleftEvent, hrightEvent⟩
  · exfalso
    exact physical_linkOverlappingRootOccurrences_not_both
      hleftCanonical hsharedCanonical hleftSharedNe
      hleftSharedOverlap physical ⟨hleftEvent, hsharedEvent⟩
  · exfalso
    exact physical_linkOverlappingRootOccurrences_not_both
      hleftCanonical hrightCanonical hleftRightNe
      hleftRightOverlap physical ⟨hleftEvent, hrightEvent⟩

theorem threeBlockPatternMass_eqv_zero_of_oneHot_support
    {State : Type} (law : ThreeBlockOverlapFiniteLaw State)
    (pattern : ThreeBlockPattern)
    (hsupport : ∀ state, ExactComponentOneHotPattern
      (threeBlockPattern law state))
    (hpattern : ¬ ExactComponentOneHotPattern pattern) :
    threeBlockPatternMass law pattern ≈ 0 := by
  unfold threeBlockPatternMass
  refine Q'.eqv_trans _
    (listQSum (fun _ : State => (0 : Q')) law.states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    have hne : threeBlockPattern law state ≠ pattern := by
      intro heq
      exact hpattern (heq ▸ hsupport state)
    rw [if_neg hne]
    exact Q'.eqv_refl 0
  · exact listQSum_zero _

/-! ## 4. Concrete fine and coarse one-hot support masses -/

theorem threeAxisFinePatternMass_110_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedFineThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisFineRoots)
        (true, true, false) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw fineCoupling hfine cutoff 6
        (axisFineRoot xAxisOffset, axisFineRoot yAxisOffset,
          axisFineRoot zeroAxisOffset))
      (true, true, false) ≈ 0
  exact normalizedPhysical_leftSharedOverlappingPatternMass_eqv_zero
    fineCoupling hfine cutoff 6
    (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset)
    (axisFineRoot zeroAxisOffset)
    (axisFineRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisFineRoot_mem_canonical yAxisOffset (Or.inr (Or.inr rfl)))
    fineXAxisRoot_ne_yAxisRoot fineXAxisYAxis_shareProductionLink false

theorem threeAxisFinePatternMass_101_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedFineThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisFineRoots)
        (true, false, true) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw fineCoupling hfine cutoff 6
        (axisFineRoot xAxisOffset, axisFineRoot yAxisOffset,
          axisFineRoot zeroAxisOffset))
      (true, false, true) ≈ 0
  exact normalizedPhysical_linkOverlappingPatternMass_eqv_zero
    fineCoupling hfine cutoff 6
    (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset)
    (axisFineRoot zeroAxisOffset)
    (axisFineRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    fineXAxisRoot_ne_zeroRoot fineXAxisZero_shareProductionLink false

theorem threeAxisFinePatternMass_011_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedFineThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisFineRoots)
        (false, true, true) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw fineCoupling hfine cutoff 6
        (axisFineRoot xAxisOffset, axisFineRoot yAxisOffset,
          axisFineRoot zeroAxisOffset))
      (false, true, true) ≈ 0
  exact normalizedPhysical_sharedRightOverlappingPatternMass_eqv_zero
    fineCoupling hfine cutoff 6
    (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset)
    (axisFineRoot zeroAxisOffset)
    (axisFineRoot_mem_canonical yAxisOffset (Or.inr (Or.inr rfl)))
    (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    fineYAxisRoot_ne_zeroRoot fineYAxisZero_shareProductionLink false

theorem threeAxisFinePatternMass_111_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedFineThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisFineRoots)
        (true, true, true) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw fineCoupling hfine cutoff 6
        (axisFineRoot xAxisOffset, axisFineRoot yAxisOffset,
          axisFineRoot zeroAxisOffset))
      (true, true, true) ≈ 0
  exact normalizedPhysical_linkOverlappingPatternMass_eqv_zero
    fineCoupling hfine cutoff 6
    (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset)
    (axisFineRoot zeroAxisOffset)
    (axisFineRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    fineXAxisRoot_ne_zeroRoot fineXAxisZero_shareProductionLink true

theorem threeAxisCoarsePatternMass_110_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisCoarseRoots)
        (true, true, false) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
        (axisCoarseRoot xAxisOffset, axisCoarseRoot yAxisOffset,
          axisCoarseRoot zeroAxisOffset))
      (true, true, false) ≈ 0
  exact normalizedPhysical_leftSharedOverlappingPatternMass_eqv_zero
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
    (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset)
    (axisCoarseRoot zeroAxisOffset)
    (axisCoarseRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisCoarseRoot_mem_canonical yAxisOffset (Or.inr (Or.inr rfl)))
    coarseXAxisRoot_ne_yAxisRoot coarseXAxisYAxis_shareProductionLink false

theorem threeAxisCoarsePatternMass_101_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisCoarseRoots)
        (true, false, true) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
        (axisCoarseRoot xAxisOffset, axisCoarseRoot yAxisOffset,
          axisCoarseRoot zeroAxisOffset))
      (true, false, true) ≈ 0
  exact normalizedPhysical_linkOverlappingPatternMass_eqv_zero
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
    (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset)
    (axisCoarseRoot zeroAxisOffset)
    (axisCoarseRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    coarseXAxisRoot_ne_zeroRoot coarseXAxisZero_shareProductionLink false

theorem threeAxisCoarsePatternMass_011_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisCoarseRoots)
        (false, true, true) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
        (axisCoarseRoot xAxisOffset, axisCoarseRoot yAxisOffset,
          axisCoarseRoot zeroAxisOffset))
      (false, true, true) ≈ 0
  exact normalizedPhysical_sharedRightOverlappingPatternMass_eqv_zero
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
    (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset)
    (axisCoarseRoot zeroAxisOffset)
    (axisCoarseRoot_mem_canonical yAxisOffset (Or.inr (Or.inr rfl)))
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    coarseYAxisRoot_ne_zeroRoot coarseYAxisZero_shareProductionLink false

theorem threeAxisCoarsePatternMass_111_eqv_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) :
    threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisCoarseRoots)
        (true, true, true) ≈ 0 := by
  change threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
        (axisCoarseRoot xAxisOffset, axisCoarseRoot yAxisOffset,
          axisCoarseRoot zeroAxisOffset))
      (true, true, true) ≈ 0
  exact normalizedPhysical_linkOverlappingPatternMass_eqv_zero
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
    (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset)
    (axisCoarseRoot zeroAxisOffset)
    (axisCoarseRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    coarseXAxisRoot_ne_zeroRoot coarseXAxisZero_shareProductionLink true

theorem threeAxisFinePattern_oneHot
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) (physical : EdgeLabelling) :
    ExactComponentOneHotPattern
      (threeBlockPattern
        (activityMatchedFineThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisFineRoots) physical) := by
  change ExactComponentOneHotPattern
    (threeBlockPattern
      (normalizedPhysicalThreeRootLaw fineCoupling hfine cutoff 6
        (axisFineRoot xAxisOffset, axisFineRoot yAxisOffset,
          axisFineRoot zeroAxisOffset)) physical)
  exact normalizedPhysical_threePairOverlapping_pattern_oneHot
    fineCoupling hfine cutoff 6
    (axisFineRoot xAxisOffset) (axisFineRoot yAxisOffset)
    (axisFineRoot zeroAxisOffset)
    (axisFineRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisFineRoot_mem_canonical yAxisOffset (Or.inr (Or.inr rfl)))
    (axisFineRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    fineXAxisRoot_ne_yAxisRoot fineXAxisRoot_ne_zeroRoot
    fineYAxisRoot_ne_zeroRoot fineXAxisYAxis_shareProductionLink
    fineXAxisZero_shareProductionLink fineYAxisZero_shareProductionLink
    physical

theorem threeAxisCoarsePattern_oneHot
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) (physical : EdgeLabelling) :
    ExactComponentOneHotPattern
      (threeBlockPattern
        (activityMatchedCoarseThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisCoarseRoots) physical) := by
  change ExactComponentOneHotPattern
    (threeBlockPattern
      (normalizedPhysicalThreeRootLaw (unitCubeBlockCoupling fineCoupling)
        (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
        (axisCoarseRoot xAxisOffset, axisCoarseRoot yAxisOffset,
          axisCoarseRoot zeroAxisOffset)) physical)
  exact normalizedPhysical_threePairOverlapping_pattern_oneHot
    (unitCubeBlockCoupling fineCoupling)
    (unitCubeBlockCoupling_nonnegative hfine) cutoff 6
    (axisCoarseRoot xAxisOffset) (axisCoarseRoot yAxisOffset)
    (axisCoarseRoot zeroAxisOffset)
    (axisCoarseRoot_mem_canonical xAxisOffset (Or.inr (Or.inl rfl)))
    (axisCoarseRoot_mem_canonical yAxisOffset (Or.inr (Or.inr rfl)))
    (axisCoarseRoot_mem_canonical zeroAxisOffset (Or.inl rfl))
    coarseXAxisRoot_ne_yAxisRoot coarseXAxisRoot_ne_zeroRoot
    coarseYAxisRoot_ne_zeroRoot coarseXAxisYAxis_shareProductionLink
    coarseXAxisZero_shareProductionLink coarseYAxisZero_shareProductionLink
    physical

theorem threeAxisFinePatternMass_eqv_zero_of_not_oneHot
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) (pattern : ThreeBlockPattern)
    (hpattern : ¬ ExactComponentOneHotPattern pattern) :
    threeBlockPatternMass
        (activityMatchedFineThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisFineRoots) pattern ≈ 0 := by
  exact threeBlockPatternMass_eqv_zero_of_oneHot_support _ pattern
    (threeAxisFinePattern_oneHot fineCoupling hfine cutoff) hpattern

theorem threeAxisCoarsePatternMass_eqv_zero_of_not_oneHot
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff : Nat) (pattern : ThreeBlockPattern)
    (hpattern : ¬ ExactComponentOneHotPattern pattern) :
    threeBlockPatternMass
        (activityMatchedCoarseThreeRootLaw fineCoupling hfine cutoff 6
          threeAxisCoarseRoots) pattern ≈ 0 := by
  exact threeBlockPatternMass_eqv_zero_of_oneHot_support _ pattern
    (threeAxisCoarsePattern_oneHot fineCoupling hfine cutoff) hpattern

/-! ## 5. The exact-component all-eight fibre route is impossible -/

theorem normalizedPhysical_linkOverlapping_no_patternMatch
    {Source : Type} (source : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (left shared right : List Nat)
    (hleftCanonical : left ∈ canonicalSurfacePolymers n)
    (hrightCanonical : right ∈ canonicalSurfacePolymers n)
    (hne : left ≠ right)
    (hoverlap : CanonicalRootsShareProductionLink n left right) :
    ¬ ThreeBlockPatternMatch source
      (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
        (left, shared, right)) := by
  intro hmatch
  have hpositive := hmatch.target_pattern_mass_pos (true, false, true)
  have hzero := normalizedPhysical_linkOverlappingPatternMass_eqv_zero
    coupling hcoupling cutoff n left shared right
    hleftCanonical hrightCanonical hne hoverlap false
  have hle : threeBlockPatternMass
      (normalizedPhysicalThreeRootLaw coupling hcoupling cutoff n
        (left, shared, right)) (true, false, true) ≤ 0 :=
    Q'.le_of_eqv hzero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hpositive hle)

#print axioms compatibleFamily_not_contains_linkOverlappingRoots
#print axioms physical_linkOverlappingRootOccurrences_not_both
#print axioms axisCoarseFace_mem_geometricRoot
#print axioms coarseXAxisYAxis_shareProductionLink
#print axioms coarseXAxisZero_shareProductionLink
#print axioms coarseYAxisZero_shareProductionLink
#print axioms xOuterCoarseFace_not_mem_y
#print axioms coarseXAxisRoot_ne_yAxisRoot
#print axioms fineXAxisRoot_ne_yAxisRoot
#print axioms normalizedPhysical_linkOverlappingPattern_ne
#print axioms normalizedPhysical_linkOverlappingPatternMass_eqv_zero
#print axioms normalizedPhysical_leftSharedOverlappingPattern_ne
#print axioms normalizedPhysical_leftSharedOverlappingPatternMass_eqv_zero
#print axioms normalizedPhysical_sharedRightOverlappingPattern_ne
#print axioms normalizedPhysical_sharedRightOverlappingPatternMass_eqv_zero
#print axioms normalizedPhysical_threePairOverlapping_pattern_oneHot
#print axioms threeBlockPatternMass_eqv_zero_of_oneHot_support
#print axioms threeAxisFinePatternMass_110_eqv_zero
#print axioms threeAxisFinePatternMass_101_eqv_zero
#print axioms threeAxisFinePatternMass_011_eqv_zero
#print axioms threeAxisFinePatternMass_111_eqv_zero
#print axioms threeAxisCoarsePatternMass_110_eqv_zero
#print axioms threeAxisCoarsePatternMass_101_eqv_zero
#print axioms threeAxisCoarsePatternMass_011_eqv_zero
#print axioms threeAxisCoarsePatternMass_111_eqv_zero
#print axioms threeAxisFinePattern_oneHot
#print axioms threeAxisCoarsePattern_oneHot
#print axioms threeAxisFinePatternMass_eqv_zero_of_not_oneHot
#print axioms threeAxisCoarsePatternMass_eqv_zero_of_not_oneHot
#print axioms normalizedPhysical_linkOverlapping_no_patternMatch

end YMGap.Continuum.Z4OverlappingCanonicalRootOccurrenceFence
