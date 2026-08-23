/-
# Canonical cross-path load on each cutoff-two boundary edge

The polynomial canonical cross-path budget is a stationary-weighted sum over
old/new endpoint pairs.  This module flattens those paths into literal
weighted directed-edge occurrences and groups equal occurrences into a
coefficient-independent physical edge load.

The central identity is

  canonicalCrossLengthLinearPathBudget
    = Dirichlet(full sector, canonicalCrossEdgeLoad * physicalKernel).

Thus the remaining congestion problem can be asked pointwise on the four
old/old, old/new, new/old, and new/new edge blocks.

No pointwise load bound, cofinal family, uniform gap, continuum limit, or Clay
conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Physical lists and cross endpoint pairs -/

def cutoffTwoEdgeLoadFullStates (later : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) later 0

def cutoffTwoEdgeLoadOldStates (later : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorOldBlockIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0

def cutoffTwoEdgeLoadNewStates (later : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorNewBlockIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0

def cutoffTwoEdgeLoadWeight (later : Nat) : Nat → Q' :=
  centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0

def cutoffTwoEdgeLoadKernel (later : Nat) : Nat → Nat → Q' :=
  centralPhysicalFiniteKernel
    cutoffTwoHalfCoupling (by decide) later 0

def cutoffTwoCanonicalCrossEndpointPairs (later : Nat) :
    List (Nat × Nat) :=
  cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadNewStates later) ++
    cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadOldStates later)

private theorem oldState_mem_full
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadOldStates later) :
    state ∈ cutoffTwoEdgeLoadFullStates later := by
  exact (List.mem_filter.mp hstate).1

private theorem newState_mem_full
    {later state : Nat}
    (hstate : state ∈ cutoffTwoEdgeLoadNewStates later) :
    state ∈ cutoffTwoEdgeLoadFullStates later := by
  exact (List.mem_filter.mp hstate).1

theorem cutoffTwoCanonicalCrossEndpointPair_mem_full
    {later : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ cutoffTwoCanonicalCrossEndpointPairs later) :
    pair.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
      pair.2 ∈ cutoffTwoEdgeLoadFullStates later := by
  rcases List.mem_append.mp hpair with holdNew | hnewOld
  · have hparts :=
      (mem_cartesian_iff
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadNewStates later) pair).mp holdNew
    exact ⟨oldState_mem_full hparts.1, newState_mem_full hparts.2⟩
  · have hparts :=
      (mem_cartesian_iff
        (cutoffTwoEdgeLoadNewStates later)
        (cutoffTwoEdgeLoadOldStates later) pair).mp hnewOld
    exact ⟨newState_mem_full hparts.1, oldState_mem_full hparts.2⟩

/-! ## 2. Weighted occurrences of one canonical endpoint path -/

/-- Every literal edge occurrence of one canonical path receives the
stationary endpoint-pair weight times the path length. -/
def cutoffTwoCanonicalWeightedPathOccurrences
    (later left right : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  if hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      let path := centralPhysicalFiniteVacuumSectorPositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        left right hleft hright
      let load :=
        (cutoffTwoEdgeLoadWeight later left *
            cutoffTwoEdgeLoadWeight later right) *
          Q'.ofNat
            (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              path)
      (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path).map
        (fun edge => (edge, load))
    else []
  else []

def cutoffTwoCanonicalCrossWeightedEdgeOccurrences (later : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (cutoffTwoCanonicalCrossEndpointPairs later).flatMap
    (fun pair =>
      cutoffTwoCanonicalWeightedPathOccurrences
        later pair.1 pair.2)

private theorem onePath_occurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoCanonicalWeightedPathOccurrences later left right)
        coefficient (cutoffTwoEdgeLoadKernel later) ≈
      (cutoffTwoEdgeLoadWeight later left *
          cutoffTwoEdgeLoadWeight later right) *
        cutoffTwoCanonicalFullLengthLinearPathBudget
          later coefficient left right := by
  let path := centralPhysicalFiniteVacuumSectorPositivePath
    cutoffTwoHalfCoupling (by decide) later 0
    left right hleft hright
  let pairWeight := cutoffTwoEdgeLoadWeight later left *
    cutoffTwoEdgeLoadWeight later right
  let lengthQ := Q'.ofNat
    (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
      path)
  let edgeEnergy : Nat × Nat → Q' := fun edge =>
    cutoffTwoEdgeLoadKernel later edge.1 edge.2 *
      ((coefficient edge.1 + -coefficient edge.2) *
        (coefficient edge.1 + -coefficient edge.2))
  have hlinear :=
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.linearEnergy_eqv_directedEdges_sum
      coefficient path
  unfold cutoffTwoCanonicalWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((pairWeight * lengthQ) *
      listQSum edgeEnergy
        (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path)) _ ?_ ?_
  · exact listQSum_mul_left (pairWeight * lengthQ) edgeEnergy _
  refine Q'.eqv_trans _
    (pairWeight *
      (lengthQ *
        listQSum edgeEnergy
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path))) _ ?_ ?_
  · exact Q'.mul_assoc_eqv _ _ _
  refine Q'.eqv_trans _
    (pairWeight *
      (lengthQ *
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
          coefficient path)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left pairWeight _ _
      (Q'.mul_eqv_congr_left lengthQ _ _
        (Q'.eqv_symm hlinear))
  exact Q'.mul_eqv_congr_left pairWeight _ _
    (Q'.eqv_symm
      (cutoffTwoCanonicalFullLengthLinearPathBudget_eqv_of_mem
        later coefficient left right hleft hright))

/-! ## 3. Flatten all cross paths and identify the loaded Dirichlet form -/

def cutoffTwoCanonicalCrossPairBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2) *
        cutoffTwoCanonicalFullLengthLinearPathBudget
          later coefficient pair.1 pair.2)
    (cutoffTwoCanonicalCrossEndpointPairs later)

private theorem finiteWeightedRectangularEndpointBudget_eqv_cartesian
    {State : Type}
    (leftStates rightStates : List State)
    (weight : State → Q') (endpointBudget : State → State → Q') :
    finiteWeightedRectangularEndpointBudget
        leftStates rightStates weight endpointBudget ≈
      listQSum
        (fun pair =>
          (weight pair.1 * weight pair.2) *
            endpointBudget pair.1 pair.2)
        (cartesian leftStates rightStates) := by
  unfold finiteWeightedRectangularEndpointBudget cartesian
  let entry : State × State → Q' := fun pair =>
    (weight pair.1 * weight pair.2) *
      endpointBudget pair.1 pair.2
  have hflat := listQSum_flatMap entry
    (fun left => rightStates.map (fun right => (left, right))) leftStates
  have hrows : listQSum
      (fun left =>
        listQSum entry
          (rightStates.map (fun right => (left, right))))
      leftStates ≈
      listQSum
        (fun left => listQSum
          (fun right =>
            (weight left * weight right) * endpointBudget left right)
          rightStates)
        leftStates := by
    apply listQSum_congr
    intro left
    rw [listQSum_map]
    exact Q'.eqv_refl _
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hflat hrows)

theorem cutoffTwoCanonicalCrossPairBudget_eqv_lengthLinearPathBudget
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossPairBudget later coefficient ≈
      cutoffTwoCanonicalCrossLengthLinearPathBudget later coefficient := by
  unfold cutoffTwoCanonicalCrossPairBudget
    cutoffTwoCanonicalCrossEndpointPairs
    cutoffTwoCanonicalCrossLengthLinearPathBudget
    cutoffTwoOldNewCanonicalLengthLinearPathBudget
    cutoffTwoNewOldCanonicalLengthLinearPathBudget
  refine Q'.eqv_trans _
    (listQSum
        (fun pair =>
          (cutoffTwoEdgeLoadWeight later pair.1 *
              cutoffTwoEdgeLoadWeight later pair.2) *
            cutoffTwoCanonicalFullLengthLinearPathBudget
              later coefficient pair.1 pair.2)
        (cartesian
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadNewStates later)) +
      listQSum
        (fun pair =>
          (cutoffTwoEdgeLoadWeight later pair.1 *
              cutoffTwoEdgeLoadWeight later pair.2) *
            cutoffTwoCanonicalFullLengthLinearPathBudget
              later coefficient pair.1 pair.2)
        (cartesian
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadOldStates later))) _ ?_ ?_
  · exact listQSum_append _ _ _
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteWeightedRectangularEndpointBudget_eqv_cartesian
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadWeight later)
          (cutoffTwoCanonicalFullLengthLinearPathBudget later coefficient)))
      (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteWeightedRectangularEndpointBudget_eqv_cartesian
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadOldStates later)
          (cutoffTwoEdgeLoadWeight later)
          (cutoffTwoCanonicalFullLengthLinearPathBudget later coefficient)))
      (Q'.eqv_refl _))

theorem cutoffTwoCanonicalCrossOccurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q') :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoCanonicalCrossWeightedEdgeOccurrences later)
        coefficient (cutoffTwoEdgeLoadKernel later) ≈
      cutoffTwoCanonicalCrossPairBudget later coefficient := by
  unfold cutoffTwoCanonicalCrossWeightedEdgeOccurrences
    cutoffTwoCanonicalCrossPairBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finiteWeightedOccurrenceEnergy
          (cutoffTwoCanonicalWeightedPathOccurrences
            later pair.1 pair.2)
          coefficient (cutoffTwoEdgeLoadKernel later))
      (cutoffTwoCanonicalCrossEndpointPairs later)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  apply listQSum_congr_on
  intro pair hpair
  have hfull := cutoffTwoCanonicalCrossEndpointPair_mem_full hpair
  exact onePath_occurrenceEnergy_eqv_pairBudget
    later coefficient pair.1 pair.2 hfull.1 hfull.2

def cutoffTwoCanonicalCrossEdgeLoad
    (later source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (cutoffTwoCanonicalCrossWeightedEdgeOccurrences later)
    source target

def cutoffTwoCanonicalCrossLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoCanonicalCrossWeightedEdgeOccurrences later)
    coefficient (cutoffTwoEdgeLoadKernel later)

private theorem cutoffTwoCanonicalCrossOccurrence_mem_full
    (later : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoCanonicalCrossWeightedEdgeOccurrences later) :
    occurrence.1.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
      occurrence.1.2 ∈ cutoffTwoEdgeLoadFullStates later := by
  unfold cutoffTwoCanonicalCrossWeightedEdgeOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  have hfull := cutoffTwoCanonicalCrossEndpointPair_mem_full hpair
  unfold cutoffTwoCanonicalWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  rw [← heq]
  exact
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      hfull.1
      (centralPhysicalFiniteVacuumSectorPositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        pair.1 pair.2 hfull.1 hfull.2)
      edge hedge

/-- The exact coefficient-independent edge-load representation of the
polynomial canonical cross-path budget. -/
theorem cutoffTwoCanonicalCrossLengthLinearPathBudget_eqv_loadedDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLengthLinearPathBudget later coefficient ≈
      cutoffTwoCanonicalCrossLoadedDirichlet later coefficient := by
  have hregroup :=
    finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (cutoffTwoEdgeLoadFullStates later)
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) later 0)
      coefficient (cutoffTwoEdgeLoadKernel later)
      (cutoffTwoCanonicalCrossWeightedEdgeOccurrences later)
      (cutoffTwoCanonicalCrossOccurrence_mem_full later)
  exact Q'.eqv_trans _
    (cutoffTwoCanonicalCrossPairBudget later coefficient) _
    (Q'.eqv_symm
      (cutoffTwoCanonicalCrossPairBudget_eqv_lengthLinearPathBudget
        later coefficient))
    (Q'.eqv_trans _
      (finiteWeightedOccurrenceEnergy
        (cutoffTwoCanonicalCrossWeightedEdgeOccurrences later)
        coefficient (cutoffTwoEdgeLoadKernel later)) _
      (Q'.eqv_symm
        (cutoffTwoCanonicalCrossOccurrenceEnergy_eqv_pairBudget
          later coefficient))
      (Q'.eqv_symm hregroup))

/-! ## 4. Pointwise edge loads imply the allocated cross budget -/

/-- A pointwise upper bound on a load function bounds its loaded Dirichlet
block by the same scale times the physical block. -/
theorem finiteLoadedDirichletBlock_le_scale_mul
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (kernel load : State → State → Q') (scale : Q')
    (hkernel : ∀ left right, (0 : Q') ≤ kernel left right)
    (hload : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates → load left right ≤ scale) :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => load left right * kernel left right) ≤
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient kernel := by
  have hsum :
      finiteJointDirichletBlock leftStates rightStates coefficient
          (fun left right => load left right * kernel left right) ≤
        finiteJointDirichletBlock leftStates rightStates coefficient
          (fun left right => scale * kernel left right) := by
    unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    have hkernelScale :
        load left right * kernel left right ≤
          scale * kernel left right :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (hload left hleft right hright) (hkernel left right)
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hkernelScale
      (SumOfSquares.q_mul_self_nonneg
        (coefficient left + -coefficient right))
  have hscale :
      finiteJointDirichletBlock leftStates rightStates coefficient
          (fun left right => scale * kernel left right) ≈
        scale * finiteJointDirichletBlock
          leftStates rightStates coefficient kernel := by
    unfold finiteJointDirichletBlock
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          scale * listQSum
            (fun right =>
              kernel left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
            rightStates)
        leftStates) _ ?_ ?_
    · apply listQSum_congr
      intro left
      refine Q'.eqv_trans _
        (listQSum
          (fun right =>
            scale *
              (kernel left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right))))
          rightStates) _ ?_ ?_
      · apply listQSum_congr
        intro right
        exact Q'.mul_assoc_eqv _ _ _
      · exact listQSum_mul_left scale _ rightStates
    · exact listQSum_mul_left scale _ leftStates
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hscale)

private def cutoffTwoLoadedJoint (later : Nat) : Nat → Nat → Q' :=
  fun source target =>
    cutoffTwoCanonicalCrossEdgeLoad later source target *
      cutoffTwoEdgeLoadKernel later source target

def cutoffTwoCanonicalCrossLoadedOldOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadOldStates later)
    coefficient (cutoffTwoLoadedJoint later)

def cutoffTwoCanonicalCrossLoadedOldNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadNewStates later)
    coefficient (cutoffTwoLoadedJoint later)

def cutoffTwoCanonicalCrossLoadedNewOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadOldStates later)
    coefficient (cutoffTwoLoadedJoint later)

def cutoffTwoCanonicalCrossLoadedNewNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadNewStates later)
    coefficient (cutoffTwoLoadedJoint later)

private theorem four_term_within_cross_reshuffle
    (oldOld oldNew newOld newNew : Q') :
    (oldOld + oldNew) + (newOld + newNew) ≈
      (oldOld + newNew) + (oldNew + newOld) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv oldOld oldNew (newOld + newNew)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left oldOld _ _
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv oldNew newOld newNew))
        (Q'.add_comm_eqv (oldNew + newOld) newNew))) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv oldOld newNew (oldNew + newOld))

theorem cutoffTwoCanonicalCrossLoadedDirichlet_eqv_four_blocks
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedDirichlet later coefficient ≈
      (cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient) +
      (cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient) := by
  unfold cutoffTwoCanonicalCrossLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change finiteJointDirichletEnergy
      (cutoffTwoEdgeLoadFullStates later) coefficient
      (cutoffTwoLoadedJoint later) ≈ _
  unfold
    cutoffTwoCanonicalCrossLoadedOldOldDirichlet
    cutoffTwoCanonicalCrossLoadedOldNewDirichlet
    cutoffTwoCanonicalCrossLoadedNewOldDirichlet
    cutoffTwoCanonicalCrossLoadedNewNewDirichlet
  unfold cutoffTwoEdgeLoadFullStates cutoffTwoEdgeLoadOldStates
    cutoffTwoEdgeLoadNewStates
  change finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0)
      coefficient _ ≈ _
  exact finiteJointDirichletEnergy_filter_four_blocks
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
    (centralPhysicalFiniteEmbeddedVacuumSectorB
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient _

theorem cutoffTwoCanonicalCrossLoadedDirichlet_eqv_within_add_cross
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedDirichlet later coefficient ≈
      (cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient) +
      (cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient) := by
  exact Q'.eqv_trans _ _ _
    (cutoffTwoCanonicalCrossLoadedDirichlet_eqv_four_blocks
      later coefficient)
    (four_term_within_cross_reshuffle _ _ _ _)

/-- Coefficient-independent congestion bounds on the four physical edge
blocks.  Internal edges may consume `withinShare`; bridge edges have unit
capacity because all cross Dirichlet energy is allocated to the bridge
budget. -/
structure CutoffTwoCanonicalCrossEdgeLoadBoundsAt
    (later : Nat) (withinShare : Q') : Type 1 where
  old_old : ∀ source, source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ withinShare
  new_new : ∀ source, source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ withinShare
  old_new : ∀ source, source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ 1
  new_old : ∀ source, source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ 1

namespace CutoffTwoCanonicalCrossEdgeLoadBoundsAt

private theorem kernel_nonnegative (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoEdgeLoadKernel centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_nonnegative
    (by decide) later 0 _ _

theorem loaded_oldOld_le
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient ≤
      withinShare * cutoffTwoOldOldDirichlet later coefficient := by
  unfold cutoffTwoCanonicalCrossLoadedOldOldDirichlet
    cutoffTwoLoadedJoint cutoffTwoOldOldDirichlet
    cutoffTwoEdgeLoadOldStates cutoffTwoEdgeLoadKernel
  exact finiteLoadedDirichletBlock_le_scale_mul _ _ coefficient _ _ _
    (kernel_nonnegative later) bounds.old_old

theorem loaded_newNew_le
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient ≤
      withinShare * cutoffTwoNewNewDirichlet later coefficient := by
  unfold cutoffTwoCanonicalCrossLoadedNewNewDirichlet
    cutoffTwoLoadedJoint cutoffTwoNewNewDirichlet
    cutoffTwoEdgeLoadNewStates cutoffTwoEdgeLoadKernel
  exact finiteLoadedDirichletBlock_le_scale_mul _ _ coefficient _ _ _
    (kernel_nonnegative later) bounds.new_new

theorem loaded_oldNew_le
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient ≤
      cutoffTwoOldNewDirichlet later coefficient := by
  have h := finiteLoadedDirichletBlock_le_scale_mul
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadNewStates later) coefficient
    (cutoffTwoEdgeLoadKernel later)
    (cutoffTwoCanonicalCrossEdgeLoad later) 1
    (kernel_nonnegative later) bounds.old_new
  change cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient ≤
    1 * cutoffTwoOldNewDirichlet later coefficient at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

theorem loaded_newOld_le
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient ≤
      cutoffTwoNewOldDirichlet later coefficient := by
  have h := finiteLoadedDirichletBlock_le_scale_mul
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadOldStates later) coefficient
    (cutoffTwoEdgeLoadKernel later)
    (cutoffTwoCanonicalCrossEdgeLoad later) 1
    (kernel_nonnegative later) bounds.new_old
  change cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient ≤
    1 * cutoffTwoNewOldDirichlet later coefficient at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

theorem loadedWithin_le_physicalWithin
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient ≤
      withinShare * cutoffTwoWithinBlockDirichlet later coefficient := by
  have h := Q'.add_le_add
    (loaded_oldOld_le bounds coefficient)
    (loaded_newNew_le bounds coefficient)
  refine Q'.le_trans' _
    (withinShare * cutoffTwoOldOldDirichlet later coefficient +
      withinShare * cutoffTwoNewNewDirichlet later coefficient) _ h ?_
  unfold cutoffTwoWithinBlockDirichlet
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_add_eqv withinShare _ _))

theorem loadedCross_le_physicalCross
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient ≤
      cutoffTwoCrossBlockDirichlet later coefficient := by
  unfold cutoffTwoCrossBlockDirichlet
  exact Q'.add_le_add
    (loaded_oldNew_le bounds coefficient)
    (loaded_newOld_le bounds coefficient)

theorem loadedDirichlet_le_allocatedEnergy
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedDirichlet later coefficient ≤
      withinShare * cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient := by
  refine Q'.le_trans' _
    ((cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient) +
      (cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (cutoffTwoCanonicalCrossLoadedDirichlet_eqv_within_add_cross
        later coefficient)
  exact Q'.add_le_add
    (loadedWithin_le_physicalWithin bounds coefficient)
    (loadedCross_le_physicalCross bounds coefficient)

/-- Four pointwise load bounds imply the allocated aggregate congestion
inequality for every coefficient. -/
theorem lengthLinearPathBudget_le_allocatedEnergy
    {later : Nat} {withinShare : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadBoundsAt later withinShare)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLengthLinearPathBudget later coefficient ≤
      withinShare * cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoCanonicalCrossLengthLinearPathBudget_eqv_loadedDirichlet
        later coefficient))
    (loadedDirichlet_le_allocatedEnergy bounds coefficient)

end CutoffTwoCanonicalCrossEdgeLoadBoundsAt

/-! ## 5. Pointwise load certificates compile through completion -/

structure CutoffTwoPointwiseEdgeLoadAllocatedGluingAt
    (later : Nat) (floor massFloor withinShare crossShare : Q') : Type 1 where
  later_ge : 2 ≤ later
  floor_nonnegative : (0 : Q') ≤ floor
  within_share_nonnegative : (0 : Q') ≤ withinShare
  cross_share_nonnegative : (0 : Q') ≤ crossShare
  shares_sum_one : withinShare + crossShare ≈ 1
  floor_le_edgeFloor :
    floor ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  within_budget : ∀ coefficient,
    floor * cutoffTwoWithinBlockPairwiseVariance later coefficient ≤
      withinShare * cutoffTwoWithinBlockDirichlet later coefficient
  edge_load_bounds :
    CutoffTwoCanonicalCrossEdgeLoadBoundsAt later crossShare

namespace CutoffTwoPointwiseEdgeLoadAllocatedGluingAt

def toSparseLinearPathAllocatedGluingAt
    {later : Nat} {floor massFloor withinShare crossShare : Q'}
    (certificate : CutoffTwoPointwiseEdgeLoadAllocatedGluingAt
      later floor massFloor withinShare crossShare) :
    CutoffTwoSparseLinearPathAllocatedGluingAt
      later floor massFloor withinShare crossShare where
  later_ge := certificate.later_ge
  floor_nonnegative := certificate.floor_nonnegative
  within_share_nonnegative := certificate.within_share_nonnegative
  cross_share_nonnegative := certificate.cross_share_nonnegative
  shares_sum_one := certificate.shares_sum_one
  floor_le_edgeFloor := certificate.floor_le_edgeFloor
  mass_floor_le := certificate.mass_floor_le
  within_budget := certificate.within_budget
  cross_path_congestion :=
    certificate.edge_load_bounds.lengthLinearPathBudget_le_allocatedEnergy

def toAllocatedDirichletGluingAt
    {later : Nat} {floor massFloor withinShare crossShare : Q'}
    (certificate : CutoffTwoPointwiseEdgeLoadAllocatedGluingAt
      later floor massFloor withinShare crossShare) :
    CutoffTwoAllocatedDirichletGluingAt
      later floor massFloor withinShare crossShare :=
  certificate.toSparseLinearPathAllocatedGluingAt
    |>.toAllocatedDirichletGluingAt

end CutoffTwoPointwiseEdgeLoadAllocatedGluingAt

structure CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing
    (floor massFloor withinShare crossShare : Q') : Type 1 where
  floor_pos : (0 : Q') < floor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  pointwise : ∀ request,
    CutoffTwoPointwiseEdgeLoadAllocatedGluingAt
      (anchor request) floor massFloor withinShare crossShare

namespace CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing

def toCofinalAllocatedDirichletGluing
    {floor massFloor withinShare crossShare : Q'}
    (family : CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing
      floor massFloor withinShare crossShare) :
    CutoffTwoCofinalAllocatedDirichletGluing
      floor massFloor withinShare crossShare where
  floor_pos := family.floor_pos
  mass_floor_pos := family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  allocated := fun request =>
    (family.pointwise request).toAllocatedDirichletGluingAt

def toCompletedStrictContractionData
    {floor massFloor withinShare crossShare : Q'}
    (family : CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing
      floor massFloor withinShare crossShare) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalAllocatedDirichletGluing
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.cutoffTwoCanonicalCrossEndpointPair_mem_full
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.cutoffTwoCanonicalCrossPairBudget_eqv_lengthLinearPathBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.cutoffTwoCanonicalCrossOccurrenceEnergy_eqv_pairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.cutoffTwoCanonicalCrossLengthLinearPathBudget_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.finiteLoadedDirichletBlock_le_scale_mul
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.cutoffTwoCanonicalCrossLoadedDirichlet_eqv_four_blocks
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.CutoffTwoCanonicalCrossEdgeLoadBoundsAt.lengthLinearPathBudget_le_allocatedEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.CutoffTwoPointwiseEdgeLoadAllocatedGluingAt.toAllocatedDirichletGluingAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing.toCompletedStrictContractionData
