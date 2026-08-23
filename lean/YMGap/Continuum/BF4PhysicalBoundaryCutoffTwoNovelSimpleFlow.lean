/-
# Floor-free simple-path flow for the genuinely new cutoff-two sector

The cutoff-two old block already has a constructed uniform coercivity floor.
For every ordered endpoint pair with at least one genuinely new endpoint,
this module sends its exact stationary-product weight along the existing
loop-erased positive-kernel path.  Each traversed directed edge is charged

  endpointWeight * pathLength.

Finite Cauchy--Schwarz then controls the endpoint square by the unweighted
edge-square flow, before any global minimum of the physical kernel is taken.
All occurrences are regrouped exactly into a coefficient-independent edge
load.  Thus the remaining analytic question can be stated locally as a
comparison of weighted flow load with physical edge capacity.

No such uniform capacity comparison is inhabited here.  In particular no
uniform full-sector gap, thermodynamic/continuum limit, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Novel endpoint pairs and their exact stationary variance -/

/-- Ordered endpoint pairs with at least one state not present at cutoff two. -/
def cutoffTwoNovelEndpointPairs (later : Nat) : List (Nat × Nat) :=
  cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later) ++
    cutoffTwoCanonicalCrossEndpointPairs later

theorem cutoffTwoNovelEndpointPair_mem_full
    {later : Nat} {pair : Nat × Nat}
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    pair.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
      pair.2 ∈ cutoffTwoEdgeLoadFullStates later := by
  rcases List.mem_append.mp hpair with hnewNew | hcross
  · have hparts := (mem_cartesian_iff
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later) pair).mp hnewNew
    exact ⟨(List.mem_filter.mp hparts.1).1,
      (List.mem_filter.mp hparts.2).1⟩
  · exact cutoffTwoCanonicalCrossEndpointPair_mem_full hcross

/-- The stationary-product pairwise variance carried by all novel endpoint
pairs, written in the same order as the flow occurrences below. -/
def cutoffTwoNovelPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2) *
        ((coefficient pair.1 + -coefficient pair.2) *
          (coefficient pair.1 + -coefficient pair.2)))
    (cutoffTwoNovelEndpointPairs later)

private theorem finiteStationaryBlock_eqv_cartesian
    {State : Type}
    (leftStates rightStates : List State)
    (weight coefficient : State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (finiteStationaryProductJoint weight) ≈
      listQSum
        (fun pair =>
          (weight pair.1 * weight pair.2) *
            ((coefficient pair.1 + -coefficient pair.2) *
              (coefficient pair.1 + -coefficient pair.2)))
        (cartesian leftStates rightStates) := by
  unfold finiteJointDirichletBlock finiteStationaryProductJoint cartesian
  let entry : State × State → Q' := fun pair =>
    (weight pair.1 * weight pair.2) *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
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
            (weight left * weight right) *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
        leftStates := by
    apply listQSum_congr
    intro left
    rw [listQSum_map]
    exact Q'.eqv_refl _
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hflat hrows)

/-- The novel endpoint enumeration is exactly the new-new plus both directed
cross blocks of stationary pairwise variance. -/
theorem cutoffTwoNovelPairwiseVariance_eqv_newNew_add_cross
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelPairwiseVariance later coefficient ≈
      cutoffTwoNewNewPairwiseVariance later coefficient +
        cutoffTwoCrossBlockPairwiseVariance later coefficient := by
  let entry : Nat × Nat → Q' := fun pair =>
    (cutoffTwoEdgeLoadWeight later pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  unfold cutoffTwoNovelPairwiseVariance cutoffTwoNovelEndpointPairs
  refine Q'.eqv_trans _
    (listQSum entry
        (cartesian
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadNewStates later)) +
      (listQSum entry
          (cartesian
            (cutoffTwoEdgeLoadOldStates later)
            (cutoffTwoEdgeLoadNewStates later)) +
        listQSum entry
          (cartesian
            (cutoffTwoEdgeLoadNewStates later)
            (cutoffTwoEdgeLoadOldStates later)))) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum entry
          (cartesian
            (cutoffTwoEdgeLoadNewStates later)
            (cutoffTwoEdgeLoadNewStates later)) +
        listQSum entry
          (cutoffTwoCanonicalCrossEndpointPairs later)) _
      (listQSum_append _ _ _) ?_
    unfold cutoffTwoCanonicalCrossEndpointPairs
    exact Q'.add_eqv_congr_left _ _ _ (listQSum_append _ _ _)
  · unfold cutoffTwoNewNewPairwiseVariance
      cutoffTwoCrossBlockPairwiseVariance
      cutoffTwoOldNewPairwiseVariance cutoffTwoNewOldPairwiseVariance
    dsimp only [entry]
    unfold
      cutoffTwoEdgeLoadWeight cutoffTwoEdgeLoadOldStates
      cutoffTwoEdgeLoadNewStates
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm
        (finiteStationaryBlock_eqv_cartesian _ _ _ coefficient))
      (Q'.add_eqv_congr'
        (Q'.eqv_symm
          (finiteStationaryBlock_eqv_cartesian _ _ _ coefficient))
        (Q'.eqv_symm
          (finiteStationaryBlock_eqv_cartesian _ _ _ coefficient)))

/-! ## 2. Floor-free Cauchy budget on one simple path -/

def cutoffTwoSimpleRawPathBudget
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat) : Q' :=
  if hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        left right hleft hright
      Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path) *
        listQSum (fun value => value * value)
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeDifferences
            coefficient path)
    else 0
  else 0

theorem cutoffTwo_endpoint_sq_le_simpleRawPathBudget
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    (coefficient left + -coefficient right) *
        (coefficient left + -coefficient right) ≤
      cutoffTwoSimpleRawPathBudget later coefficient left right := by
  unfold cutoffTwoSimpleRawPathBudget
  rw [dif_pos hleft, dif_pos hright]
  exact
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum
      coefficient
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        left right hleft hright)

def cutoffTwoNovelRawPairBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2) *
        cutoffTwoSimpleRawPathBudget
          later coefficient pair.1 pair.2)
    (cutoffTwoNovelEndpointPairs later)

private theorem cutoffTwoWeight_nonnegative
    (later state : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadWeight later state := by
  unfold cutoffTwoEdgeLoadWeight
  exact centralPhysicalRowMarginal_nonnegative
    (by decide) later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 state)

/-- Summed Cauchy--Schwarz controls every novel stationary endpoint square by
the raw weighted edge-square path budget, without a global kernel floor. -/
theorem cutoffTwoNovelPairwiseVariance_le_rawPairBudget
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelPairwiseVariance later coefficient ≤
      cutoffTwoNovelRawPairBudget later coefficient := by
  unfold cutoffTwoNovelPairwiseVariance cutoffTwoNovelRawPairBudget
  apply listQSum_mono
  intro pair hpair
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (cutoffTwo_endpoint_sq_le_simpleRawPathBudget
      later coefficient pair.1 pair.2 hfull.1 hfull.2)
    (Q'.mul_nonneg _ _
      (cutoffTwoWeight_nonnegative later pair.1)
      (cutoffTwoWeight_nonnegative later pair.2))

/-! ## 3. Literal novel occurrences and exact edge-load regrouping -/

def cutoffTwoNovelSimpleWeightedEdgeOccurrences (later : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (cutoffTwoNovelEndpointPairs later).flatMap
    (fun pair =>
      cutoffTwoSimpleWeightedPathOccurrences later pair.1 pair.2)

def cutoffTwoNovelSimpleEdgeLoad
    (later source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
    source target

def cutoffTwoNovelSimpleRawLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
    coefficient (fun _ _ => 1)

theorem cutoffTwoSimpleWeightedPathRawOccurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoSimpleWeightedPathOccurrences later left right)
        coefficient (fun _ _ => 1) ≈
      (cutoffTwoEdgeLoadWeight later left *
          cutoffTwoEdgeLoadWeight later right) *
        cutoffTwoSimpleRawPathBudget later coefficient left right := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    cutoffTwoHalfCoupling (by decide) later 0
    left right hleft hright
  let pairWeight := cutoffTwoEdgeLoadWeight later left *
    cutoffTwoEdgeLoadWeight later right
  let lengthQ := Q'.ofNat
    (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
      path)
  let edgeSquare : Nat × Nat → Q' := fun edge =>
    (coefficient edge.1 + -coefficient edge.2) *
      (coefficient edge.1 + -coefficient edge.2)
  have hedges :=
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences
      coefficient path
  unfold cutoffTwoSimpleWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((pairWeight * lengthQ) *
      listQSum edgeSquare
        (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((pairWeight * lengthQ) *
        listQSum
          (fun edge => (1 : Q') * edgeSquare edge)
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path)) _ ?_ ?_
    · exact listQSum_mul_left (pairWeight * lengthQ) _ _
    · exact Q'.mul_eqv_congr_left (pairWeight * lengthQ) _ _
        (Q'.eqv_trans _
          (listQSum edgeSquare
            (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
              path)) _
          (listQSum_congr
            (fun edge => Q'.one_mul_eqv (edgeSquare edge)) _)
          (Q'.eqv_refl _))
  · refine Q'.eqv_trans _
      (pairWeight *
        (lengthQ *
          listQSum edgeSquare
            (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
              path))) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.mul_eqv_congr_left pairWeight _ _ ?_
    refine Q'.eqv_trans _
      (lengthQ *
        listQSum (fun value => value * value)
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeDifferences
            coefficient path)) _
      (Q'.mul_eqv_congr_left lengthQ _ _ hedges) ?_
    unfold cutoffTwoSimpleRawPathBudget
    rw [dif_pos hleft, dif_pos hright]
    exact Q'.eqv_refl _

theorem cutoffTwoNovelRawOccurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q') :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
        coefficient (fun _ _ => 1) ≈
      cutoffTwoNovelRawPairBudget later coefficient := by
  unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences
    cutoffTwoNovelRawPairBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finiteWeightedOccurrenceEnergy
          (cutoffTwoSimpleWeightedPathOccurrences
            later pair.1 pair.2)
          coefficient (fun _ _ => 1))
      (cutoffTwoNovelEndpointPairs later)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro pair hpair
    have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
    exact cutoffTwoSimpleWeightedPathRawOccurrenceEnergy_eqv_pairBudget
      later coefficient pair.1 pair.2 hfull.1 hfull.2

theorem cutoffTwoNovelOccurrence_mem_full
    (later : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later) :
    occurrence.1.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
      occurrence.1.2 ∈ cutoffTwoEdgeLoadFullStates later := by
  unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  unfold cutoffTwoSimpleWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      hfull.1
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        pair.1 pair.2 hfull.1 hfull.2)
      edge hedge

/-- Every literal occurrence of the novel simple flow traverses a strictly
positive entry of the genuine normalized physical kernel. -/
theorem cutoffTwoNovelOccurrence_kernel_pos
    (later : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later) :
    (0 : Q') < cutoffTwoEdgeLoadKernel
      later occurrence.1.1 occurrence.1.2 := by
  unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  unfold cutoffTwoSimpleWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_kernel_pos
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        pair.1 pair.2 hfull.1 hfull.2)
      edge hedge

/-- Every occurrence weight in the novel simple flow is nonnegative. -/
theorem cutoffTwoNovelOccurrence_load_nonnegative
    (later : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later) :
    (0 : Q') ≤ occurrence.2 := by
  unfold cutoffTwoNovelSimpleWeightedEdgeOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  unfold cutoffTwoSimpleWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (cutoffTwoWeight_nonnegative later pair.1)
      (cutoffTwoWeight_nonnegative later pair.2))
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

/-- The regrouped novel load is nonnegative on every directed edge. -/
theorem cutoffTwoNovelSimpleEdgeLoad_nonnegative
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoNovelSimpleEdgeLoad later source target := by
  unfold cutoffTwoNovelSimpleEdgeLoad
  exact weightedDirectedEdgeLoad_nonnegative
    (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
    (cutoffTwoNovelOccurrence_load_nonnegative later)
    source target

/-- A positive regrouped novel load can occur only on a strictly positive
physical-kernel edge. -/
theorem cutoffTwoNovelSimpleEdgeLoad_pos_implies_kernel_pos
    (later source target : Nat)
    (hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target) :
    (0 : Q') < cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoNovelSimpleEdgeLoad at hload
  rcases exists_occurrence_of_weightedDirectedEdgeLoad_pos
      (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
      (cutoffTwoNovelOccurrence_load_nonnegative later)
      source target hload with
    ⟨occurrence, hoccurrence, hedge⟩
  have hpositive := cutoffTwoNovelOccurrence_kernel_pos
    later occurrence hoccurrence
  simpa only [hedge] using hpositive

/-- The novel raw endpoint budget is exactly the full-sector Dirichlet block
whose joint coefficient is the regrouped flow load (times the unit kernel). -/
theorem cutoffTwoNovelRawPairBudget_eqv_loadedDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelRawPairBudget later coefficient ≈
      cutoffTwoNovelSimpleRawLoadedDirichlet later coefficient := by
  have hregroup :=
    finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (cutoffTwoEdgeLoadFullStates later)
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) later 0)
      coefficient (fun _ _ => 1)
      (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
      (cutoffTwoNovelOccurrence_mem_full later)
  exact Q'.eqv_trans _
    (finiteWeightedOccurrenceEnergy
      (cutoffTwoNovelSimpleWeightedEdgeOccurrences later)
      coefficient (fun _ _ => 1)) _
    (Q'.eqv_symm
      (cutoffTwoNovelRawOccurrenceEnergy_eqv_pairBudget
        later coefficient))
    (Q'.eqv_symm hregroup)

/-- Floor-free novel variance control, fully contracted to one explicit
coefficient-independent directed-edge load. -/
theorem cutoffTwoNovelPairwiseVariance_le_rawLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelPairwiseVariance later coefficient ≤
      cutoffTwoNovelSimpleRawLoadedDirichlet later coefficient := by
  exact Q'.le_trans' _ _ _
    (cutoffTwoNovelPairwiseVariance_le_rawPairBudget later coefficient)
    (Q'.le_of_eqv
      (cutoffTwoNovelRawPairBudget_eqv_loadedDirichlet later coefficient))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelPairwiseVariance_eqv_newNew_add_cross
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwo_endpoint_sq_le_simpleRawPathBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelPairwiseVariance_le_rawPairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoSimpleWeightedPathRawOccurrenceEnergy_eqv_pairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelOccurrence_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelSimpleEdgeLoad_pos_implies_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelRawPairBudget_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.cutoffTwoNovelPairwiseVariance_le_rawLoadedDirichlet
