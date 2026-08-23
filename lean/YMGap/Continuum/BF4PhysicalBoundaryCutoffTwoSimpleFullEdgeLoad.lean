/-
# Linear simple-path congestion at the cutoff-two boundary

The carrier-square fallback bounds every endpoint path separately by the
whole Dirichlet form and therefore pays for all ordered endpoint pairs.  This
module keeps the literal edge occurrences of the loop-erased paths instead.
A vertex-simple path uses each directed edge at most once.  Consequently the
load on a fixed edge is at most the common path-length bound times the total
stationary endpoint-pair mass.

At half extent zero this reduces the explicit finite coercivity cost from the
degree-48 square-carrier fallback to the degree-24 linear-carrier fallback

  1 + |vacuum sector| <= 1 + (cutoff + 1)^24.

The estimate still contains the shrinking positive-edge floor.  No uniform
ratio, completed gap inhabitant, thermodynamic/continuum limit, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Loop-erased BF4 paths have no repeated directed edge -/

private theorem directedEdges_ofSupportedWalk
    {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool)
    (kernel : State → State → Q') (support : List State)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      adjacent first next = true → (0 : Q') < kernel first next) :
    ∀ {first last : State} (hfirst : first ∈ support)
      (path : FiniteBoolGraphSimplePaths.Walk
        (supportedEdge adjacent support) first last),
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
            adjacent kernel support edgePositive hfirst path) =
        FiniteBoolGraphSimplePaths.Walk.directedEdges path
  | _, _, _, FiniteBoolGraphSimplePaths.Walk.single _ => rfl
  | first, _, hfirst,
      FiniteBoolGraphSimplePaths.Walk.cons hedge rest => by
      have hparts := (Bool.and_eq_true _ _).mp hedge
      have hnext : rest.start ∈ support := of_decide_eq_true hparts.2
      simp only [
        BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk,
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges,
        FiniteBoolGraphSimplePaths.Walk.directedEdges]
      exact congrArg (List.cons (first, rest.start))
        (directedEdges_ofSupportedWalk adjacent kernel support edgePositive
          hnext rest)

theorem cutoffTwoSimplePositivePath_directedEdges_nodup
    (later left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        left right hleft hright)).Nodup := by
  let simple := centralPhysicalFiniteVacuumSectorSimpleWalk
    cutoffTwoHalfCoupling (by decide) later 0
    left right hleft hright
  change (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
    (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
      (centralPhysicalFiniteSupportAdjacentB
        cutoffTwoHalfCoupling (by decide) later 0)
      (centralPhysicalFiniteKernel
        cutoffTwoHalfCoupling (by decide) later 0)
      (cutoffTwoEdgeLoadFullStates later)
      _ hleft simple.walk)).Nodup
  rw [directedEdges_ofSupportedWalk]
  exact FiniteBoolGraphSimplePaths.Walk.directedEdges_nodup_of_vertices_nodup
    simple.walk simple.nodup

/-! ## 2. A duplicate-free constant occurrence list charges an edge once -/

private theorem weightedDirectedEdgeLoad_constantMap_eqv_indicator
    {State : Type} [DecidableEq State]
    (load : Q') (source target : State) :
    ∀ edges : List (State × State), edges.Nodup →
      weightedDirectedEdgeLoad
          (edges.map (fun edge => (edge, load))) source target ≈
        if (source, target) ∈ edges then load else 0
  | [], _ => Q'.eqv_refl 0
  | edge :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [weightedDirectedEdgeLoad, List.map_cons, listQSum,
        weightedDirectedEdgeIndicator]
      by_cases hhead : edge = (source, target)
      · rw [if_pos hhead]
        have hnotmem : (source, target) ∉ rest := by
          intro hmem
          exact hparts.1 (hhead ▸ hmem)
        have hmem : (source, target) ∈ edge :: rest := by
          exact List.mem_cons.mpr (Or.inl hhead.symm)
        rw [if_pos hmem]
        have htail : weightedDirectedEdgeLoad
            (rest.map (fun traversed => (traversed, load)))
            source target ≈ 0 :=
          Q'.eqv_trans _ (if (source, target) ∈ rest then load else 0) _
            (weightedDirectedEdgeLoad_constantMap_eqv_indicator
              load source target rest hparts.2)
            (by rw [if_neg hnotmem]; exact Q'.eqv_refl 0)
        change load + weightedDirectedEdgeLoad
            (rest.map (fun traversed => (traversed, load)))
            source target ≈ load
        exact Q'.eqv_trans _ (load + 0) _
          (Q'.add_eqv_congr_left load _ _ htail)
          (Q'.eqv_of_eq (Q'.add_zero' load))
      · rw [if_neg hhead]
        have hne : (source, target) ≠ edge := fun heq => hhead heq.symm
        by_cases htailMem : (source, target) ∈ rest
        · have hmem : (source, target) ∈ edge :: rest :=
            List.mem_cons_of_mem edge htailMem
          rw [if_pos hmem]
          have htail : weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ load :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then load else 0) _
              (weightedDirectedEdgeLoad_constantMap_eqv_indicator
                load source target rest hparts.2)
              (by rw [if_pos htailMem]; exact Q'.eqv_refl load)
          change 0 + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ load
          exact Q'.eqv_trans _ (0 + load) _
            (Q'.add_eqv_congr_left 0 _ _ htail)
            (Q'.eqv_of_eq (Q'.zero_add' load))
        · have hnotmem : (source, target) ∉ edge :: rest := by
            intro hmem
            rcases List.mem_cons.mp hmem with hedge | hrest
            · exact hne hedge
            · exact htailMem hrest
          rw [if_neg hnotmem]
          have htail : weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0 :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then load else 0) _
              (weightedDirectedEdgeLoad_constantMap_eqv_indicator
                load source target rest hparts.2)
              (by rw [if_neg htailMem]; exact Q'.eqv_refl 0)
          change 0 + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0
          exact Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr_left 0 _ _ htail)
            (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem weightedDirectedEdgeLoad_constantMap_le
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (hnodup : edges.Nodup)
    (load : Q') (hload : (0 : Q') ≤ load)
    (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≤ load := by
  have heq := weightedDirectedEdgeLoad_constantMap_eqv_indicator
    load source target edges hnodup
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
  by_cases hmem : (source, target) ∈ edges
  · rw [if_pos hmem]
    exact Q'.le_refl' load
  · rw [if_neg hmem]
    exact hload

/-! ## 3. Simple length-linear path budgets and literal occurrences -/

def cutoffTwoSimpleFullLengthLinearPathBudget
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
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
          coefficient path
    else 0
  else 0

theorem cutoffTwoSimpleFullLengthLinearPathBudget_eqv_of_mem
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoSimpleFullLengthLinearPathBudget
        later coefficient left right ≈
      let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        left right hleft hright
      Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path) *
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
          coefficient path := by
  unfold cutoffTwoSimpleFullLengthLinearPathBudget
  rw [dif_pos hleft, dif_pos hright]
  exact Q'.eqv_refl _

theorem cutoffTwo_edgeFloor_mul_endpoint_sq_le_simpleLengthLinearPathBudget
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      cutoffTwoSimpleFullLengthLinearPathBudget
        later coefficient left right := by
  unfold cutoffTwoSimpleFullLengthLinearPathBudget
  rw [dif_pos hleft, dif_pos hright]
  exact
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_length_mul_linearEnergy
      coefficient
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) later 0)
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
          cutoffTwoHalfCoupling (by decide) later 0))
      (centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
        cutoffTwoHalfCoupling (by decide) later 0)
      hleft
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        left right hleft hright)

/-- Every edge of one loop-erased endpoint path receives the stationary
endpoint-pair weight times the path length. -/
def cutoffTwoSimpleWeightedPathOccurrences
    (later left right : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  if hleft : left ∈ cutoffTwoEdgeLoadFullStates later then
    if hright : right ∈ cutoffTwoEdgeLoadFullStates later then
      let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
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

theorem cutoffTwoSimpleWeightedPathOccurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoSimpleWeightedPathOccurrences later left right)
        coefficient (cutoffTwoEdgeLoadKernel later) ≈
      (cutoffTwoEdgeLoadWeight later left *
          cutoffTwoEdgeLoadWeight later right) *
        cutoffTwoSimpleFullLengthLinearPathBudget
          later coefficient left right := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
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
  unfold cutoffTwoSimpleWeightedPathOccurrences
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
      (cutoffTwoSimpleFullLengthLinearPathBudget_eqv_of_mem
        later coefficient left right hleft hright))

private theorem cutoffTwoWeight_nonnegative_local
    (later state : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadWeight later state := by
  unfold cutoffTwoEdgeLoadWeight
  exact centralPhysicalRowMarginal_nonnegative
    (by decide) later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 state)

/-- A fixed directed edge is charged at most once by one loop-erased path;
its one-path load is therefore at most pairWeight times sector size. -/
theorem cutoffTwoSimpleWeightedPathEdgeLoad_le_pairWeight_mul_sectorSize
    (later left right source target : Nat)
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    weightedDirectedEdgeLoad
        (cutoffTwoSimpleWeightedPathOccurrences later left right)
        source target ≤
      (cutoffTwoEdgeLoadWeight later left *
          cutoffTwoEdgeLoadWeight later right) *
        Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    cutoffTwoHalfCoupling (by decide) later 0
    left right hleft hright
  let pairWeight := cutoffTwoEdgeLoadWeight later left *
    cutoffTwoEdgeLoadWeight later right
  let pathLength :=
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
      path
  let load := pairWeight * Q'.ofNat pathLength
  have hpairWeight0 : (0 : Q') ≤ pairWeight :=
    Q'.mul_nonneg _ _
      (cutoffTwoWeight_nonnegative_local later left)
      (cutoffTwoWeight_nonnegative_local later right)
  have hload0 : (0 : Q') ≤ load :=
    Q'.mul_nonneg _ _ hpairWeight0
      (Q'.ofNat_le_ofNat (Nat.zero_le pathLength))
  have hone := weightedDirectedEdgeLoad_constantMap_le
    (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
      path)
    (cutoffTwoSimplePositivePath_directedEdges_nodup
      later left right hleft hright)
    load hload0 source target
  have hlength : pathLength ≤
      (cutoffTwoEdgeLoadFullStates later).length :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
      cutoffTwoHalfCoupling (by decide) later 0
      left right hleft hright
  have hscaled : load ≤
      pairWeight * Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length :=
    Q'.mul_le_mul_of_nonneg_left _ _ pairWeight
      (Q'.ofNat_le_ofNat hlength) hpairWeight0
  unfold cutoffTwoSimpleWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  exact Q'.le_trans' _ _ _ hone hscaled

/-! ## 4. Aggregate every ordered endpoint pair and regroup by edge -/

def cutoffTwoSimpleFullWeightedEdgeOccurrences (later : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (cutoffTwoCanonicalFullEndpointPairs later).flatMap
    (fun pair =>
      cutoffTwoSimpleWeightedPathOccurrences later pair.1 pair.2)

def cutoffTwoSimpleFullPairBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun pair =>
      (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2) *
        cutoffTwoSimpleFullLengthLinearPathBudget
          later coefficient pair.1 pair.2)
    (cutoffTwoCanonicalFullEndpointPairs later)

def cutoffTwoSimpleFullLengthLinearAggregateBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedRectangularEndpointBudget
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoSimpleFullLengthLinearPathBudget later coefficient)

private theorem finiteWeightedRectangularEndpointBudget_eqv_cartesian_local
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

theorem cutoffTwoSimpleFullPairBudget_eqv_aggregateBudget
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoSimpleFullPairBudget later coefficient ≈
      cutoffTwoSimpleFullLengthLinearAggregateBudget
        later coefficient := by
  unfold cutoffTwoSimpleFullPairBudget
    cutoffTwoCanonicalFullEndpointPairs
    cutoffTwoSimpleFullLengthLinearAggregateBudget
  exact Q'.eqv_symm
    (finiteWeightedRectangularEndpointBudget_eqv_cartesian_local
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadWeight later)
      (cutoffTwoSimpleFullLengthLinearPathBudget later coefficient))

theorem cutoffTwoSimpleFullOccurrenceEnergy_eqv_pairBudget
    (later : Nat) (coefficient : Nat → Q') :
    finiteWeightedOccurrenceEnergy
        (cutoffTwoSimpleFullWeightedEdgeOccurrences later)
        coefficient (cutoffTwoEdgeLoadKernel later) ≈
      cutoffTwoSimpleFullPairBudget later coefficient := by
  unfold cutoffTwoSimpleFullWeightedEdgeOccurrences
    cutoffTwoSimpleFullPairBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finiteWeightedOccurrenceEnergy
          (cutoffTwoSimpleWeightedPathOccurrences
            later pair.1 pair.2)
          coefficient (cutoffTwoEdgeLoadKernel later))
      (cutoffTwoCanonicalFullEndpointPairs later)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  apply listQSum_congr_on
  intro pair hpair
  have hparts := (mem_cartesian_iff
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  exact cutoffTwoSimpleWeightedPathOccurrenceEnergy_eqv_pairBudget
    later coefficient pair.1 pair.2 hparts.1 hparts.2

def cutoffTwoSimpleFullEdgeLoad
    (later source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (cutoffTwoSimpleFullWeightedEdgeOccurrences later)
    source target

def cutoffTwoSimpleFullLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoSimpleFullWeightedEdgeOccurrences later)
    coefficient (cutoffTwoEdgeLoadKernel later)

private theorem cutoffTwoSimpleFullOccurrence_mem_full
    (later : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoSimpleFullWeightedEdgeOccurrences later) :
    occurrence.1.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
      occurrence.1.2 ∈ cutoffTwoEdgeLoadFullStates later := by
  unfold cutoffTwoSimpleFullWeightedEdgeOccurrences at hoccurrence
  obtain ⟨pair, hpair, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  have hfull := (mem_cartesian_iff
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  unfold cutoffTwoSimpleWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hfull.1, dif_pos hfull.2] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  rw [← heq]
  exact
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      hfull.1
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0
        pair.1 pair.2 hfull.1 hfull.2)
      edge hedge

theorem cutoffTwoSimpleFullLengthLinearAggregateBudget_eqv_loadedDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoSimpleFullLengthLinearAggregateBudget later coefficient ≈
      cutoffTwoSimpleFullLoadedDirichlet later coefficient := by
  have hregroup :=
    finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (cutoffTwoEdgeLoadFullStates later)
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) later 0)
      coefficient (cutoffTwoEdgeLoadKernel later)
      (cutoffTwoSimpleFullWeightedEdgeOccurrences later)
      (cutoffTwoSimpleFullOccurrence_mem_full later)
  exact Q'.eqv_trans _
    (cutoffTwoSimpleFullPairBudget later coefficient) _
    (Q'.eqv_symm
      (cutoffTwoSimpleFullPairBudget_eqv_aggregateBudget
        later coefficient))
    (Q'.eqv_trans _
      (finiteWeightedOccurrenceEnergy
        (cutoffTwoSimpleFullWeightedEdgeOccurrences later)
        coefficient (cutoffTwoEdgeLoadKernel later)) _
      (Q'.eqv_symm
        (cutoffTwoSimpleFullOccurrenceEnergy_eqv_pairBudget
          later coefficient))
      (Q'.eqv_symm hregroup))

/-! ## 5. The full simple-path edge load is at most sector size -/

private theorem weightedDirectedEdgeLoad_flatMap_eqv
    {Class State : Type} [DecidableEq State]
    (classes : List Class)
    (occurrences : Class → List (WeightedDirectedEdgeOccurrence State))
    (source target : State) :
    weightedDirectedEdgeLoad
        (classes.flatMap occurrences) source target ≈
      listQSum
        (fun item =>
          weightedDirectedEdgeLoad (occurrences item) source target)
        classes := by
  unfold weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

theorem cutoffTwoSimpleFullEdgeLoad_eqv_pathLoadSum
    (later source target : Nat) :
    cutoffTwoSimpleFullEdgeLoad later source target ≈
      listQSum
        (fun pair => weightedDirectedEdgeLoad
          (cutoffTwoSimpleWeightedPathOccurrences
            later pair.1 pair.2) source target)
        (cutoffTwoCanonicalFullEndpointPairs later) := by
  unfold cutoffTwoSimpleFullEdgeLoad
    cutoffTwoSimpleFullWeightedEdgeOccurrences
  exact weightedDirectedEdgeLoad_flatMap_eqv
    (cutoffTwoCanonicalFullEndpointPairs later)
    (fun pair => cutoffTwoSimpleWeightedPathOccurrences
      later pair.1 pair.2) source target

theorem cutoffTwoSimplePathLoadSum_le_sizeWeightedPairSum
    (later source target : Nat) :
    listQSum
        (fun pair => weightedDirectedEdgeLoad
          (cutoffTwoSimpleWeightedPathOccurrences
            later pair.1 pair.2) source target)
        (cutoffTwoCanonicalFullEndpointPairs later) ≤
      listQSum
        (fun pair =>
          Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
            (cutoffTwoEdgeLoadWeight later pair.1 *
              cutoffTwoEdgeLoadWeight later pair.2))
        (cutoffTwoCanonicalFullEndpointPairs later) := by
  apply listQSum_mono
  intro pair hpair
  have hparts := (mem_cartesian_iff
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  have hone :=
    cutoffTwoSimpleWeightedPathEdgeLoad_le_pairWeight_mul_sectorSize
      later pair.1 pair.2 source target hparts.1 hparts.2
  exact Q'.le_trans' _ _ _ hone
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2)
        (Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length)))

theorem cutoffTwoFullEndpointPairWeightSum_eqv_mass_square
    (later : Nat) :
    listQSum
        (fun pair =>
          cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2)
        (cutoffTwoCanonicalFullEndpointPairs later) ≈
      centralPhysicalFiniteVacuumSectorMass
          cutoffTwoHalfCoupling (by decide) later 0 *
        centralPhysicalFiniteVacuumSectorMass
          cutoffTwoHalfCoupling (by decide) later 0 := by
  change listQSum
      (fun pair =>
        cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2)
      (cartesian
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later)) ≈
    listQSum (cutoffTwoEdgeLoadWeight later)
        (cutoffTwoEdgeLoadFullStates later) *
      listQSum (cutoffTwoEdgeLoadWeight later)
        (cutoffTwoEdgeLoadFullStates later)
  exact listQSum_cartesian_product
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadWeight later)
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)

theorem cutoffTwoSizeWeightedPairSum_eqv_size_mul_mass_square
    (later : Nat) :
    listQSum
        (fun pair =>
          Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
            (cutoffTwoEdgeLoadWeight later pair.1 *
              cutoffTwoEdgeLoadWeight later pair.2))
        (cutoffTwoCanonicalFullEndpointPairs later) ≈
      Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
        (centralPhysicalFiniteVacuumSectorMass
            cutoffTwoHalfCoupling (by decide) later 0 *
          centralPhysicalFiniteVacuumSectorMass
            cutoffTwoHalfCoupling (by decide) later 0) := by
  let sizeQ := Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length
  let pairWeight : Nat × Nat → Q' := fun pair =>
    cutoffTwoEdgeLoadWeight later pair.1 *
      cutoffTwoEdgeLoadWeight later pair.2
  let pairs := cutoffTwoCanonicalFullEndpointPairs later
  let mass := centralPhysicalFiniteVacuumSectorMass
    cutoffTwoHalfCoupling (by decide) later 0
  have hfactor : listQSum (fun pair => sizeQ * pairWeight pair) pairs ≈
      sizeQ * listQSum pairWeight pairs :=
    listQSum_mul_left sizeQ pairWeight pairs
  have hmass : listQSum pairWeight pairs ≈ mass * mass :=
    cutoffTwoFullEndpointPairWeightSum_eqv_mass_square later
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.mul_eqv_congr_left sizeQ
      (listQSum pairWeight pairs) (mass * mass) hmass)

theorem cutoffTwoSimpleFullEdgeLoad_le_sectorSize
    (later source target : Nat) :
    cutoffTwoSimpleFullEdgeLoad later source target ≤
      Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length := by
  let sizeQ := Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length
  let mass := centralPhysicalFiniteVacuumSectorMass
    cutoffTwoHalfCoupling (by decide) later 0
  have hsize0 : (0 : Q') ≤ sizeQ :=
    Q'.ofNat_le_ofNat
      (Nat.zero_le (cutoffTwoEdgeLoadFullStates later).length)
  have hmassScale : sizeQ * (mass * mass) ≤ sizeQ * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ sizeQ
      (cutoffTwoFullSectorMass_square_le_one later) hsize0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoSimpleFullEdgeLoad_eqv_pathLoadSum
        later source target))
    (Q'.le_trans' _ _ _
      (cutoffTwoSimplePathLoadSum_le_sizeWeightedPairSum
        later source target)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (cutoffTwoSizeWeightedPairSum_eqv_size_mul_mass_square later))
        (Q'.le_trans' _ _ _ hmassScale
          (Q'.le_of_eqv (Q'.mul_one_eqv sizeQ)))))

/-! ## 6. Linear-carrier full-sector coercivity -/

def cutoffTwoLinearFullSectorCost (later : Nat) : Q' :=
  1 + Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length

theorem cutoffTwoLinearFullSectorCost_pos (later : Nat) :
    (0 : Q') < cutoffTwoLinearFullSectorCost later := by
  unfold cutoffTwoLinearFullSectorCost
  exact Q'.pos_add_nonneg (by decide)
    (Q'.ofNat_le_ofNat
      (Nat.zero_le (cutoffTwoEdgeLoadFullStates later).length))

theorem cutoffTwoSimpleFullEdgeLoad_le_linearCost
    (later source target : Nat) :
    cutoffTwoSimpleFullEdgeLoad later source target ≤
      cutoffTwoLinearFullSectorCost later := by
  have hsize := cutoffTwoSimpleFullEdgeLoad_le_sectorSize
    later source target
  have hadd := Q'.add_le_add_right
    (0 : Q') 1
    (Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length)
    (by decide : (0 : Q') ≤ 1)
  have hsizeCost : Q'.ofNat
        (cutoffTwoEdgeLoadFullStates later).length ≤
      cutoffTwoLinearFullSectorCost later := by
    unfold cutoffTwoLinearFullSectorCost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hsize hsizeCost

private theorem cutoffTwoKernel_nonnegative_local
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoEdgeLoadKernel centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_nonnegative
    (by decide) later 0 _ _

theorem cutoffTwoSimpleFullLoadedDirichlet_le_linearCost_mul_fullDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoSimpleFullLoadedDirichlet later coefficient ≤
      cutoffTwoLinearFullSectorCost later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  unfold cutoffTwoSimpleFullLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
    cutoffTwoFullSectorDirichlet
  exact finiteLoadedDirichletBlock_le_scale_mul
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    coefficient (cutoffTwoEdgeLoadKernel later)
    (weightedDirectedEdgeLoad
      (cutoffTwoSimpleFullWeightedEdgeOccurrences later))
    (cutoffTwoLinearFullSectorCost later)
    (cutoffTwoKernel_nonnegative_local later)
    (fun source _hsource target _htarget => by
      change cutoffTwoSimpleFullEdgeLoad later source target ≤
        cutoffTwoLinearFullSectorCost later
      exact cutoffTwoSimpleFullEdgeLoad_le_linearCost
        later source target)

theorem cutoffTwo_edgeFloor_mul_fullVariance_le_simpleAggregateBudget
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoSimpleFullLengthLinearAggregateBudget
        later coefficient := by
  unfold cutoffTwoFullSectorPairwiseVariance
    centralPhysicalFiniteVacuumSectorPairwiseVariance
    finiteWeightedPairwiseVariance finiteJointDirichletEnergy
    cutoffTwoSimpleFullLengthLinearAggregateBudget
  exact floor_mul_finiteStationaryRectangularVariance_le_endpointBudget
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadWeight later) coefficient
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0)
    (cutoffTwoSimpleFullLengthLinearPathBudget later coefficient)
    (fun state _ => cutoffTwoWeight_nonnegative_local later state)
    (fun state _ => cutoffTwoWeight_nonnegative_local later state)
    (fun left hleft right hright =>
      cutoffTwo_edgeFloor_mul_endpoint_sq_le_simpleLengthLinearPathBudget
        later coefficient left right hleft hright)

/-- Retaining literal simple-path edge congestion reduces the explicit
full-sector cost from carrier size squared to carrier size. -/
theorem cutoffTwo_edgeFloor_mul_fullVariance_le_linearCost_mul_Dirichlet
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoLinearFullSectorCost later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  exact Q'.le_trans' _ _ _
    (cutoffTwo_edgeFloor_mul_fullVariance_le_simpleAggregateBudget
      later coefficient)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (cutoffTwoSimpleFullLengthLinearAggregateBudget_eqv_loadedDirichlet
          later coefficient))
      (cutoffTwoSimpleFullLoadedDirichlet_le_linearCost_mul_fullDirichlet
        later coefficient))

def cutoffTwoLinearFullSectorClearedDirichletAt
    (later : Nat) (hlater : 2 ≤ later)
    (massFloor : Q')
    (hmass : massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoCapacityClearedDirichletAt later
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) later 0)
      (cutoffTwoLinearFullSectorCost later)
      massFloor where
  later_ge := hlater
  total_cost_pos := cutoffTwoLinearFullSectorCost_pos later
  mass_floor_le := hmass
  cleared_coercivity :=
    cutoffTwo_edgeFloor_mul_fullVariance_le_linearCost_mul_Dirichlet later

/-! ## 7. Degree-24 ambient cost and the remaining cofinal ratio -/

def cutoffTwoAmbientLinearFullSectorCost (later : Nat) : Q' :=
  1 + Q'.ofNat
    (centralPhysicalFiniteVacuumSectorAmbientCarrierSize later 0)

theorem cutoffTwoLinearFullSectorCost_le_ambient
    (later : Nat) :
    cutoffTwoLinearFullSectorCost later ≤
      cutoffTwoAmbientLinearFullSectorCost later := by
  have hsize :=
    centralPhysicalFiniteVacuumSectorIndices_length_le_ambient
      cutoffTwoHalfCoupling (by decide) later 0
  have hcast := Q'.ofNat_le_ofNat hsize
  unfold cutoffTwoLinearFullSectorCost
    cutoffTwoAmbientLinearFullSectorCost cutoffTwoEdgeLoadFullStates
  exact Q'.add_le_add_left 1 _ _ hcast

theorem cutoffTwoAmbientLinearFullSectorCost_pos (later : Nat) :
    (0 : Q') < cutoffTwoAmbientLinearFullSectorCost later := by
  unfold cutoffTwoAmbientLinearFullSectorCost
  exact Q'.pos_add_nonneg (by decide)
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

theorem cutoffTwoAmbientLinearFullSectorCost_eqv_power
    (later : Nat) :
    cutoffTwoAmbientLinearFullSectorCost later ≈
      1 + Q'.ofNat ((later + 1) ^ 24) := by
  unfold cutoffTwoAmbientLinearFullSectorCost
    centralPhysicalFiniteVacuumSectorAmbientCarrierSize
  rw [centralLowerFaceIds_zero_length]
  exact Q'.eqv_refl _

theorem cutoffTwo_edgeFloor_mul_fullVariance_le_ambientLinearCost_mul_Dirichlet
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoAmbientLinearFullSectorCost later *
        cutoffTwoFullSectorDirichlet later coefficient := by
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    (cutoffTwoLinearFullSectorCost_le_ambient later)
    (cutoffTwoFullSectorDirichlet_nonnegative later coefficient)
  exact Q'.le_trans' _ _ _
    (cutoffTwo_edgeFloor_mul_fullVariance_le_linearCost_mul_Dirichlet
      later coefficient)
    hscale

def cutoffTwoAmbientLinearFullSectorClearedDirichletAt
    (later : Nat) (hlater : 2 ≤ later)
    (massFloor : Q')
    (hmass : massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoCapacityClearedDirichletAt later
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) later 0)
      (cutoffTwoAmbientLinearFullSectorCost later)
      massFloor where
  later_ge := hlater
  total_cost_pos := cutoffTwoAmbientLinearFullSectorCost_pos later
  mass_floor_le := hmass
  cleared_coercivity :=
    cutoffTwo_edgeFloor_mul_fullVariance_le_ambientLinearCost_mul_Dirichlet
      later

structure CutoffTwoCofinalAmbientLinearFullSectorRatio
    (effectiveFloor massFloor : Q') : Type 1 where
  effective_floor_pos : (0 : Q') < effectiveFloor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  mass_floor_le : ∀ request,
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) (anchor request) 0
  ratio_bound : ∀ request,
    effectiveFloor *
        cutoffTwoAmbientLinearFullSectorCost (anchor request) ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalAmbientLinearFullSectorRatio

def toCofinalCapacityClearedGluing
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalAmbientLinearFullSectorRatio
      effectiveFloor massFloor) :
    CutoffTwoCofinalCapacityClearedGluing
      effectiveFloor massFloor where
  effective_floor_pos := family.effective_floor_pos
  mass_floor_pos := family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  baseFloor := fun request =>
    centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) (family.anchor request) 0
  totalCost := fun request =>
    cutoffTwoAmbientLinearFullSectorCost (family.anchor request)
  cleared := fun request =>
    cutoffTwoAmbientLinearFullSectorClearedDirichletAt
      (family.anchor request)
      (Nat.le_trans (Nat.le_max_left 2 request)
        (family.anchor_ge request))
      massFloor (family.mass_floor_le request)
  ratio_bound := family.ratio_bound

def toCompletedStrictContractionData
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalAmbientLinearFullSectorRatio
      effectiveFloor massFloor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalCapacityClearedGluing
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalAmbientLinearFullSectorRatio

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoSimplePositivePath_directedEdges_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoSimpleWeightedPathOccurrenceEnergy_eqv_pairBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoSimpleFullLengthLinearAggregateBudget_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoSimpleFullEdgeLoad_le_sectorSize
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwo_edgeFloor_mul_fullVariance_le_linearCost_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoLinearFullSectorClearedDirichletAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoLinearFullSectorCost_le_ambient
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwoAmbientLinearFullSectorCost_eqv_power
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.cutoffTwo_edgeFloor_mul_fullVariance_le_ambientLinearCost_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.CutoffTwoCofinalAmbientLinearFullSectorRatio.toCompletedStrictContractionData
