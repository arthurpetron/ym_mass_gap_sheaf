/-
# One-body vacuum-root traffic for the full finite physical sector

The full pairwise variance has been reduced to twice the weighted square
distance of the same coefficient from the physical vacuum.  This module
routes each such one-body demand along the existing loop-erased positive
physical-kernel path from that state to the vacuum.

Each literal directed occurrence receives twice the state weight times its
path length.  Finite Cauchy--Schwarz pays the rooted endpoint square, and the
generic duplicate-preserving regrouping theorem contracts all occurrences to
one explicit coefficient-independent directed-edge traffic function.

No comparison between that traffic and the physical kernel is asserted here.
In particular no cutoff-uniform gap, completion or continuum limit, continuum
QFT, or Clay conclusion is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K half state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K half state := by
  exact centralPhysicalRowMarginal_nonnegative hw K half
    (centralPhysicalFiniteStateAt w hw K half state)

/-! ## 1. One rooted Cauchy budget per physical state -/

def centralPhysicalFiniteVacuumSectorRootRawPathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') (state : Nat) : Q' :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half then
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    Q'.ofNat (PositiveKernelChainIn.edgeLength path) *
      listQSum (fun value => value * value)
        (PositiveKernelChainIn.edgeDifferences coefficient path)
  else 0

theorem centralPhysicalFiniteVacuumSector_root_sq_le_rawPathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    (coefficient state + -coefficient 0) *
        (coefficient state + -coefficient 0) ≤
      centralPhysicalFiniteVacuumSectorRootRawPathBudget
        w hw K half coefficient state := by
  unfold centralPhysicalFiniteVacuumSectorRootRawPathBudget
  rw [dif_pos hstate]
  exact PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum
    coefficient
    (centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half))

/-- Twice the weighted one-body path budget.  The doubling is exactly the
factor in the pairwise-to-root contraction. -/
def centralPhysicalFiniteVacuumSectorRootRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun state =>
      let term := centralPhysicalFiniteWeight w hw K half state *
        centralPhysicalFiniteVacuumSectorRootRawPathBudget
          w hw K half coefficient state
      term + term)
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootRawBudget
        w hw K half coefficient := by
  have hroot :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rootVariance
      w hw K half coefficient
  refine Q'.le_trans' _ _ _ hroot ?_
  unfold centralPhysicalFiniteVacuumSectorRootVariance
    finiteWeightedRootVariance
    centralPhysicalFiniteVacuumSectorRootRawBudget
  refine Q'.le_trans' _
    (listQSum
      (fun state =>
        let term := centralPhysicalFiniteWeight w hw K half state *
          ((coefficient state + -coefficient 0) *
            (coefficient state + -coefficient 0))
        term + term)
      (centralPhysicalFiniteVacuumSectorIndices w hw K half)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_add _ _
          (centralPhysicalFiniteVacuumSectorIndices w hw K half)))
  · apply listQSum_mono
    intro state hstate
    let weight := centralPhysicalFiniteWeight w hw K half state
    let rootSquare := (coefficient state + -coefficient 0) *
      (coefficient state + -coefficient 0)
    let pathBudget :=
      centralPhysicalFiniteVacuumSectorRootRawPathBudget
        w hw K half coefficient state
    have hscaled : weight * rootSquare ≤ weight * pathBudget :=
      Q'.mul_le_mul_of_nonneg_left _ _ weight
        (centralPhysicalFiniteVacuumSector_root_sq_le_rawPathBudget
          w hw K half coefficient state hstate)
        (centralPhysicalFiniteWeight_nonnegative_local
          w hw K half state)
    exact Q'.add_le_add hscaled hscaled

/-! ## 2. Literal doubled root-path occurrences -/

def centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K half state : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half then
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    let singleLoad :=
      centralPhysicalFiniteWeight w hw K half state *
        Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    (PositiveKernelChainIn.directedEdges path).map
      (fun edge => (edge, singleLoad + singleLoad))
  else []

def centralPhysicalFiniteVacuumSectorRootFlowOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K half).flatMap
    (centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
      w hw K half)

/-- The local observable-independent traffic created by all doubled
state-to-vacuum demands. -/
def centralPhysicalFiniteVacuumSectorRootFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half)
    source target

def centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half)
    coefficient (fun _ _ => 1)

def centralPhysicalFiniteVacuumSectorRootRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half)
    coefficient (fun _ _ => 1)

theorem centralPhysicalFiniteVacuumSectorRootWeightedPathRawOccurrenceEnergy_eqv_budget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    finiteWeightedOccurrenceEnergy
        (centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
          w hw K half state)
        coefficient (fun _ _ => 1) ≈
      let term := centralPhysicalFiniteWeight w hw K half state *
        centralPhysicalFiniteVacuumSectorRootRawPathBudget
          w hw K half coefficient state
      term + term := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K half state 0 hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
  let stateWeight := centralPhysicalFiniteWeight w hw K half state
  let lengthQ := Q'.ofNat (PositiveKernelChainIn.edgeLength path)
  let singleLoad := stateWeight * lengthQ
  let edgeSquare : Nat × Nat → Q' := fun edge =>
    (coefficient edge.1 + -coefficient edge.2) *
      (coefficient edge.1 + -coefficient edge.2)
  have hedges := PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences
    coefficient path
  unfold centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
  rw [dif_pos hstate]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((singleLoad + singleLoad) *
      listQSum edgeSquare (PositiveKernelChainIn.directedEdges path)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((singleLoad + singleLoad) *
        listQSum (fun edge => (1 : Q') * edgeSquare edge)
          (PositiveKernelChainIn.directedEdges path)) _ ?_ ?_
    · exact listQSum_mul_left (singleLoad + singleLoad) _ _
    · exact Q'.mul_eqv_congr_left (singleLoad + singleLoad) _ _
        (Q'.eqv_trans _ _ _
          (listQSum_congr
            (fun edge => Q'.one_mul_eqv (edgeSquare edge)) _)
          (Q'.eqv_refl _))
  · refine Q'.eqv_trans _
      (singleLoad * listQSum edgeSquare
          (PositiveKernelChainIn.directedEdges path) +
        singleLoad * listQSum edgeSquare
          (PositiveKernelChainIn.directedEdges path)) _
      (Q'.add_mul_eqv _ _ _) ?_
    apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (stateWeight *
          (lengthQ * listQSum edgeSquare
            (PositiveKernelChainIn.directedEdges path))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.mul_eqv_congr_left stateWeight _ _ ?_
      refine Q'.eqv_trans _
        (lengthQ * listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path)) _
        (Q'.mul_eqv_congr_left lengthQ _ _ hedges) ?_
      unfold centralPhysicalFiniteVacuumSectorRootRawPathBudget
      rw [dif_pos hstate]
      exact Q'.eqv_refl _
    · refine Q'.eqv_trans _
        (stateWeight *
          (lengthQ * listQSum edgeSquare
            (PositiveKernelChainIn.directedEdges path))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.mul_eqv_congr_left stateWeight _ _ ?_
      refine Q'.eqv_trans _
        (lengthQ * listQSum (fun value => value * value)
          (PositiveKernelChainIn.edgeDifferences coefficient path)) _
        (Q'.mul_eqv_congr_left lengthQ _ _ hedges) ?_
      unfold centralPhysicalFiniteVacuumSectorRootRawPathBudget
      rw [dif_pos hstate]
      exact Q'.eqv_refl _

theorem centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_rawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy
        w hw K half coefficient ≈
      centralPhysicalFiniteVacuumSectorRootRawBudget
        w hw K half coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy
    centralPhysicalFiniteVacuumSectorRootFlowOccurrences
    centralPhysicalFiniteVacuumSectorRootRawBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        finiteWeightedOccurrenceEnergy
          (centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
            w hw K half state)
          coefficient (fun _ _ => 1))
      (centralPhysicalFiniteVacuumSectorIndices w hw K half)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro state hstate
    exact
      centralPhysicalFiniteVacuumSectorRootWeightedPathRawOccurrenceEnergy_eqv_budget
        w hw K half coefficient state hstate

/-! ## 3. Support, positivity, regrouping, and the full rooted flow theorem -/

theorem centralPhysicalFiniteVacuumSectorRootOccurrence_mem_sector
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K half ∧
      occurrence.1.2 ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using PositiveKernelChainIn.directedEdges_mem_support hstate
    (centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half))
    edge hedge

theorem centralPhysicalFiniteVacuumSectorRootOccurrence_kernel_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half) :
    (0 : Q') < centralPhysicalFiniteKernel
      w hw K half occurrence.1.1 occurrence.1.2 := by
  unfold centralPhysicalFiniteVacuumSectorRootFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact PositiveKernelChainIn.directedEdges_kernel_pos
    (centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half))
    edge hedge

theorem centralPhysicalFiniteVacuumSectorRootOccurrence_load_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralPhysicalFiniteVacuumSectorRootFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ :=
    List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  have hsingle : (0 : Q') ≤
      centralPhysicalFiniteWeight w hw K half state *
        Q'.ofNat
          (PositiveKernelChainIn.edgeLength
            (centralPhysicalFiniteVacuumSectorSimplePositivePath
              w hw K half state 0 hstate
              (zero_mem_centralPhysicalFiniteVacuumSectorIndices
                w hw K half))) :=
    Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K half state)
      (Q'.ofNat_le_ofNat (Nat.zero_le _))
  exact Q'.zero_le_add _ _ hsingle hsingle

theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorRootFlowLoad
      w hw K half source target := by
  unfold centralPhysicalFiniteVacuumSectorRootFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralPhysicalFiniteVacuumSectorRootOccurrence_load_nonnegative
      w hw K half)
    source target

theorem centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_loadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy
        w hw K half coefficient ≈
      centralPhysicalFiniteVacuumSectorRootRawLoadedDirichlet
        w hw K half coefficient := by
  exact Q'.eqv_symm
    (finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
      (centralPhysicalFiniteVacuumSectorIndices w hw K half)
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K half)
      coefficient (fun _ _ => 1)
      (centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half)
      (centralPhysicalFiniteVacuumSectorRootOccurrence_mem_sector
        w hw K half))

/-- The complete pairwise variance of the same finite observable is bounded
by the loaded Dirichlet form of one explicit local vacuum-root traffic. -/
theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootRawLoadedDirichlet
        w hw K half coefficient := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawBudget
      w hw K half coefficient)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_rawBudget
            w hw K half coefficient))
        (centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_loadedDirichlet
          w hw K half coefficient)))

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSector_root_sq_le_rawPathBudget
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawBudget
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_rawBudget
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSectorRootOccurrence_mem_sector
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSectorRootOccurrence_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_loadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawLoadedDirichlet
