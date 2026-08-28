/-
# Mass-normalized resistance flow on the full BF4 vacuum sector

The full pairwise variance is first contracted to twice the weighted square
distance from the physical vacuum.  For each state, exact resistance
Cauchy--Schwarz then absorbs every physical conductance along the existing
loop-free positive path before the paths are aggregated.

The resulting directed-edge load has a canonical conditional normalization

    normalizedLoad = resistanceFlowLoad / componentMass.

A pointwise estimate

    fraction * normalizedLoad(source,target) <= 1

therefore compiles to

    fraction * pairwiseVariance
      <= componentMass * physicalDirichlet,

and hence to the existing posterior-variance and completed-transfer gap
compiler without a separate component-mass loss.  Every finite cutoff has a
strictly positive explicit fraction, obtained from its total normalized
resistance traffic.  The remaining cofinal frontier is exactly one uniform
bound on the normalized directed-edge congestion.

This construction avoids the global minimum physical edge and is not covered
by the root-linear-ratio no-go theorem.  No cofinal congestion bound,
thermodynamic or continuum limit, continuum QFT, or Clay conclusion is
asserted here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
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
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedPairwiseGapBridge
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

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

private theorem recipPos_mul_eqv_one_local
    (value : Q') (hvalue : (0 : Q') < value) :
    Q'.recipPos value hvalue * value ≈ 1 := by
  exact Q'.eqv_trans _ (value * Q'.recipPos value hvalue) _
    (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv value hvalue)

private theorem mass_mul_divPos_eqv_local
    (mass value : Q') (hmass : (0 : Q') < mass) :
    mass * Q'.divPos value mass hmass ≈ value := by
  let reciprocal := Q'.recipPos mass hmass
  unfold Q'.divPos
  change mass * (value * reciprocal) ≈ value
  refine Q'.eqv_trans _ ((mass * value) * reciprocal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv mass value reciprocal)) ?_
  refine Q'.eqv_trans _ ((value * mass) * reciprocal) _
    (Q'.mul_eqv_congr_right _ _ reciprocal
      (Q'.mul_comm_eqv mass value)) ?_
  refine Q'.eqv_trans _ (value * (mass * reciprocal)) _
    (Q'.mul_assoc_eqv value mass reciprocal) ?_
  refine Q'.eqv_trans _ (value * 1) _
    (Q'.mul_eqv_congr_left value _ _
      (Q'.mul_recipPos_eqv mass hmass)) ?_
  exact Q'.mul_one_eqv value

/-! ## 1. Exact full-sector resistance routing -/

def centralPhysicalFiniteVacuumSectorRootResistancePathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') (state : Nat) : Q' :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half then
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
        path *
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
        coefficient path
  else 0

theorem centralPhysicalFiniteVacuumSector_root_sq_le_resistancePathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    (coefficient state + -coefficient 0) *
        (coefficient state + -coefficient 0) ≤
      centralPhysicalFiniteVacuumSectorRootResistancePathBudget
        w hw K half coefficient state := by
  unfold centralPhysicalFiniteVacuumSectorRootResistancePathBudget
  rw [dif_pos hstate]
  exact
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.endpointDifference_sq_le_resistance_mul_linearEnergy
      coefficient
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K half state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half))

def centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun state =>
      centralPhysicalFiniteWeight w hw K half state *
        centralPhysicalFiniteVacuumSectorRootResistancePathBudget
          w hw K half coefficient state)
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)

def centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
      w hw K half coefficient +
    centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
      w hw K half coefficient

private theorem centralPhysicalFiniteVacuumSectorRootVariance_le_rootResistanceSingleRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
        w hw K half coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRootVariance
    finiteWeightedRootVariance
    centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
  apply listQSum_mono
  intro state hstate
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (centralPhysicalFiniteVacuumSector_root_sq_le_resistancePathBudget
      w hw K half coefficient state hstate)
    (centralPhysicalFiniteWeight_nonnegative_local w hw K half state)

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootResistanceRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
        w hw K half coefficient := by
  have hroot :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rootVariance
      w hw K half coefficient
  exact Q'.le_trans' _ _ _ hroot
    (Q'.add_le_add
      (centralPhysicalFiniteVacuumSectorRootVariance_le_rootResistanceSingleRawBudget
        w hw K half coefficient)
      (centralPhysicalFiniteVacuumSectorRootVariance_le_rootResistanceSingleRawBudget
        w hw K half coefficient))

/-! ## 2. Literal doubled resistance occurrences -/

def centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K half state : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half then
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    let singleLoad := centralPhysicalFiniteWeight w hw K half state *
      BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
        path
    (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
      path).map (fun edge => (edge, singleLoad + singleLoad))
  else []

def centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K half).flatMap
    (centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences
      w hw K half)

def centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
      w hw K half)
    source target

def centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
      w hw K half)
    coefficient (centralPhysicalFiniteKernel w hw K half)

def centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
      w hw K half)
    coefficient (centralPhysicalFiniteKernel w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrenceEnergy_eqv_budget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    finiteWeightedOccurrenceEnergy
        (centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences
          w hw K half state)
        coefficient (centralPhysicalFiniteKernel w hw K half) ≈
      let term := centralPhysicalFiniteWeight w hw K half state *
        centralPhysicalFiniteVacuumSectorRootResistancePathBudget
          w hw K half coefficient state
      term + term := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K half state 0 hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
  let weight := centralPhysicalFiniteWeight w hw K half state
  let pathResistance :=
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
      path
  let singleLoad := weight * pathResistance
  let edgeEnergy : Nat × Nat → Q' := fun edge =>
    centralPhysicalFiniteKernel w hw K half edge.1 edge.2 *
      ((coefficient edge.1 + -coefficient edge.2) *
        (coefficient edge.1 + -coefficient edge.2))
  have hlinear :=
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.linearEnergy_eqv_directedEdges_sum
      coefficient path
  unfold
    centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences
  rw [dif_pos hstate]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((singleLoad + singleLoad) *
      listQSum edgeEnergy
        (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path)) _ ?_ ?_
  · exact listQSum_mul_left (singleLoad + singleLoad) _ _
  · refine Q'.eqv_trans _
      (singleLoad * listQSum edgeEnergy
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path) +
        singleLoad * listQSum edgeEnergy
          (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            path)) _
      (Q'.add_mul_eqv _ _ _) ?_
    apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (weight *
          (pathResistance *
            listQSum edgeEnergy
              (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
                path))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.mul_eqv_congr_left weight _ _ ?_
      refine Q'.eqv_trans _
        (pathResistance *
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
            coefficient path) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left pathResistance _ _
          (Q'.eqv_symm hlinear)
      · unfold centralPhysicalFiniteVacuumSectorRootResistancePathBudget
        rw [dif_pos hstate]
        exact Q'.eqv_refl _

    · refine Q'.eqv_trans _
        (weight *
          (pathResistance *
            listQSum edgeEnergy
              (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
                path))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.mul_eqv_congr_left weight _ _ ?_
      refine Q'.eqv_trans _
        (pathResistance *
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
            coefficient path) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left pathResistance _ _
          (Q'.eqv_symm hlinear)
      · unfold centralPhysicalFiniteVacuumSectorRootResistancePathBudget
        rw [dif_pos hstate]
        exact Q'.eqv_refl _

theorem centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy_eqv_rawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy
        w hw K half coefficient ≈
      centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
        w hw K half coefficient := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy
    centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
    centralPhysicalFiniteVacuumSectorRootResistanceRawBudget
    centralPhysicalFiniteVacuumSectorRootResistanceSingleRawBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        finiteWeightedOccurrenceEnergy
          (centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences
            w hw K half state)
          coefficient (centralPhysicalFiniteKernel w hw K half))
      (centralPhysicalFiniteVacuumSectorIndices w hw K half)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          let term := centralPhysicalFiniteWeight w hw K half state *
            centralPhysicalFiniteVacuumSectorRootResistancePathBudget
              w hw K half coefficient state
          term + term)
        (centralPhysicalFiniteVacuumSectorIndices w hw K half)) _ ?_ ?_
    · apply listQSum_congr_on
      intro state hstate
      exact
        centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrenceEnergy_eqv_budget
          w hw K half coefficient state hstate
    · exact listQSum_add _ _
        (centralPhysicalFiniteVacuumSectorIndices w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootResistanceOccurrence_mem_sector
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
        w hw K half) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K half ∧
      occurrence.1.2 ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      hstate
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K half state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half))
      edge hedge

theorem centralPhysicalFiniteVacuumSectorRootResistanceOccurrence_load_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
        w hw K half) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralPhysicalFiniteVacuumSectorRootResistanceWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  have hsingle : (0 : Q') ≤
      centralPhysicalFiniteWeight w hw K half state *
        BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
          (centralPhysicalFiniteVacuumSectorSimplePositivePath
            w hw K half state 0 hstate
            (zero_mem_centralPhysicalFiniteVacuumSectorIndices
              w hw K half)) :=
    Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K half state)
      (BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance_nonnegative
        (centralPhysicalFiniteVacuumSectorSimplePositivePath
          w hw K half state 0 hstate
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            w hw K half)))
  exact Q'.zero_le_add _ _ hsingle hsingle

theorem centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
        w hw K half source target := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralPhysicalFiniteVacuumSectorRootResistanceOccurrence_load_nonnegative
      w hw K half)
    source target

theorem centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
        w hw K half coefficient ≈
      centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy
        w hw K half coefficient := by
  exact finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K half)
    coefficient (centralPhysicalFiniteKernel w hw K half)
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
      w hw K half)
    (centralPhysicalFiniteVacuumSectorRootResistanceOccurrence_mem_sector
      w hw K half)

theorem centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootResistanceRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorPairwiseVariance
        w hw K half coefficient ≤
      centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
        w hw K half coefficient := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootResistanceRawBudget
      w hw K half coefficient)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteVacuumSectorRootResistanceRawOccurrenceEnergy_eqv_rawBudget
            w hw K half coefficient))
        (Q'.eqv_symm
          (centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
            w hw K half coefficient))))

/-! ## 3. Conditional normalized resistance congestion -/

def centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
      w (Q'.le_of_lt hw) K half source target)
    (centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) K half)

theorem centralPhysicalFiniteVacuumSectorMass_mul_rootResistanceNormalizedFlowLoad_eqv
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) K half *
        centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
          hw K half source target ≈
      centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K half source target := by
  exact mass_mul_divPos_eqv_local _ _
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) K half)

theorem centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
        hw K half source target := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
    Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_nonnegative
      w (Q'.le_of_lt hw) K half source target)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w (Q'.le_of_lt hw) K half)))

/-! ## 4. Normalized edge capacity compiles to the posterior gap -/

structure CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  edge_capacity : ∀ source target,
    fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
          hw K half source target ≤
      1

private theorem finiteJointDirichletBlock_scale_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left => scale * listQSum
        (fun right =>
          joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)))
        rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right => scale *
          (joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

private theorem mass_mul_fraction_mul_normalized_eqv_fraction_mul_load_local
    (mass fraction normalized load : Q')
    (hnormalized : mass * normalized ≈ load) :
    mass * (fraction * normalized) ≈ fraction * load := by
  refine Q'.eqv_trans _ ((mass * fraction) * normalized) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv mass fraction normalized)) ?_
  refine Q'.eqv_trans _ ((fraction * mass) * normalized) _
    (Q'.mul_eqv_congr_right _ _ normalized
      (Q'.mul_comm_eqv mass fraction)) ?_
  refine Q'.eqv_trans _ (fraction * (mass * normalized)) _
    (Q'.mul_assoc_eqv fraction mass normalized) ?_
  exact Q'.mul_eqv_congr_left fraction _ _ hnormalized

namespace CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt

theorem edge_capacity_unnormalized
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
        hw K half)
    (source target : Nat) :
    capacity.fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K half source target ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K half := by
  let mass := centralPhysicalFiniteVacuumSectorMass
    w (Q'.le_of_lt hw) K half
  let normalized :=
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
      hw K half source target
  have hmass : (0 : Q') < mass := by
    unfold mass
    exact centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) K half
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ mass
    (capacity.edge_capacity source target) (Q'.le_of_lt hmass)
  refine Q'.le_trans' _ (mass * (capacity.fraction * normalized)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (mass_mul_fraction_mul_normalized_eqv_fraction_mul_load_local
          mass capacity.fraction normalized
          (centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
            w (Q'.le_of_lt hw) K half source target)
          (centralPhysicalFiniteVacuumSectorMass_mul_rootResistanceNormalizedFlowLoad_eqv
            hw K half source target)))
  · exact Q'.le_trans' _ (mass * 1) _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv mass))

private theorem fraction_mul_loadedDirichlet_le_mass_mul_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
        hw K half)
    (coefficient : Nat → Q') :
    capacity.fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
          w (Q'.le_of_lt hw) K half coefficient ≤
      centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) K half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K half)
          coefficient
          (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half) := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K half
  let load := centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
    w (Q'.le_of_lt hw) K half
  let kernel := centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half
  let mass := centralPhysicalFiniteVacuumSectorMass
    w (Q'.le_of_lt hw) K half
  unfold centralPhysicalFiniteVacuumSectorRootResistanceRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change capacity.fraction *
      finiteJointDirichletBlock states states coefficient
        (fun source target => load source target * kernel source target) ≤
    mass * finiteJointDirichletBlock states states coefficient kernel
  refine Q'.le_trans' _
    (finiteJointDirichletBlock states states coefficient
      (fun source target =>
        capacity.fraction *
          (load source target * kernel source target))) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint_local
          states states coefficient capacity.fraction
          (fun source target => load source target * kernel source target)))
  · refine Q'.le_trans' _
      (finiteJointDirichletBlock states states coefficient
        (fun source target => mass * kernel source target)) _ ?_ ?_
    · unfold finiteJointDirichletBlock
      apply listQSum_mono
      intro source _hsource
      apply listQSum_mono
      intro target _htarget
      have hkernel0 : (0 : Q') ≤ kernel source target := by
        unfold kernel centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K half _ _
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
        (kernel source target)
        (capacity.edge_capacity_unnormalized source target)
        hkernel0
      have hjoint :
          capacity.fraction *
              (load source target * kernel source target) ≤
            mass * kernel source target := by
        exact Q'.le_trans' _
          ((capacity.fraction * load source target) *
            kernel source target) _
          (Q'.le_of_eqv
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) hscaled
      exact Q'.mul_le_mul_of_nonneg_right _ _ _ hjoint
        (SumOfSquares.q_mul_self_nonneg
          (coefficient source + -coefficient target))
    · exact Q'.le_of_eqv
        (finiteJointDirichletBlock_scale_joint_local
          states states coefficient mass kernel)

def toMassNormalizedPairwiseCoercivityData
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
        hw K half) :
    CentralPhysicalFiniteMassNormalizedPairwiseCoercivityData
      w (Q'.le_of_lt hw) K half where
  fraction := capacity.fraction
  fraction_pos := capacity.fraction_pos
  fraction_le_one := capacity.fraction_le_one
  coercivity := fun coefficient => by
    have hroot :=
      centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootResistanceRawLoadedDirichlet
        w (Q'.le_of_lt hw) K half coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ capacity.fraction
      hroot (Q'.le_of_lt capacity.fraction_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.fraction_mul_loadedDirichlet_le_mass_mul_physicalDirichlet
        coefficient)

def toConditionalVarianceGapData
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity :
      CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
        hw K half) :=
  capacity.toMassNormalizedPairwiseCoercivityData
    |>.toConditionalVarianceGapData

end CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt

/-! ## 5. Every finite cutoff has an explicit normalized fraction -/

def centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  listQSum (fun occurrence => occurrence.2)
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowOccurrences
      w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
        w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
  apply listQSum_nonnegative_on
  intro occurrence hoccurrence
  exact centralPhysicalFiniteVacuumSectorRootResistanceOccurrence_load_nonnegative
    w hw K half occurrence hoccurrence

theorem centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_le_totalTraffic
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
        w hw K half source target ≤
      centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
        w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad
    weightedDirectedEdgeLoad
    centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
  apply listQSum_mono
  intro occurrence hoccurrence
  unfold weightedDirectedEdgeIndicator
  by_cases hedge : occurrence.1 = (source, target)
  · rw [if_pos hedge]
    exact Q'.le_refl' _
  · rw [if_neg hedge]
    exact centralPhysicalFiniteVacuumSectorRootResistanceOccurrence_load_nonnegative
      w hw K half occurrence hoccurrence

def centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) K half)

theorem centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
        hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
    Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralPhysicalFiniteVacuumSectorRootResistanceTotalTraffic_nonnegative
      w (Q'.le_of_lt hw) K half)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w (Q'.le_of_lt hw) K half)))

theorem centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad_le_totalTraffic
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
        hw K half source target ≤
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
        hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
    Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (centralPhysicalFiniteVacuumSectorRootResistanceFlowLoad_le_totalTraffic
      w (Q'.le_of_lt hw) K half source target)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (centralPhysicalFiniteVacuumSectorWeightSum_pos
          w (Q'.le_of_lt hw) K half)))

def centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
    hw K half

theorem centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost_pos
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost
        hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic_nonnegative
      hw K half)

def centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Q' :=
  Q'.min' 1
    (Q'.recipPos
      (centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost
        hw K half)
      (centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost_pos
        hw K half))

theorem centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction_pos
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
        hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
  exact q_min_pos_local (by decide) (Q'.recipPos_pos _ _)

theorem centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction_le_one
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
        hw K half ≤ 1 := by
  unfold centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
  exact Q'.min_le_left' _ _

theorem centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction_mul_normalizedFlowLoad_le_one
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
          hw K half *
        centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
          hw K half source target ≤
      1 := by
  let total :=
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTotalTraffic
      hw K half
  let cost :=
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost
      hw K half
  let reciprocal := Q'.recipPos cost
    (centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost_pos
      hw K half)
  let fraction :=
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
      hw K half
  let load :=
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
      hw K half source target
  have hloadTotal : load ≤ total := by
    unfold load total
    exact
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad_le_totalTraffic
        hw K half source target
  have htotalCost : total ≤ cost := by
    unfold cost
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost
    have hadd := Q'.add_le_add_right (0 : Q') 1 total
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  have hfractionReciprocal : fraction ≤ reciprocal := by
    unfold fraction
      centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction
      reciprocal cost
    exact Q'.min_le_right' _ _
  have hload0 : (0 : Q') ≤ load := by
    unfold load
    exact
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad_nonnegative
        hw K half source target
  have hreciprocal0 : (0 : Q') ≤ reciprocal := by
    unfold reciprocal
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ load
    hfractionReciprocal hload0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ reciprocal
    (Q'.le_trans' _ _ _ hloadTotal htotalCost) hreciprocal0
  exact Q'.le_trans' _ (reciprocal * load) _ hfirst
    (Q'.le_trans' _ (reciprocal * cost) _ hsecond
      (Q'.le_of_eqv
        (recipPos_mul_eqv_one_local cost
          (centralPhysicalFiniteVacuumSectorRootResistanceNormalizedTrafficCost_pos
            hw K half))))

def centralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFiniteCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
      hw K half where
  fraction :=
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction hw K half
  fraction_pos :=
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction_pos hw K half
  fraction_le_one :=
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction_le_one
      hw K half
  edge_capacity := fun source target =>
    centralPhysicalFiniteVacuumSectorRootResistanceFiniteFraction_mul_normalizedFlowLoad_le_one
      hw K half source target

/-! ## 6. The exact cofinal normalized-congestion frontier -/

structure FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  bound : Q'
  bound_nonnegative : (0 : Q') ≤ bound
  normalizedFlowLoad_le : ∀ K, start ≤ K → ∀ source target,
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
        hw K 0 source target ≤
      bound

namespace FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound

def cost
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) : Q' :=
  1 + family.bound

theorem cost_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) :
    (0 : Q') < family.cost := by
  unfold cost
  exact Q'.pos_add_nonneg (by decide) family.bound_nonnegative

def fraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) : Q' :=
  Q'.min' 1 (Q'.recipPos family.cost family.cost_pos)

theorem fraction_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) :
    (0 : Q') < family.fraction := by
  unfold fraction
  exact q_min_pos_local (by decide) (Q'.recipPos_pos _ _)

theorem fraction_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) :
    family.fraction ≤ (1 : Q') := by
  unfold fraction
  exact Q'.min_le_left' _ _

theorem normalizedFlowLoad_le_cost
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
        hw K 0 source target ≤
      family.cost := by
  have hbound := family.normalizedFlowLoad_le K hK source target
  have hadd := Q'.add_le_add_right (0 : Q') 1 family.bound
    (by decide : (0 : Q') ≤ 1)
  have hboundCost : family.bound ≤ family.cost := by
    unfold cost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hbound hboundCost

theorem fraction_mul_normalizedFlowLoad_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    family.fraction *
        centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
          hw K 0 source target ≤
      1 := by
  let reciprocal := Q'.recipPos family.cost family.cost_pos
  let load :=
    centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad
      hw K 0 source target
  have hfraction : family.fraction ≤ reciprocal := by
    unfold fraction reciprocal
    exact Q'.min_le_right' _ _
  have hload0 : (0 : Q') ≤ load := by
    unfold load
    exact
      centralPhysicalFiniteVacuumSectorRootResistanceNormalizedFlowLoad_nonnegative
        hw K 0 source target
  have hreciprocal0 : (0 : Q') ≤ reciprocal := by
    unfold reciprocal
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ load
    hfraction hload0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ reciprocal
    (family.normalizedFlowLoad_le_cost hK source target) hreciprocal0
  exact Q'.le_trans' _ (reciprocal * load) _ hfirst
    (Q'.le_trans' _ (reciprocal * family.cost) _ hsecond
      (Q'.le_of_eqv
        (recipPos_mul_eqv_one_local family.cost family.cost_pos)))

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt
      hw K 0 where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  edge_capacity := fun source target =>
    family.fraction_mul_normalizedFlowLoad_le_one hK source target

def toCofinalMassNormalizedPairwiseCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) :
    FixedNomeCofinalMassNormalizedPairwiseCoercivity hw where
  start := family.start
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  coercivity := fun K hK coefficient =>
    (family.finiteCapacityAt K hK).toMassNormalizedPairwiseCoercivityData
      |>.coercivity coefficient

def toCofinalConditionalVarianceFraction
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound
        hw) :=
  family.toCofinalMassNormalizedPairwiseCoercivity
    |>.toCofinalConditionalVarianceFraction

end FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow.centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootResistanceRawLoadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow.CentralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFlowCapacityAt.toMassNormalizedPairwiseCoercivityData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow.centralPhysicalFiniteVacuumSectorMassNormalizedRootResistanceFiniteCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRootResistanceFlow.FixedNomeCofinalVacuumSectorMassNormalizedRootResistanceCongestionBound.toCofinalConditionalVarianceFraction
