/-
# Resistance flow for the BF4 off-ray vacuum-root variance

The off-ray frontier is a one-body variance from each off-ray state to the
physical vacuum.  This module routes that demand along the existing finite
positive physical-kernel path, but pays the path by its exact electrical
resistance rather than by path length followed by a global minimum-edge
estimate.

For a state `x`, resistance-weighted Cauchy gives

    (f(x) - f(0))^2
      <= R(path x 0) * sum_path K(e) (df(e))^2.

After multiplying by the stationary weight, the literal occurrence load is
therefore `weight(x) * R(path x 0)`.  Regrouping occurrences by directed edge
produces a dimensionless resistance congestion.  At every finite cutoff,
the reciprocal of `1 + total congestion` is a strictly positive off-ray
coercivity constant.  No minimum physical edge occurs in that constant.

The remaining cofinal problem is to bound this resistance congestion
uniformly in the cutoff.  No such bound, completed gap, thermodynamic or
continuum limit, continuum QFT, or Clay conclusion is asserted here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
any noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

private theorem offRay_mem_sector
    {w : Q'} {hw : (0 : Q') ≤ w} {K state : Nat}
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    state ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 :=
  (List.mem_filter.mp hstate).1

/-! ## 1. One exact resistance budget per off-ray state -/

def centralLowerExcitedSpinCubeOffRayRootPositivePath
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (state : Nat)
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw K 0)
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
      state 0 :=
  centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K 0 state 0 (offRay_mem_sector hstate)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)

def centralLowerExcitedSpinCubeOffRayRootResistancePathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (state : Nat) : Q' :=
  if hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K then
    let path := centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
        path *
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.linearEnergy
        coefficient path
  else 0

theorem centralLowerExcitedSpinCubeOffRayRoot_sq_le_resistancePathBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    (coefficient state + -coefficient 0) *
        (coefficient state + -coefficient 0) ≤
      centralLowerExcitedSpinCubeOffRayRootResistancePathBudget
        w hw K coefficient state := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistancePathBudget
  rw [dif_pos hstate]
  exact
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.endpointDifference_sq_le_resistance_mul_linearEnergy
      coefficient
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)

def centralLowerExcitedSpinCubeOffRayRootResistanceRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun state =>
      centralPhysicalFiniteWeight w hw K 0 state *
        centralLowerExcitedSpinCubeOffRayRootResistancePathBudget
          w hw K coefficient state)
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)

theorem centralLowerExcitedSpinCubeOffRayRootVariance_le_resistanceRawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayRootVariance w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceRawBudget
        w hw K coefficient := by
  unfold centralLowerExcitedSpinCubeOffRayRootVariance
    finiteWeightedRootVariance
    centralLowerExcitedSpinCubeOffRayRootResistanceRawBudget
  apply listQSum_mono
  intro state hstate
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (centralLowerExcitedSpinCubeOffRayRoot_sq_le_resistancePathBudget
      w hw K coefficient state hstate)
    (centralPhysicalFiniteWeight_nonnegative_local w hw K state)

/-! ## 2. Literal resistance-weighted path occurrences -/

def centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  if hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K then
    let path := centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate
    let load := centralPhysicalFiniteWeight w hw K 0 state *
      BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
        path
    (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
      path).map (fun edge => (edge, load))
  else []

def centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (centralLowerExcitedSpinCubeOffRayIndices w hw K).flatMap
    (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
      w hw K)

def centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences w hw K)
    source target

def centralLowerExcitedSpinCubeOffRayRootResistanceRawOccurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceEnergy
    (centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences w hw K)
    coefficient (centralPhysicalFiniteKernel w hw K 0)

def centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteWeightedOccurrenceLoadedDirichlet
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences w hw K)
    coefficient (centralPhysicalFiniteKernel w hw K 0)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrenceEnergy_eqv_budget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') (state : Nat)
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    finiteWeightedOccurrenceEnergy
        (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
          w hw K state)
        coefficient (centralPhysicalFiniteKernel w hw K 0) ≈
      centralPhysicalFiniteWeight w hw K 0 state *
        centralLowerExcitedSpinCubeOffRayRootResistancePathBudget
          w hw K coefficient state := by
  let path := centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate
  let weight := centralPhysicalFiniteWeight w hw K 0 state
  let pathResistance :=
    BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance
      path
  let edgeEnergy : Nat × Nat → Q' := fun edge =>
    centralPhysicalFiniteKernel w hw K 0 edge.1 edge.2 *
      ((coefficient edge.1 + -coefficient edge.2) *
        (coefficient edge.1 + -coefficient edge.2))
  have hlinear :=
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.linearEnergy_eqv_directedEdges_sum
      coefficient path
  unfold
    centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
  rw [dif_pos hstate]
  unfold finiteWeightedOccurrenceEnergy
  rw [listQSum_map]
  refine Q'.eqv_trans _
    ((weight * pathResistance) *
      listQSum edgeEnergy
        (BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path)) _ ?_ ?_
  · exact listQSum_mul_left (weight * pathResistance) _ _
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
    · exact Q'.mul_eqv_congr_left pathResistance _ _ (Q'.eqv_symm hlinear)
    · unfold centralLowerExcitedSpinCubeOffRayRootResistancePathBudget
      rw [dif_pos hstate]
      exact Q'.eqv_refl _

theorem centralLowerExcitedSpinCubeOffRayRootResistanceRawOccurrenceEnergy_eqv_rawBudget
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayRootResistanceRawOccurrenceEnergy
        w hw K coefficient ≈
      centralLowerExcitedSpinCubeOffRayRootResistanceRawBudget
        w hw K coefficient := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceRawOccurrenceEnergy
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences
    centralLowerExcitedSpinCubeOffRayRootResistanceRawBudget
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        finiteWeightedOccurrenceEnergy
          (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
            w hw K state)
          coefficient (centralPhysicalFiniteKernel w hw K 0))
      (centralLowerExcitedSpinCubeOffRayIndices w hw K)) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro state hstate
    exact
      centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrenceEnergy_eqv_budget
        w hw K coefficient state hstate

/-! ## 3. Regrouping into dimensionless resistance congestion -/

theorem centralLowerExcitedSpinCubeOffRayRootResistanceOccurrence_mem_sector
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences
        w hw K) :
    occurrence.1.1 ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
      occurrence.1.2 ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  simpa only using
    BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges_mem_support
      (offRay_mem_sector hstate)
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)
      edge hedge

theorem centralLowerExcitedSpinCubeOffRayRootResistanceOccurrence_load_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (occurrence : WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences
        w hw K) :
    (0 : Q') ≤ occurrence.2 := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences at hoccurrence
  obtain ⟨state, hstate, hpathOccurrence⟩ := List.mem_flatMap.mp hoccurrence
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences at hpathOccurrence
  rw [dif_pos hstate] at hpathOccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hpathOccurrence
  subst occurrence
  exact Q'.mul_nonneg _ _
    (centralPhysicalFiniteWeight_nonnegative_local w hw K state)
    (BF4PhysicalFiniteVacuumSectorResistanceCauchy.PositiveKernelChainIn.resistance_nonnegative
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate))

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
  exact weightedDirectedEdgeLoad_nonnegative _
    (centralLowerExcitedSpinCubeOffRayRootResistanceOccurrence_load_nonnegative
      w hw K)
    source target

theorem centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet
        w hw K coefficient ≈
      centralLowerExcitedSpinCubeOffRayRootResistanceRawOccurrenceEnergy
        w hw K coefficient := by
  exact finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
    coefficient (centralPhysicalFiniteKernel w hw K 0)
    (centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences w hw K)
    (centralLowerExcitedSpinCubeOffRayRootResistanceOccurrence_mem_sector
      w hw K)

/-- The off-ray rooted variance is paid by an explicit resistance-loaded
physical Dirichlet form.  This is the exact analytic contraction preceding
the scalar congestion estimate. -/
theorem centralLowerExcitedSpinCubeOffRayRootVariance_le_resistanceRawLoadedDirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayRootVariance w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet
        w hw K coefficient := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeOffRayRootVariance_le_resistanceRawBudget
      w hw K coefficient)
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (centralLowerExcitedSpinCubeOffRayRootResistanceRawOccurrenceEnergy_eqv_rawBudget
            w hw K coefficient))
        (Q'.eqv_symm
          (centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet_eqv_occurrenceEnergy
            w hw K coefficient))))

/-! ## 4. A strictly positive finite coercivity constant with no edge floor -/

def centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  listQSum (fun occurrence => occurrence.2)
    (centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences w hw K)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic
  apply listQSum_nonnegative_on
  intro occurrence hoccurrence
  exact
    centralLowerExcitedSpinCubeOffRayRootResistanceOccurrence_load_nonnegative
      w hw K occurrence hoccurrence

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_totalTraffic
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
    weightedDirectedEdgeLoad
    centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic
  apply listQSum_mono
  intro occurrence hoccurrence
  unfold weightedDirectedEdgeIndicator
  by_cases hedge : occurrence.1 = (source, target)
  · rw [if_pos hedge]
    exact Q'.le_refl' _
  · rw [if_neg hedge]
    exact
      centralLowerExcitedSpinCubeOffRayRootResistanceOccurrence_load_nonnegative
        w hw K occurrence hoccurrence

def centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  1 + centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic w hw K

theorem centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost
  exact Q'.pos_add_nonneg (by decide)
    (centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic_nonnegative
      w hw K)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_trafficCost
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost w hw K := by
  have hload :=
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_totalTraffic
      w hw K source target
  have hadd := Q'.add_le_add_right (0 : Q') 1
    (centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic w hw K)
    (by decide : (0 : Q') ≤ 1)
  have htotal :
      centralLowerExcitedSpinCubeOffRayRootResistanceTotalTraffic w hw K ≤
        centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost w hw K := by
    unfold centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hload htotal

def centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) : Q' :=
  Q'.recipPos
    (centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost
      w (Q'.le_of_lt hw) K)
    (centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost_pos
      w (Q'.le_of_lt hw) K)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_pos
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta
  exact Q'.recipPos_pos _ _

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_mul_flowLoad_le_one
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K *
        centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K source target ≤
      1 := by
  let cost := centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost
    w (Q'.le_of_lt hw) K
  let eta := centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ eta
    (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_trafficCost
      w (Q'.le_of_lt hw) K source target)
    (Q'.le_of_lt
      (centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_pos hw K))
  exact Q'.le_trans' _ (eta * cost) _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_trans _ (cost * eta) _
        (Q'.mul_comm_eqv eta cost)
        (by
          unfold eta centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta
          exact Q'.mul_recipPos_eqv cost
            (centralLowerExcitedSpinCubeOffRayRootResistanceTrafficCost_pos
              w (Q'.le_of_lt hw) K))))

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

private theorem eta_mul_resistanceRawLoadedDirichlet_le_physicalDirichlet
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (eta : Q')
    (hedge : ∀ source target,
      eta * centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K source target ≤ 1)
    (coefficient : Nat → Q') :
    eta *
        centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet
          w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let load := centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
    w (Q'.le_of_lt hw) K
  let kernel := centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change eta * finiteJointDirichletBlock states states coefficient
      (fun source target => load source target * kernel source target) ≤
    finiteJointDirichletBlock states states coefficient kernel
  refine Q'.le_trans' _
    (finiteJointDirichletBlock states states coefficient
      (fun source target =>
        eta * (load source target * kernel source target))) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint_local
          states states coefficient eta
          (fun source target =>
            load source target * kernel source target)))
  · unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro source _hsource
    apply listQSum_mono
    intro target _htarget
    have hkernel0 : (0 : Q') ≤ kernel source target := by
      unfold kernel centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0 _ _
    have hload := hedge source target
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (kernel source target) hload hkernel0
    have hjoint : eta * (load source target * kernel source target) ≤
        kernel source target := by
      exact Q'.le_trans' _ ((eta * load source target) * kernel source target) _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        (Q'.le_trans' _ (1 * kernel source target) _ hscaled
          (Q'.le_of_eqv (Q'.one_mul_eqv _)))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hjoint
      (SumOfSquares.q_mul_self_nonneg
        (coefficient source + -coefficient target))

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_mul_loadedDirichlet_le_physicalDirichlet
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K *
        centralLowerExcitedSpinCubeOffRayRootResistanceRawLoadedDirichlet
          w (Q'.le_of_lt hw) K coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact eta_mul_resistanceRawLoadedDirichlet_le_physicalDirichlet
    hw K
    (centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K)
    (centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_mul_flowLoad_le_one
      hw K)
    coefficient

/-! ## 5. The exact cofinal resistance-congestion frontier -/

/-- A pointwise dimensionless resistance-flow capacity.  Unlike the old
kernel capacity, its right side is the constant one because the physical
conductance has already been absorbed edge by edge. -/
structure CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (eta : Q') : Type 1 where
  eta_pos : (0 : Q') < eta
  edge_capacity : ∀ source target,
    eta * centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K source target ≤ 1

namespace CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt

def toOffRayRootCoercivityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {eta : Q'}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt
        hw K eta) :
    CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K eta where
  eta_pos := capacity.eta_pos
  offRayRoot_coercivity := fun coefficient => by
    have hroot :=
      centralLowerExcitedSpinCubeOffRayRootVariance_le_resistanceRawLoadedDirichlet
        w (Q'.le_of_lt hw) K coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ eta hroot
      (Q'.le_of_lt capacity.eta_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (eta_mul_resistanceRawLoadedDirichlet_le_physicalDirichlet
        hw K eta capacity.edge_capacity coefficient)

end CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt

def centralLowerExcitedSpinCubeOffRayRootResistanceFiniteCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt hw K
      (centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K) where
  eta_pos :=
    centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_pos hw K
  edge_capacity :=
    centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_mul_flowLoad_le_one
      hw K

/-- Every finite cutoff has a concrete, strictly positive off-ray root
coercivity certificate.  Its strength is the reciprocal resistance traffic
cost and contains no global minimum-edge factor. -/
def centralLowerExcitedSpinCubeOffRayRootResistanceFiniteCoercivityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    CentralLowerExcitedSpinCubeOffRayRootCoercivityAt hw K
      (centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta hw K) :=
  (centralLowerExcitedSpinCubeOffRayRootResistanceFiniteCapacityAt hw K)
    |>.toOffRayRootCoercivityAt

/-- The remaining uniform analytic datum: one scalar bounds every directed
edge's dimensionless resistance congestion at every later cutoff. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  bound : Q'
  bound_nonnegative : (0 : Q') ≤ bound
  flowLoad_le : ∀ K, start ≤ K → ∀ source target,
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K source target ≤ bound

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound

def cost
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw) :
    Q' :=
  1 + family.bound

theorem cost_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw) :
    (0 : Q') < family.cost := by
  unfold cost
  exact Q'.pos_add_nonneg (by decide) family.bound_nonnegative

def eta
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw) :
    Q' :=
  Q'.recipPos family.cost family.cost_pos

theorem eta_pos
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw) :
    (0 : Q') < family.eta := by
  unfold eta
  exact Q'.recipPos_pos _ _

theorem flowLoad_le_cost
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw)
    {K : Nat} (hK : family.start ≤ K) (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K source target ≤ family.cost := by
  have hbound := family.flowLoad_le K hK source target
  have hadd := Q'.add_le_add_right (0 : Q') 1 family.bound
    (by decide : (0 : Q') ≤ 1)
  have hboundCost : family.bound ≤ family.cost := by
    unfold cost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hbound hboundCost

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw)
    (K : Nat) (hK : family.start ≤ K) :
    CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt
      hw K family.eta where
  eta_pos := family.eta_pos
  edge_capacity := fun source target => by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ family.eta
      (family.flowLoad_le_cost hK source target)
      (Q'.le_of_lt family.eta_pos)
    exact Q'.le_trans' _ (family.eta * family.cost) _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_trans _ (family.cost * family.eta) _
          (Q'.mul_comm_eqv _ _)
          (by
            unfold eta
            exact Q'.mul_recipPos_eqv family.cost family.cost_pos)))

/-- A uniform resistance-congestion bound compiles into the exact cofinal
off-ray root certificate consumed by the full finite-sector compiler. -/
def toCofinalOffRayRootCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw) :
    FixedNomeCofinalSpinCubeOffRayRootCoercivity hw where
  start := family.start
  eta := family.eta
  eta_pos := family.eta_pos
  finite := fun K hK =>
    (family.finiteCapacityAt K hK).toOffRayRootCoercivityAt

end FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow.centralLowerExcitedSpinCubeOffRayRootVariance_le_resistanceRawLoadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow.centralLowerExcitedSpinCubeOffRayRootResistanceFiniteEta_mul_loadedDirichlet_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow.centralLowerExcitedSpinCubeOffRayRootResistanceFiniteCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow.CentralLowerExcitedSpinCubeOffRayRootResistanceFlowCapacityAt.toOffRayRootCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow.FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound.toCofinalOffRayRootCoercivity
