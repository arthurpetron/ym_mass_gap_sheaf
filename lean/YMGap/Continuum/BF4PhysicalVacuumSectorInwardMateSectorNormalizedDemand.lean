/-
# Positive demand on the existing normalized vacuum-sector OS flow

The sector test is constant on each fixed-physical complete-source block.
Moving that test through exact finite Fubini identifies the original filtered
source-weight sum with the already bounded raw successful sector mass.
Production weights agree termwise, and the traffic uses the same positive
physical partition. Thus the existing sector flow carries at least 7/85
times the partition-normalized physical sector-event mass, and in particular
at least 448/5525 total traffic, at every cutoff K >= 1.

No path, source list, weight, normalization, or congestion factor is changed.
This connects the raw demand theorem to the traffic in the proved OS energy
comparisons. The exact Boolean path identity also gives a strictly positive
cutoff-independent sector Dirichlet floor for central-face parity, with the
sharper factor 1+transportCost. It does not give all-vector norm coverage.
Fixed anchor coupling 1/400 and slab extent one; no volume, beta, spacing,
completed gap, or continuum conclusion. Constants are independently checked
in computations/bf4_anchor_sector_escape_budget.py and by the Lean kernel.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSEdgeCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceProductionTransport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFraction
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionSourceMarginal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem filter_of_constant_test {A : Type} (test : A → Bool) (decision : Bool) :
    ∀ items : List A, (∀ item, item ∈ items → test item = decision) →
    items.filter test = if decision then items else []
  | [], _ => by cases decision <;> rfl
  | head :: tail, htest => by
    have hh := htest head List.mem_cons_self
    have ht := filter_of_constant_test test decision tail
      (fun item hi => htest item (List.mem_cons_of_mem head hi))
    cases decision <;> simp only [List.filter_cons, hh, ht, Bool.false_eq_true, if_false, if_true]

private theorem sum_if_eq_filter {A : Type} (test : A → Bool) (value : A → Q') :
    ∀ items : List A,
    listQSum (fun item => if test item then value item else 0) items ≈
      listQSum value (items.filter test)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
    cases ht : test head with
    | true =>
      simp only [listQSum, List.filter, ht, if_true]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_if_eq_filter test value tail)
    | false =>
      simp only [listQSum, List.filter, ht, Bool.false_eq_true, if_false, Q'.zero_add']
      exact sum_if_eq_filter test value tail

/-- Exact sector-restricted Fubini: no source is selected a second time. -/
theorem sectorSourceWeights_eqv_rawSuccessfulMass (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalInwardMateVacuumSectorSources K hK) ≈
      globalInwardMateVacuumSectorAllTargetMass K hK := by
  let sourceTest := fun source : GlobalCubeInwardMateCertifiedTargetFullSource K hK =>
    centralPhysicalFiniteVacuumSectorStateB anchorCoupling (by decide) K 0 (sourceLower source)
  let physicalTest := fun physicalSource : CubeInwardMatePhysicalSource K =>
    centralPhysicalFiniteVacuumSectorStateB anchorCoupling (by decide) K 0
      (centralLowerRestriction 0 physicalSource.val)
  let block := globalCubeInwardMateCertifiedTargetFullSourceBlock K hK
  have hconstant : ∀ physicalSource source,
      source ∈ block physicalSource → sourceTest source = physicalTest physicalSource := by
    intro physicalSource source hs
    obtain ⟨entry, _, heq⟩ := List.mem_map.mp hs
    rw [← heq]
    rfl
  have hblock : ∀ physicalSource,
      listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        ((block physicalSource).filter sourceTest) ≈
      (if physicalTest physicalSource then cubeInwardMateCertifiedTargetFullPhysicalMass K hK physicalSource else 0) := by
    intro physicalSource
    rw [filter_of_constant_test sourceTest (physicalTest physicalSource)
      (block physicalSource) (hconstant physicalSource)]
    cases ht : physicalTest physicalSource with
    | false => exact Q'.eqv_refl 0
    | true =>
      simp only [if_true]
      unfold block globalCubeInwardMateCertifiedTargetFullSourceBlock
      rw [listQSum_map]
      exact Q'.eqv_refl _
  unfold globalInwardMateVacuumSectorSources globalCubeInwardMateCertifiedTargetFullSources
  rw [List.filter_flatMap]
  refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (listQSum_congr hblock _) ?_
  exact sum_if_eq_filter physicalTest (cubeInwardMateCertifiedTargetFullPhysicalMass K hK)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach

/-- The production source weights used by the actual traffic have that same
raw mass, by the already checked termwise source compiler. -/
theorem sectorProductionWeights_eqv_rawSuccessfulMass (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight
        (globalInwardMateVacuumSectorSources K hK) ≈
      globalInwardMateVacuumSectorAllTargetMass K hK := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      GlobalCubeInwardMateCertifiedTargetFullSource.sourceProductionWeight_eqv_weight _)
    (sectorSourceWeights_eqv_rawSuccessfulMass K hK)

/-- **Exact handoff:** the original normalized OS traffic is the raw
successful sector mass divided by the same physical partition. -/
theorem sectorTotalTraffic_eqv_rawMass_div_partition (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorTotalTraffic K hK ≈
      Q'.divPos (globalInwardMateVacuumSectorAllTargetMass K hK)
        (slabParametricKPhysicalPartition anchorCoupling K 1)
        (slabParametricKPhysicalPartition_pos (by decide) K 1) := by
  unfold globalInwardMateVacuumSectorTotalTraffic globalInwardMateSourceTraffic Q'.divPos
  exact Q'.eqv_trans _ _ _ (listQSum_mul_right _ _ _)
    (Q'.mul_eqv_congr_right _ _ _ (sectorProductionWeights_eqv_rawSuccessfulMass K hK))

/-- Sector-relative demand on the original partition-normalized OS traffic. -/
theorem sectorSuccessFraction_mul_normalizedMass_le_traffic (K : Nat) (hK : 1 ≤ K) :
    sectorSuccessFraction *
      Q'.divPos (globalInwardMateVacuumSectorPhysicalMass K)
        (slabParametricKPhysicalPartition anchorCoupling K 1)
        (slabParametricKPhysicalPartition_pos (by decide) K 1) ≤
      globalInwardMateVacuumSectorTotalTraffic K hK := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  have hp : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos (by decide) K 1
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos partition hp)
    (sectorSuccessfulMass_ge K hK) (Q'.le_of_lt (Q'.recipPos_pos partition hp))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.ge_of_eqv (sectorTotalTraffic_eqv_rawMass_div_partition K hK)))

/-- Explicit cutoff-independent positive total-traffic floor, at the fixed
anchor and extent: (7/85)/(65/64). -/
def sectorTrafficFloor : Q' := Q'.mkPos 448 5525 (by decide)

theorem sectorTrafficFloor_pos : (0 : Q') < sectorTrafficFloor := by decide

/-- **Positive normalized flow demand** on the unchanged sector source list. -/
theorem sectorTrafficFloor_le_totalTraffic (K : Nat) (hK : 1 ≤ K) :
    sectorTrafficFloor ≤ globalInwardMateVacuumSectorTotalTraffic K hK := by
  let partition := slabParametricKPhysicalPartition anchorCoupling K 1
  have hraw : sectorSuccessFraction ≤ globalInwardMateVacuumSectorAllTargetMass K hK :=
    Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv sectorSuccessFraction))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (sectorPhysicalMass_one_le K) (by decide)))
      (sectorSuccessfulMass_ge K hK)
  have hpaid : sectorTrafficFloor * partition ≤
      globalInwardMateVacuumSectorAllTargetMass K hK :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (anchorSlabPartition_one_le_ceiling K) (by decide))
      (Q'.le_trans' _ _ _
        (by decide : sectorTrafficFloor * Q'.mkPos 65 64 (by decide) ≤ sectorSuccessFraction) hraw)
  exact Q'.le_trans' _ _ _
    (Q'.le_divPos_of_mul_le _ partition
      (slabParametricKPhysicalPartition_pos (by decide) K 1) hpaid)
    (Q'.ge_of_eqv (sectorTotalTraffic_eqv_rawMass_div_partition K hK))

theorem sectorTotalTraffic_pos (K : Nat) (hK : 1 ≤ K) :
    (0 : Q') < globalInwardMateVacuumSectorTotalTraffic K hK :=
  Q'.pos_of_lt_of_le sectorTrafficFloor_pos (sectorTrafficFloor_le_totalTraffic K hK)

/-! ## Direct observable consequence on the same indexed sector -/

/-- Exactly one of the two Boolean parity edges changes on each selected
path, so the restricted parity energies sum to this same traffic. -/
theorem sectorTraffic_eqv_parityEdgeEnergies (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorTotalTraffic K hK ≈
      sectorSelectedFirstEnergy K hK centralFaceZeroParityCoefficient +
        sectorSelectedSecondEnergy K hK centralFaceZeroParityCoefficient := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr globalInwardMateSourceTraffic_eqv_parityEdgeTerms _)
    (listQSum_add _ _ _)

theorem sectorTrafficFloor_le_cost_mul_parityDirichlet (K : Nat) (hK : 1 ≤ K) :
    sectorTrafficFloor ≤ globalInwardMateParityDirichletCost *
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) K 0)
        (centralPhysicalFiniteCoefficient anchorCoupling (by decide) K 0 centralFaceZeroParityCoefficient)
        (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) K 0)
    (centralPhysicalFiniteCoefficient anchorCoupling (by decide) K 0 centralFaceZeroParityCoefficient)
    (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0)
  have hregroup : energy + globalInwardMateTransportCost * energy ≈
      globalInwardMateParityDirichletCost * energy :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv energy)))
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
  exact Q'.le_trans' _ _ _ (sectorTrafficFloor_le_totalTraffic K hK)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sectorTraffic_eqv_parityEdgeEnergies K hK))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add
          (sectorSelectedFirstEnergy_le_Dirichlet K hK centralFaceZeroParityCoefficient)
          (sectorSelectedSecondEnergy_le_cost_mul_Dirichlet K hK centralFaceZeroParityCoefficient))
        (Q'.le_of_eqv hregroup)))

/-- A concrete positive sector-observable energy floor, independent of K. -/
def sectorParityDirichletFloor : Q' :=
  Q'.divPos sectorTrafficFloor globalInwardMateParityDirichletCost
    globalInwardMateParityDirichletCost_positive

theorem sectorParityDirichletFloor_pos : (0 : Q') < sectorParityDirichletFloor :=
  Q'.divPos_pos _ _ globalInwardMateParityDirichletCost_positive sectorTrafficFloor_pos

/-- **Nonvacuous physical consequence:** central-face parity has this positive
Dirichlet energy on the exact vacuum component at every cutoff K >= 1. -/
theorem sectorParityDirichletFloor_le (K : Nat) (hK : 1 ≤ K) :
    sectorParityDirichletFloor ≤ finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) K 0)
      (centralPhysicalFiniteCoefficient anchorCoupling (by decide) K 0 centralFaceZeroParityCoefficient)
      (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  apply Q'.divPos_le_of_le_mul _ _ globalInwardMateParityDirichletCost_positive
  exact Q'.le_trans' _ _ _ (sectorTrafficFloor_le_cost_mul_parityDirichlet K hK)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorSourceWeights_eqv_rawSuccessfulMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorProductionWeights_eqv_rawSuccessfulMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorTotalTraffic_eqv_rawMass_div_partition
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorSuccessFraction_mul_normalizedMass_le_traffic
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorTrafficFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorTrafficFloor_le_totalTraffic
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorTotalTraffic_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorTraffic_eqv_parityEdgeEnergies
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorTrafficFloor_le_cost_mul_parityDirichlet
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorParityDirichletFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.sectorParityDirichletFloor_le
