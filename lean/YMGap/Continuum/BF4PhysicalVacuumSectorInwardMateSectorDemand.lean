/-
# Absorb exact sector leakage at the fixed BF4 anchor

The vacuum field has physical weight one and lies in the exact vacuum
component. The sharp fixed-volume partition ceiling therefore leaves at
most 1/64 of raw physical mass outside that component. Apply the existing
target-weighted 384/425 contraction to the complementary event: every bad
source escaping the sector is charged there. Its mass is at most 6/425 of
sector physical mass. Absorbing this in the proved 41/425 demand inequality
leaves a strictly positive successful fraction 7/85, for every cutoff K >= 1.

This closes scalar successful demand on the exact sector event. It does not
show that this move family separates all sector observables, nor prove an
all-vector Poincare bound. Coupling and slab extent remain fixed. No volume,
spacing, completed spectral, or continuum claim is made.
-/

import YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual
import YMGap.Continuum.FinitePositiveMaximumEntry

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveMaximumEntry
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- The complementary physical-field event, defined on the same field. -/
def physicalVacuumSectorComplementIndicator (K : Nat) (physical : EdgeLabelling) : Q' :=
  if centralPhysicalFiniteVacuumSectorStateB anchorCoupling (by decide) K 0
      (centralLowerRestriction 0 physical) then 0 else 1

theorem physicalVacuumSectorComplementIndicator_nonnegative
    (K : Nat) (physical : EdgeLabelling) :
    (0 : Q') ≤ physicalVacuumSectorComplementIndicator K physical := by
  unfold physicalVacuumSectorComplementIndicator
  split
  · exact Q'.le_refl' 0
  · exact Q'.zero_le_one

/-- Raw physical mass outside the exact vacuum component. -/
def physicalVacuumSectorComplementMass (K : Nat) : Q' :=
  listQSum (fun physical => physicalVacuumSectorComplementIndicator K physical *
      slabParametricKPhysicalTerm anchorCoupling K 1 physical)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))

theorem physicalVacuumSectorComplementMass_add_sectorMass (K : Nat) :
    physicalVacuumSectorComplementMass K + globalInwardMateVacuumSectorPhysicalMass K ≈
      slabParametricKPhysicalPartition anchorCoupling K 1 := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (physicalVacuumSectorIndicator_mass_eqv K))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add _ _ _)) ?_
  apply listQSum_congr
  intro physical
  unfold physicalVacuumSectorComplementIndicator physicalVacuumSectorIndicator
  split
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) (Q'.one_mul_eqv _))
      (Q'.eqv_of_eq (Q'.zero_add' _))
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.zero_mul_eqv _))
      (Q'.eqv_of_eq (Q'.add_zero' _))

/-- The literal zero field supplies weight one inside the sector event. -/
theorem sectorPhysicalMass_one_le (K : Nat) :
    (1 : Q') ≤ globalInwardMateVacuumSectorPhysicalMass K := by
  have hzero : zeroEdgeLabelling ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) := by
    apply boundedEdgeLabellings_complete
    · intro _ _
      change 0 < K + 1
      omega
    · intro _ _
      rfl
  have hrestrict : centralLowerRestriction 0 zeroEdgeLabelling = zeroEdgeLabelling := by
    funext face
    simp only [centralLowerRestriction, zeroEdgeLabelling, ite_self]
  have hsector : (⟨zeroEdgeLabelling, hzero⟩ : CubeInwardMatePhysicalSource K) ∈
      globalInwardMateVacuumSectorPhysicalSources K := by
    apply mem_globalInwardMateVacuumSectorPhysicalSources_iff.mpr
    change centralLowerRestriction 0 zeroEdgeLabelling ∈ _
    rw [hrestrict]
    exact zeroEdgeLabelling_mem_centralPhysicalFiniteVacuumSectorStates
      anchorCoupling (by decide) K 0
  have hmember := le_listQSum_of_mem_nonnegative
    (fun physicalSource : CubeInwardMatePhysicalSource K =>
      slabParametricKPhysicalTerm anchorCoupling K 1 physicalSource.val)
    (globalInwardMateVacuumSectorPhysicalSources K) ⟨zeroEdgeLabelling, hzero⟩ hsector
    (fun physicalSource _ => slabParametricKPhysicalTerm_nonnegative
      (by decide) K 1 physicalSource.val)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (slabParametricKPhysicalTerm_zero_eqv_one anchorCoupling K 1)) hmember

private theorem add_right_cancel_le {left right common : Q'}
    (h : left + common ≤ right + common) : left ≤ right := by
  have simplify (x : Q') : (x + common) + -common ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv common))
        (Q'.eqv_of_eq (Q'.add_zero' x)))
  have hshift := Q'.add_le_add_right _ _ (-common) h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (simplify left))
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv (simplify right)))

/-- Fixed-volume near-vacuum bound, uniform only in the spin cutoff. -/
theorem physicalVacuumSectorComplementMass_le (K : Nat) :
    physicalVacuumSectorComplementMass K ≤ Q'.mkPos 1 64 (by decide) := by
  apply add_right_cancel_le (common := 1)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ (sectorPhysicalMass_one_le K))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (physicalVacuumSectorComplementMass_add_sectorMass K))
      (Q'.le_trans' _ _ _ (anchorSlabPartition_one_le_ceiling K)
        (by decide : Q'.mkPos 65 64 (by decide) ≤ Q'.mkPos 1 64 (by decide) + 1)))

private theorem filter_sum_le_sum {A : Type}
    (test : A → Bool) (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → (0 : Q') ≤ right item) →
    (∀ item, item ∈ items → test item = true → left item ≤ right item) →
    listQSum left (items.filter test) ≤ listQSum right items
  | [], _, _ => Q'.le_refl' 0
  | head :: tail, hnonneg, hbound => by
    have ih := filter_sum_le_sum test left right tail
      (fun item hitem => hnonneg item (List.mem_cons_of_mem head hitem))
      (fun item hitem => hbound item (List.mem_cons_of_mem head hitem))
    cases htest : test head with
    | true =>
      simp only [List.filter, htest, listQSum]
      exact Q'.add_le_add (hbound head List.mem_cons_self htest) ih
    | false =>
      simp only [List.filter, htest, listQSum]
      have hadd := Q'.add_le_add (hnonneg head List.mem_cons_self) ih
      rwa [Q'.zero_add'] at hadd

/-- Escaping sources form a subevent of the actual target complement mass. -/
theorem sectorEscapingMass_le_targetComplementMass (K : Nat) (hK : 1 ≤ K) :
    sectorEscapingFirstStretchedMass K hK ≤
      listQSum
        (fun source => physicalVacuumSectorComplementIndicator K
          source.adaptiveInverseData.lowerPhysical * source.weight)
        (globalEnumeratedCubeInwardMateFullSources K hK) := by
  let targetWeight : GlobalEnumeratedCubeInwardMateFullSource K hK → Q' :=
    fun source => physicalVacuumSectorComplementIndicator K
      source.adaptiveInverseData.lowerPhysical * source.weight
  have hnonneg : ∀ source, (0 : Q') ≤ targetWeight source := fun source =>
    Q'.mul_nonneg _ _ (physicalVacuumSectorComplementIndicator_nonnegative K _)
      (firstStretchedSourceWeight_nonnegative source)
  have hflat := listQSum_flatMap targetWeight
    (globalEnumeratedCubeInwardMateFullSourceBlock K hK)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hflat)
  unfold sectorEscapingFirstStretchedMass
    globalInwardMateVacuumSectorFilteredFirstStretchedMass
    globalInwardMateVacuumSectorPhysicalSources
  apply filter_sum_le_sum
  · intro physicalSource _
    exact listQSum_nonnegative_on targetWeight _ (fun source _ => hnonneg source)
  · intro physicalSource _ _
    apply filter_sum_le_sum
    · intro source _
      exact hnonneg source
    · intro source _ hescape
      have houtside : firstStretchedTargetSectorB source = false := by
        cases ht : firstStretchedTargetSectorB source with
        | false => rfl
        | true => simp only [ht, Bool.not_true, Bool.false_eq_true] at hescape
      change source.weight ≤
        (if firstStretchedTargetSectorB source then (0 : Q') else 1) * source.weight
      rw [houtside]
      exact Q'.ge_of_eqv (Q'.one_mul_eqv _)

/-- The same 384/425 contraction charges escaping sources to outside fields. -/
theorem sectorEscapingMass_le_failure_mul_complement (K : Nat) (hK : 1 ≤ K) :
    sectorEscapingFirstStretchedMass K hK ≤
      Q'.mkPos 384 425 (by decide) * physicalVacuumSectorComplementMass K :=
  Q'.le_trans' _ _ _ (sectorEscapingMass_le_targetComplementMass K hK)
    (targetWeightedFirstStretchedMass_le_physicalMass K hK
      (physicalVacuumSectorComplementIndicator K)
      (physicalVacuumSectorComplementIndicator_nonnegative K))

/-- **Absorbed leakage:** at most 6/425 of the actual sector mass. -/
theorem sectorEscapingMass_le (K : Nat) (hK : 1 ≤ K) :
    sectorEscapingFirstStretchedMass K hK ≤
      Q'.mkPos 6 425 (by decide) * globalInwardMateVacuumSectorPhysicalMass K := by
  have hraw := Q'.le_trans' _ _ _
    (sectorEscapingMass_le_failure_mul_complement K hK)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 384 425 (by decide))
      (physicalVacuumSectorComplementMass_le K) (by decide))
  have hconstant : Q'.mkPos 384 425 (by decide) * Q'.mkPos 1 64 (by decide) ≤
      Q'.mkPos 6 425 (by decide) * 1 := by decide
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hconstant
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (sectorPhysicalMass_one_le K) (by decide)))

/-- Explicit positive successful fraction; data, not an erased witness. -/
def sectorSuccessFraction : Q' := Q'.mkPos 7 85 (by decide)

theorem sectorSuccessFraction_pos : (0 : Q') < sectorSuccessFraction := by decide

/-- **Positive sector demand.** At every cutoff K >= 1, actual successful
inward-mate branch mass is at least 7/85 of the exact sector physical mass. -/
theorem sectorSuccessfulMass_ge (K : Nat) (hK : 1 ≤ K) :
    sectorSuccessFraction * globalInwardMateVacuumSectorPhysicalMass K ≤
      globalInwardMateVacuumSectorAllTargetMass K hK := by
  let mass := globalInwardMateVacuumSectorPhysicalMass K
  let escapeRate : Q' := Q'.mkPos 6 425 (by decide)
  have hrates : sectorSuccessFraction * mass + escapeRate * mass ≈
      Q'.mkPos 41 425 (by decide) * mass :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (by decide :
        sectorSuccessFraction + escapeRate ≈ Q'.mkPos 41 425 (by decide)))
  apply add_right_cancel_le (common := escapeRate * mass)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrates)
    (Q'.le_trans' _ _ _ (sectorSuccessfulMass_add_escape_ge K hK)
      (Q'.add_le_add_left _ _ _ (sectorEscapingMass_le K hK)))

/-- Nonvacuity: the successful sector event has strictly positive raw mass. -/
theorem sectorSuccessfulMass_pos (K : Nat) (hK : 1 ≤ K) :
    (0 : Q') < globalInwardMateVacuumSectorAllTargetMass K hK := by
  have hlower : sectorSuccessFraction ≤
      sectorSuccessFraction * globalInwardMateVacuumSectorPhysicalMass K :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv sectorSuccessFraction))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (sectorPhysicalMass_one_le K) (by decide))
  exact Q'.pos_of_lt_of_le sectorSuccessFraction_pos
    (Q'.le_trans' _ _ _ hlower (sectorSuccessfulMass_ge K hK))

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.physicalVacuumSectorComplementIndicator_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.physicalVacuumSectorComplementMass_add_sectorMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorPhysicalMass_one_le
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.physicalVacuumSectorComplementMass_le
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorEscapingMass_le_targetComplementMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorEscapingMass_le_failure_mul_complement
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorEscapingMass_le
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorSuccessFraction_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorSuccessfulMass_ge
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemand.sectorSuccessfulMass_pos
