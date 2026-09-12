/-
# Sector-relative first-stretched bound with an explicit two-sided residual

The target-weighted `384/425` theorem applies to the exact vacuum-sector
indicator.  Every one-sided source selected above sector physical fields has
its lowered target in that event.  Nonnegative finite summation therefore
bounds the one-sided bad mass by `384/425` of the sector physical mass.

The stronger exact source/target event split also includes every two-sided
peel whose target stays in the sector.  It gives the quantitative consequence
`(41/425) * sectorMass <= successfulMass + escapingBadMass`, alongside the
coarser two-sided bound.  Every escaping source is proved two-sided.
The residual is actual weighted first-stretched source mass, not a supplied
constant.  A positive lower bound on successful mass alone still needs a
strict sector-relative estimate on that residual (or a stronger support
argument).  No all-vector gap or continuum result is asserted.

Fixed anchor coupling and extent one, arbitrary cutoff K >= 1.
No new analytic hypothesis, sorry, classical axiom, or enlarged proof budget.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem indicator_sum_eqv_filter {A : Type}
    (test : A → Bool) (weight : A → Q') : ∀ items : List A,
    listQSum (fun item => (if test item then (1 : Q') else 0) * weight item)
        items ≈ listQSum weight (items.filter test)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
    have ih := indicator_sum_eqv_filter test weight tail
    cases htest : test head with
    | true =>
      simp only [listQSum, List.filter, htest, if_true]
      exact Q'.add_eqv_congr' (Q'.one_mul_eqv _) ih
    | false =>
      simp only [listQSum, List.filter, htest, Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) ih)
        (Q'.eqv_of_eq (Q'.zero_add' _))

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

/-- The indicator of the exact physical-field sector event, with no
assumption on positivity of a field's physical weight. -/
def physicalVacuumSectorIndicator (K : Nat) (physical : EdgeLabelling) : Q' :=
  if centralPhysicalFiniteVacuumSectorStateB anchorCoupling (by decide) K 0
      (centralLowerRestriction 0 physical) then 1 else 0

theorem physicalVacuumSectorIndicator_nonnegative
    (K : Nat) (physical : EdgeLabelling) :
    (0 : Q') ≤ physicalVacuumSectorIndicator K physical := by
  unfold physicalVacuumSectorIndicator
  split
  · exact Q'.zero_le_one
  · exact Q'.le_refl' 0

/-- The indicator-weighted full physical sum is exactly the already-defined
sector physical mass, including its dependent bounded-field carrier. -/
theorem physicalVacuumSectorIndicator_mass_eqv
    (K : Nat) :
    listQSum
        (fun physical => physicalVacuumSectorIndicator K physical *
          slabParametricKPhysicalTerm anchorCoupling K 1 physical)
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) ≈
      globalInwardMateVacuumSectorPhysicalMass K := by
  rw [← listQSum_attach]
  unfold globalInwardMateVacuumSectorPhysicalMass
    globalInwardMateVacuumSectorPhysicalSources physicalVacuumSectorIndicator
  exact indicator_sum_eqv_filter _ _ _

theorem firstStretchedSourceWeight_nonnegative
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (0 : Q') ≤ source.weight := by
  unfold GlobalEnumeratedCubeInwardMateFullSource.weight
    cubeInwardMateFullSourceEntryWeight
  exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
    K 0 source.physical source.entry.raw

/-- All first-stretched sources whose targets lie in the sector cost at most
`384/425` of sector physical mass.  Their source fields are unrestricted. -/
theorem firstStretchedTargetSectorMass_le_sectorPhysicalMass
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        (fun source => physicalVacuumSectorIndicator K
            source.adaptiveInverseData.lowerPhysical * source.weight)
        (globalEnumeratedCubeInwardMateFullSources K hK) ≤
      Q'.mkPos 384 425 (by decide) *
        globalInwardMateVacuumSectorPhysicalMass K := by
  have hweighted := targetWeightedFirstStretchedMass_le_physicalMass
    K hK (physicalVacuumSectorIndicator K)
    (physicalVacuumSectorIndicator_nonnegative K)
  exact Q'.le_trans' _ _ _ hweighted
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (physicalVacuumSectorIndicator_mass_eqv K)))

/-- Any selected sector-source bad branch with sector targets is covered by
the full target-sector mass.  The inclusion, rather than equality of source
and target events, is the hypothesis used in the finite sums. -/
theorem selectedSectorMass_le_targetSectorMass
    (K : Nat) (hK : 1 ≤ K)
    (test : GlobalEnumeratedCubeInwardMateFullSource K hK → Bool)
    (hpreserves : ∀ physicalSource,
      physicalSource ∈ globalInwardMateVacuumSectorPhysicalSources K →
      ∀ source, source ∈ globalEnumeratedCubeInwardMateFullSourceBlock
        K hK physicalSource → test source = true →
          physicalVacuumSectorIndicator K source.adaptiveInverseData.lowerPhysical = 1) :
    globalInwardMateVacuumSectorFilteredFirstStretchedMass K hK test ≤
      listQSum
        (fun source => physicalVacuumSectorIndicator K
            source.adaptiveInverseData.lowerPhysical * source.weight)
        (globalEnumeratedCubeInwardMateFullSources K hK) := by
  let targetWeight : GlobalEnumeratedCubeInwardMateFullSource K hK → Q' :=
    fun source => physicalVacuumSectorIndicator K
      source.adaptiveInverseData.lowerPhysical * source.weight
  have hnonneg : ∀ source, (0 : Q') ≤ targetWeight source := fun source =>
    Q'.mul_nonneg _ _
      (physicalVacuumSectorIndicator_nonnegative K _)
      (firstStretchedSourceWeight_nonnegative source)
  have hflat := listQSum_flatMap targetWeight
    (globalEnumeratedCubeInwardMateFullSourceBlock K hK)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hflat)
  unfold globalInwardMateVacuumSectorFilteredFirstStretchedMass
    globalInwardMateVacuumSectorPhysicalSources
  apply filter_sum_le_sum
  · intro physicalSource _
    exact listQSum_nonnegative_on targetWeight _
      (fun source _ => hnonneg source)
  · intro physicalSource _ hsectorTest
    have hphysicalSector : physicalSource ∈
        globalInwardMateVacuumSectorPhysicalSources K := by
      unfold globalInwardMateVacuumSectorPhysicalSources
      exact List.mem_filter.mpr
        ⟨List.mem_attach _ physicalSource, hsectorTest⟩
    apply filter_sum_le_sum
    · intro source _
      exact hnonneg source
    · intro source hsource htest
      have hindicator := hpreserves physicalSource hphysicalSector
        source hsource htest
      unfold targetWeight
      rw [hindicator]
      exact Q'.ge_of_eqv (Q'.one_mul_eqv source.weight)

/-- One-sided bad mass above sector fields is covered by the target-sector
mass, by the already-proved one-sided support theorem. -/
theorem oneSidedSectorMass_le_targetSectorMass
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorOneSidedFirstStretchedMass K hK ≤
      listQSum
        (fun source => physicalVacuumSectorIndicator K
            source.adaptiveInverseData.lowerPhysical * source.weight)
        (globalEnumeratedCubeInwardMateFullSources K hK) := by
  apply selectedSectorMass_le_targetSectorMass K hK firstStretchedTargetOneSidedB
  intro physicalSource hphysicalSector source hsource honeSided
  have htarget :=
    (globalInwardMateOneSidedFirstStretchedSource_endpoints_internal
      hphysicalSector (List.mem_filter.mpr ⟨hsource, honeSided⟩)).2
  have htargetTest :=
    (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
      anchorCoupling (by decide) K 0
      (firstStretchedTargetLower_mem source)).mpr htarget
  unfold physicalVacuumSectorIndicator
  change (if centralPhysicalFiniteVacuumSectorStateB
    anchorCoupling (by decide) K 0 (firstStretchedTargetLower source)
    then (1 : Q') else 0) = 1
  rw [htargetTest]
  rfl

/-- **Localized bad-branch contraction.**  All one-sided first-stretched
mass is bounded by `384/425` of the exact sector mass, at every cutoff K >= 1. -/
theorem oneSidedSectorMass_le_failureRate_mul_sectorPhysicalMass
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorOneSidedFirstStretchedMass K hK ≤
      Q'.mkPos 384 425 (by decide) *
        globalInwardMateVacuumSectorPhysicalMass K :=
  Q'.le_trans' _ _ _ (oneSidedSectorMass_le_targetSectorMass K hK)
    (firstStretchedTargetSectorMass_le_sectorPhysicalMass K hK)

/-! ## Exact escaping mass and the quantitative demand residual -/

/-- Decidable membership of the actual lowered half-state in the exact
vacuum sector.  This tests the target, not preservation of its coordinates. -/
def firstStretchedTargetSectorB {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) : Bool :=
  centralPhysicalFiniteVacuumSectorStateB anchorCoupling (by decide) K 0
    (firstStretchedTargetLower source)

theorem firstStretchedTargetSectorB_eq_true_iff
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedTargetSectorB source = true ↔
      firstStretchedTargetLower source ∈
        centralPhysicalFiniteVacuumSectorStates anchorCoupling (by decide) K 0 :=
  centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
    anchorCoupling (by decide) K 0 (firstStretchedTargetLower_mem source)

/-- First-stretched mass starting in the sector and ending in the sector. -/
def sectorInternalFirstStretchedMass (K : Nat) (hK : 1 ≤ K) : Q' :=
  globalInwardMateVacuumSectorFilteredFirstStretchedMass K hK
    firstStretchedTargetSectorB

/-- The actual outgoing bad mass: the source lower state is in the vacuum
sector, but the lowered target lower state is outside it. -/
def sectorEscapingFirstStretchedMass (K : Nat) (hK : 1 ≤ K) : Q' :=
  globalInwardMateVacuumSectorFilteredFirstStretchedMass K hK
    (fun source => !(firstStretchedTargetSectorB source))

theorem sectorInternalFirstStretchedMass_le
    (K : Nat) (hK : 1 ≤ K) :
    sectorInternalFirstStretchedMass K hK ≤
      Q'.mkPos 384 425 (by decide) *
        globalInwardMateVacuumSectorPhysicalMass K := by
  refine Q'.le_trans' _ _ _
    (selectedSectorMass_le_targetSectorMass K hK firstStretchedTargetSectorB ?_)
    (firstStretchedTargetSectorMass_le_sectorPhysicalMass K hK)
  intro physicalSource _ source _ htarget
  change (if firstStretchedTargetSectorB source then (1 : Q') else 0) = 1
  rw [htarget]
  rfl

theorem sectorFirstStretched_internal_escape_split
    (K : Nat) (hK : 1 ≤ K) :
    sectorInternalFirstStretchedMass K hK +
        sectorEscapingFirstStretchedMass K hK ≈
      globalInwardMateVacuumSectorFirstStretchedMass K hK :=
  globalInwardMateVacuumSectorFilteredFirstStretchedMass_partition
    K hK firstStretchedTargetSectorB

/-- An escaping source above a sector field must change both half-states.
Thus the exact escaping event lies inside the geometric two-sided residual. -/
theorem sectorEscapingSource_is_twoSided
    {K : Nat} {hK : 1 ≤ K}
    {physicalSource : CubeInwardMatePhysicalSource K}
    {source : GlobalEnumeratedCubeInwardMateFullSource K hK}
    (hphysicalSector : physicalSource ∈ globalInwardMateVacuumSectorPhysicalSources K)
    (hsource : source ∈ globalEnumeratedCubeInwardMateFullSourceBlock
      K hK physicalSource)
    (hescape : firstStretchedTargetSectorB source = false) :
    firstStretchedTargetOneSidedB source = false := by
  cases hone : firstStretchedTargetOneSidedB source with
  | false => rfl
  | true =>
    have htarget :=
      (globalInwardMateOneSidedFirstStretchedSource_endpoints_internal
        hphysicalSector (List.mem_filter.mpr ⟨hsource, hone⟩)).2
    have htargetTest := (firstStretchedTargetSectorB_eq_true_iff source).mpr htarget
    rw [hescape] at htargetTest
    cases htargetTest

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

private theorem demand_with_residual
    {good controlled residual total : Q'}
    (hnormalized : good + (controlled + residual) ≈ total)
    (hcontrolled : controlled ≤ Q'.mkPos 384 425 (by decide) * total) :
    Q'.mkPos 41 425 (by decide) * total ≤ good + residual := by
  let success : Q' := Q'.mkPos 41 425 (by decide)
  let failure : Q' := Q'.mkPos 384 425 (by decide)
  have hrates : success * total + failure * total ≈ total :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ total (by decide : success + failure ≈ 1))
        (Q'.one_mul_eqv total))
  have hreordered : (good + residual) + controlled ≈ total :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv residual controlled))
        hnormalized)
  apply add_right_cancel_le (common := controlled)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (success * total) _ _ hcontrolled)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrates) (Q'.ge_of_eqv hreordered))

/-- **Sector-relative demand with exact leakage.**  Successful mass plus
the actual escaping bad mass is at least `41/425` of sector physical mass.
Thus the weighted localization is complete; positive successful demand alone
still requires a strict estimate on the explicit escaping mass. -/
theorem sectorSuccessfulMass_add_escape_ge
    (K : Nat) (hK : 1 ≤ K) :
    Q'.mkPos 41 425 (by decide) *
        globalInwardMateVacuumSectorPhysicalMass K ≤
      globalInwardMateVacuumSectorAllTargetMass K hK +
        sectorEscapingFirstStretchedMass K hK := by
  apply demand_with_residual
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (sectorFirstStretched_internal_escape_split K hK))
      (globalInwardMateVacuumSectorBranches_weight_total K hK)
  · exact sectorInternalFirstStretchedMass_le K hK

/-- The coarser geometric residual also gives an unconditional demand bound. -/
theorem sectorSuccessfulMass_add_twoSided_ge
    (K : Nat) (hK : 1 ≤ K) :
    Q'.mkPos 41 425 (by decide) *
        globalInwardMateVacuumSectorPhysicalMass K ≤
      globalInwardMateVacuumSectorAllTargetMass K hK +
        globalInwardMateVacuumSectorTwoSidedFirstStretchedMass K hK :=
  demand_with_residual (globalInwardMateVacuumSectorBranches_oneSided_total K hK)
    (oneSidedSectorMass_le_failureRate_mul_sectorPhysicalMass K hK)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.physicalVacuumSectorIndicator_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.physicalVacuumSectorIndicator_mass_eqv
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.firstStretchedSourceWeight_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.firstStretchedTargetSectorMass_le_sectorPhysicalMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.oneSidedSectorMass_le_targetSectorMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.oneSidedSectorMass_le_failureRate_mul_sectorPhysicalMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.selectedSectorMass_le_targetSectorMass
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.firstStretchedTargetSectorB_eq_true_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.sectorInternalFirstStretchedMass_le
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.sectorFirstStretched_internal_escape_split
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.sectorSuccessfulMass_add_escape_ge
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.sectorSuccessfulMass_add_twoSided_ge
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.sectorEscapingSource_is_twoSided
