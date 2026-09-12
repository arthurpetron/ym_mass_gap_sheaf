/-
# OS-local first-stretched targets stay in the finite vacuum component

The entropy injection for the first-stretched branch lowers two complete
strand components.  Unlike the successful six-face inward mate, this global
peel need not definitionally fix the reflection boundary and upper half.
Those two equalities put both lower endpoints over one common boundary
summand.  Boundary equality is unnecessary for support in the summed OS
kernel: equal reflected upper states suffice, using each field's own boundary.

This module makes that condition finite and decidable.  It then proves that
every OS-local first-stretched target has positive raw OS support through the
source's reflected upper state and therefore remains in the canonical finite
vacuum component whenever its source lower state does.

The strengthened theorem also covers every target with unchanged lower state.
Thus only changes to both half-states remain outside this support argument.
No claim is made that every first-stretched source is one-sided, and no sector demand,
Poincare, spectral-gap, continuum, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction
import YMGap.Continuum.CompactDualCutoffOneTotalKernel

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetProductionCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Positive physical terms from presented assignments -/

private theorem qOfNat_pos_of_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ predecessor => exact Q'.ofNat_succ_pos predecessor

private theorem natListProduct_pos_of_pointwise_local {A : Type}
    (value : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> 0 < value item) ->
      0 < natListProduct value items
  | [], _ => by
      change 0 < 1
      omega
  | head :: tail, hvalue => by
      rw [natListProduct]
      exact Nat.mul_pos
        (hvalue head List.mem_cons_self)
        (natListProduct_pos_of_pointwise_local value tail
          (fun item hitem =>
            hvalue item (List.mem_cons_of_mem head hitem)))

/-- One accepted presentation at every complete slab link certifies that the
actual production multiplicity product is strictly positive.  The presented
orders may differ from production order; permutation invariance of the SU(2)
fusion multiplicity supplies the bridge. -/
theorem slabExplicitLinkMultiplicityProduct_pos_of_presentedAssignment
    {K extent : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K extent physical)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical (boundaryCompleteSlabLinks extent)) :
    0 < slabExplicitLinkMultiplicityProduct K extent physical := by
  unfold slabExplicitLinkMultiplicityProduct
  apply natListProduct_pos_of_pointwise_local
  intro link hlink
  let linked : {link // link ∈ boundaryCompleteSlabLinks extent} :=
    ⟨link, hlink⟩
  have hlength : 0 <
      (orderedSlabLinkFusionWitnesses K physical
        (assignment linked).order).length :=
    List.length_pos_of_mem (assignment linked).auxiliary_mem
  have hlengthEq :
      (orderedSlabLinkFusionWitnesses K physical
          (assignment linked).order).length =
        slabExplicitLinkMultiplicity K extent physical link := by
    unfold orderedSlabLinkFusionWitnesses
    rw [fusionWitnessesForSpins_length_eq_explicit _ _
      (by
        simpa only [List.length_map] using
          (assignment linked).order.length_le_six)]
    unfold slabExplicitLinkMultiplicity
    exact (explicitValenceMultiplicity_physical_perm
      ((assignment linked).order.production_perm.map physical)
      (by
        simpa only [List.length_map] using
          slabIncidentPlaqIds_length_le_six extent link)
      (slabIncidentSpins_bounded hbounded link)).symm
  rwa [hlengthEq] at hlength

/-- Positive heat coefficients and a complete presented assignment make the
genuine corrected-slab physical term strictly positive. -/
theorem slabPhysicalTerm_pos_of_presentedAssignment
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (physical : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded D.cutoff D.extent physical)
    (assignment : PresentedSlabFusionWitnessAssignment
      D.cutoff D.extent physical
        (boundaryCompleteSlabLinks D.extent)) :
    (0 : Q') < D.physicalTerm physical := by
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      D.coupling D.cutoff D.extent physical :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      D hcoupling physical hbounded
  have hmultiplicity : 0 < slabExplicitLinkMultiplicityProduct
      D.cutoff D.extent physical :=
    slabExplicitLinkMultiplicityProduct_pos_of_presentedAssignment
      hbounded assignment
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos_local hmultiplicity)

/-! ## 2. The exact finite OS-locality predicate -/

def firstStretchedSourceLower
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    EdgeLabelling :=
  centralLowerRestriction 0 source.physical

def firstStretchedTargetPhysical
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    EdgeLabelling :=
  source.adaptiveInverseData.lowerPhysical

def firstStretchedTargetLower
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    EdgeLabelling :=
  centralLowerRestriction 0 (firstStretchedTargetPhysical source)

def firstStretchedCommonBoundary
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    EdgeLabelling :=
  centralBoundaryRestriction 0 source.physical

def firstStretchedCommonRight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    EdgeLabelling :=
  centralReflectedUpperRestriction 0 source.physical

/-- The lowered target is OS-local when it fixes exactly the boundary channel
and reflected upper state needed to put both lower endpoints over one common
raw-kernel summand. -/
structure FirstStretchedTargetOSLocal
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) : Prop where
  boundary_eq :
    centralBoundaryRestriction 0 (firstStretchedTargetPhysical source) =
      firstStretchedCommonBoundary source
  right_eq :
    centralReflectedUpperRestriction 0
        (firstStretchedTargetPhysical source) =
      firstStretchedCommonRight source

/-- Finite Boolean test for the two exact OS-locality equalities. -/
def firstStretchedTargetOSLocalB
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) : Bool :=
  supportedLabellingEqB (centralFixedFaceIds 0)
      (centralBoundaryRestriction 0 (firstStretchedTargetPhysical source))
      (firstStretchedCommonBoundary source) &&
    supportedLabellingEqB (centralLowerFaceIds 0)
      (centralReflectedUpperRestriction 0
        (firstStretchedTargetPhysical source))
      (firstStretchedCommonRight source)

/-- The finite test is equivalent to the exact OS-locality structure. -/
theorem firstStretchedTargetOSLocalB_eq_true_iff
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedTargetOSLocalB source = true ↔
      FirstStretchedTargetOSLocal source := by
  have hsourceMem : source.physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
    source.physicalSource.2
  have htargetMem : firstStretchedTargetPhysical source ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
    source.lowerPhysical_mem
  have hsourceBoundary := centralBoundaryRestriction_mem
    (half := 0) hsourceMem
  have htargetBoundary := centralBoundaryRestriction_mem
    (half := 0) htargetMem
  have hsourceRight := centralReflectedUpperRestriction_mem
    (half := 0) hsourceMem
  have htargetRight := centralReflectedUpperRestriction_mem
    (half := 0) htargetMem
  unfold firstStretchedTargetOSLocalB
  rw [Bool.and_eq_true]
  constructor
  · intro hparts
    exact {
      boundary_eq :=
        (supportedLabellingEqB_true_iff
          htargetBoundary hsourceBoundary).mp hparts.1
      right_eq :=
        (supportedLabellingEqB_true_iff
          htargetRight hsourceRight).mp hparts.2 }
  · intro hlocal
    exact ⟨
      (supportedLabellingEqB_true_iff
        htargetBoundary hsourceBoundary).mpr hlocal.boundary_eq,
      (supportedLabellingEqB_true_iff
        htargetRight hsourceRight).mpr hlocal.right_eq⟩

/-! ## 3. Positive two-edge OS support -/

theorem firstStretchedSourceLower_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedSourceLower source ∈ centralHalfStates K 0 := by
  unfold firstStretchedSourceLower centralHalfStates
  exact centralLowerRestriction_mem source.physicalSource.2

theorem firstStretchedTargetLower_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedTargetLower source ∈ centralHalfStates K 0 := by
  unfold firstStretchedTargetLower centralHalfStates
  exact centralLowerRestriction_mem source.lowerPhysical_mem

theorem firstStretchedCommonBoundary_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedCommonBoundary source ∈ centralBoundaryChannels K 0 := by
  unfold firstStretchedCommonBoundary centralBoundaryChannels
  exact centralBoundaryRestriction_mem source.physicalSource.2

theorem firstStretchedCommonRight_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedCommonRight source ∈ centralHalfStates K 0 := by
  unfold firstStretchedCommonRight centralHalfStates
  exact centralReflectedUpperRestriction_mem source.physicalSource.2

theorem assemble_firstStretchedSource
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    assembleReflectedSlabLabelling 0
        (firstStretchedSourceLower source)
        (firstStretchedCommonBoundary source)
        (firstStretchedCommonRight source) = source.physical := by
  exact assembleReflectedSlabLabelling_restrictions
    source.physicalSource.2

theorem assemble_firstStretchedTarget
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hlocal : FirstStretchedTargetOSLocal source) :
    assembleReflectedSlabLabelling 0
        (firstStretchedTargetLower source)
        (firstStretchedCommonBoundary source)
        (firstStretchedCommonRight source) =
      firstStretchedTargetPhysical source := by
  rw [← hlocal.boundary_eq, ← hlocal.right_eq]
  exact assembleReflectedSlabLabelling_restrictions
    source.lowerPhysical_mem

theorem firstStretchedSourcePhysicalTerm_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (0 : Q') < slabParametricKPhysicalTerm
      anchorCoupling K 1 source.physical := by
  have hpositive := slabPhysicalTerm_pos_of_presentedAssignment
    (globalInwardMateAnchorSlabData K)
    (by decide : (0 : Q') < anchorCoupling)
    source.physical
    (cubeInwardMatePhysicalBoundedOfMem
      K source.physical source.physicalSource.2)
    source.entry.source.toPresented
  simpa [globalInwardMateAnchorSlabData,
    SlabPhysicalData.physicalTerm, SlabPhysicalData.extent,
    centralExtent] using hpositive

theorem firstStretchedTargetPhysicalTerm_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (0 : Q') < slabParametricKPhysicalTerm
      anchorCoupling K 1 (firstStretchedTargetPhysical source) := by
  have hpositive := slabPhysicalTerm_pos_of_presentedAssignment
    (globalInwardMateAnchorSlabData K)
    (by decide : (0 : Q') < anchorCoupling)
    (firstStretchedTargetPhysical source)
    (cubeInwardMatePhysicalBoundedOfMem
      K (firstStretchedTargetPhysical source) source.lowerPhysical_mem)
    source.adaptiveInverseData.lowerAssignment
  simpa [globalInwardMateAnchorSlabData,
    SlabPhysicalData.physicalTerm, SlabPhysicalData.extent,
    centralExtent] using hpositive

theorem firstStretchedSource_commonRight_rawKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (0 : Q') < centralPhysicalReflectedKernel anchorCoupling K 0
      (firstStretchedSourceLower source)
      (firstStretchedCommonRight source) := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_pos_of_mem
  · intro boundary
    exact slabParametricKPhysicalTerm_nonnegative
      (by decide) K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (firstStretchedSourceLower source) boundary
          (firstStretchedCommonRight source))
  · exact firstStretchedCommonBoundary_mem source
  · rw [assemble_firstStretchedSource source]
    simpa [centralExtent] using
      firstStretchedSourcePhysicalTerm_pos source

theorem firstStretchedTarget_commonRight_rawKernel_pos
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hlocal : FirstStretchedTargetOSLocal source) :
    (0 : Q') < centralPhysicalReflectedKernel anchorCoupling K 0
      (firstStretchedTargetLower source)
      (firstStretchedCommonRight source) := by
  unfold centralPhysicalReflectedKernel
  apply listQSum_pos_of_mem
  · intro boundary
    exact slabParametricKPhysicalTerm_nonnegative
      (by decide) K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (firstStretchedTargetLower source) boundary
          (firstStretchedCommonRight source))
  · exact firstStretchedCommonBoundary_mem source
  · rw [assemble_firstStretchedTarget source hlocal]
    simpa [centralExtent] using
      firstStretchedTargetPhysicalTerm_pos source

/-- The boundary is summed out in the raw OS kernel.  The target's own
boundary gives positive support whenever its reflected upper state agrees
with the source's, even if the two boundary labellings differ. -/
theorem firstStretchedTarget_commonRight_rawKernel_pos_of_right_eq
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hright : centralReflectedUpperRestriction 0
        (firstStretchedTargetPhysical source) =
      firstStretchedCommonRight source) :
    (0 : Q') < centralPhysicalReflectedKernel anchorCoupling K 0
      (firstStretchedTargetLower source)
      (firstStretchedCommonRight source) := by
  have htargetMem : firstStretchedTargetPhysical source ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
    source.lowerPhysical_mem
  have htargetAssemble : assembleReflectedSlabLabelling 0
      (centralLowerRestriction 0 (firstStretchedTargetPhysical source))
      (centralBoundaryRestriction 0 (firstStretchedTargetPhysical source))
      (centralReflectedUpperRestriction 0 (firstStretchedTargetPhysical source)) =
        firstStretchedTargetPhysical source :=
    assembleReflectedSlabLabelling_restrictions htargetMem
  unfold centralPhysicalReflectedKernel
  apply listQSum_pos_of_mem
  · intro boundary
    exact slabParametricKPhysicalTerm_nonnegative
      (by decide) K (centralExtent 0)
        (assembleReflectedSlabLabelling 0
          (firstStretchedTargetLower source) boundary
          (firstStretchedCommonRight source))
  · exact centralBoundaryRestriction_mem (half := 0) htargetMem
  · rw [← hright]
    change (0 : Q') < slabParametricKPhysicalTerm anchorCoupling K
      (centralExtent 0)
      (assembleReflectedSlabLabelling 0
        (centralLowerRestriction 0 (firstStretchedTargetPhysical source))
        (centralBoundaryRestriction 0 (firstStretchedTargetPhysical source))
        (centralReflectedUpperRestriction 0 (firstStretchedTargetPhysical source)))
    rw [htargetAssemble]
    simpa [centralExtent] using firstStretchedTargetPhysicalTerm_pos source

private theorem firstStretchedRawKernelTarget_mem_positive
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hright : centralReflectedUpperRestriction 0
        (firstStretchedTargetPhysical source) =
      firstStretchedCommonRight source) :
    firstStretchedTargetLower source ∈
      centralPositiveHalfStates anchorCoupling (by decide) K 0 := by
  apply mem_centralPositiveHalfStates_iff.mpr
  refine ⟨firstStretchedTargetLower_mem source, ?_⟩
  unfold centralPhysicalRowMarginal
  apply listQSum_pos_of_mem
  · intro target
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) K 0 (firstStretchedTargetLower source) target
  · exact firstStretchedCommonRight_mem source
  · unfold centralNormalizedPhysicalReflectedKernel
    exact Q'.divPos_pos _ _
      (slabParametricKPhysicalPartition_pos
        (by decide) K (centralExtent 0))
      (firstStretchedTarget_commonRight_rawKernel_pos_of_right_eq source hright)

private theorem firstStretchedRawKernelCommon_mem_positive
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedCommonRight source ∈
      centralPositiveHalfStates anchorCoupling (by decide) K 0 := by
  apply mem_centralPositiveHalfStates_iff.mpr
  refine ⟨firstStretchedCommonRight_mem source, ?_⟩
  unfold centralPhysicalRowMarginal
  apply listQSum_pos_of_mem
  · intro target
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) K 0 (firstStretchedCommonRight source) target
  · exact firstStretchedSourceLower_mem source
  · have hforward : (0 : Q') < centralNormalizedPhysicalReflectedKernel
        anchorCoupling (by decide) K 0
        (firstStretchedSourceLower source)
        (firstStretchedCommonRight source) := by
      unfold centralNormalizedPhysicalReflectedKernel
      exact Q'.divPos_pos _ _
        (slabParametricKPhysicalPartition_pos
          (by decide) K (centralExtent 0))
        (firstStretchedSource_commonRight_rawKernel_pos source)
    have hsymm := centralNormalizedPhysicalReflectedKernel_symm
      (w := anchorCoupling) (hw := by decide)
      (firstStretchedSourceLower_mem source)
      (firstStretchedCommonRight_mem source)
    exact Q'.pos_of_lt_of_le hforward (Q'.le_of_eqv hsymm)

/-! ## 4. Vacuum-component preservation -/

/-- A first-stretched target with unchanged reflected upper state remains
in the exact vacuum component.  No equality of boundary labels is required. -/
theorem firstStretchedTargetLower_mem_vacuumSector_of_right_eq
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hright : centralReflectedUpperRestriction 0
        (firstStretchedTargetPhysical source) =
      firstStretchedCommonRight source)
    (hsourceSector : firstStretchedSourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0) :
    firstStretchedTargetLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 := by
  have hcommonSector : firstStretchedCommonRight source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_rawKernel_pos
      anchorCoupling (by decide) K 0 hsourceSector
      (firstStretchedRawKernelCommon_mem_positive source)
      (firstStretchedSource_commonRight_rawKernel_pos source)
  exact centralPhysicalFiniteVacuumSectorState_mem_of_reverse_rawKernel_pos
    anchorCoupling (by decide) K 0 hcommonSector
      (firstStretchedRawKernelTarget_mem_positive source hright)
      (firstStretchedTarget_commonRight_rawKernel_pos_of_right_eq source hright)

/-- The original boundary-and-upper locality bridge is retained at its
original type as a consequence of the stronger upper-only theorem. -/
theorem firstStretchedTargetLower_mem_vacuumSector_of_source_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hlocal : FirstStretchedTargetOSLocal source)
    (hsourceSector : firstStretchedSourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0) :
    firstStretchedTargetLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 :=
  firstStretchedTargetLower_mem_vacuumSector_of_right_eq
    source hlocal.right_eq hsourceSector

/-! ## 5. One-sided changes suffice; only two-sided changes remain -/

/-- A peel is one-sided when it preserves at least one half-state.
The boundary labels are unrestricted in both cases. -/
def FirstStretchedTargetOneSided
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) : Prop :=
  firstStretchedTargetLower source = firstStretchedSourceLower source ∨
    centralReflectedUpperRestriction 0 (firstStretchedTargetPhysical source) =
      firstStretchedCommonRight source

/-- A finite test of equality of at least one half-state. -/
def firstStretchedTargetOneSidedB
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) : Bool :=
  supportedLabellingEqB (centralLowerFaceIds 0)
      (firstStretchedTargetLower source) (firstStretchedSourceLower source) ||
    supportedLabellingEqB (centralLowerFaceIds 0)
      (centralReflectedUpperRestriction 0 (firstStretchedTargetPhysical source))
      (firstStretchedCommonRight source)

theorem firstStretchedTargetOneSidedB_eq_true_iff
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedTargetOneSidedB source = true ↔
      FirstStretchedTargetOneSided source := by
  have htargetMem : firstStretchedTargetPhysical source ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
    source.lowerPhysical_mem
  have htargetRight := centralReflectedUpperRestriction_mem
    (half := 0) htargetMem
  unfold firstStretchedTargetOneSidedB FirstStretchedTargetOneSided
  rw [Bool.or_eq_true,
    supportedLabellingEqB_true_iff
      (firstStretchedTargetLower_mem source)
      (firstStretchedSourceLower_mem source),
    supportedLabellingEqB_true_iff
      htargetRight
      (firstStretchedCommonRight_mem source)]

/-- Every case covered by the former locality test is still covered. -/
theorem firstStretchedTargetOneSided_of_osLocal
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hlocal : FirstStretchedTargetOSLocal source) :
    FirstStretchedTargetOneSided source :=
  Or.inr hlocal.right_eq

/-- **One-sided bad-target bridge.**  A target that preserves either
half-state stays in the source's vacuum component, regardless of its boundary. -/
theorem firstStretchedTargetLower_mem_vacuumSector_of_oneSided
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (honeSided : FirstStretchedTargetOneSided source)
    (hsourceSector : firstStretchedSourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0) :
    firstStretchedTargetLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 := by
  rcases honeSided with hlower | hright
  · rw [hlower]
    exact hsourceSector
  · exact firstStretchedTargetLower_mem_vacuumSector_of_right_eq
      source hright hsourceSector

/-- The remaining finite test fails exactly when both half-states change.
This statement asserts no estimate on the mass of those cases. -/
theorem firstStretchedTargetOneSidedB_eq_false_iff
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    firstStretchedTargetOneSidedB source = false ↔
      firstStretchedTargetLower source ≠ firstStretchedSourceLower source ∧
        centralReflectedUpperRestriction 0 (firstStretchedTargetPhysical source) ≠
          firstStretchedCommonRight source := by
  constructor
  · intro hfalse
    have hnot : ¬ FirstStretchedTargetOneSided source := by
      intro hone
      have htrue := (firstStretchedTargetOneSidedB_eq_true_iff source).mpr hone
      rw [hfalse] at htrue
      cases htrue
    exact ⟨fun heq => hnot (Or.inl heq), fun heq => hnot (Or.inr heq)⟩
  · intro hboth
    cases htest : firstStretchedTargetOneSidedB source with
    | false => rfl
    | true =>
      have hone := (firstStretchedTargetOneSidedB_eq_true_iff source).mp htest
      exact False.elim (hone.elim hboth.1 hboth.2)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.slabExplicitLinkMultiplicityProduct_pos_of_presentedAssignment
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetOSLocalB_eq_true_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedSource_commonRight_rawKernel_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTarget_commonRight_rawKernel_pos
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetLower_mem_vacuumSector_of_source_mem
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTarget_commonRight_rawKernel_pos_of_right_eq
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetLower_mem_vacuumSector_of_right_eq
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetOneSidedB_eq_true_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetOneSided_of_osLocal
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetLower_mem_vacuumSector_of_oneSided
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.firstStretchedTargetOneSidedB_eq_false_iff
