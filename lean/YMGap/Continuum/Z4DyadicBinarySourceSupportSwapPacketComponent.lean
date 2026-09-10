/-
# Packet-total disagreement is carried by the target-rooted component

The exact tilted-row response compiler leaves two finite lists of coarse
faces whose four-bit packet totals change under the canonical fine-source
support swap.  This file proves the required geometric containment: every
such coarse disagreement face has a concrete fine dyadic preimage belonging
to the target-rooted union-support component.

Thus a nonzero response defect cannot be supported away from the component
selected by the existing recoupling involution.  This is a support theorem,
not a decay estimate.  No component activity sum, volume-uniform centered
remainder, continuum construction, OS/GNS reconstruction, Hamiltonian gap,
or Yang--Mills mass gap is asserted here.

Constructive contract: finite Boolean graph membership and explicit dyadic
fibres only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
import YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality

namespace YMGap.Continuum.Z4DyadicBinarySourceSupportSwapPacketComponent

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Dyadic packet locality under the support swap -/

/-- The target-rooted support mask is absent from all four fine faces read by
one coarse packet. -/
def fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat) : Prop :=
  ∀ fineFaceId, fineFaceId ∈
      dyadicCoarseFaceFineFaceIds S coarseFaceId →
    fineCouplingPhysicalSupportSwapMask
      S targetFaceId pair fineFaceId = false

/-- Boolean recognition that the support component touches at least one of
the four fine faces read by a coarse packet. -/
def fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat) : Bool :=
  (dyadicCoarseFaceFineFaceIds S coarseFaceId).any
    (fineCouplingPhysicalSupportSwapMask S targetFaceId pair)

theorem fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB_eq_false_iff
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat) :
    fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
        S targetFaceId pair coarseFaceId = false ↔
      fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
        S targetFaceId pair coarseFaceId := by
  unfold fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
    fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
  constructor
  · intro hfalse fineFaceId hfine
    have hnot := List.any_eq_false.mp hfalse fineFaceId hfine
    cases hmask : fineCouplingPhysicalSupportSwapMask
        S targetFaceId pair fineFaceId with
    | false => rfl
    | true => exact False.elim (hnot hmask)
  · intro havoid
    apply List.any_eq_false.mpr
    intro fineFaceId hfine htrue
    rw [havoid fineFaceId hfine] at htrue
    exact Bool.noConfusion htrue

/-- If the target-rooted mask avoids the dyadic fibre, the left swapped
source has exactly the original four-spin packet. -/
theorem wholeSlabFinePacket_supportSwappedLeft_eq_of_avoids
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
      S targetFaceId pair coarseFaceId) :
    wholeSlabFinePacket S
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair).1 coarseFaceId =
      wholeSlabFinePacket S pair.1 coarseFaceId := by
  unfold wholeSlabFinePacket
  apply dyadicFaceSpinPacket_eq_of_local
  intro finePlaquette hpreimage
  have hcoarsePlaquette :
      slabPlaquetteAt S.coarse.extent coarseFaceId ∈
        boundaryCompleteSlabPlaquettes S.coarse.extent :=
    slabPlaquetteAt_mem hcoarse
  have hfineDyadic := dyadicFacePreimage_mem_boundaryCompleteFineSlab
    hcoarsePlaquette hpreimage
  have hfine : finePlaquette ∈
      boundaryCompleteSlabPlaquettes S.fine.extent := by
    rw [S.fine_extent]
    exact hfineDyadic
  have hfaceId : slabFaceIdOfPlaquette S.fine.extent finePlaquette ∈
      dyadicCoarseFaceFineFaceIds S coarseFaceId := by
    unfold dyadicCoarseFaceFineFaceIds
    exact List.mem_map.mpr ⟨finePlaquette, hpreimage, rfl⟩
  have hmask := havoid
    (slabFaceIdOfPlaquette S.fine.extent finePlaquette) hfaceId
  have hmaskIndex :
      fineCouplingPhysicalSupportSwapMask S targetFaceId pair
          (listIndexOf finePlaquette
            (boundaryCompleteSlabPlaquettes S.fine.extent)) = false := by
    simpa only [slabFaceIdOfPlaquette] using hmask
  rw [slabSpinAtPlaquette_eq_of_mem hfine,
    slabSpinAtPlaquette_eq_of_mem hfine]
  simp only [fineCouplingPhysicalSupportSwappedPair,
    twoReplicaFaceSwapLeft, hmaskIndex, Bool.false_eq_true, if_false]

/-- The same avoided fibre leaves the right swapped packet unchanged. -/
theorem wholeSlabFinePacket_supportSwappedRight_eq_of_avoids
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
      S targetFaceId pair coarseFaceId) :
    wholeSlabFinePacket S
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair).2 coarseFaceId =
      wholeSlabFinePacket S pair.2 coarseFaceId := by
  unfold wholeSlabFinePacket
  apply dyadicFaceSpinPacket_eq_of_local
  intro finePlaquette hpreimage
  have hcoarsePlaquette :
      slabPlaquetteAt S.coarse.extent coarseFaceId ∈
        boundaryCompleteSlabPlaquettes S.coarse.extent :=
    slabPlaquetteAt_mem hcoarse
  have hfineDyadic := dyadicFacePreimage_mem_boundaryCompleteFineSlab
    hcoarsePlaquette hpreimage
  have hfine : finePlaquette ∈
      boundaryCompleteSlabPlaquettes S.fine.extent := by
    rw [S.fine_extent]
    exact hfineDyadic
  have hfaceId : slabFaceIdOfPlaquette S.fine.extent finePlaquette ∈
      dyadicCoarseFaceFineFaceIds S coarseFaceId := by
    unfold dyadicCoarseFaceFineFaceIds
    exact List.mem_map.mpr ⟨finePlaquette, hpreimage, rfl⟩
  have hmask := havoid
    (slabFaceIdOfPlaquette S.fine.extent finePlaquette) hfaceId
  have hmaskIndex :
      fineCouplingPhysicalSupportSwapMask S targetFaceId pair
          (listIndexOf finePlaquette
            (boundaryCompleteSlabPlaquettes S.fine.extent)) = false := by
    simpa only [slabFaceIdOfPlaquette] using hmask
  rw [slabSpinAtPlaquette_eq_of_mem hfine,
    slabSpinAtPlaquette_eq_of_mem hfine]
  simp only [fineCouplingPhysicalSupportSwappedPair,
    twoReplicaFaceSwapRight, hmaskIndex, Bool.false_eq_true, if_false]

/-- Avoidance preserves the left packet-total coordinate read by the tilted
row law. -/
theorem wholeSlabFinePacketTotalLabelling_supportSwappedLeft_eq_of_avoids
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
      S targetFaceId pair coarseFaceId) :
    wholeSlabFinePacketTotalLabelling S
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair).1 coarseFaceId =
      wholeSlabFinePacketTotalLabelling S pair.1 coarseFaceId := by
  unfold wholeSlabFinePacketTotalLabelling
  rw [wholeSlabFinePacket_supportSwappedLeft_eq_of_avoids
    S targetFaceId pair coarseFaceId hcoarse havoid]

/-- Avoidance preserves the corresponding right packet-total coordinate. -/
theorem wholeSlabFinePacketTotalLabelling_supportSwappedRight_eq_of_avoids
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    (coarseFaceId : Nat)
    (hcoarse : coarseFaceId ∈ S.coarse.faceEdges)
    (havoid : fineCouplingPhysicalSupportSwapAvoidsDyadicCoarseFace
      S targetFaceId pair coarseFaceId) :
    wholeSlabFinePacketTotalLabelling S
        (fineCouplingPhysicalSupportSwappedPair
          S targetFaceId pair).2 coarseFaceId =
      wholeSlabFinePacketTotalLabelling S pair.2 coarseFaceId := by
  unfold wholeSlabFinePacketTotalLabelling
  rw [wholeSlabFinePacket_supportSwappedRight_eq_of_avoids
    S targetFaceId pair coarseFaceId hcoarse havoid]

/-! ## 2. Every disagreement face is touched by the component -/

/-- Generic left packet-total disagreement carrier for a physical source
pair and its canonical support swap. -/
def fineCouplingPhysicalSupportSwapLeftPacketTotalDisagreementFaces
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) : List Nat :=
  finePacketTotalDisagreementCoarseFaces S pair.1
    (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair).1

/-- Generic right packet-total disagreement carrier. -/
def fineCouplingPhysicalSupportSwapRightPacketTotalDisagreementFaces
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair) : List Nat :=
  finePacketTotalDisagreementCoarseFaces S pair.2
    (fineCouplingPhysicalSupportSwappedPair S targetFaceId pair).2

/-- A left packet-total disagreement forces a selected fine face in that
coarse dyadic fibre. -/
theorem mem_leftPacketTotalDisagreementFaces_implies_touch
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    {coarseFaceId : Nat}
    (hmem : coarseFaceId ∈
      fineCouplingPhysicalSupportSwapLeftPacketTotalDisagreementFaces
        S targetFaceId pair) :
    fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
      S targetFaceId pair coarseFaceId = true := by
  have hparts := List.mem_filter.mp hmem
  have hne := of_decide_eq_true hparts.2
  cases htouch : fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
      S targetFaceId pair coarseFaceId with
  | false =>
      have havoid :=
        (fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB_eq_false_iff
          S targetFaceId pair coarseFaceId).mp htouch
      have heq :=
        wholeSlabFinePacketTotalLabelling_supportSwappedLeft_eq_of_avoids
          S targetFaceId pair coarseFaceId hparts.1 havoid
      exact False.elim (hne heq.symm)
  | true => rfl

/-- A right packet-total disagreement forces the same component touch. -/
theorem mem_rightPacketTotalDisagreementFaces_implies_touch
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    {coarseFaceId : Nat}
    (hmem : coarseFaceId ∈
      fineCouplingPhysicalSupportSwapRightPacketTotalDisagreementFaces
        S targetFaceId pair) :
    fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
      S targetFaceId pair coarseFaceId = true := by
  have hparts := List.mem_filter.mp hmem
  have hne := of_decide_eq_true hparts.2
  cases htouch : fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB
      S targetFaceId pair coarseFaceId with
  | false =>
      have havoid :=
        (fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB_eq_false_iff
          S targetFaceId pair coarseFaceId).mp htouch
      have heq :=
        wholeSlabFinePacketTotalLabelling_supportSwappedRight_eq_of_avoids
          S targetFaceId pair coarseFaceId hparts.1 havoid
      exact False.elim (hne heq.symm)
  | true => rfl

/-- Every left disagreement coarse face has a concrete fine dyadic preimage
inside the target-rooted union-support component. -/
theorem mem_leftPacketTotalDisagreementFaces_exists_mem_targetComponent
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    {coarseFaceId : Nat}
    (hmem : coarseFaceId ∈
      fineCouplingPhysicalSupportSwapLeftPacketTotalDisagreementFaces
        S targetFaceId pair) :
    ∃ fineFaceId,
      fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId ∧
      fineFaceId ∈ slabTwoReplicaTargetSupportComponent
        S.fine.extent pair.1 pair.2 targetFaceId := by
  have htouch := mem_leftPacketTotalDisagreementFaces_implies_touch
    S targetFaceId pair hmem
  obtain ⟨fineFaceId, hfine, hmask⟩ := List.any_eq_true.mp htouch
  refine ⟨fineFaceId, hfine, ?_⟩
  unfold fineCouplingPhysicalSupportSwapMask
    slabTwoReplicaSupportSwapMask at hmask
  exact of_decide_eq_true hmask

/-- Every right disagreement coarse face has the analogous concrete fine
component witness. -/
theorem mem_rightPacketTotalDisagreementFaces_exists_mem_targetComponent
    (S : SlabScalePair) (targetFaceId : Nat)
    (pair : FineCouplingPhysicalSourcePair)
    {coarseFaceId : Nat}
    (hmem : coarseFaceId ∈
      fineCouplingPhysicalSupportSwapRightPacketTotalDisagreementFaces
        S targetFaceId pair) :
    ∃ fineFaceId,
      fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId ∧
      fineFaceId ∈ slabTwoReplicaTargetSupportComponent
        S.fine.extent pair.1 pair.2 targetFaceId := by
  have htouch := mem_rightPacketTotalDisagreementFaces_implies_touch
    S targetFaceId pair hmem
  obtain ⟨fineFaceId, hfine, hmask⟩ := List.any_eq_true.mp htouch
  refine ⟨fineFaceId, hfine, ?_⟩
  unfold fineCouplingPhysicalSupportSwapMask
    slabTwoReplicaSupportSwapMask at hmask
  exact of_decide_eq_true hmask

/-! ## 3. Accepted separated rows and their rooted geometry -/

/-- The accepted left-row carrier in the exact response identity is
literally the generic support-swap disagreement carrier. -/
theorem fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces_eq
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source =
      fineCouplingPhysicalSupportSwapLeftPacketTotalDisagreementFaces
        S targetFaceId
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source) := by
  unfold fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
    fineCouplingPhysicalSupportSwapLeftPacketTotalDisagreementFaces
    fineCouplingAcceptedSeparatedLeftPositiveSource
    fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
  rw [fineCouplingAcceptedSeparated_supportSwapped_left
    S rootFaceId targetFaceId source]

/-- The accepted right-row carrier is the corresponding generic carrier. -/
theorem fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces_eq
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source =
      fineCouplingPhysicalSupportSwapRightPacketTotalDisagreementFaces
        S targetFaceId
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source) := by
  unfold fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
    fineCouplingPhysicalSupportSwapRightPacketTotalDisagreementFaces
    fineCouplingAcceptedSeparatedRightPositiveSource
    fineCouplingAcceptedSeparatedSwappedRightPositiveSource
  rw [fineCouplingAcceptedSeparated_supportSwapped_right
    S rootFaceId targetFaceId source]

/-- Every accepted left-row disagreement face from the exact tilted-Gibbs
response has a fine preimage in the target-rooted physical component. -/
theorem mem_fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces_exists_mem_targetComponent
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    {coarseFaceId : Nat}
    (hmem : coarseFaceId ∈
      fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source) :
    ∃ fineFaceId,
      fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId ∧
      fineFaceId ∈ slabTwoReplicaTargetSupportComponent
        S.fine.extent
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source).1
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source).2
          targetFaceId := by
  apply mem_leftPacketTotalDisagreementFaces_exists_mem_targetComponent
    S targetFaceId
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
  rw [← fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces_eq
    S hfineCoupling rootFaceId targetFaceId htarget source]
  exact hmem

/-- Every accepted right-row disagreement face has the same target-component
localization. -/
theorem mem_fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces_exists_mem_targetComponent
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    {coarseFaceId : Nat}
    (hmem : coarseFaceId ∈
      fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source) :
    ∃ fineFaceId,
      fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId ∧
      fineFaceId ∈ slabTwoReplicaTargetSupportComponent
        S.fine.extent
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source).1
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source).2
          targetFaceId := by
  apply mem_rightPacketTotalDisagreementFaces_exists_mem_targetComponent
    S targetFaceId
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
  rw [← fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces_eq
    S hfineCoupling rootFaceId targetFaceId htarget source]
  exact hmem

/-- The observable target belongs to the target-rooted component for every
accepted separated source. -/
theorem fineCouplingAcceptedSeparated_target_mem_targetComponent
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    targetFaceId ∈ slabTwoReplicaTargetSupportComponent
      S.fine.extent
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source).1
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source).2
        targetFaceId := by
  have hmask :=
    slabObservableTwoReplicaPairPairedSupportSwapMask_target
      S.fine rootFaceId targetFaceId htarget source.1
        source.pair_mem_fourCell
  unfold slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask at hmask
  simpa only [fineCouplingAcceptedSeparatedPhysicalPair] using
    (of_decide_eq_true hmask)

/-- Separation means the observable root is outside the component that
carries every packet-total response disagreement. -/
theorem fineCouplingAcceptedSeparated_root_not_mem_targetComponent
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    rootFaceId ∉ slabTwoReplicaTargetSupportComponent
      S.fine.extent
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source).1
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source).2
        targetFaceId := by
  have hmask := source.disconnected
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask at hmask
  simpa only [fineCouplingAcceptedSeparatedPhysicalPair] using
    (of_decide_eq_false hmask)

/-! ## 4. Axiom audit -/

#print axioms fineCouplingPhysicalSupportSwapTouchesDyadicCoarseFaceB_eq_false_iff
#print axioms wholeSlabFinePacket_supportSwappedLeft_eq_of_avoids
#print axioms wholeSlabFinePacket_supportSwappedRight_eq_of_avoids
#print axioms wholeSlabFinePacketTotalLabelling_supportSwappedLeft_eq_of_avoids
#print axioms wholeSlabFinePacketTotalLabelling_supportSwappedRight_eq_of_avoids
#print axioms mem_leftPacketTotalDisagreementFaces_implies_touch
#print axioms mem_rightPacketTotalDisagreementFaces_implies_touch
#print axioms mem_leftPacketTotalDisagreementFaces_exists_mem_targetComponent
#print axioms mem_rightPacketTotalDisagreementFaces_exists_mem_targetComponent
#print axioms fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces_eq
#print axioms fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces_eq
#print axioms mem_fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces_exists_mem_targetComponent
#print axioms mem_fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces_exists_mem_targetComponent
#print axioms fineCouplingAcceptedSeparated_target_mem_targetComponent
#print axioms fineCouplingAcceptedSeparated_root_not_mem_targetComponent

end YMGap.Continuum.Z4DyadicBinarySourceSupportSwapPacketComponent
