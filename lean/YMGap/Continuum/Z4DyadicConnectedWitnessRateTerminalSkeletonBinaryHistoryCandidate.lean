/-
# The concrete terminal-history binary candidate

For a realized terminal/skeleton row, concatenate the positive peel sizes of
the fine and coarse canonical histories and encode that positive composition
by unary runs.  The resulting word is literally binary and has length equal
to the complete profile mass.  This module therefore supplies the concrete
encoder required by the abstract binary-history reduction.

What remains is stated without disguise: inside one normalization fiber,
equality of the concatenated peel-size word must determine the complete row.
The final theorem constructs the abstract binary certificate from precisely
that geometric adequacy property and no stronger assumption.

Constructive contract: explicit list coding and canonical-peeling witnesses
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new trusted principle.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryReduction

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryCandidate

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryReduction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonHistoryMassFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem natListSum_map_eq_listNatWeight_local {A : Type}
    (weight : A -> Nat) : forall items : List A,
    natListSum (items.map weight) = listNatWeight weight items
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, natListSum, listNatWeight]
      exact congrArg (Nat.add (weight head))
        (natListSum_map_eq_listNatWeight_local weight tail)

private theorem slabAcceptedPairCanonicalHighSpinProfile_trace_peelSize_pos
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    forall record,
      record ∈ (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.1 ->
      0 < record.peelSize := by
  have hforget := congrArg Prod.snd
    (slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
      D threshold faces hphysical state)
  change
    (slabAcceptedPairCanonicalHighSpinProfile
        D threshold faces hphysical state).2.1 =
      (slabAcceptedPairCanonicalPeeling D faces hphysical state).2
    at hforget
  intro record hrecord
  rw [hforget] at hrecord
  exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
    D faces hphysical state record hrecord

/-! ## 1. Positivity inherited from canonical peeling -/

theorem finePacketConnectedRateProfiledStructural_fineSkeleton_peelSize_pos
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    forall skeleton,
      skeleton ∈ structural.fineProfile.2.1.map
          SlabAcceptedPairedPeelRecord.skeleton ->
        0 < skeleton.peelSize := by
  obtain ⟨reference, _hreferenceOption, _hreferenceMem,
      hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hprofile := congrArg
    FinePacketConnectedRateProfiledStructuralCode.fineProfile
      hreferenceStructural
  change structural.fineProfile =
    slabAcceptedPairedHighSpinProfileExactKey
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).1 at hprofile
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hprofile
  change structural.fineProfile.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).1.2.1
    at htrace
  intro skeleton hskeleton
  rw [htrace] at hskeleton
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hskeleton
  exact slabAcceptedPairCanonicalHighSpinProfile_trace_peelSize_pos
    (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
    (anchorPaidExteriorThreshold rate)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId reference.1)
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace reference.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (finePacketFineUnitCouplingSlabPhysicalData S)
      rate hrate0 reference.2.1.1) record hrecord

theorem finePacketConnectedRateProfiledStructural_coarseSkeleton_peelSize_pos
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    forall skeleton,
      skeleton ∈ structural.coarseProfile.2.1.map
          SlabAcceptedPairedPeelRecord.skeleton ->
        0 < skeleton.peelSize := by
  obtain ⟨reference, _hreferenceOption, _hreferenceMem,
      hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  have hprofile := congrArg
    FinePacketConnectedRateProfiledStructuralCode.coarseProfile
      hreferenceStructural
  change structural.coarseProfile =
    slabAcceptedPairedHighSpinProfileExactKey
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace
          reference).2 at hprofile
  have htrace := congrArg
    (fun key : SlabAcceptedPairedHighSpinProfileExactKey => key.2.1) hprofile
  change structural.coarseProfile.2.1 =
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace reference).2.2.1
    at htrace
  intro skeleton hskeleton
  rw [htrace] at hskeleton
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hskeleton
  exact slabAcceptedPairCanonicalHighSpinProfile_trace_peelSize_pos
    (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
    (anchorPaidExteriorThreshold rate)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId reference.1)
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace reference.1)
    (slabAcceptedTwoReplicaStateAtCoupling
      (coarseUnitCouplingSlabPhysicalData S)
      rate hrate0
      (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
        S reference.2.1)) record hrecord

theorem finePacketConnectedRateProfiledTerminalSkeletonRow_fineSkeleton_peelSize_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    forall skeleton, skeleton ∈ row.fineSkeletons ->
      0 < skeleton.peelSize := by
  obtain ⟨structural, _hfirst, hstructural⟩ :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hcarrier :=
    finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  have hskeletons :=
    finePacketConnectedRateProfiledStructural_fineSkeleton_eq_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  intro skeleton hskeleton
  rw [← hskeletons] at hskeleton
  exact finePacketConnectedRateProfiledStructural_fineSkeleton_peelSize_pos
    S rate hrate0 orientation observableFaceId hobservableFace structural
      hcarrier skeleton hskeleton

theorem finePacketConnectedRateProfiledTerminalSkeletonRow_coarseSkeleton_peelSize_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    forall skeleton, skeleton ∈ row.coarseSkeletons ->
      0 < skeleton.peelSize := by
  obtain ⟨structural, _hfirst, hstructural⟩ :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hcarrier :=
    finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  have hskeletons :=
    finePacketConnectedRateProfiledStructural_coarseSkeleton_eq_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  intro skeleton hskeleton
  rw [← hskeletons] at hskeleton
  exact finePacketConnectedRateProfiledStructural_coarseSkeleton_peelSize_pos
    S rate hrate0 orientation observableFaceId hobservableFace structural
      hcarrier skeleton hskeleton

/-! ## 2. The length-exact binary candidate -/

def finePacketConnectedRateTerminalSkeletonHistorySizeWord
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : List Nat :=
  row.fineSkeletons.map SlabAcceptedPairedPeelSkeleton.peelSize ++
    row.coarseSkeletons.map SlabAcceptedPairedPeelSkeleton.peelSize

def finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : List Nat :=
  positiveCompositionBinaryCode
    (finePacketConnectedRateTerminalSkeletonHistorySizeWord row)

theorem finePacketConnectedRateTerminalSkeletonHistorySizeWord_positive
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    forall size,
      size ∈ finePacketConnectedRateTerminalSkeletonHistorySizeWord row ->
        0 < size := by
  intro size hsize
  rcases List.mem_append.mp hsize with hfine | hcoarse
  · obtain ⟨skeleton, hskeleton, rfl⟩ := List.mem_map.mp hfine
    exact
      finePacketConnectedRateProfiledTerminalSkeletonRow_fineSkeleton_peelSize_pos
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row hrow skeleton hskeleton
  · obtain ⟨skeleton, hskeleton, rfl⟩ := List.mem_map.mp hcoarse
    exact
      finePacketConnectedRateProfiledTerminalSkeletonRow_coarseSkeleton_peelSize_pos
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row hrow skeleton hskeleton

theorem finePacketConnectedRateTerminalSkeletonHistorySizeWord_sum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    natListSum
        (finePacketConnectedRateTerminalSkeletonHistorySizeWord row) =
      finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row := by
  unfold finePacketConnectedRateTerminalSkeletonHistorySizeWord
  rw [natListSum_append,
    natListSum_map_eq_listNatWeight_local,
    natListSum_map_eq_listNatWeight_local]
  change
    slabAcceptedPairedPeelSkeletonMass row.fineSkeletons +
        slabAcceptedPairedPeelSkeletonMass row.coarseSkeletons =
      finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row
  exact
    finePacketConnectedRateProfiledTerminalSkeletonRow_skeletonMass_eq_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow

theorem finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (mass : Nat)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (hmass : finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row =
      mass) :
    finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate row ∈
      allSeqs 2 mass := by
  apply positiveCompositionBinaryCode_mem_allSeqs mass
  · exact finePacketConnectedRateTerminalSkeletonHistorySizeWord_positive
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  · rw [finePacketConnectedRateTerminalSkeletonHistorySizeWord_sum
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow, hmass]

/-! ## 3. The exact remaining geometric adequacy theorem -/

def FinePacketConnectedRateTerminalSkeletonHistorySizeWordAdequate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) : Prop :=
  forall left,
    left ∈ finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code ->
  forall right,
    right ∈ finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code ->
  finePacketConnectedRateTerminalSkeletonHistorySizeWord left =
      finePacketConnectedRateTerminalSkeletonHistorySizeWord right ->
    left = right

theorem finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate_eq_iff_sizeWord_eq
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (left right : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hleft : left ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (hright : right ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate left =
        finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate right ↔
      finePacketConnectedRateTerminalSkeletonHistorySizeWord left =
        finePacketConnectedRateTerminalSkeletonHistorySizeWord right := by
  constructor
  · intro hcode
    exact positiveCompositionBinaryCode_injective _ _
      (finePacketConnectedRateTerminalSkeletonHistorySizeWord_positive
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace left hleft)
      (finePacketConnectedRateTerminalSkeletonHistorySizeWord_positive
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace right hright)
      hcode
  · exact congrArg positiveCompositionBinaryCode

def finePacketConnectedRateTerminalSkeletonBinaryHistoryCertificateOfSizeWordAdequate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (hadequate :
      FinePacketConnectedRateTerminalSkeletonHistorySizeWordAdequate
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code) :
    FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code where
  encode := fun _ row =>
    finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate row
  encode_mem := by
    intro mass row hrow hmass
    have hglobal := (List.mem_filter.mp hrow).1
    exact finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace mass row hglobal hmass
  injectiveAtMass := by
    intro _mass left hleft _hleftMass right hright _hrightMass hcode
    apply hadequate left hleft right hright
    have hleftGlobal := (List.mem_filter.mp hleft).1
    have hrightGlobal := (List.mem_filter.mp hright).1
    exact
      (finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate_eq_iff_sizeWord_eq
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace left right hleftGlobal hrightGlobal).mp hcode

#print axioms finePacketConnectedRateTerminalSkeletonBinaryHistoryCandidate_mem
#print axioms finePacketConnectedRateTerminalSkeletonBinaryHistoryCertificateOfSizeWordAdequate

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryCandidate
