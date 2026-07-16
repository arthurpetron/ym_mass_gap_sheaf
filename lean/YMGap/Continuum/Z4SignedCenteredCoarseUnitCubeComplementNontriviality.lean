/-
# Positive complement of the centered coarse-cube occurrence

Positive occurrence alone would not show that the centered local observable
is nonconstant.  This module proves a second uniform floor for root absence.
Every compatible family in the contact-deleted ambient is an explicit
root-absent family in the full gas.  Its partition is nonempty because the
vacuum family contributes one, and the previously derived contact deletion
bound controls the full partition by `2^150` times this deleted contribution.

After normalization in the actual finite compatible-support law, the exact
rational absence floor passes to the centered constructive real.  Translating
the signed chart genuinely translates its support while leaving the
approximants unchanged, so both occurrence and complement are strictly
positive at every `Int^4` translate.
-/

import YMGap.Continuum.Z4SignedCenteredCoarseUnitCubeTranslationNontriviality
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.Z4SignedCenteredCoarseUnitCubeComplementNontriviality

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityRootInsertion
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalContactLayerDeletion
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity
open YMGap.Continuum.Z4CenteredCoarseUnitCubeStateNontriviality
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4SignedCenteredCoarseUnitCubeTranslationNontriviality
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredCylinderStateLaws
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A deleted compatible gas injects into root absence -/

private def ambientOrderedFamily {A : Type} [DecidableEq A]
    (ambient family : List A) : List A :=
  ambient.filter (memberB family)

theorem partition_le_rootAbsenceNumerator_of_deleted
    {A : Type} [DecidableEq A]
    (compat : A → A → Bool)
    (hsymm : ∀ left right, compat left right = compat right left)
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (ambient deleted : List A) (root : A)
    (hambient : ambient.Nodup) (hdeleted : deleted.Nodup)
    (hrootDeleted : root ∉ deleted)
    (hdeletedSource : ∀ atom, atom ∈ deleted → atom ∈ ambient) :
    partition compat weight deleted ≤
      eventNumerator compat weight ambient
        (fun family => !(memberB family root)) := by
  let source := compatibleFamilies compat deleted
  let target := (compatibleFamilies compat ambient).filter
    (fun family => !(memberB family root))
  let encode := ambientOrderedFamily ambient
  have hsourceNodup : source.Nodup := by
    unfold source compatibleFamilies
    exact List.filter_sublist.nodup (sublists_nodup deleted hdeleted)
  have hinjection :
      listQSum (familyWeight weight) source ≤
        listQSum (familyWeight weight) target := by
    apply listQSum_le_of_injective source target
      (familyWeight weight) (familyWeight weight) encode hsourceNodup
    · intro family hfamily
      have hparts : family ∈ sublists deleted ∧
          familyCompatibleB compat family = true :=
        List.mem_filter.mp hfamily
      have hencodedCompat :
          familyCompatibleB compat (encode family) = true := by
        apply familyCompatibleB_of_pairwise compat
          (List.filter_sublist.nodup hambient)
        intro left hleft right hright hne
        have hleftFamily : left ∈ family := by
          have hbit := (List.mem_filter.mp hleft).2
          exact (memberB_eq_true_iff family left).1 hbit
        have hrightFamily : right ∈ family := by
          have hbit := (List.mem_filter.mp hright).2
          exact (memberB_eq_true_iff family right).1 hbit
        exact familyCompatibleB_pairwise compat hsymm hparts.2
          hleftFamily hrightFamily hne
      have htargetFamily : encode family ∈
          compatibleFamilies compat ambient := by
        unfold compatibleFamilies encode ambientOrderedFamily
        apply List.mem_filter.mpr
        exact ⟨filter_mem_sublists _ _, hencodedCompat⟩
      have hrootNotFamily : root ∉ family := by
        intro hrootFamily
        exact hrootDeleted
          (mem_of_mem_sublists deleted family hparts.1 root hrootFamily)
      have hrootNotEncoded : root ∉ encode family := by
        intro hrootEncoded
        have hbit := (List.mem_filter.mp hrootEncoded).2
        exact hrootNotFamily ((memberB_eq_true_iff family root).1 hbit)
      unfold target
      apply List.mem_filter.mpr
      exact ⟨htargetFamily, by simp [memberB, hrootNotEncoded]⟩
    · intro left hleft right hright heq
      have hleftParts : left ∈ sublists deleted ∧
          familyCompatibleB compat left = true :=
        List.mem_filter.mp hleft
      have hrightParts : right ∈ sublists deleted ∧
          familyCompatibleB compat right = true :=
        List.mem_filter.mp hright
      apply sublists_eq_of_mem_iff deleted left right hdeleted
        hleftParts.1 hrightParts.1
      intro atom
      constructor
      · intro hatomLeft
        have hatomDeleted := mem_of_mem_sublists deleted left
          hleftParts.1 atom hatomLeft
        have hatomEncoded : atom ∈ encode left := by
          unfold encode ambientOrderedFamily
          apply List.mem_filter.mpr
          exact ⟨hdeletedSource atom hatomDeleted,
            (memberB_eq_true_iff left atom).2 hatomLeft⟩
        rw [heq] at hatomEncoded
        have hbit := (List.mem_filter.mp hatomEncoded).2
        exact (memberB_eq_true_iff right atom).1 hbit
      · intro hatomRight
        have hatomDeleted := mem_of_mem_sublists deleted right
          hrightParts.1 atom hatomRight
        have hatomEncoded : atom ∈ encode right := by
          unfold encode ambientOrderedFamily
          apply List.mem_filter.mpr
          exact ⟨hdeletedSource atom hatomDeleted,
            (memberB_eq_true_iff right atom).2 hatomRight⟩
        rw [← heq] at hatomEncoded
        have hbit := (List.mem_filter.mp hatomEncoded).2
        exact (memberB_eq_true_iff left atom).1 hbit
    · intro family hfamily
      have hparts : family ∈ sublists deleted ∧
          familyCompatibleB compat family = true :=
        List.mem_filter.mp hfamily
      have hfamilyNodup : family.Nodup := by
        have hfiltered : (deleted.filter (memberB family)).Nodup :=
          List.filter_sublist.nodup hdeleted
        rw [filter_memberB_eq_of_mem_sublists hdeleted hparts.1]
          at hfiltered
        exact hfiltered
      have hperm : family.Perm (encode family) := by
        apply perm_of_nodup_mem_iff family (encode family)
          hfamilyNodup (List.filter_sublist.nodup hambient)
        intro atom
        constructor
        · intro hatom
          have hatomDeleted := mem_of_mem_sublists deleted family
            hparts.1 atom hatom
          unfold encode ambientOrderedFamily
          apply List.mem_filter.mpr
          exact ⟨hdeletedSource atom hatomDeleted,
            (memberB_eq_true_iff family atom).2 hatom⟩
        · intro hatom
          have hbit := (List.mem_filter.mp hatom).2
          exact (memberB_eq_true_iff family atom).1 hbit
      exact Q'.le_of_eqv (familyWeight_perm weight hperm)
    · intro family _
      exact familyWeight_nonnegative weight hweight family
  unfold source target at hinjection
  unfold partition eventNumerator
  exact hinjection

/-! ## 2. Explicit centered deleted and absence contributions -/

def activityMatchedCoarseUnitCubeUniformAbsenceFloor : Q' :=
  Q'.divPos (1 : Q') activityMatchedCoarseUnitCubeOccurrenceCost
    activityMatchedCoarseUnitCubeOccurrenceCost_pos

theorem activityMatchedCoarseUnitCubeUniformAbsenceFloor_pos :
    (0 : Q') < activityMatchedCoarseUnitCubeUniformAbsenceFloor := by
  unfold activityMatchedCoarseUnitCubeUniformAbsenceFloor
  exact Q'.divPos_pos _ _
    activityMatchedCoarseUnitCubeOccurrenceCost_pos (by decide)

theorem recedingCenteredCoarseDeletedPartition_one_le
    (cutoff radius : Nat) :
    (1 : Q') ≤
      couplingParametricKCanonicalPolymerPartition
        (unitCubeBlockCoupling anchorCoupling) cutoff
        (centeredBoxBase radius)
        (canonicalContactDeletedAmbient (centeredBoxBase radius)
          (recedingCenteredCoarseUnitCubeRoot radius)) := by
  unfold couplingParametricKCanonicalPolymerPartition
  exact partition_ge_one
    (canonicalPolymerCompatibleB (centeredBoxBase radius))
    (couplingParametricKSupportActivity
      (unitCubeBlockCoupling anchorCoupling) cutoff
      (centeredBoxBase radius))
    (couplingParametricKSupportActivity_nonnegative
      (unitCubeBlockCoupling_nonnegative (by decide)) cutoff
      (centeredBoxBase radius)) _

theorem recedingCenteredCoarseDeletedPartition_le_absenceNumerator
    {cutoff radius : Nat} (hradius : 3 ≤ radius) :
    couplingParametricKCanonicalPolymerPartition
        (unitCubeBlockCoupling anchorCoupling) cutoff
        (centeredBoxBase radius)
        (canonicalContactDeletedAmbient (centeredBoxBase radius)
          (recedingCenteredCoarseUnitCubeRoot radius)) ≤
      couplingParametricKCanonicalPolymerEventNumerator
        (unitCubeBlockCoupling anchorCoupling) cutoff
        (centeredBoxBase radius)
        (canonicalSurfacePolymers (centeredBoxBase radius))
        (fun family =>
          !(familyContainsPolymerB
            (recedingCenteredCoarseUnitCubeRoot radius) family)) := by
  let volume := centeredBoxBase radius
  let root := recedingCenteredCoarseUnitCubeRoot radius
  let coupling := unitCubeBlockCoupling anchorCoupling
  have hroot : root ∈ canonicalSurfacePolymers volume := by
    unfold root volume
    exact recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hraw := partition_le_rootAbsenceNumerator_of_deleted
    (canonicalPolymerCompatibleB volume)
    (canonicalPolymerCompatibleB_symm volume)
    (couplingParametricKSupportActivity coupling cutoff volume)
    (couplingParametricKSupportActivity_nonnegative
      (unitCubeBlockCoupling_nonnegative (by decide)) cutoff volume)
    (canonicalSurfacePolymers volume)
    (canonicalContactDeletedAmbient volume root) root
    (canonicalSurfacePolymers_nodup volume)
    (canonicalContactDeletedAmbient_nodup volume root)
    (canonicalRoot_not_mem_contactDeleted hroot)
    (fun atom hatom =>
      mem_deleteMarkedLayers_source
        (fun face candidate => canonicalContainsFaceB face candidate)
        (canonicalContactFaceCandidates volume root)
        (canonicalSurfacePolymers volume) atom hatom)
  have hevent :
      (fun family => !(memberB family root)) =
        (fun family => !(familyContainsPolymerB root family)) := by
    funext family
    simp [memberB, familyContainsPolymerB]
  unfold couplingParametricKCanonicalPolymerPartition
    couplingParametricKCanonicalPolymerEventNumerator
  rw [← hevent]
  exact hraw

theorem one_le_recedingCenteredCoarseAbsenceNumerator
    {cutoff radius : Nat} (hradius : 3 ≤ radius) :
    (1 : Q') ≤
      couplingParametricKCanonicalPolymerEventNumerator
        (unitCubeBlockCoupling anchorCoupling) cutoff
        (centeredBoxBase radius)
        (canonicalSurfacePolymers (centeredBoxBase radius))
        (fun family =>
          !(familyContainsPolymerB
            (recedingCenteredCoarseUnitCubeRoot radius) family)) :=
  Q'.le_trans' _ _ _
    (recedingCenteredCoarseDeletedPartition_one_le cutoff radius)
    (recedingCenteredCoarseDeletedPartition_le_absenceNumerator hradius)

/-! ## 3. The normalized finite complement floor -/

theorem activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_recedingCenteredProbability
    {cutoff radius : Nat} (hradius : 3 ≤ radius) :
    activityMatchedCoarseUnitCubeUniformAbsenceFloor ≤
      couplingParametricKCompatibleSupportEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) cutoff
        (centeredBoxBase radius)
        (fun family =>
          !(familyContainsPolymerB
            (recedingCenteredCoarseUnitCubeRoot radius) family)) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let volume := centeredBoxBase radius
  let root := recedingCenteredCoarseUnitCubeRoot radius
  let fullPartition := couplingParametricKCanonicalPolymerPartition
    coupling cutoff volume (canonicalSurfacePolymers volume)
  let deletedPartition := couplingParametricKCanonicalPolymerPartition
    coupling cutoff volume (canonicalContactDeletedAmbient volume root)
  let genericNumerator :=
    couplingParametricKCanonicalPolymerEventNumerator
      coupling cutoff volume (canonicalSurfacePolymers volume)
      (fun family => !(familyContainsPolymerB root family))
  let gasPartition := couplingParametricKCompatibleSupportGasPartition
    coupling cutoff volume
  let numerator := couplingParametricKCompatibleSupportEventNumerator
    coupling cutoff volume
      (fun family => !(familyContainsPolymerB root family))
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hpartition : fullPartition ≤
      activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition := by
    unfold fullPartition deletedPartition volume root
    exact recedingCenteredCoarseSpinSummedPartition_le_cost_mul_deleted
      hradius
  have habsence : deletedPartition ≤ genericNumerator := by
    unfold deletedPartition genericNumerator volume root coupling
    exact
      recedingCenteredCoarseDeletedPartition_le_absenceNumerator hradius
  have hfloor0 : (0 : Q') ≤
      activityMatchedCoarseUnitCubeUniformAbsenceFloor :=
    Q'.le_of_lt activityMatchedCoarseUnitCubeUniformAbsenceFloor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      activityMatchedCoarseUnitCubeUniformAbsenceFloor *
          (activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition) ≈
        deletedPartition := by
    refine Q'.eqv_trans _
      ((activityMatchedCoarseUnitCubeUniformAbsenceFloor *
          activityMatchedCoarseUnitCubeOccurrenceCost) *
        deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ ((1 : Q') * deletedPartition) _ ?_
      (Q'.one_mul_eqv deletedPartition)
    apply Q'.mul_eqv_congr_right
    unfold activityMatchedCoarseUnitCubeUniformAbsenceFloor
    exact Q'.divPos_mul_eqv _ _
      activityMatchedCoarseUnitCubeOccurrenceCost_pos
  have hgeneric :
      activityMatchedCoarseUnitCubeUniformAbsenceFloor *
          fullPartition ≤ genericNumerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) habsence)
  have hfullGas : fullPartition ≈ gasPartition := by
    unfold fullPartition gasPartition
    exact couplingParametricKCanonicalPolymerPartition_eqv_compatible
      coupling cutoff volume
  have hgenericNumerator : genericNumerator ≈ numerator := by
    unfold genericNumerator numerator
    exact couplingParametricKCanonicalPolymerEventNumerator_eqv_compatible
      coupling cutoff volume
      (fun family => !(familyContainsPolymerB root family))
  have hmul :
      activityMatchedCoarseUnitCubeUniformAbsenceFloor * gasPartition ≤
        numerator :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          activityMatchedCoarseUnitCubeUniformAbsenceFloor
          gasPartition fullPartition (Q'.eqv_symm hfullGas)))
      (Q'.le_trans' _ _ _ hgeneric
        (Q'.le_of_eqv hgenericNumerator))
  unfold couplingParametricKCompatibleSupportEventProbability
  exact Q'.le_divPos_of_mul_le numerator gasPartition
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff volume) hmul

theorem activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_physicalProbability
    {cutoff radius : Nat} (hradius : 3 ≤ radius) :
    activityMatchedCoarseUnitCubeUniformAbsenceFloor ≤
      couplingKFamilyEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) cutoff
        (centeredBoxBase radius)
        (fun family =>
          !(familyContainsPolymerB
            (recedingCenteredCoarseUnitCubeRoot radius) family)) := by
  have hcompatible :=
    activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_recedingCenteredProbability
      (cutoff := cutoff) hradius
  have hbridge := couplingKFamilyEventProbability_eqv_compatible
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide)) cutoff
    (centeredBoxBase radius)
    (fun family =>
      !(familyContainsPolymerB
        (recedingCenteredCoarseUnitCubeRoot radius) family))
  exact Q'.le_trans' _ _ _ hcompatible (Q'.ge_of_eqv hbridge)

/-! ## 4. The complement floor on the centered diagonal -/

theorem centeredCoarseUnitCube_stageComplementEvent_eq_absence
    (stage : Nat) :
    centeredRecedingCylinderEvent 3 stage
        centeredCoarseUnitCubeCylinderRootsAtThree
        (complementCylinderPredicate unitCubeSingleOccurrencePredicate) =
      fun family =>
        !(familyContainsPolymerB
          (recedingCenteredCoarseUnitCubeRoot (3 + stage)) family) := by
  rfl

theorem activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_centeredComplementStage
    (stage : Nat) :
    activityMatchedCoarseUnitCubeUniformAbsenceFloor ≤
      couplingParametricCenteredRecedingCylinderSequence
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) 3
        centeredCoarseUnitCubeCylinderRootsAtThree
        (complementCylinderPredicate unitCubeSingleOccurrencePredicate)
        stage := by
  unfold couplingParametricCenteredRecedingCylinderSequence
  rw [centeredCoarseUnitCube_stageComplementEvent_eq_absence]
  simpa only [centeredRecedingStageBase,
    centeredRecedingStageRadius] using
    (activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_recedingCenteredProbability
      (cutoff := centeredRecedingStageCutoff 3 stage)
      (radius := 3 + stage) (by omega))

/-! ## 5. Signed translation of the complementary observable -/

def centeredCoarseUnitCubeSignedComplementPresentation :
    SignedCenteredCylinderPresentation where
  chart := centeredCoarseUnitCubeSignedChart
  predicate := complementCylinderPredicate unitCubeSingleOccurrencePredicate

theorem centeredCoarseUnitCubeSignedComplementPresentation_translate_aligned
    (shift : SignedZ4Vector) :
    SignedCenteredPresentationAlignedEquivalent
      (centeredCoarseUnitCubeSignedComplementPresentation.translate shift)
      centeredCoarseUnitCubeSignedComplementPresentation :=
  signedCenteredPresentationAlignedEquivalent_translate
    shift centeredCoarseUnitCubeSignedComplementPresentation

def centeredCoarseUnitCubeSignedComplementStateOccurrence : CReal :=
  couplingParametricSignedCenteredPresentationValueAtAnchor
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    centeredCoarseUnitCubeSignedComplementPresentation

def centeredCoarseUnitCubeTranslatedComplementStateOccurrence
    (shift : SignedZ4Vector) : CReal :=
  couplingParametricSignedCenteredPresentationValueAtAnchor
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    (centeredCoarseUnitCubeSignedComplementPresentation.translate shift)

theorem centeredCoarseUnitCubeTranslatedComplementStateOccurrence_equiv_base
    (shift : SignedZ4Vector) :
    CReal.Equiv
      (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift)
      centeredCoarseUnitCubeSignedComplementStateOccurrence := by
  exact couplingParametricSignedCenteredPresentationValueAtAnchor_respects
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    (centeredCoarseUnitCubeSignedComplementPresentation_translate_aligned
      shift)

@[simp] theorem centeredCoarseUnitCubeTranslatedComplementStateOccurrence_approx
    (shift : SignedZ4Vector) (stage : Nat) :
    (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift).approx
        stage =
      couplingParametricCenteredRecedingCylinderSequence
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) 3
        centeredCoarseUnitCubeCylinderRootsAtThree
        (complementCylinderPredicate unitCubeSingleOccurrencePredicate)
        stage := by
  rfl

theorem activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_translatedComplementState
    (shift : SignedZ4Vector) :
    CReal.ofQ' activityMatchedCoarseUnitCubeUniformAbsenceFloor ≤
      centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [centeredCoarseUnitCubeTranslatedComplementStateOccurrence_approx]
  exact
    activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_centeredComplementStage
      stage

theorem centeredCoarseUnitCubeTranslatedComplementStateOccurrence_pos
    (shift : SignedZ4Vector) :
    CReal.IsPositive
      (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift) :=
  ⟨activityMatchedCoarseUnitCubeUniformAbsenceFloor,
    activityMatchedCoarseUnitCubeUniformAbsenceFloor_pos,
    activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_translatedComplementState
      shift⟩

/-! ## 6. Constructive strict-below-one certificate -/

private theorem equiv_ofQ'_of_eqv_complement_local
    {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_complement_local
    {A B : CReal} (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_complement_local (h stage))

/-- The translated occurrence has a positive complementary observable and
the two add exactly to one.  This is the repository's witness-bearing
constructive replacement for an undecidable bare inequality `value < 1`. -/
theorem centeredCoarseUnitCubeTranslatedStateOccurrence_add_complement_eqv_one
    (shift : SignedZ4Vector) :
    CReal.Equiv
      (CReal.add
        (centeredCoarseUnitCubeTranslatedStateOccurrence shift)
        (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_complement_local
  intro stage
  simp only [CReal.add_approx,
    centeredCoarseUnitCubeTranslatedStateOccurrence_approx,
    centeredCoarseUnitCubeTranslatedComplementStateOccurrence_approx,
    CReal.ofQ'_approx]
  exact couplingParametricCenteredRecedingCylinderSequence_complement
    (unitCubeBlockCoupling_nonnegative (by decide)) 3
    centeredCoarseUnitCubeCylinderRootsAtThree
    unitCubeSingleOccurrencePredicate stage

theorem centeredCoarseUnitCubeTranslatedStateOccurrence_and_complement_pos
    (shift : SignedZ4Vector) :
    CReal.IsPositive
        (centeredCoarseUnitCubeTranslatedStateOccurrence shift) ∧
      CReal.IsPositive
        (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift) :=
  ⟨centeredCoarseUnitCubeTranslatedStateOccurrence_pos shift,
    centeredCoarseUnitCubeTranslatedComplementStateOccurrence_pos shift⟩

theorem centeredCoarseUnitCubeTranslatedStateOccurrence_strictlyBelowOneWitness
    (shift : SignedZ4Vector) :
    CReal.IsPositive
        (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift) ∧
      CReal.Equiv
        (CReal.add
          (centeredCoarseUnitCubeTranslatedStateOccurrence shift)
          (centeredCoarseUnitCubeTranslatedComplementStateOccurrence shift))
        (CReal.ofQ' 1) :=
  ⟨centeredCoarseUnitCubeTranslatedComplementStateOccurrence_pos shift,
    centeredCoarseUnitCubeTranslatedStateOccurrence_add_complement_eqv_one
      shift⟩

#print axioms partition_le_rootAbsenceNumerator_of_deleted
#print axioms activityMatchedCoarseUnitCubeUniformAbsenceFloor_pos
#print axioms recedingCenteredCoarseDeletedPartition_one_le
#print axioms recedingCenteredCoarseDeletedPartition_le_absenceNumerator
#print axioms one_le_recedingCenteredCoarseAbsenceNumerator
#print axioms activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_recedingCenteredProbability
#print axioms activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_physicalProbability
#print axioms centeredCoarseUnitCube_stageComplementEvent_eq_absence
#print axioms activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_centeredComplementStage
#print axioms centeredCoarseUnitCubeSignedComplementPresentation_translate_aligned
#print axioms centeredCoarseUnitCubeTranslatedComplementStateOccurrence_equiv_base
#print axioms centeredCoarseUnitCubeTranslatedComplementStateOccurrence_approx
#print axioms activityMatchedCoarseUnitCubeUniformAbsenceFloor_le_translatedComplementState
#print axioms centeredCoarseUnitCubeTranslatedComplementStateOccurrence_pos
#print axioms centeredCoarseUnitCubeTranslatedStateOccurrence_add_complement_eqv_one
#print axioms centeredCoarseUnitCubeTranslatedStateOccurrence_and_complement_pos
#print axioms centeredCoarseUnitCubeTranslatedStateOccurrence_strictlyBelowOneWitness

end YMGap.Continuum.Z4SignedCenteredCoarseUnitCubeComplementNontriviality
