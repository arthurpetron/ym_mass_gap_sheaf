/-
# Isolated low-spin source factorization of the physical half amplitude

The selected growing-volume low-spin cube lies strictly below the reflection
interface.  Every link touched by that cube is incident only to lower faces,
so the cube is link-separated from the source-free boundary remainder even
inside the lower half-amplitude factor.  Consequently the genuine physical
half amplitude factors exactly as

  A(low-spin source, boundary)
    = lowerFactor(low-spin source) * A(vacuum, boundary).

In particular, every zero of the vacuum boundary row is also a zero of the
selected growing reference row.  This is the support-containment bridge
needed by the boundary-support obstruction route.  It does not construct a
positive boundary outside that support, and it asserts no cofinal gap,
continuum limit, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization
import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry
open YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_four_regroup_local (A B C D : Q') :
    ((A * B) * (C * D)) ≈ ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

/-! ## 1. Binary-union factorization on selected slab factors -/

private theorem slabFaceFactorOn_union_factor
    (w : Q') (K : Nat) (left right : EdgeLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id < K + 1) →
      (∀ id, id ∈ ids → right id < K + 1) →
      (∀ id, id ∈ ids → left id = 0 ∨ right id = 0) →
      slabFaceFactorOn w K (binaryUnionLabel left right) ids ≈
        slabFaceFactorOn w K left ids *
          slabFaceFactorOn w K right ids
  | [], _, _, _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | id :: rest, hleft, hright, hdisjoint => by
      have hhead := parametricKFaceCoefficient_union_eqv_mul w K
        (hleft id List.mem_cons_self)
        (hright id List.mem_cons_self)
        (hdisjoint id List.mem_cons_self)
      have hrest := slabFaceFactorOn_union_factor w K left right rest
        (fun item hitem => hleft item (List.mem_cons_of_mem id hitem))
        (fun item hitem => hright item (List.mem_cons_of_mem id hitem))
        (fun item hitem => hdisjoint item
          (List.mem_cons_of_mem id hitem))
      unfold slabFaceFactorOn eliminateLinks
      exact Q'.eqv_trans _
        ((coeffAt (heatKernelPacket K w) (left id) *
            coeffAt (heatKernelPacket K w) (right id)) *
          (slabFaceFactorOn w K left rest *
            slabFaceFactorOn w K right rest)) _
        (qmul_congr_local hhead hrest)
        (mul_four_regroup_local _ _ _ _)

private def slabLinkTouchesExcitationB
    (extent : Nat) (physical : EdgeLabelling) (link : Z4Link) : Bool :=
  hasExcitedB physical (slabIncidentPlaqIds extent link)

private theorem slabExplicitLinkMultiplicity_eq_one_of_untouched
    {K extent : Nat} {physical : EdgeLabelling} {link : Z4Link}
    (huntouched :
      slabLinkTouchesExcitationB extent physical link = false) :
    slabExplicitLinkMultiplicity K extent physical link = 1 := by
  have hzeroOn :=
    (hasExcitedB_false_iff_zero_on physical
      (slabIncidentPlaqIds extent link)).1 huntouched
  have hmap :
      (slabIncidentPlaqIds extent link).map physical =
        (slabIncidentPlaqIds extent link).map zeroEdgeLabelling := by
    apply List.map_congr_left
    intro id hid
    exact hzeroOn id hid
  unfold slabExplicitLinkMultiplicity
  rw [hmap]
  exact slabExplicitLinkMultiplicity_zero_eq_one K extent link

private theorem slabExplicitLinkMultiplicity_union_eq_right_of_left_untouched
    {K extent : Nat} {left right : EdgeLabelling} {link : Z4Link}
    (huntouched :
      slabLinkTouchesExcitationB extent left link = false) :
    slabExplicitLinkMultiplicity K extent
        (binaryUnionLabel left right) link =
      slabExplicitLinkMultiplicity K extent right link := by
  have hzeroOn :=
    (hasExcitedB_false_iff_zero_on left
      (slabIncidentPlaqIds extent link)).1 huntouched
  have hmap :
      (slabIncidentPlaqIds extent link).map
          (binaryUnionLabel left right) =
        (slabIncidentPlaqIds extent link).map right := by
    apply List.map_congr_left
    intro id hid
    unfold binaryUnionLabel
    rw [hzeroOn id hid, Nat.zero_add]
  unfold slabExplicitLinkMultiplicity
  rw [hmap]

private theorem slabExplicitLinkMultiplicity_union_eq_left_of_right_untouched
    {K extent : Nat} {left right : EdgeLabelling} {link : Z4Link}
    (huntouched :
      slabLinkTouchesExcitationB extent right link = false) :
    slabExplicitLinkMultiplicity K extent
        (binaryUnionLabel left right) link =
      slabExplicitLinkMultiplicity K extent left link := by
  have hzeroOn :=
    (hasExcitedB_false_iff_zero_on right
      (slabIncidentPlaqIds extent link)).1 huntouched
  have hmap :
      (slabIncidentPlaqIds extent link).map
          (binaryUnionLabel left right) =
        (slabIncidentPlaqIds extent link).map left := by
    apply List.map_congr_left
    intro id hid
    unfold binaryUnionLabel
    rw [hzeroOn id hid, Nat.add_zero]
  unfold slabExplicitLinkMultiplicity
  rw [hmap]

private theorem slabExplicitLinkMultiplicity_union_factor
    {K extent : Nat} {left right : EdgeLabelling} {link : Z4Link}
    (hseparated : ¬
      (slabLinkTouchesExcitationB extent left link = true ∧
        slabLinkTouchesExcitationB extent right link = true)) :
    slabExplicitLinkMultiplicity K extent
        (binaryUnionLabel left right) link =
      slabExplicitLinkMultiplicity K extent left link *
        slabExplicitLinkMultiplicity K extent right link := by
  cases hleft : slabLinkTouchesExcitationB extent left link with
  | false =>
      rw [slabExplicitLinkMultiplicity_union_eq_right_of_left_untouched
          hleft,
        slabExplicitLinkMultiplicity_eq_one_of_untouched hleft,
        Nat.one_mul]
  | true =>
      have hright :
          slabLinkTouchesExcitationB extent right link = false := by
        cases hright : slabLinkTouchesExcitationB extent right link with
        | false => rfl
        | true => exact False.elim (hseparated ⟨hleft, hright⟩)
      rw [slabExplicitLinkMultiplicity_union_eq_left_of_right_untouched
          hright,
        slabExplicitLinkMultiplicity_eq_one_of_untouched hright,
        Nat.mul_one]

private theorem natListProduct_slab_union_factor
    (K extent : Nat) (left right : EdgeLabelling) :
    ∀ links : List Z4Link,
      (∀ link, link ∈ links → ¬
        (slabLinkTouchesExcitationB extent left link = true ∧
          slabLinkTouchesExcitationB extent right link = true)) →
      natListProduct
          (slabExplicitLinkMultiplicity K extent
            (binaryUnionLabel left right)) links =
        natListProduct
            (slabExplicitLinkMultiplicity K extent left) links *
          natListProduct
            (slabExplicitLinkMultiplicity K extent right) links
  | [], _ => by simp [natListProduct]
  | link :: rest, hseparated => by
      have hhead := slabExplicitLinkMultiplicity_union_factor
        (K := K) (extent := extent) (left := left) (right := right)
        (hseparated link List.mem_cons_self)
      have hrest := natListProduct_slab_union_factor
        K extent left right rest
        (fun item hitem => hseparated item
          (List.mem_cons_of_mem link hitem))
      simp only [natListProduct]
      rw [hhead, hrest]
      ac_rfl

private theorem centralLowerFactor_union_factor
    {w : Q'} {K half : Nat} {left right : EdgeLabelling}
    (hleft : ∀ id, id ∈ centralLowerFaceIds half → left id < K + 1)
    (hright : ∀ id, id ∈ centralLowerFaceIds half → right id < K + 1)
    (hface : ∀ id, id ∈ centralLowerFaceIds half →
      left id = 0 ∨ right id = 0)
    (hlink : ∀ link, link ∈ centralLowerLinks half → ¬
      (slabLinkTouchesExcitationB (centralExtent half) left link = true ∧
        slabLinkTouchesExcitationB
          (centralExtent half) right link = true)) :
    centralLowerFactor w K half (binaryUnionLabel left right) ≈
      centralLowerFactor w K half left *
        centralLowerFactor w K half right := by
  have hfaces := slabFaceFactorOn_union_factor
    w K left right (centralLowerFaceIds half) hleft hright hface
  have hlinksNat := natListProduct_slab_union_factor
    K (centralExtent half) left right (centralLowerLinks half) hlink
  have hlinks :
      Q'.ofNat
          (slabLinkMultiplicityProductOn K (centralExtent half)
            (binaryUnionLabel left right) (centralLowerLinks half)) ≈
        Q'.ofNat
            (slabLinkMultiplicityProductOn K (centralExtent half)
              left (centralLowerLinks half)) *
          Q'.ofNat
            (slabLinkMultiplicityProductOn K (centralExtent half)
              right (centralLowerLinks half)) := by
    unfold slabLinkMultiplicityProductOn
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg Q'.ofNat hlinksNat))
      (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv _ _)
  unfold centralLowerFactor
  exact Q'.eqv_trans _ _ _
    (qmul_congr_local hfaces hlinks)
    (mul_four_regroup_local _ _ _ _)

/-! ## 2. The growing low-spin source is separated inside the lower factor -/

private theorem hasExcitedB_exists_local (label : EdgeLabelling) :
    ∀ edges, hasExcitedB label edges = true →
      ∃ edge, edge ∈ edges ∧ 1 ≤ label edge
  | [], h => by cases h
  | edge :: rest, h => by
      by_cases hexcited : 1 ≤ label edge
      · exact ⟨edge, List.mem_cons_self, hexcited⟩
      · have hrest : hasExcitedB label rest = true := by
          simpa [hasExcitedB, hexcited] using h
        obtain ⟨found, hmem, hfound⟩ :=
          hasExcitedB_exists_local label rest hrest
        exact ⟨found, List.mem_cons_of_mem edge hmem, hfound⟩

private theorem slabPlaquetteAt_eq_of_enumerate_local
    {extent id : Nat} {plaquette : Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabPlaquetteAt extent id = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

private theorem lowSpinCentralSourceTouch_incident_lower
    {volume : Nat} (index : LowSpinCentralIndex volume)
    {link : Z4Link}
    (htouched :
      slabLinkTouchesExcitationB
        (centralExtent (volume + 1))
        (lowSpinCentralLowerState volume index) link = true) :
    ∀ id,
      id ∈ slabIncidentPlaqIds (centralExtent (volume + 1)) link →
        id ∈ centralLowerFaceIds (volume + 1) := by
  obtain ⟨sourceId, hsourceIncident, hsourcePositive⟩ :=
    hasExcitedB_exists_local
      (lowSpinCentralLowerState volume index)
      (slabIncidentPlaqIds (centralExtent (volume + 1)) link)
      htouched
  obtain ⟨sourceFace, hsourceIndexed, hsourceLink⟩ :=
    mem_slabIncidentPlaqIds.mp hsourceIncident
  have hsourceSlab :
      lowSpinCentralSlabPhysical volume index sourceId =
        lowSpinCentralLowerState volume index sourceId := by
    rw [lowSpinCentralLowerState_eq_slabPhysical index]
  have hsourceBox : sourceFace ∈
      boxPlaquettes (centralAmbient (volume + 1)) := by
    have hslab : sourceFace ∈
        boundaryCompleteSlabPlaquettes
          (centralExtent (volume + 1)) :=
      by
        have hmapped : sourceFace ∈
            (enumerate (boundaryCompleteSlabPlaquettes
              (centralExtent (volume + 1)))).map Prod.snd :=
          List.mem_map.mpr ⟨(sourceId, sourceFace), hsourceIndexed, rfl⟩
        rw [enumerate_map_snd] at hmapped
        exact hmapped
    exact (mem_boundaryCompleteSlabPlaquettes
      (centralExtent (volume + 1)) sourceFace).mp hslab |>.1
  obtain ⟨targetId, htargetIndexed⟩ := exists_mem_enumerate hsourceBox
  have hroundtrip := congrFun
    (lowSpinCentralSlabPhysical_roundtrip index) targetId
  rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
    slabGeometricSpin_eq_of_enumerate hsourceIndexed] at hroundtrip
  have htargetPositive :
      1 ≤ timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) targetId := by
    rw [← hroundtrip, hsourceSlab]
    exact hsourcePositive
  have htargetSupport : targetId ∈
      timeSliceSupportIds (2 * volume)
        (lowSpinCentralTimeSliceIndex index) := by
    unfold timeSlicePhysical at htargetPositive
    by_cases hmem : targetId ∈
        timeSliceSupportIds (2 * volume)
          (lowSpinCentralTimeSliceIndex index)
    · exact hmem
    · rw [componentLabel_eq_zero_of_not_mem hmem] at htargetPositive
      omega
  have hsourceAt :
      boxPlaquetteAt (centralAmbient (volume + 1)) targetId =
        sourceFace :=
    boxPlaquetteAt_eq_of_enumerate htargetIndexed
  have hsourceGeometric : sourceFace ∈
      geometricPolymer (4 + 2 * volume)
        (timeSliceSupportIds (2 * volume)
          (lowSpinCentralTimeSliceIndex index)) := by
    rw [← lowSpinCentralAmbient_eq volume] at hsourceAt
    exact List.mem_map.mpr ⟨targetId, htargetSupport, hsourceAt⟩
  have hsourceShifted : sourceFace ∈
      shiftedOddFineCubeSurface index.val :=
    (timeSliceSupportIds_sameSupport
      (lowSpinCentralTimeSliceIndex index)).1 _ hsourceGeometric
  intro id hid
  obtain ⟨otherFace, hotherIndexed, hotherLink⟩ :=
    mem_slabIncidentPlaqIds.mp hid
  have hotherLower :
      plaquetteHalfSide (volume + 1) otherFace = .lower :=
    lowSpinCentralSourceLink_incidentFace_lower index
      hsourceShifted hsourceLink hotherLink
  apply mem_centralLowerFaceIds.mpr
  refine ⟨slabIncidentPlaqId_physical hid, ?_⟩
  rw [slabPlaquetteAt_eq_of_enumerate_local hotherIndexed]
  exact hotherLower

private theorem lowSpinCentralSource_completionRemainder_slabLinkSeparated
    {volume : Nat} (index : LowSpinCentralIndex volume)
    (boundary : EdgeLabelling) :
    ∀ link, link ∈ centralLowerLinks (volume + 1) → ¬
      (slabLinkTouchesExcitationB
          (centralExtent (volume + 1))
          (lowSpinCentralLowerState volume index) link = true ∧
        slabLinkTouchesExcitationB
          (centralExtent (volume + 1))
          (lowSpinCentralCompletionRemainder
            volume boundary zeroEdgeLabelling) link = true) := by
  intro link _hlink hboth
  have hzeroOn : ∀ id,
      id ∈ slabIncidentPlaqIds
          (centralExtent (volume + 1)) link →
        lowSpinCentralCompletionRemainder
            volume boundary zeroEdgeLabelling id = 0 := by
    intro id hid
    have hlower := lowSpinCentralSourceTouch_incident_lower
      index hboth.1 id hid
    have hparts := mem_centralLowerFaceIds.mp hlower
    exact lowSpinCentralCompletionRemainder_zero_on_lower
      hparts.1 hparts.2
  have huntouched :
      slabLinkTouchesExcitationB
        (centralExtent (volume + 1))
        (lowSpinCentralCompletionRemainder
          volume boundary zeroEdgeLabelling) link = false :=
    (hasExcitedB_false_iff_zero_on _ _).2 hzeroOn
  rw [huntouched] at hboth
  cases hboth.2

/-! ## 3. Exact half-amplitude factorization and support containment -/

/-- The genuine growing-volume half amplitude factors through the vacuum
boundary row and the isolated lower source factor. -/
theorem lowSpinCentralHalfAmplitude_eqv_sourceFactor_mul_vacuum
    {w : Q'} {K volume : Nat} (hK : 1 ≤ K)
    (index : LowSpinCentralIndex volume)
    (boundary : EdgeLabelling) :
    centralHalfAmplitude w K (volume + 1)
        (lowSpinCentralLowerState volume index) boundary ≈
      centralLowerFactor w K (volume + 1)
          (lowSpinCentralLowerState volume index) *
        centralHalfAmplitude w K (volume + 1)
          zeroEdgeLabelling boundary := by
  let source := lowSpinCentralLowerState volume index
  let remainder := lowSpinCentralCompletionRemainder
    volume boundary zeroEdgeLabelling
  have hsourceBound : ∀ id,
      id ∈ centralLowerFaceIds (volume + 1) → source id < K + 1 := by
    have hsourceMem := lowSpinCentralLowerState_mem index
    have hsound := boundedEdgeLabellings_sound 1
      (centralLowerFaceIds (volume + 1)) source hsourceMem
    intro id hid
    have hone := hsound.1 id hid
    omega
  have hremainderZero : ∀ id,
      id ∈ centralLowerFaceIds (volume + 1) → remainder id = 0 := by
    intro id hid
    have hparts := mem_centralLowerFaceIds.mp hid
    exact lowSpinCentralCompletionRemainder_zero_on_lower
      hparts.1 hparts.2
  have hremainderBound : ∀ id,
      id ∈ centralLowerFaceIds (volume + 1) → remainder id < K + 1 := by
    intro id hid
    rw [hremainderZero id hid]
    omega
  have hfactor := centralLowerFactor_union_factor
    (w := w) (K := K) (half := volume + 1)
    (left := source) (right := remainder)
    hsourceBound hremainderBound
    (fun id hid => Or.inr (hremainderZero id hid))
    (lowSpinCentralSource_completionRemainder_slabLinkSeparated
      index boundary)
  unfold centralHalfAmplitude
  rw [lowSpinCentralAssembled_eq_binaryUnion
    index boundary zeroEdgeLabelling]
  simpa only [source, remainder,
    lowSpinCentralCompletionRemainder] using hfactor

/-- Every vacuum-row zero is inherited by the selected low-spin source row. -/
theorem lowSpinCentralHalfAmplitude_eqv_zero_of_vacuum_eqv_zero
    {w : Q'} {K volume : Nat} (hK : 1 ≤ K)
    (index : LowSpinCentralIndex volume)
    (boundary : EdgeLabelling)
    (hzero :
      centralHalfAmplitude w K (volume + 1)
        zeroEdgeLabelling boundary ≈ 0) :
    centralHalfAmplitude w K (volume + 1)
        (lowSpinCentralLowerState volume index) boundary ≈
      0 := by
  refine Q'.eqv_trans _ _ _
    (lowSpinCentralHalfAmplitude_eqv_sourceFactor_mul_vacuum
      hK index boundary) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (centralLowerFactor w K (volume + 1)
        (lowSpinCentralLowerState volume index)) _ _ hzero)
    (Q'.mul_zero_eqv _)

/-- The literal slice-zero growing reference has support contained in the
vacuum boundary row. -/
theorem lowSpinCentralReferenceHalfAmplitude_eqv_zero_of_vacuum_eqv_zero
    {w : Q'} {K volume : Nat} (hK : 1 ≤ K)
    (boundary : EdgeLabelling)
    (hzero :
      centralHalfAmplitude w K (volume + 1)
        zeroEdgeLabelling boundary ≈ 0) :
    centralHalfAmplitude w K (volume + 1)
        (lowSpinCentralReferenceState volume) boundary ≈
      0 := by
  unfold lowSpinCentralReferenceState
  exact lowSpinCentralHalfAmplitude_eqv_zero_of_vacuum_eqv_zero
    hK (lowSpinCentralReferenceIndex volume) boundary hzero

end YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization.lowSpinCentralHalfAmplitude_eqv_sourceFactor_mul_vacuum
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization.lowSpinCentralHalfAmplitude_eqv_zero_of_vacuum_eqv_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization.lowSpinCentralReferenceHalfAmplitude_eqv_zero_of_vacuum_eqv_zero
