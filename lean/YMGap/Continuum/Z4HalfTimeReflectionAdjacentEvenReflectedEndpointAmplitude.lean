/-
# Reflected endpoint amplitudes on the adjacent-even slab

The palindromic boundary assembly becomes useful only after the link-channel
amplitudes are shown to read the same common half-state coordinate.  This file
proves that identification.  A sum-budget permutation lemma first strengthens
the existing physical permutation theorem: an arbitrary spin word may be
permuted in front of a fixed trailing endpoint channel whenever the word's
total spin fits in the auxiliary window.  Reflection transports the literal
upper incident-face word to the lower word, and the production `6*K` bound
pays that exact budget.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedEndpointAmplitude

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Permuting a word before a fixed endpoint channel -/

private theorem natListSum_eq_of_permLocal
    {left right : List Nat} (hperm : left.Perm right) :
    natListSum left = natListSum right := by
  induction hperm with
  | nil => rfl
  | cons head _ ih =>
      simp only [natListSum]
      rw [ih]
  | swap first second rest =>
      simp only [natListSum]
      omega
  | trans _ _ ihleft ihrigh =>
      exact ihleft.trans ihrigh

/-- Prefix-stable permutation invariance with a fixed arbitrary tail.  The
tail is deliberately absent from the budget: adjacent swaps occur entirely
inside the permuted word, before the endpoint channel. -/
theorem fusionPathMultiplicity_perm_before_tail
    {cutoff : Nat} {left right : List Nat}
    (hperm : left.Perm right) : ∀ before after : List Nat,
    natListSum before + natListSum left ≤ cutoff →
      fusionPathMultiplicity cutoff (before ++ left ++ after) =
        fusionPathMultiplicity cutoff (before ++ right ++ after) := by
  induction hperm with
  | nil =>
      intro before after _
      rfl
  | @cons spin left right hperm ih =>
      intro before after hbudget
      have hbudget' :
          natListSum (before ++ [spin]) + natListSum left ≤ cutoff := by
        rw [natListSum_append]
        simp only [natListSum]
        simp only [natListSum] at hbudget
        omega
      simpa only [List.append_assoc, List.singleton_append] using
        ih (before ++ [spin]) after hbudget'
  | swap first second rest =>
      intro before after hbudget
      have hpref : natListSum before + first + second ≤ cutoff := by
        simp only [natListSum] at hbudget
        omega
      simpa only [List.append_assoc] using
        (fusionPathMultiplicity_swap_adjacent
          (cutoff := cutoff) before (rest ++ after) hpref).symm
  | @trans first middle last hleft hright ihleft ihrigh =>
      intro before after hbudget
      have hmiddleBudget :
          natListSum before + natListSum middle ≤ cutoff := by
        rw [← natListSum_eq_of_permLocal hleft]
        exact hbudget
      exact (ihleft before after hbudget).trans
        (ihrigh before after hmiddleBudget)

/-- Channel amplitudes are invariant under a permutation of the preceding
spin word whenever that word, by itself, fits in the channel cutoff. -/
theorem fusionChannelAmplitude_perm_of_sum_le
    {cutoff channel : Nat} {left right : List Nat}
    (hperm : left.Perm right)
    (hbudget : natListSum left ≤ cutoff) :
    fusionChannelAmplitude cutoff left channel =
      fusionChannelAmplitude cutoff right channel := by
  unfold fusionChannelAmplitude
  have hbudget' : natListSum [] + natListSum left ≤ cutoff := by
    simpa only [natListSum, Nat.zero_add] using hbudget
  simpa only [List.nil_append, Nat.zero_add] using
    (fusionPathMultiplicity_perm_before_tail hperm
      [] [channel] hbudget')

/-! ## 2. Reflection transports the literal upper incident word -/

/-- Reflection fixes every link classified as adjacent-even fixed. -/
theorem adjacentEvenTimeReflectLink_eq_self_of_fixed_side
    {radius : Nat} {link : Z4Link}
    (hside : adjacentEvenLinkSide radius link = .fixed) :
    timeReflectLink (adjacentEvenExtent radius) link = link := by
  obtain ⟨⟨a, b, c, time⟩, direction⟩ := link
  cases direction
  all_goals simp only [adjacentEvenLinkSide] at hside
  all_goals simp only [timeReflectLink, adjacentEvenExtent,
    centralExtent]
  all_goals
    simp only [adjacentEvenSpatialSide,
      adjacentEvenTemporalSide, adjacentEvenCenter] at hside
    repeat' split at hside
    all_goals simp_all
    all_goals omega

/-- The upper incident IDs, numerically reflected, are a permutation of the
lower incident IDs at the reflected link. -/
theorem adjacentEvenIncidentUpperFaceIds_reflection_perm
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks
      (adjacentEvenExtent radius)) :
    (((adjacentEvenIncidentFaceIdParts radius link).2.2).map
        (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (adjacentEvenIncidentFaceIdParts radius
        (timeReflectLink (adjacentEvenExtent radius) link)).1 := by
  let extent := adjacentEvenExtent radius
  let faces := slabIncidentPlaqIds extent link
  let reflectedFaces := slabIncidentPlaqIds extent
    (timeReflectLink extent link)
  let reflectId := slabFaceReflectId extent
  let side : Nat → CrossPlaneSide := fun id =>
    adjacentEvenPlaquetteSide radius (slabPlaquetteAt extent id)
  let lowerPredicate : Nat → Bool := fun id =>
    decide (side id = .lower)
  let upperPredicate : Nat → Bool := fun id =>
    decide (side id = .upper)
  have hfiltered :=
    (slabIncidentPlaqIds_reflection_perm hlink).filter lowerPredicate
  rw [List.filter_map] at hfiltered
  have hsource :
      faces.filter (lowerPredicate ∘ reflectId) =
        faces.filter upperPredicate := by
    apply List.filter_congr
    intro id hid
    have hidPhysical := slabIncidentPlaqId_physical hid
    have hside := adjacentEvenSlabFaceReflectId_side
      (radius := radius) hidPhysical
    change side (reflectId id) = flipSide (side id) at hside
    cases horiginal : side id with
    | lower =>
        have hreflected : side (reflectId id) = .upper := by
          simpa [horiginal, flipSide] using hside
        simp [lowerPredicate, upperPredicate, Function.comp_apply,
          horiginal, hreflected]
    | fixed =>
        have hreflected : side (reflectId id) = .fixed := by
          simpa [horiginal, flipSide] using hside
        simp [lowerPredicate, upperPredicate, Function.comp_apply,
          horiginal, hreflected]
    | upper =>
        have hreflected : side (reflectId id) = .lower := by
          simpa [horiginal, flipSide] using hside
        simp [lowerPredicate, upperPredicate, Function.comp_apply,
          horiginal, hreflected]
  rw [hsource] at hfiltered
  simpa [adjacentEvenIncidentFaceIdParts, extent, faces,
    reflectedFaces, reflectId, side, lowerPredicate, upperPredicate,
    partitionBySide_lower_eq_filter,
    partitionBySide_upper_eq_filter] using hfiltered

/-- With the reflected labelling, the reflected link's lower spin word is a
permutation of the original link's upper word. -/
theorem adjacentEvenIncidentUpperSpins_reflection_perm
    (radius : Nat) (physical : Nat → Nat)
    {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks
      (adjacentEvenExtent radius)) :
    (adjacentEvenIncidentUpperSpins radius physical link).Perm
      (adjacentEvenIncidentLowerSpins radius
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        (timeReflectLink (adjacentEvenExtent radius) link)) := by
  have hids :=
    (adjacentEvenIncidentUpperFaceIds_reflection_perm hlink).map
      (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
  have hleft :
      (((adjacentEvenIncidentFaceIdParts radius link).2.2).map
          (slabFaceReflectId (adjacentEvenExtent radius))).map
          (reflectSlabFaceLabelling
            (adjacentEvenExtent radius) physical) =
        ((adjacentEvenIncidentFaceIdParts radius link).2.2).map
          physical := by
    rw [List.map_map]
    apply List.map_congr_left
    intro id hid
    simp only [Function.comp_apply, reflectSlabFaceLabelling]
    have hidFull : id ∈ slabIncidentPlaqIds
        (adjacentEvenExtent radius) link := by
      have hconcat : id ∈
          (adjacentEvenIncidentFaceIdParts radius link).1 ++
            (adjacentEvenIncidentFaceIdParts radius link).2.1 ++
              (adjacentEvenIncidentFaceIdParts radius link).2.2 :=
        List.mem_append_right _ hid
      exact ((partitionBySide_perm
        (fun faceId => adjacentEvenPlaquetteSide radius
          (slabPlaquetteAt (adjacentEvenExtent radius) faceId))
        (slabIncidentPlaqIds
          (adjacentEvenExtent radius) link)).mem_iff).mp hconcat
    rw [slabFaceReflectId_involutive
      (slabIncidentPlaqId_physical hidFull)]
  rw [hleft] at hids
  exact hids

/-! ## 3. The actual endpoint-amplitude palindromic identity -/

private theorem adjacentEvenUpperWord_sum_le_auxiliary
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    natListSum
        (adjacentEvenIncidentUpperSpins radius physical link).reverse ≤
      linkAuxiliaryCutoff K := by
  have hboundedFull :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  have hupper : SpinsBounded K
      (adjacentEvenIncidentUpperSpins radius physical link).reverse := by
    intro spin hspin
    apply hboundedFull spin
    unfold adjacentEvenPartitionedIncidentSpins
    exact List.mem_append_right _
      (List.mem_reverse.mp hspin)
  have hsum := natListSum_le_length_mul
    (adjacentEvenIncidentUpperSpins radius physical link).reverse hupper
  have hlength :
      (adjacentEvenIncidentUpperSpins radius physical link).reverse.length ≤
        6 := by
    rw [List.length_reverse]
    have htotal :=
      adjacentEvenPartitionedIncidentSpins_length_le_six
        radius physical link
    unfold adjacentEvenPartitionedIncidentSpins at htotal
    simp only [List.length_append] at htotal
    omega
  have hscaled := Nat.mul_le_mul_right K hlength
  exact Nat.le_trans hsum (by
    unfold linkAuxiliaryCutoff
    simpa [Nat.mul_comm] using hscaled)

/-- On every literal fixed link, the reflected-upper endpoint amplitude is
the lower endpoint amplitude of the reflected physical labelling, at the same
channel. -/
theorem adjacentEvenReflectedUpperLinkAmplitude_eqv_reflectedLower
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius)
    (channel : Nat) :
    adjacentEvenReflectedUpperLinkAmplitude
        K radius physical link channel ≈
      adjacentEvenLowerLinkAmplitude K radius
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        link channel := by
  have hfixed := (mem_adjacentEvenFixedSlabLinks).mp hlink
  have hreflectLink :=
    adjacentEvenTimeReflectLink_eq_self_of_fixed_side hfixed.2
  have hperm :
      (adjacentEvenIncidentUpperSpins radius physical link).reverse.Perm
        (adjacentEvenIncidentLowerSpins radius
          (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
          link) := by
    have hupperPerm :=
      adjacentEvenIncidentUpperSpins_reflection_perm
        radius physical (link := link) hfixed.1
    rw [hreflectLink] at hupperPerm
    exact (List.reverse_perm
      (adjacentEvenIncidentUpperSpins radius physical link)).trans
        hupperPerm
  unfold adjacentEvenReflectedUpperLinkAmplitude
    adjacentEvenLowerLinkAmplitude
  exact Q'.eqv_of_eq (congrArg Q'.ofNat
    (fusionChannelAmplitude_perm_of_sum_le hperm
      (adjacentEvenUpperWord_sum_le_auxiliary hphysical link)
      (channel := channel)))

/-- The complete fixed-link endpoint product uses the same lower-amplitude
map after reflection.  This is the literal `A`/`A^t` identification needed by
the finite palindromic sandwich theorem. -/
theorem adjacentEvenReflectedUpperAmplitudeProduct_eqv_reflectedLower
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (channel : Z4Link → Nat) :
    adjacentEvenReflectedUpperAmplitudeProduct
        K radius physical channel ≈
      adjacentEvenLowerAmplitudeProduct K radius
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        channel := by
  unfold adjacentEvenReflectedUpperAmplitudeProduct
    adjacentEvenLowerAmplitudeProduct
  apply listQProduct_congr_eqv
  intro link hlink
  exact adjacentEvenReflectedUpperLinkAmplitude_eqv_reflectedLower
    hphysical hlink (channel link)

private theorem adjacentEvenLowerSpins_rawReflect_eq_supportedReflect
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) :
    adjacentEvenIncidentLowerSpins radius
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        link =
      adjacentEvenIncidentLowerSpins radius
        (reflectSupportedSlabFaceLabelling
          (adjacentEvenExtent radius) physical) link := by
  unfold adjacentEvenIncidentLowerSpins
  apply List.map_congr_left
  intro id hid
  have hidFull : id ∈ slabIncidentPlaqIds
      (adjacentEvenExtent radius) link := by
    have hconcat : id ∈
        (adjacentEvenIncidentFaceIdParts radius link).1 ++
          (adjacentEvenIncidentFaceIdParts radius link).2.1 ++
            (adjacentEvenIncidentFaceIdParts radius link).2.2 :=
      List.mem_append_left _
        (List.mem_append_left _ hid)
    exact ((partitionBySide_perm
      (fun faceId => adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) faceId))
      (slabIncidentPlaqIds
        (adjacentEvenExtent radius) link)).mem_iff).mp hconcat
  exact (reflectSupportedSlabFaceLabelling_eq_on_physical
    (adjacentEvenExtent radius) physical
    (slabIncidentPlaqId_physical hidFull)).symm

theorem adjacentEvenLowerAmplitudeProduct_rawReflect_eqv_supportedReflect
    (K radius : Nat) (physical : Nat → Nat)
    (channel : Z4Link → Nat) :
    adjacentEvenLowerAmplitudeProduct K radius
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        channel ≈
      adjacentEvenLowerAmplitudeProduct K radius
        (reflectSupportedSlabFaceLabelling
          (adjacentEvenExtent radius) physical) channel := by
  unfold adjacentEvenLowerAmplitudeProduct
    adjacentEvenLowerLinkAmplitude
  apply listQProduct_congr_eqv
  intro link _
  rw [adjacentEvenLowerSpins_rawReflect_eq_supportedReflect]
  exact Q'.eqv_refl _

/-- For an actual bounded reflected assembly, the complete upper endpoint
factor is the same lower-amplitude map evaluated on the right common
half-state coordinate. -/
theorem adjacentEvenAssembledUpperAmplitude_eqv_commonLower
    {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (hboundary : boundary ∈ boundedEdgeLabellings K
      (adjacentEvenFixedFaceIds radius))
    (hright : right ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (channel : Z4Link → Nat) :
    adjacentEvenReflectedUpperAmplitudeProduct K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) channel ≈
      adjacentEvenLowerAmplitudeProduct K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left) channel := by
  let physical := assembleAdjacentEvenReflectedSlabLabelling
    radius left boundary right
  have hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical :=
    assembleAdjacentEvenReflectedSlabLabelling_bounded
      hleft hboundary hright
  refine Q'.eqv_trans _ _ _
    (adjacentEvenReflectedUpperAmplitudeProduct_eqv_reflectedLower
      hphysical channel) ?_
  refine Q'.eqv_trans _ _ _
    (adjacentEvenLowerAmplitudeProduct_rawReflect_eqv_supportedReflect
      K radius physical channel) ?_
  rw [assembleAdjacentEvenReflectedSlabLabelling_reflection_swap]
  exact Q'.eqv_refl _

#print axioms fusionPathMultiplicity_perm_before_tail
#print axioms fusionChannelAmplitude_perm_of_sum_le
#print axioms adjacentEvenIncidentUpperFaceIds_reflection_perm
#print axioms adjacentEvenIncidentUpperSpins_reflection_perm
#print axioms adjacentEvenReflectedUpperLinkAmplitude_eqv_reflectedLower
#print axioms adjacentEvenReflectedUpperAmplitudeProduct_eqv_reflectedLower
#print axioms adjacentEvenLowerAmplitudeProduct_rawReflect_eqv_supportedReflect
#print axioms adjacentEvenAssembledUpperAmplitude_eqv_commonLower

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedEndpointAmplitude
