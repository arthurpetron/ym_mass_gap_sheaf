/-
# Uniform support bound for adjacent-even lower endpoint amplitudes

Reflection pairs the lower and upper incidence subwords of every fixed link.
Since the complete four-dimensional incidence word has length at most six,
each half-word has length at most three.  This file combines that geometry
with an exact fusion-walk support lemma: an endpoint channel above the sum of
the traversed spins has zero amplitude.  Hence every physical lower endpoint
lies below `3*K`, uniformly in the radius, while the auxiliary trajectory
window remains `6*K`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSupportGeneric

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedEndpointAmplitude
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem natListSum_map_eq_zeroLocal
    {A : Type} (value : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → value item = 0) →
      natListSum (items.map value) = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [List.map_cons, natListSum]
      rw [hzero head List.mem_cons_self,
        natListSum_map_eq_zeroLocal value tail
          (fun item hitem => hzero item
            (List.mem_cons_of_mem head hitem)), Nat.zero_add]

/-! ## 1. Fusion support cannot outrun total input spin -/

theorem fusionWalkMultiplicity_eq_zero_of_finish_gt
    (cutoff finish : Nat) : ∀ (spins : List Nat) (start : Nat),
    start + natListSum spins < finish →
      fusionWalkMultiplicity cutoff start finish spins = 0
  | [], start, hfinish => by
      unfold fusionWalkMultiplicity
      have hne : start ≠ finish := by omega
      simp [hne, boolMultiplicity]
  | spin :: rest, start, hfinish => by
      simp only [fusionWalkMultiplicity]
      apply natListSum_map_eq_zeroLocal
      intro next hnext
      by_cases hfusion : fusionOK start spin next
      · rw [if_pos hfusion]
        apply fusionWalkMultiplicity_eq_zero_of_finish_gt
        have hnext := fusionOK_output_le_add hfusion
        simp only [natListSum] at hfinish
        omega
      · rw [if_neg hfusion]

/-- A half-channel amplitude vanishes above the total spin in its word. -/
theorem fusionChannelAmplitude_eq_zero_of_sum_lt
    {cutoff channel : Nat} {spins : List Nat}
    (hchannel : channel ≤ cutoff)
    (hspins : SpinsBounded cutoff spins)
    (hlarge : natListSum spins < channel) :
    fusionChannelAmplitude cutoff spins channel = 0 := by
  rw [fusionChannelAmplitude_eq_walk hchannel hspins]
  exact fusionWalkMultiplicity_eq_zero_of_finish_gt
    cutoff channel spins 0 (by simpa using hlarge)

/-! ## 2. Every fixed-link lower word has length at most three -/

theorem adjacentEvenFixedLink_lowerSpins_length_le_three
    (radius : Nat) (physical : Nat → Nat)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius) :
    (adjacentEvenIncidentLowerSpins radius physical link).length ≤ 3 := by
  have hfixed := (mem_adjacentEvenFixedSlabLinks).mp hlink
  have hreflect :=
    adjacentEvenTimeReflectLink_eq_self_of_fixed_side hfixed.2
  have hperm := adjacentEvenIncidentUpperFaceIds_reflection_perm
    (radius := radius) hfixed.1
  rw [hreflect] at hperm
  have hhalves :
      (adjacentEvenIncidentUpperSpins radius physical link).length =
        (adjacentEvenIncidentLowerSpins radius physical link).length := by
    unfold adjacentEvenIncidentUpperSpins
      adjacentEvenIncidentLowerSpins
    simp only [List.length_map]
    simpa only [List.length_map] using hperm.length_eq
  have htotal :=
    adjacentEvenPartitionedIncidentSpins_length_le_six
      radius physical link
  unfold adjacentEvenPartitionedIncidentSpins at htotal
  simp only [List.length_append] at htotal
  omega

theorem adjacentEvenFixedLink_lowerSpinSum_le_three_mul
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius) :
    natListSum (adjacentEvenIncidentLowerSpins radius physical link) ≤
      3 * K := by
  have hfull :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  have hlower : SpinsBounded K
      (adjacentEvenIncidentLowerSpins radius physical link) := by
    intro spin hspin
    apply hfull spin
    unfold adjacentEvenPartitionedIncidentSpins
    exact List.mem_append_left _
      (List.mem_append_left _ hspin)
  have hsum := natListSum_le_length_mul
    (adjacentEvenIncidentLowerSpins radius physical link) hlower
  have hlength := adjacentEvenFixedLink_lowerSpins_length_le_three
    radius physical hlink
  exact Nat.le_trans hsum (Nat.mul_le_mul_right K hlength)

/-- The coupled lower-plus-fixed incidence length, unlike independent loose
`3+3` bounds, stays inside the six-leg production budget. -/
theorem adjacentEvenFixedLink_lower_add_fixed_length_le_six
    (radius : Nat) (physical : Nat → Nat) (link : Z4Link) :
    (adjacentEvenIncidentLowerSpins radius physical link).length +
        (adjacentEvenIncidentFixedSpins radius physical link).length ≤ 6 := by
  have htotal :=
    adjacentEvenPartitionedIncidentSpins_length_le_six
      radius physical link
  unfold adjacentEvenPartitionedIncidentSpins at htotal
  simp only [List.length_append] at htotal
  omega

/-- Exact coupled spin-sum budget: a reachable source paid by the lower word
and every fixed spin together remain inside `6*K`. -/
theorem adjacentEvenFixedLink_lower_add_fixed_sum_le_auxiliary
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    natListSum (adjacentEvenIncidentLowerSpins radius physical link) +
        natListSum (adjacentEvenIncidentFixedSpins radius physical link) ≤
      linkAuxiliaryCutoff K := by
  let combined :=
    adjacentEvenIncidentLowerSpins radius physical link ++
      adjacentEvenIncidentFixedSpins radius physical link
  have hfull :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  have hcombined : SpinsBounded K combined := by
    intro spin hspin
    dsimp [combined] at hspin
    apply hfull spin
    unfold adjacentEvenPartitionedIncidentSpins
    exact List.mem_append_left _ hspin
  have hsum := natListSum_le_length_mul combined hcombined
  have hlength : combined.length ≤ 6 := by
    unfold combined
    simpa only [List.length_append] using
      adjacentEvenFixedLink_lower_add_fixed_length_le_six
        radius physical link
  have hscaled := Nat.mul_le_mul_right K hlength
  rw [natListSum_append] at hsum
  exact Nat.le_trans hsum (by
    unfold linkAuxiliaryCutoff
    simpa [Nat.mul_comm] using hscaled)

/-- A nonzero lower channel amplitude forces its endpoint below the exact
lower-word spin sum. -/
theorem fusionChannelAmplitude_nonzero_implies_le_sum
    {cutoff channel : Nat} {spins : List Nat}
    (hchannel : channel ≤ cutoff)
    (hspins : SpinsBounded cutoff spins)
    (hnonzero : fusionChannelAmplitude cutoff spins channel ≠ 0) :
    channel ≤ natListSum spins := by
  by_cases hle : channel ≤ natListSum spins
  · exact hle
  · have hlarge : natListSum spins < channel := by omega
    exact False.elim (hnonzero
      (fusionChannelAmplitude_eq_zero_of_sum_lt
        hchannel hspins hlarge))

private theorem natListSum_reverseLocal : ∀ spins : List Nat,
    natListSum spins.reverse = natListSum spins
  | [] => rfl
  | spin :: rest => by
      rw [List.reverse_cons, natListSum_append,
        natListSum_reverseLocal rest]
      simp only [natListSum]
      omega

/-! ## 3. Permutation and symmetry inside the nonbinding budget -/

theorem fusionWalkMultiplicity_perm_of_start_sum_le
    {cutoff start finish : Nat} {left right : List Nat}
    (hperm : left.Perm right)
    (hstart : start ≤ cutoff) (hfinish : finish ≤ cutoff)
    (hleft : SpinsBounded cutoff left)
    (hbudget : start + natListSum left ≤ cutoff) :
    fusionWalkMultiplicity cutoff start finish left =
      fusionWalkMultiplicity cutoff start finish right := by
  have hright : SpinsBounded cutoff right :=
    spinsBounded_of_perm hperm hleft
  rw [← fusionPathMultiplicity_cons_append_eq_walk
      left start finish hstart hfinish hleft,
    ← fusionPathMultiplicity_cons_append_eq_walk
      right start finish hstart hfinish hright]
  have hprefix : natListSum [start] + natListSum left ≤ cutoff := by
    simpa [natListSum] using hbudget
  simpa only [List.singleton_append] using
    fusionPathMultiplicity_perm_before_tail hperm
      [start] [finish] hprefix

/-- Reversal plus safe permutation makes the fixed-word transition symmetric
whenever both endpoints and the whole word fit from either side. -/
theorem fusionWalkMultiplicity_symmetric_of_endpoint_budgets
    {cutoff start finish : Nat} (spins : List Nat)
    (hstart : start ≤ cutoff) (hfinish : finish ≤ cutoff)
    (hspins : SpinsBounded cutoff spins)
    (_hstartBudget : start + natListSum spins ≤ cutoff)
    (hfinishBudget : finish + natListSum spins ≤ cutoff) :
    fusionWalkMultiplicity cutoff start finish spins =
      fusionWalkMultiplicity cutoff finish start spins := by
  refine (fusionWalkMultiplicity_reverse spins hstart hfinish).trans ?_
  exact fusionWalkMultiplicity_perm_of_start_sum_le
    (List.reverse_perm spins) hfinish hstart
    (fun spin hspin => hspins spin (List.mem_reverse.mp hspin))
    (by rw [natListSum_reverseLocal]; exact hfinishBudget)

/-- Uniform physical support: every lower endpoint above `3*K` has exactly
zero amplitude, even though the compatible-trajectory enumerator is retained
through `6*K`. -/
theorem adjacentEvenLowerLinkAmplitude_eq_zero_above_three_mul
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks radius)
    {channel : Nat} (hchannel : channel ≤ linkAuxiliaryCutoff K)
    (hlarge : 3 * K < channel) :
    adjacentEvenLowerLinkAmplitude K radius physical link channel = 0 := by
  unfold adjacentEvenLowerLinkAmplitude
  apply congrArg Q'.ofNat
  apply fusionChannelAmplitude_eq_zero_of_sum_lt hchannel
  · have hfull :=
      adjacentEvenPartitionedIncidentSpins_bounded hphysical link
    intro spin hspin
    exact Nat.le_trans
      (hfull spin (by
        unfold adjacentEvenPartitionedIncidentSpins
        exact List.mem_append_left _
          (List.mem_append_left _ hspin)))
      (externalCutoff_le_linkAuxiliaryCutoff K)
  · exact Nat.lt_of_le_of_lt
      (adjacentEvenFixedLink_lowerSpinSum_le_three_mul
        hphysical hlink) hlarge

#print axioms fusionWalkMultiplicity_eq_zero_of_finish_gt
#print axioms fusionChannelAmplitude_eq_zero_of_sum_lt
#print axioms adjacentEvenFixedLink_lowerSpins_length_le_three
#print axioms adjacentEvenFixedLink_lowerSpinSum_le_three_mul
#print axioms adjacentEvenFixedLink_lower_add_fixed_length_le_six
#print axioms adjacentEvenFixedLink_lower_add_fixed_sum_le_auxiliary
#print axioms fusionChannelAmplitude_nonzero_implies_le_sum
#print axioms fusionWalkMultiplicity_perm_of_start_sum_le
#print axioms fusionWalkMultiplicity_symmetric_of_endpoint_budgets
#print axioms adjacentEvenLowerLinkAmplitude_eq_zero_above_three_mul

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSupportGeneric
