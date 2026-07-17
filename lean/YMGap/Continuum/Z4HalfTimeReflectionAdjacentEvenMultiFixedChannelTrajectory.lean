/-
# Multi-fixed channel trajectories at the adjacent-even interface

A fixed spatial link on the integer reflection plane can meet several fixed
spatial faces, in addition to one lower and one reflected-upper temporal word.
The fixed word cannot be treated as several transitions with a single unchanged
pair of endpoints: intermediate fusion channels are essential.  This file
banks that obstruction, expands an arbitrary fixed word through its compatible
open-channel trajectory, and specializes the identity to every literal link of
the production adjacent-even slab.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenMultiFixedChannelTrajectory

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact normalization fence: intermediate channels are necessary -/

def naiveUnchangedEndpointTwoFixedTransition : Nat :=
  boolMultiplicity (fusionOK 0 1 0) *
    boolMultiplicity (fusionOK 0 1 0)

theorem twoFixed_actualTransition_eq_one :
    fusionWalkMultiplicity 2 0 0 [1, 1] = 1 := by
  decide

theorem twoFixed_naiveUnchangedEndpointTransition_eq_zero :
    naiveUnchangedEndpointTwoFixedTransition = 0 := by
  decide

/-- Two fundamental fixed faces return vacuum to vacuum through the unique
intermediate channel `1`; forcing one unchanged endpoint pair loses that path. -/
theorem twoFixed_requires_intermediate_channel :
    fusionWalkMultiplicity 2 0 0 [1, 1] ≠
      naiveUnchangedEndpointTwoFixedTransition := by
  rw [twoFixed_actualTransition_eq_one,
    twoFixed_naiveUnchangedEndpointTransition_eq_zero]
  decide

/-! ## 2. Arbitrary fixed-word three-stage factorization -/

private theorem natListSumMapMulLeftLocal {A : Type}
    (factor : Nat) (value : A → Nat) : ∀ xs : List A,
    factor * natListSum (xs.map value) =
      natListSum (xs.map fun item => factor * value item)
  | [] => by simp [natListSum]
  | head :: tail => by
      simp only [List.map_cons, natListSum]
      rw [Nat.mul_add, natListSumMapMulLeftLocal factor value tail]

/-- A vacuum-ending word with a lower half, an arbitrary fixed-interface word,
and a reflected upper half is a double finite sum over its two endpoint
channels.  `fusionWalkMultiplicity` on the fixed word is the exact compatible
intermediate-channel trajectory count. -/
theorem fusionPathMultiplicity_multiFixed_channel_factorization
    {cutoff : Nat} {left fixed right : List Nat}
    (hleft : SpinsBounded cutoff left)
    (hfixed : SpinsBounded cutoff fixed)
    (hright : SpinsBounded cutoff right) :
    fusionPathMultiplicity cutoff
        (left ++ fixed ++ right.reverse) =
      natListSum ((List.range (cutoff + 1)).map fun source =>
        natListSum ((List.range (cutoff + 1)).map fun target =>
          (fusionChannelAmplitude cutoff left source *
            fusionWalkMultiplicity cutoff source target fixed) *
            fusionChannelAmplitude cutoff right target)) := by
  have hbounded :
      SpinsBounded cutoff (left ++ fixed ++ right.reverse) := by
    intro spin hspin
    rcases List.mem_append.mp hspin with hleftFixed | hrightReverse
    · rcases List.mem_append.mp hleftFixed with hsource | hmiddle
      · exact hleft spin hsource
      · exact hfixed spin hmiddle
    · exact hright spin (List.mem_reverse.mp hrightReverse)
  calc
    fusionPathMultiplicity cutoff
        (left ++ fixed ++ right.reverse) =
        fusionWalkMultiplicity cutoff 0 0
          (left ++ (fixed ++ right.reverse)) := by
      rw [fusionPathMultiplicity_eq_walk hbounded]
      simp only [List.append_assoc]
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          fusionWalkMultiplicity cutoff 0 source left *
            fusionWalkMultiplicity cutoff source 0
              (fixed ++ right.reverse)) :=
      fusionWalkMultiplicity_append left (fixed ++ right.reverse) 0
        (Nat.zero_le cutoff)
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          fusionWalkMultiplicity cutoff 0 source left *
            natListSum ((List.range (cutoff + 1)).map fun target =>
              fusionWalkMultiplicity cutoff source target fixed *
                fusionWalkMultiplicity cutoff target 0
                  right.reverse)) := by
      apply natListSum_map_congr
      intro source hsource
      apply congrArg
        (fun value =>
          fusionWalkMultiplicity cutoff 0 source left * value)
      exact fusionWalkMultiplicity_append fixed right.reverse 0 (by
        have hlt := List.mem_range.mp hsource
        omega)
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          natListSum ((List.range (cutoff + 1)).map fun target =>
            (fusionWalkMultiplicity cutoff 0 source left *
              fusionWalkMultiplicity cutoff source target fixed) *
              fusionWalkMultiplicity cutoff target 0
                right.reverse)) := by
      apply natListSum_map_congr
      intro source _
      rw [natListSumMapMulLeftLocal]
      apply natListSum_map_congr
      intro target _
      simp only [Nat.mul_assoc]
    _ = natListSum ((List.range (cutoff + 1)).map fun source =>
          natListSum ((List.range (cutoff + 1)).map fun target =>
            (fusionChannelAmplitude cutoff left source *
              fusionWalkMultiplicity cutoff source target fixed) *
              fusionChannelAmplitude cutoff right target)) := by
      apply natListSum_map_congr
      intro source hsource
      have hsourceBound : source ≤ cutoff := by
        have hlt := List.mem_range.mp hsource
        omega
      rw [fusionChannelAmplitude_eq_walk hsourceBound hleft]
      apply natListSum_map_congr
      intro target htarget
      have htargetBound : target ≤ cutoff := by
        have hlt := List.mem_range.mp htarget
        omega
      rw [fusionChannelAmplitude_eq_walk htargetBound hright]
      rw [fusionWalkMultiplicity_reverse right.reverse
        htargetBound (Nat.zero_le cutoff)]
      simp only [List.reverse_reverse]

/-! ## 3. Exact rational form used by the slab weight -/

private theorem ofNat_natListSumMap_eqvLocal
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListSum (items.map value)) ≈
      listQSum (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      simp only [List.map_cons, natListSum, listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.ofNat_add_eqv (value head)
          (natListSum (tail.map value)))
        (Q'.add_eqv_congr_left _ _ _
          (ofNat_natListSumMap_eqvLocal value tail))

private theorem ofNat_threeMul_eqvLocal (a b c : Nat) :
    Q'.ofNat ((a * b) * c) ≈
      (Q'.ofNat a * Q'.ofNat b) * Q'.ofNat c := by
  exact Q'.eqv_trans _ _ _ (ofNat_mul_eqv (a * b) c)
    (Q'.mul_eqv_congr_right _ _ (Q'.ofNat c)
      (ofNat_mul_eqv a b))

private theorem ofNat_nestedChannelSum_eqvLocal
    (cutoff : Nat) (term : Nat → Nat → Nat) :
    Q'.ofNat
        (natListSum ((List.range (cutoff + 1)).map fun source =>
          natListSum ((List.range (cutoff + 1)).map fun target =>
            term source target))) ≈
      listQSum (fun source =>
        listQSum (fun target => Q'.ofNat (term source target))
          (List.range (cutoff + 1)))
        (List.range (cutoff + 1)) := by
  refine Q'.eqv_trans _ _ _
    (ofNat_natListSumMap_eqvLocal
      (fun source =>
        natListSum ((List.range (cutoff + 1)).map fun target =>
          term source target))
      (List.range (cutoff + 1))) ?_
  apply listQSum_congr
  intro source
  exact ofNat_natListSumMap_eqvLocal (term source)
    (List.range (cutoff + 1))

/-- Rationalized three-stage trajectory identity, ready to multiply by the
derived heat-kernel face coefficients. -/
theorem ofNat_fusionPathMultiplicity_multiFixed_eqv_channelTrajectory
    {cutoff : Nat} {left fixed right : List Nat}
    (hleft : SpinsBounded cutoff left)
    (hfixed : SpinsBounded cutoff fixed)
    (hright : SpinsBounded cutoff right) :
    Q'.ofNat (fusionPathMultiplicity cutoff
        (left ++ fixed ++ right.reverse)) ≈
      listQSum (fun source =>
        listQSum (fun target =>
          (Q'.ofNat (fusionChannelAmplitude cutoff left source) *
            Q'.ofNat (fusionWalkMultiplicity
              cutoff source target fixed)) *
            Q'.ofNat (fusionChannelAmplitude cutoff right target))
          (List.range (cutoff + 1)))
        (List.range (cutoff + 1)) := by
  rw [fusionPathMultiplicity_multiFixed_channel_factorization
    hleft hfixed hright]
  refine Q'.eqv_trans _ _ _
    (ofNat_nestedChannelSum_eqvLocal cutoff
      (fun source target =>
        (fusionChannelAmplitude cutoff left source *
          fusionWalkMultiplicity cutoff source target fixed) *
          fusionChannelAmplitude cutoff right target)) ?_
  apply listQSum_congr
  intro source
  apply listQSum_congr
  intro target
  exact ofNat_threeMul_eqvLocal
    (fusionChannelAmplitude cutoff left source)
    (fusionWalkMultiplicity cutoff source target fixed)
    (fusionChannelAmplitude cutoff right target)

/-! ## 4. Literal production-link specialization -/

def adjacentEvenThreeStageLinkChannelKernel
    (K radius : Nat) (physical : Nat → Nat)
    (link : Z4Link) : Q' :=
  let cutoff := linkAuxiliaryCutoff K
  let lower := adjacentEvenIncidentLowerSpins radius physical link
  let fixed := adjacentEvenIncidentFixedSpins radius physical link
  let reflectedUpper :=
    (adjacentEvenIncidentUpperSpins radius physical link).reverse
  listQSum (fun source =>
    listQSum (fun target =>
      (Q'.ofNat (fusionChannelAmplitude cutoff lower source) *
        Q'.ofNat (fusionWalkMultiplicity
          cutoff source target fixed)) *
        Q'.ofNat (fusionChannelAmplitude
          cutoff reflectedUpper target))
      (List.range (cutoff + 1)))
    (List.range (cutoff + 1))

/-- Every literal production link multiplicity equals its lower-amplitude,
multi-fixed-trajectory, reflected-upper-amplitude contraction. -/
theorem slabExplicitLinkMultiplicity_eqv_threeStageChannelKernel
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    Q'.ofNat (slabExplicitLinkMultiplicity K
        (adjacentEvenExtent radius) physical link) ≈
      adjacentEvenThreeStageLinkChannelKernel
        K radius physical link := by
  let cutoff := linkAuxiliaryCutoff K
  let lower := adjacentEvenIncidentLowerSpins radius physical link
  let fixed := adjacentEvenIncidentFixedSpins radius physical link
  let upper := adjacentEvenIncidentUpperSpins radius physical link
  have hfullK := adjacentEvenPartitionedIncidentSpins_bounded
    hphysical link
  have hfull : SpinsBounded cutoff
      (adjacentEvenPartitionedIncidentSpins radius physical link) := by
    intro spin hspin
    exact Nat.le_trans (hfullK spin hspin)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hword :
      adjacentEvenPartitionedIncidentSpins radius physical link =
        lower ++ (fixed ++ upper) := by
    unfold adjacentEvenPartitionedIncidentSpins lower fixed upper
    exact List.append_assoc _ _ _
  rw [hword] at hfull
  have hsplit := spinsBounded_append hfull
  have hrest := spinsBounded_append hsplit.2
  have hproduction := slabExplicitLinkMultiplicity_eq_partitionedFusionPath
    hphysical link
  rw [hproduction]
  unfold adjacentEvenThreeStageLinkChannelKernel
  change Q'.ofNat (fusionPathMultiplicity cutoff
      (lower ++ fixed ++ upper)) ≈ _
  have htrajectory :=
    ofNat_fusionPathMultiplicity_multiFixed_eqv_channelTrajectory
      hsplit.1 hrest.1
      (right := upper.reverse) (by
        intro spin hspin
        exact hrest.2 spin (List.mem_reverse.mp hspin))
  simpa only [List.reverse_reverse, List.append_assoc] using htrajectory

/-! ## 5. The complete fixed-link product -/

private theorem ofNat_natListProduct_eqv_listQProductLocal
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListProduct value items) ≈
      listQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, listQProduct]
      exact Q'.eqv_trans _ _ _
        (ofNat_mul_eqv (value head)
          (natListProduct value tail))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_listQProductLocal value tail))

def adjacentEvenThreeStageFixedLinkProduct
    (K radius : Nat) (physical : Nat → Nat) : Q' :=
  listQProduct
    (adjacentEvenThreeStageLinkChannelKernel K radius physical)
    (adjacentEvenFixedLinks radius)

/-- The full literal fixed-link multiplicity product is exactly the product of
the linkwise lower/fixed/reflected-upper trajectory contractions. -/
theorem slabFixedLinkMultiplicityProduct_eqv_threeStageProduct
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical) :
    Q'.ofNat (slabLinkMultiplicityProductOn K
        (adjacentEvenExtent radius) physical
        (adjacentEvenFixedLinks radius)) ≈
      adjacentEvenThreeStageFixedLinkProduct
        K radius physical := by
  unfold slabLinkMultiplicityProductOn
    adjacentEvenThreeStageFixedLinkProduct
  refine Q'.eqv_trans _ _ _
    (ofNat_natListProduct_eqv_listQProductLocal
      (slabExplicitLinkMultiplicity K
        (adjacentEvenExtent radius) physical)
      (adjacentEvenFixedLinks radius)) ?_
  apply listQProduct_congr_eqv
  intro link _
  exact slabExplicitLinkMultiplicity_eqv_threeStageChannelKernel
    hphysical link

#print axioms twoFixed_requires_intermediate_channel
#print axioms fusionPathMultiplicity_multiFixed_channel_factorization
#print axioms ofNat_fusionPathMultiplicity_multiFixed_eqv_channelTrajectory
#print axioms slabExplicitLinkMultiplicity_eqv_threeStageChannelKernel
#print axioms slabFixedLinkMultiplicityProduct_eqv_threeStageProduct

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenMultiFixedChannelTrajectory
