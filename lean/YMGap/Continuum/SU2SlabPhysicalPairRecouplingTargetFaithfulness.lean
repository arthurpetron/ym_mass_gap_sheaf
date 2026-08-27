/-
# Faithfulness of physical-pair target realization

Equal-rank recoding is useful for column capacity only when distinct target
columns remain distinct after reconstruction as accepted production
witnesses.  This module proves that fact at every possible 4D link valence.

The proof has two finite ingredients.  First, the written complete source
lists are duplicate free.  Second, writing a complete left carrier into the
canonical auxiliary coordinates and extracting the production carrier again
returns the original carrier.  Equal reconstructed witnesses therefore give
equal equal-rank source codes, and positional reindexing then gives equal
target columns.

Constructive contract: explicit finite lists and canonical SU(2) channel
coordinates only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2CompleteCarrierDecidableEquality
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Duplicate-free complete source carriers -/

private theorem nodup_map_of_injective {A B : Type} (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := heq ▸ htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

private theorem valenceFiveLeftFiber_nodup
    {a b c d e : Nat} (index : ValenceFiveTransientIndex a b c d e) :
    (valenceFiveLeftFiber index).Nodup := by
  unfold valenceFiveLeftFiber
  apply nodup_map_of_injective
  · intro left right heq
    apply fixedLeftChannel_eq_of_k_eq
    exact congrArg (fun carrier => carrier.firstLeft.k) heq
  · exact fixedLeftChannels_nodup a b c index.val

theorem valenceFiveLeftCarriers_nodup (a b c d e : Nat) :
    (valenceFiveLeftCarriers a b c d e).Nodup := by
  unfold valenceFiveLeftCarriers
  apply nodup_flatMap_of_disjoint_blocks
  · exact attach_nodup_of_nodup _
      (valenceFiveTransientOutputs_nodup a b c d e)
  · intro index _
    exact valenceFiveLeftFiber_nodup index
  · intro left _ right _ hne value hleft hrightMem
    obtain ⟨leftChannel, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightChannel, _, hrightEq⟩ := List.mem_map.mp hrightMem
    have hindex : left = right := by
      apply Subtype.ext
      exact congrArg ValenceFiveLeftCarrier.y
        (hleftEq.trans hrightEq.symm)
    exact hne hindex

theorem valenceSixLeftCarriers_nodup (a b c d e f : Nat) :
    (valenceSixBistochasticKernel a b c d e f).sources.Nodup := by
  change (valenceSixPrefixBistochasticKernel a b c d e f).sources.Nodup
  unfold valenceSixPrefixBistochasticKernel
  apply indexedSources_nodup
  · exact valenceSixPrefixOutputs_nodup a b c d e f
  · intro z
    exact valenceFiveLeftCarriers_nodup a b c d z

/-! ## 2. Canonical auxiliary writing is a left inverse -/

private theorem fixedLeftCGChannel_k_eq_of_intermediate_eq
    {a b c leftOutput rightOutput : Nat}
    (left : FixedLeftCGChannel a b c leftOutput)
    (right : FixedLeftCGChannel a b c rightOutput)
    (hintermediate : left.intermediate = right.intermediate) :
    left.k = right.k := by
  calc
    left.k = couplingOrder a b left.intermediate :=
      (fixedLeft_inner_couplingOrder left).symm
    _ = couplingOrder a b right.intermediate :=
      congrArg (couplingOrder a b) hintermediate
    _ = right.k := fixedLeft_inner_couplingOrder right

theorem valenceFourLeftAuxiliary_roundtrip
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (bounded : SlabFaceLabellingBounded K extent physical)
    (degree_eq : (slabIncidentPlaqIds extent link).length = 4)
    (source : FixedLeftCGChannel
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)) :
    fixedLeftChannelOfSlabValenceFour K extent physical link
        (valenceFourLeftAuxiliary source) degree_eq
        (valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
          bounded degree_eq source) = source := by
  apply fixedLeftChannel_eq_of_k_eq
  apply fixedLeftCGChannel_k_eq_of_intermediate_eq
  calc
    (fixedLeftChannelOfSlabValenceFour K extent physical link
        (valenceFourLeftAuxiliary source) degree_eq
        (valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
          bounded degree_eq source)).intermediate =
      valenceFourLeftAuxiliary source 5 :=
        fixedLeftChannelOfSlabValenceFour_intermediate
          K extent physical link (valenceFourLeftAuxiliary source)
          degree_eq
          (valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
            bounded degree_eq source)
    _ = source.intermediate := by
      simp [valenceFourLeftAuxiliary]

theorem valenceFiveLeftAuxiliary_roundtrip
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (bounded : SlabFaceLabellingBounded K extent physical)
    (degree_eq : (slabIncidentPlaqIds extent link).length = 5)
    (source : ValenceFiveLeftCarrier
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)
      ((slabLinkExternalSpins extent physical link) 4)) :
    valenceFiveLeftCarrierOfChain
        (fixedLeftCGValenceFiveOfSlab K extent physical link
          (valenceFiveLeftAuxiliary source) degree_eq
          (valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
            bounded degree_eq source)) = source := by
  let chain := fixedLeftCGValenceFiveOfSlab K extent physical link
    (valenceFiveLeftAuxiliary source) degree_eq
    (valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
      bounded degree_eq source)
  apply valenceFiveLeftCarrierCode_injective
  change (chain.y, chain.prefixChannel.k) =
    (source.y, source.firstLeft.k)
  apply Prod.ext
  · exact (fixedLeftCGValenceFiveOfSlab_labels K extent physical link
      (valenceFiveLeftAuxiliary source) degree_eq
      (valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
        bounded degree_eq source)).2.trans (by
          simp [valenceFiveLeftAuxiliary])
  · apply fixedLeftCGChannel_k_eq_of_intermediate_eq
    exact chain.prefixChannel_intermediate.trans
      ((fixedLeftCGValenceFiveOfSlab_labels K extent physical link
        (valenceFiveLeftAuxiliary source) degree_eq
        (valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
          bounded degree_eq source)).1.trans (by
            simp [valenceFiveLeftAuxiliary]))

theorem valenceSixLeftAuxiliary_roundtrip
    {K extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (bounded : SlabFaceLabellingBounded K extent physical)
    (degree_eq : (slabIncidentPlaqIds extent link).length = 6)
    (source : ValenceSixLeftCarrier
      ((slabLinkExternalSpins extent physical link) 0)
      ((slabLinkExternalSpins extent physical link) 1)
      ((slabLinkExternalSpins extent physical link) 2)
      ((slabLinkExternalSpins extent physical link) 3)
      ((slabLinkExternalSpins extent physical link) 4)
      ((slabLinkExternalSpins extent physical link) 5)) :
    valenceSixLeftCarrierOfChain
        (fixedLeftCGValenceSixOfSlab K extent physical link
          (valenceSixLeftAuxiliary source) degree_eq
          (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
            bounded degree_eq source)) = source := by
  let chain := fixedLeftCGValenceSixOfSlab K extent physical link
    (valenceSixLeftAuxiliary source) degree_eq
    (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
      bounded degree_eq source)
  apply valenceSixLeftCarrierCode_injective
  change ((chain.z, chain.y), chain.prefixChannel.k) =
    ((source.index.val, source.value.y), source.value.firstLeft.k)
  apply Prod.ext
  · apply Prod.ext
    · exact (fixedLeftCGValenceSixOfSlab_labels K extent physical link
        (valenceSixLeftAuxiliary source) degree_eq
        (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
          bounded degree_eq source)).2.2.trans (by
            simp [valenceSixLeftAuxiliary])
    · exact (fixedLeftCGValenceSixOfSlab_labels K extent physical link
        (valenceSixLeftAuxiliary source) degree_eq
        (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
          bounded degree_eq source)).2.1.trans (by
            simp [valenceSixLeftAuxiliary])
  · apply fixedLeftCGChannel_k_eq_of_intermediate_eq
    exact chain.prefixChannel_intermediate.trans
      ((fixedLeftCGValenceSixOfSlab_labels K extent physical link
        (valenceSixLeftAuxiliary source) degree_eq
        (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
          bounded degree_eq source)).1.trans (by
            simp [valenceSixLeftAuxiliary]))

def SlabPhysicalPairProductionWitnessPair.toWitnessData
    {K extent degree : Nat}
    {D : SlabPhysicalPairRecouplingData extent degree}
    (pair : SlabPhysicalPairProductionWitnessPair K D) :
    SlabPhysicalPairRecouplingWitnessData K D where
  leftAuxiliary := pair.leftAuxiliary
  rightAuxiliary := pair.rightAuxiliary
  left_mem := pair.left_mem
  right_mem := pair.right_mem

/-- Extracting the production source from the canonical witnesses written by
one complete source carrier returns that carrier exactly. -/
theorem slabPhysicalPairProductionWitnessPairOfSource_roundtrip
    {K extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      (leftBounded : SlabFaceLabellingBounded K extent D.leftPhysical) →
      (rightBounded : SlabFaceLabellingBounded K extent D.rightPhysical) →
      (anchor : SlabPhysicalPairRecouplingWitnessData K D) →
      (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source) →
      slabPhysicalPairRecouplingProductionSource degree D
          (SlabPhysicalPairProductionWitnessPair.toWitnessData
            (slabPhysicalPairProductionWitnessPairOfSource degree D anchor
              leftBounded rightBounded source)) = source
  | 0, _, _, _, _, source => by cases source; rfl
  | 1, _, _, _, _, source => by cases source; rfl
  | 2, _, _, _, _, source => by cases source; rfl
  | 3, _, _, _, _, source => by cases source; rfl
  | 4, D, leftBounded, rightBounded, _, source => by
      change
        (fixedLeftChannelOfSlabValenceFour K extent D.leftPhysical D.link
            (valenceFourLeftAuxiliary source.1) D.degree_eq
            (valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
              leftBounded D.degree_eq source.1),
          fixedLeftChannelOfSlabValenceFour K extent D.rightPhysical D.link
            (valenceFourLeftAuxiliary source.2) D.degree_eq
            (valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
              rightBounded D.degree_eq source.2)) = source
      apply Prod.ext
      · exact valenceFourLeftAuxiliary_roundtrip
          leftBounded D.degree_eq source.1
      · exact valenceFourLeftAuxiliary_roundtrip
          rightBounded D.degree_eq source.2
  | 5, D, leftBounded, rightBounded, _, source => by
      change
        (valenceFiveLeftCarrierOfChain
            (fixedLeftCGValenceFiveOfSlab K extent D.leftPhysical D.link
              (valenceFiveLeftAuxiliary source.1) D.degree_eq
              (valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
                leftBounded D.degree_eq source.1)),
          valenceFiveLeftCarrierOfChain
            (fixedLeftCGValenceFiveOfSlab K extent D.rightPhysical D.link
              (valenceFiveLeftAuxiliary source.2) D.degree_eq
              (valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
                rightBounded D.degree_eq source.2))) = source
      apply Prod.ext
      · exact valenceFiveLeftAuxiliary_roundtrip
          leftBounded D.degree_eq source.1
      · exact valenceFiveLeftAuxiliary_roundtrip
          rightBounded D.degree_eq source.2
  | 6, D, leftBounded, rightBounded, _, source => by
      change
        (valenceSixLeftCarrierOfChain
            (fixedLeftCGValenceSixOfSlab K extent D.leftPhysical D.link
              (valenceSixLeftAuxiliary source.1) D.degree_eq
              (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
                leftBounded D.degree_eq source.1)),
          valenceSixLeftCarrierOfChain
            (fixedLeftCGValenceSixOfSlab K extent D.rightPhysical D.link
              (valenceSixLeftAuxiliary source.2) D.degree_eq
              (valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
                rightBounded D.degree_eq source.2))) = source
      apply Prod.ext
      · exact valenceSixLeftAuxiliary_roundtrip
          leftBounded D.degree_eq source.1
      · exact valenceSixLeftAuxiliary_roundtrip
          rightBounded D.degree_eq source.2
  | degree + 7, D, _, _, _, _ => False.elim (by
      have hdegree := D.degree_le_six
      have hseven_le_six : 7 ≤ 6 :=
        Nat.le_trans (Nat.le_add_left 7 degree) hdegree
      exact Nat.not_succ_le_self 6 hseven_le_six)

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.valenceFiveLeftCarriers_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.valenceSixLeftCarriers_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.valenceFourLeftAuxiliary_roundtrip
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.valenceFiveLeftAuxiliary_roundtrip
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.valenceSixLeftAuxiliary_roundtrip
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness.slabPhysicalPairProductionWitnessPairOfSource_roundtrip
