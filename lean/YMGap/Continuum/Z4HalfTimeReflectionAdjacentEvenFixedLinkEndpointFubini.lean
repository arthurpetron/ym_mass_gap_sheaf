/-
# Global endpoint-channel Fubini for adjacent-even fixed links

The linkwise three-stage identity leaves two bounded endpoint channels on
every fixed spatial link.  This file enumerates those channels globally,
proves an arbitrary-key constructive product Fubini theorem, and identifies
the complete literal fixed-link multiplicity product with one global sum over
source and target link-channel assignments.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenMultiFixedChannelTrajectory

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenMultiFixedChannelTrajectory
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qMulCongrLocal {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Bounded labellings on an arbitrary finite key list -/

def zeroLabellingOn {A : Type} : A → Nat := fun _ => 0

def setLabelOn {A : Type} [DecidableEq A]
    (label : A → Nat) (key : A) (value : Nat) : A → Nat :=
  fun item => if item = key then value else label item

def boundedLabellingsOn {A : Type} [DecidableEq A]
    (cutoff : Nat) : List A → List (A → Nat)
  | [] => [zeroLabellingOn]
  | key :: rest =>
      (List.range (cutoff + 1)).flatMap (fun value =>
        (boundedLabellingsOn cutoff rest).map
          (fun label => setLabelOn label key value))

theorem boundedLabellingsOn_sound
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (label : A → Nat),
      label ∈ boundedLabellingsOn cutoff keys →
      ∀ key : A, key ∈ keys → label key ≤ cutoff
  | [], _, _, key, hkey => False.elim (List.not_mem_nil hkey)
  | head :: rest, label, hlabel, key, hkey => by
      obtain ⟨selected, hselected, hselectedBlock⟩ :=
        List.mem_flatMap.mp hlabel
      obtain ⟨tailLabel, htailLabel, heq⟩ :=
        List.mem_map.mp hselectedBlock
      rw [← heq]
      by_cases hsame : key = head
      · subst key
        rw [show setLabelOn tailLabel head selected head = selected by
          simp [setLabelOn]]
        have hlt := List.mem_range.mp hselected
        omega
      · rw [show setLabelOn tailLabel head selected key =
            tailLabel key by simp [setLabelOn, hsame]]
        have hrest : key ∈ rest := by
          rcases List.mem_cons.mp hkey with heqKey | htail
          · exact False.elim (hsame heqKey)
          · exact htail
        exact boundedLabellingsOn_sound cutoff rest tailLabel
          htailLabel key hrest

theorem listQSum_boundedLabellingsOn_cons
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (key : A) (rest : List A)
    (value : (A → Nat) → Q') :
    listQSum value
        (boundedLabellingsOn cutoff (key :: rest)) ≈
      fsum (fun channel =>
        listQSum (fun label =>
          value (setLabelOn label key channel))
          (boundedLabellingsOn cutoff rest)) (cutoff + 1) := by
  change listQSum value
      ((List.range (cutoff + 1)).flatMap (fun channel =>
        (boundedLabellingsOn cutoff rest).map
          (fun label => setLabelOn label key channel))) ≈ _
  refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_congr (fun channel => Q'.eqv_of_eq
      (listQSum_map value
        (fun label => setLabelOn label key channel)
        (boundedLabellingsOn cutoff rest)))
      (List.range (cutoff + 1))) ?_
  exact listQSum_range_eq_fsum
    (fun channel =>
      listQSum (fun label =>
        value (setLabelOn label key channel))
        (boundedLabellingsOn cutoff rest)) (cutoff + 1)

private theorem listQSum_const_mul_local
    {A : Type} (constant : Q') (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => constant * value item) items ≈
        constant * listQSum value items
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | head :: tail => by
      simp only [listQSum]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (listQSum_const_mul_local constant value tail)) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv constant (value head)
          (listQSum value tail))

/-- Exact finite Fubini for a product carrying one bounded label on each key.
`Nodup` is the condition preventing overwrite from silently identifying two
nominally different summation coordinates. -/
theorem boundedLabellingsOn_product_fubini
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (factor : A → Nat → Q') :
    ∀ keys : List A, keys.Nodup →
      listQSum (fun label =>
        listQProduct (fun key => factor key (label key)) keys)
        (boundedLabellingsOn cutoff keys) ≈
      listQProduct
        (fun key => fsum (factor key) (cutoff + 1)) keys
  | [], _ => by
      change (1 : Q') + 0 ≈ 1
      exact q_add_zero_eqv 1
  | key :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      let fullValue : (A → Nat) → Q' := fun label =>
        listQProduct (fun item => factor item (label item))
          (key :: rest)
      let tailValue : (A → Nat) → Q' := fun label =>
        listQProduct (fun item => factor item (label item)) rest
      have hexpand := listQSum_boundedLabellingsOn_cons
        cutoff key rest fullValue
      have hinner : ∀ channel,
          listQSum (fun label =>
              fullValue (setLabelOn label key channel))
            (boundedLabellingsOn cutoff rest) ≈
            factor key channel *
              listQSum tailValue
                (boundedLabellingsOn cutoff rest) := by
        intro channel
        have hpoint : ∀ label,
            fullValue (setLabelOn label key channel) ≈
              factor key channel * tailValue label := by
          intro label
          unfold fullValue tailValue
          simp only [listQProduct]
          apply qMulCongrLocal
          · simp [setLabelOn]
            exact Q'.eqv_refl _
          · apply listQProduct_congr_eqv
            intro item hitem
            have hne : item ≠ key := by
              intro heq
              exact hparts.1 (heq ▸ hitem)
            simp [setLabelOn, hne]
            exact Q'.eqv_refl _
        refine Q'.eqv_trans _ _ _
          (listQSum_congr hpoint
            (boundedLabellingsOn cutoff rest)) ?_
        exact listQSum_const_mul_local
          (factor key channel) tailValue
          (boundedLabellingsOn cutoff rest)
      refine Q'.eqv_trans _ _ _ hexpand ?_
      refine Q'.eqv_trans _ _ _
        (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          _ _ hinner (cutoff + 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
            (factor key)
            (listQSum tailValue
              (boundedLabellingsOn cutoff rest))
            (cutoff + 1))) ?_
      simp only [listQProduct]
      exact Q'.mul_eqv_congr_left
        (fsum (factor key) (cutoff + 1)) _ _
        (boundedLabellingsOn_product_fubini
          cutoff factor rest hparts.2)

/-- Two independent bounded endpoint labellings turn a product of local
two-channel sums into one global source/target assignment sum. -/
theorem boundedPairLabellingsOn_product_fubini
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (factor : A → Nat → Nat → Q')
    (keys : List A) (hnodup : keys.Nodup) :
    listQSum (fun source =>
      listQSum (fun target =>
        listQProduct (fun key =>
          factor key (source key) (target key)) keys)
        (boundedLabellingsOn cutoff keys))
      (boundedLabellingsOn cutoff keys) ≈
    listQProduct (fun key =>
      fsum (fun source =>
        fsum (factor key source) (cutoff + 1))
        (cutoff + 1)) keys := by
  have hinner : ∀ source : A → Nat,
      listQSum (fun target =>
          listQProduct (fun key =>
            factor key (source key) (target key)) keys)
        (boundedLabellingsOn cutoff keys) ≈
      listQProduct (fun key =>
        fsum (factor key (source key)) (cutoff + 1)) keys := by
    intro source
    exact boundedLabellingsOn_product_fubini cutoff
      (fun key target => factor key (source key) target)
      keys hnodup
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hinner
      (boundedLabellingsOn cutoff keys)) ?_
  exact boundedLabellingsOn_product_fubini cutoff
    (fun key source =>
      fsum (factor key source) (cutoff + 1))
    keys hnodup

/-! ## 2. Concrete fixed-link endpoint sum -/

theorem adjacentEvenFixedLinks_nodup (radius : Nat) :
    (adjacentEvenFixedLinks radius).Nodup := by
  have hfull := boundaryCompleteSlabLinks_nodup
    (adjacentEvenExtent radius)
  have hall :
      ((adjacentEvenSlabLinkParts radius).1 ++
        (adjacentEvenSlabLinkParts radius).2.1 ++
        (adjacentEvenSlabLinkParts radius).2.2).Nodup :=
    (adjacentEvenSlabLinkParts_perm radius).symm.nodup hfull
  have houter := List.nodup_append.mp hall
  have hlowerFixed := List.nodup_append.mp houter.1
  exact hlowerFixed.2.1

def adjacentEvenFixedLinkEndpointFactor
    (K radius : Nat) (physical : Nat → Nat)
    (link : Z4Link) (source target : Nat) : Q' :=
  let cutoff := linkAuxiliaryCutoff K
  (Q'.ofNat (fusionChannelAmplitude cutoff
      (adjacentEvenIncidentLowerSpins radius physical link) source) *
    Q'.ofNat (fusionWalkMultiplicity cutoff source target
      (adjacentEvenIncidentFixedSpins radius physical link))) *
    Q'.ofNat (fusionChannelAmplitude cutoff
      (adjacentEvenIncidentUpperSpins radius physical link).reverse
      target)

def adjacentEvenGlobalFixedLinkEndpointTrajectorySum
    (K radius : Nat) (physical : Nat → Nat) : Q' :=
  let cutoff := linkAuxiliaryCutoff K
  let links := adjacentEvenFixedLinks radius
  listQSum (fun source =>
    listQSum (fun target =>
      listQProduct (fun link =>
        adjacentEvenFixedLinkEndpointFactor K radius physical
          link (source link) (target link)) links)
      (boundedLabellingsOn cutoff links))
    (boundedLabellingsOn cutoff links)

private theorem fixedLinkNestedFsum_eqv_threeStageKernel
    (K radius : Nat) (physical : Nat → Nat)
    (link : Z4Link) :
    fsum (fun source =>
        fsum (adjacentEvenFixedLinkEndpointFactor
          K radius physical link source)
          (linkAuxiliaryCutoff K + 1))
        (linkAuxiliaryCutoff K + 1) ≈
      adjacentEvenThreeStageLinkChannelKernel
        K radius physical link := by
  unfold adjacentEvenThreeStageLinkChannelKernel
    adjacentEvenFixedLinkEndpointFactor
  let cutoff := linkAuxiliaryCutoff K
  let term : Nat → Nat → Q' := fun source target =>
    (Q'.ofNat (fusionChannelAmplitude cutoff
        (adjacentEvenIncidentLowerSpins radius physical link) source) *
      Q'.ofNat (fusionWalkMultiplicity cutoff source target
        (adjacentEvenIncidentFixedSpins radius physical link))) *
      Q'.ofNat (fusionChannelAmplitude cutoff
        (adjacentEvenIncidentUpperSpins radius physical link).reverse
        target)
  have hinner : ∀ source,
      listQSum (term source) (List.range (cutoff + 1)) ≈
        fsum (term source) (cutoff + 1) :=
    fun source => listQSum_range_eq_fsum
      (term source) (cutoff + 1)
  have houter :
      listQSum (fun source =>
          listQSum (term source) (List.range (cutoff + 1)))
          (List.range (cutoff + 1)) ≈
        fsum (fun source =>
          fsum (term source) (cutoff + 1)) (cutoff + 1) := by
    refine Q'.eqv_trans _ _ _
      (listQSum_congr hinner (List.range (cutoff + 1))) ?_
    exact listQSum_range_eq_fsum
      (fun source => fsum (term source) (cutoff + 1))
      (cutoff + 1)
  exact Q'.eqv_symm houter

theorem adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_product
    (K radius : Nat) (physical : Nat → Nat) :
    adjacentEvenGlobalFixedLinkEndpointTrajectorySum
        K radius physical ≈
      adjacentEvenThreeStageFixedLinkProduct
        K radius physical := by
  unfold adjacentEvenGlobalFixedLinkEndpointTrajectorySum
    adjacentEvenThreeStageFixedLinkProduct
  refine Q'.eqv_trans _ _ _
    (boundedPairLabellingsOn_product_fubini
      (linkAuxiliaryCutoff K)
      (adjacentEvenFixedLinkEndpointFactor K radius physical)
      (adjacentEvenFixedLinks radius)
      (adjacentEvenFixedLinks_nodup radius)) ?_
  apply listQProduct_congr_eqv
  intro link _
  exact fixedLinkNestedFsum_eqv_threeStageKernel
    K radius physical link

/-- Final endpoint-Fubini bridge: the literal fixed-link product itself is one
global finite sum over bounded source and target link channels. -/
theorem slabFixedLinkMultiplicityProduct_eqv_globalEndpointTrajectorySum
    {K radius : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical) :
    Q'.ofNat (slabLinkMultiplicityProductOn K
        (adjacentEvenExtent radius) physical
        (adjacentEvenFixedLinks radius)) ≈
      adjacentEvenGlobalFixedLinkEndpointTrajectorySum
        K radius physical :=
  Q'.eqv_trans _ _ _
    (slabFixedLinkMultiplicityProduct_eqv_threeStageProduct hphysical)
    (Q'.eqv_symm
      (adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_product
        K radius physical))

#print axioms boundedLabellingsOn_product_fubini
#print axioms boundedLabellingsOn_sound
#print axioms boundedPairLabellingsOn_product_fubini
#print axioms adjacentEvenFixedLinks_nodup
#print axioms adjacentEvenGlobalFixedLinkEndpointTrajectorySum_eqv_product
#print axioms slabFixedLinkMultiplicityProduct_eqv_globalEndpointTrajectorySum

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
