/-
# Concrete adjacent-even fixed-face incidence and finite Fubini

This file connects the duplicate-free joint-face block to the actual
boundary-complete adjacent-even slab.  Fixed spatial face identifiers are
enumerated once; each is mapped to its four fixed spatial boundary links in
the production `edgesOf` order.  A generic exact finite-product Fubini lemma
then sums one bounded face labelling globally and produces the product of
the corresponding four-channel face blocks.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Every fixed face has exactly four fixed boundary links -/

def adjacentEvenFixedFaceIds (radius : Nat) : List Nat :=
  (adjacentEvenSlabFaceIdParts radius).2.1

def adjacentEvenFixedSlabLinks (radius : Nat) : List Z4Link :=
  (adjacentEvenSlabLinkParts radius).2.1

theorem mem_adjacentEvenFixedFaceIds
    {radius id : Nat} :
    id ∈ adjacentEvenFixedFaceIds radius ↔
      id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

theorem mem_adjacentEvenFixedSlabLinks
    {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenFixedSlabLinks radius ↔
      link ∈ boundaryCompleteSlabLinks
        (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

def adjacentEvenFixedFaceLinks
    (radius id : Nat) : List Z4Link :=
  edgesOf (slabPlaquetteAt (adjacentEvenExtent radius) id)

theorem adjacentEvenFixedFaceLinks_length
    (radius id : Nat) :
    (adjacentEvenFixedFaceLinks radius id).length = 4 := by
  unfold adjacentEvenFixedFaceLinks
  obtain ⟨vertex, plane⟩ :=
    slabPlaquetteAt (adjacentEvenExtent radius) id
  cases plane <;> rfl

private theorem fixedPlaquette_edge_side
    {radius : Nat} {plaquette : Z4Plaq}
    (hfixed : adjacentEvenPlaquetteSide radius plaquette = .fixed) :
    ∀ {link : Z4Link}, link ∈ edgesOf plaquette →
      adjacentEvenLinkSide radius link = .fixed := by
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  cases plane <;>
    simp only [adjacentEvenPlaquetteSide] at hfixed
  all_goals
    intro link hlink
  · have htime : time = adjacentEvenCenter radius := by
      unfold adjacentEvenSpatialSide at hfixed
      split at hfixed
      · contradiction
      · split at hfixed
        · assumption
        · contradiction
    subst time
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink
    rcases hlink with rfl | rfl | rfl | rfl <;>
      simp [adjacentEvenLinkSide, adjacentEvenSpatialSide,
        adjacentEvenCenter]
  · have htime : time = adjacentEvenCenter radius := by
      unfold adjacentEvenSpatialSide at hfixed
      split at hfixed
      · contradiction
      · split at hfixed
        · assumption
        · contradiction
    subst time
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink
    rcases hlink with rfl | rfl | rfl | rfl <;>
      simp [adjacentEvenLinkSide, adjacentEvenSpatialSide,
        adjacentEvenCenter]
  · unfold adjacentEvenTemporalSide at hfixed
    split at hfixed <;> contradiction
  · have htime : time = adjacentEvenCenter radius := by
      unfold adjacentEvenSpatialSide at hfixed
      split at hfixed
      · contradiction
      · split at hfixed
        · assumption
        · contradiction
    subst time
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink
    rcases hlink with rfl | rfl | rfl | rfl <;>
      simp [adjacentEvenLinkSide, adjacentEvenSpatialSide,
        adjacentEvenCenter]
  · unfold adjacentEvenTemporalSide at hfixed
    split at hfixed <;> contradiction
  · unfold adjacentEvenTemporalSide at hfixed
    split at hfixed <;> contradiction

theorem adjacentEvenFixedFaceLink_mem_fixedSlabLinks
    {radius id : Nat}
    (hid : id ∈ adjacentEvenFixedFaceIds radius)
    {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedFaceLinks radius id) :
    link ∈ adjacentEvenFixedSlabLinks radius := by
  have hparts := (mem_adjacentEvenFixedFaceIds).mp hid
  apply (mem_adjacentEvenFixedSlabLinks).mpr
  constructor
  · apply (mem_boundaryCompleteSlabLinks_iff _ _).mpr
    exact ⟨slabPlaquetteAt (adjacentEvenExtent radius) id,
      slabPlaquetteAt_mem hparts.1, hlink⟩
  · exact fixedPlaquette_edge_side hparts.2 hlink

theorem adjacentEvenFixedFaceId_mem_linkIncidence
    {radius id : Nat}
    (hid : id ∈ adjacentEvenFixedFaceIds radius)
    {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedFaceLinks radius id) :
    id ∈ slabIncidentPlaqIds
      (adjacentEvenExtent radius) link := by
  apply mem_slabIncidentPlaqIds.mpr
  exact ⟨slabPlaquetteAt (adjacentEvenExtent radius) id,
    slabPlaquetteAt_mem_enumerate
      (mem_adjacentEvenFixedFaceIds.mp hid).1, hlink⟩

def defaultZ4Link : Z4Link := (((0, 0, 0, 0), .x0) : Z4Link)

/-- Read the four boundary-link channels of one fixed spatial face in the
literal production `edgesOf` order. -/
def fixedFaceFourChannels
    (radius id : Nat) (channel : Z4Link → Nat) : FourChannels :=
  let links := adjacentEvenFixedFaceLinks radius id
  ⟨channel (links.getD 0 defaultZ4Link),
    channel (links.getD 1 defaultZ4Link),
    channel (links.getD 2 defaultZ4Link),
    channel (links.getD 3 defaultZ4Link)⟩

/-! ## 2. Duplicate-free bounded-labelling Fubini -/

private theorem rangeNodupLocal (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

theorem adjacentEvenFixedFaceIds_nodup (radius : Nat) :
    (adjacentEvenFixedFaceIds radius).Nodup := by
  have hfull :
      (slabPhysicalFaceEdges
        (adjacentEvenExtent radius)).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  have hall :
      ((adjacentEvenSlabFaceIdParts radius).1 ++
        (adjacentEvenSlabFaceIdParts radius).2.1 ++
        (adjacentEvenSlabFaceIdParts radius).2.2).Nodup :=
    (adjacentEvenSlabFaceIdParts_perm radius).symm.nodup hfull
  have houter := List.nodup_append.mp hall
  have hlowerFixed := List.nodup_append.mp houter.1
  exact hlowerFixed.2.1

private theorem eliminateLinks_eqv_congr_on
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree => by
      simp only [eliminateLinks]
      exact q_mul_congr_local
        (hagree head List.mem_cons_self)
        (eliminateLinks_eqv_congr_on left right tail
          (fun id hid => hagree id
            (List.mem_cons_of_mem head hid)))

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

/-- Exact finite Fubini for a product with one independent bounded label per
identifier.  `Nodup` is the formal no-duplication condition. -/
theorem boundedLabelling_product_fubini
    (cutoff : Nat) (factor : Nat → Nat → Q') :
    ∀ ids : List Nat, ids.Nodup →
      listQSum (fun label =>
        eliminateLinks (fun id => factor id (label id)) ids)
        (boundedEdgeLabellings cutoff ids) ≈
      eliminateLinks
        (fun id => fsum (factor id) (cutoff + 1)) ids
  | [], _ => by
      change (1 : Q') + 0 ≈ 1
      exact q_add_zero_eqv 1
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      let fullValue : EdgeLabelling → Q' := fun label =>
        eliminateLinks (fun id => factor id (label id))
          (head :: tail)
      let tailValue : EdgeLabelling → Q' := fun label =>
        eliminateLinks (fun id => factor id (label id)) tail
      have hexpand := listQSum_bounded_cons
        cutoff head tail fullValue
      have hinner : ∀ spin,
          listQSum (fun label =>
              fullValue (setEdgeLabel label head spin))
            (boundedEdgeLabellings cutoff tail) ≈
            factor head spin *
              listQSum tailValue
                (boundedEdgeLabellings cutoff tail) := by
        intro spin
        have hpoint : ∀ label,
            fullValue (setEdgeLabel label head spin) ≈
              factor head spin * tailValue label := by
          intro label
          unfold fullValue tailValue
          simp only [eliminateLinks]
          have hhead :
              factor head (setEdgeLabel label head spin head) ≈
                factor head spin := by
            simp [setEdgeLabel]
            exact Q'.eqv_refl _
          have htail :
              eliminateLinks
                  (fun id => factor id
                    (setEdgeLabel label head spin id)) tail ≈
                eliminateLinks
                  (fun id => factor id (label id)) tail := by
            apply eliminateLinks_eqv_congr_on
            intro id hid
            have hne : id ≠ head := by
              intro heq
              exact hparts.1 (heq ▸ hid)
            simp [setEdgeLabel, hne]
            exact Q'.eqv_refl _
          exact q_mul_congr_local hhead htail
        refine Q'.eqv_trans _ _ _
          (listQSum_congr hpoint
            (boundedEdgeLabellings cutoff tail)) ?_
        exact listQSum_const_mul_local
          (factor head spin) tailValue
          (boundedEdgeLabellings cutoff tail)
      refine Q'.eqv_trans _ _ _ hexpand ?_
      refine Q'.eqv_trans _ _ _
        (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
          _ _ hinner (cutoff + 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (YMGap.Continuum.CubeRatioBounds.fsum_mul_const
            (factor head)
            (listQSum tailValue
              (boundedEdgeLabellings cutoff tail))
            (cutoff + 1))) ?_
      simp only [eliminateLinks]
      exact Q'.mul_eqv_congr_left
        (fsum (factor head) (cutoff + 1)) _ _
        (boundedLabelling_product_fubini
          cutoff factor tail hparts.2)

/-! ## 3. Concrete global face sum equals the face-block product -/

def fixedFaceLabelFactor
    (cutoff radius : Nat)
    (left right : Z4Link → Nat)
    (id spin : Nat) : Q' :=
  coeffAt (heatKernelPacket cutoff anchorCoupling) spin *
    fourFusionIndicator
      (fixedFaceFourChannels radius id left) spin
      (fixedFaceFourChannels radius id right)

/-- One global bounded labelling of all fixed faces, with every face
coefficient and four-link transition included exactly once. -/
def adjacentEvenGlobalFixedFaceChannelKernel
    (cutoff radius : Nat)
    (left right : Z4Link → Nat) : Q' :=
  listQSum (fun boundary =>
    eliminateLinks (fun id =>
      fixedFaceLabelFactor cutoff radius left right id (boundary id))
      (adjacentEvenFixedFaceIds radius))
    (boundedEdgeLabellings cutoff
      (adjacentEvenFixedFaceIds radius))

def adjacentEvenFixedFaceBlockProduct
    (cutoff radius : Nat)
    (left right : Z4Link → Nat) : Q' :=
  eliminateLinks (fun id =>
    anchorJointFourResummedFaceKernel cutoff
      (fixedFaceFourChannels radius id left)
      (fixedFaceFourChannels radius id right))
    (adjacentEvenFixedFaceIds radius)

/-- The exact requested finite Fubini equality: the global boundary-label
sum is the duplicate-free product of literal joint-face blocks. -/
theorem adjacentEvenGlobalFixedFaceChannelKernel_eqv_blockProduct
    (cutoff radius : Nat)
    (left right : Z4Link → Nat) :
    adjacentEvenGlobalFixedFaceChannelKernel
        cutoff radius left right ≈
      adjacentEvenFixedFaceBlockProduct
        cutoff radius left right := by
  unfold adjacentEvenGlobalFixedFaceChannelKernel
    adjacentEvenFixedFaceBlockProduct
  refine Q'.eqv_trans _ _ _
    (boundedLabelling_product_fubini cutoff
      (fixedFaceLabelFactor cutoff radius left right)
      (adjacentEvenFixedFaceIds radius)
      (adjacentEvenFixedFaceIds_nodup radius)) ?_
  apply eliminateLinks_eqv_congr_on
  intro id _
  unfold fixedFaceLabelFactor
    anchorJointFourResummedFaceKernel
  exact Q'.eqv_symm
    (listQSum_range_eq_fsum
      (fun spin =>
        coeffAt (heatKernelPacket cutoff anchorCoupling) spin *
          fourFusionIndicator
            (fixedFaceFourChannels radius id left) spin
            (fixedFaceFourChannels radius id right))
      (cutoff + 1))

/-! ## 4. Exact specialization to the existing face-network Gram -/

/-- A four-channel tuple belongs to the explicit heterogeneous channel
window whenever each of its four coordinates does. -/
theorem fourChannels_mem_fourChannelSpace_of_le
    {channelCutoff first second third fourth : Nat}
    (hfirst : first ≤ channelCutoff)
    (hsecond : second ≤ channelCutoff)
    (hthird : third ≤ channelCutoff)
    (hfourth : fourth ≤ channelCutoff) :
    FourChannels.mk first second third fourth ∈
      fourChannelSpace channelCutoff := by
  unfold fourChannelSpace
  apply List.mem_map.mpr
  refine ⟨(((first, second), third), fourth), ?_, rfl⟩
  unfold fourChannelRawSpace
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).mpr
    constructor
    · apply (mem_cartesian_iff _ _ _).mpr
      exact ⟨List.mem_range.mpr (Nat.lt_succ_of_le hfirst),
        List.mem_range.mpr (Nat.lt_succ_of_le hsecond)⟩
    · exact List.mem_range.mpr (Nat.lt_succ_of_le hthird)
  · exact List.mem_range.mpr (Nat.lt_succ_of_le hfourth)

theorem fixedFaceFourChannels_mem_fourChannelSpace
    {channelCutoff radius id : Nat} {channel : Z4Link → Nat}
    (hchannel : ∀ link, channel link ≤ channelCutoff) :
    fixedFaceFourChannels radius id channel ∈
      fourChannelSpace channelCutoff := by
  unfold fixedFaceFourChannels
  apply fourChannels_mem_fourChannelSpace_of_le <;>
    apply hchannel

/-- Enumerate an arbitrary face list from its end.  This orientation matches
the successor convention of `anchorJointFaceNetworkKernel`; commutativity of
the exact rational product then recovers the original face-list order. -/
def faceListLocalChannels
    (radius : Nat) (ids : List Nat)
    (channelState : Nat → Z4Link → Nat)
    (position configuration : Nat) : FourChannels :=
  fixedFaceFourChannels radius
    (reverseListAt 0 ids position) (channelState configuration)

private theorem anchorJointFaceNetworkKernel_congr_prefix
    (faceCutoff : Nat)
    (first second : Nat → Nat → FourChannels) :
    ∀ count left right,
      (∀ face, face < count →
        first face left = second face left ∧
        first face right = second face right) →
      anchorJointFaceNetworkKernel faceCutoff first count left right ≈
        anchorJointFaceNetworkKernel faceCutoff second count left right
  | 0, _, _, _ => Q'.eqv_refl 1
  | count + 1, left, right, hagree => by
      simp only [anchorJointFaceNetworkKernel]
      apply q_mul_congr_local
      · apply anchorJointFaceNetworkKernel_congr_prefix
        intro face hface
        exact hagree face
          (Nat.lt_trans hface (Nat.lt_succ_self count))
      · have hcurrent := hagree count (Nat.lt_succ_self count)
        unfold anchorJointFourProductionMatrix
        rw [hcurrent.1, hcurrent.2]
        exact Q'.eqv_refl _

/-- The existing numeric face-network recursion is exactly the product over
an arbitrary concrete face list.  No face identifier is collapsed or
duplicated by the reindexing. -/
theorem faceListNetwork_eqv_blockProduct
    (faceCutoff radius : Nat)
    (channelState : Nat → Z4Link → Nat) :
    ∀ ids left right,
      anchorJointFaceNetworkKernel faceCutoff
          (faceListLocalChannels radius ids channelState)
          ids.length left right ≈
        eliminateLinks (fun id =>
          anchorJointFourResummedFaceKernel faceCutoff
            (fixedFaceFourChannels radius id (channelState left))
            (fixedFaceFourChannels radius id (channelState right))) ids
  | [], _, _ => Q'.eqv_refl 1
  | head :: tail, left, right => by
      simp only [List.length_cons, anchorJointFaceNetworkKernel,
        eliminateLinks]
      have hprefix :
          anchorJointFaceNetworkKernel faceCutoff
              (faceListLocalChannels radius (head :: tail) channelState)
              tail.length left right ≈
            anchorJointFaceNetworkKernel faceCutoff
              (faceListLocalChannels radius tail channelState)
              tail.length left right := by
        apply anchorJointFaceNetworkKernel_congr_prefix
        intro face hface
        constructor <;>
          simp [faceListLocalChannels, reverseListAt, hface]
      have htail := faceListNetwork_eqv_blockProduct
        faceCutoff radius channelState tail left right
      have hprevious := Q'.eqv_trans _ _ _ hprefix htail
      have hcurrent :
          anchorJointFourProductionMatrix faceCutoff
              (faceListLocalChannels radius (head :: tail) channelState
                tail.length) left right ≈
            anchorJointFourResummedFaceKernel faceCutoff
              (fixedFaceFourChannels radius head (channelState left))
              (fixedFaceFourChannels radius head
                (channelState right)) := by
        unfold anchorJointFourProductionMatrix faceListLocalChannels
        simp [reverseListAt]
        exact Q'.eqv_refl _
      exact Q'.eqv_trans _ _ _
        (q_mul_congr_local hprevious hcurrent)
        (Q'.mul_comm_eqv _ _)

theorem adjacentEvenAnchorJointFaceNetwork_eqv_blockProduct
    (faceCutoff radius : Nat)
    (channelState : Nat → Z4Link → Nat)
    (left right : Nat) :
    anchorJointFaceNetworkKernel faceCutoff
        (faceListLocalChannels radius
          (adjacentEvenFixedFaceIds radius) channelState)
        (adjacentEvenFixedFaceIds radius).length left right ≈
      adjacentEvenFixedFaceBlockProduct faceCutoff radius
        (channelState left) (channelState right) := by
  unfold adjacentEvenFixedFaceBlockProduct
  exact faceListNetwork_eqv_blockProduct
    faceCutoff radius channelState
    (adjacentEvenFixedFaceIds radius) left right

theorem adjacentEvenGlobalFixedFaceChannelKernel_eqv_anchorNetwork
    (faceCutoff radius : Nat)
    (channelState : Nat → Z4Link → Nat)
    (left right : Nat) :
    adjacentEvenGlobalFixedFaceChannelKernel faceCutoff radius
        (channelState left) (channelState right) ≈
      anchorJointFaceNetworkKernel faceCutoff
        (faceListLocalChannels radius
          (adjacentEvenFixedFaceIds radius) channelState)
        (adjacentEvenFixedFaceIds radius).length left right :=
  Q'.eqv_trans _ _ _
    (adjacentEvenGlobalFixedFaceChannelKernel_eqv_blockProduct
      faceCutoff radius (channelState left) (channelState right))
    (Q'.eqv_symm
      (adjacentEvenAnchorJointFaceNetwork_eqv_blockProduct
        faceCutoff radius channelState left right))

def adjacentEvenGlobalFixedFaceChannelMatrix
    (faceCutoff radius : Nat)
    (channelState : Nat → Z4Link → Nat)
    (left right : Nat) : Q' :=
  adjacentEvenGlobalFixedFaceChannelKernel faceCutoff radius
    (channelState left) (channelState right)

/-- Explicit Gram carrier for the literal global fixed-face label sum.  The
face cutoff and the auxiliary channel cutoff are independent parameters. -/
def adjacentEvenGlobalFixedFaceChannelGramRep
    (faceCutoff channelCutoff radius : Nat)
    (channelState : Nat → Z4Link → Nat)
    (hchannel : ∀ configuration link,
      channelState configuration link ≤ channelCutoff) :
    GramRep (adjacentEvenGlobalFixedFaceChannelMatrix
      faceCutoff radius channelState) := by
  let localChannels := faceListLocalChannels radius
    (adjacentEvenFixedFaceIds radius) channelState
  have hlocal : ∀ face configuration,
      localChannels face configuration ∈
        fourChannelSpace channelCutoff := by
    intro face configuration
    exact fixedFaceFourChannels_mem_fourChannelSpace
      (hchannel configuration)
  let rep := anchorJointFaceNetworkGramRep
    faceCutoff channelCutoff localChannels hlocal
    (adjacentEvenFixedFaceIds radius).length
  exact {
    r := rep.r
    d := rep.d
    hd := rep.hd
    v := rep.v
    hM := fun left right =>
      Q'.eqv_trans _ _ _
        (adjacentEvenGlobalFixedFaceChannelKernel_eqv_anchorNetwork
          faceCutoff radius channelState left right)
        (rep.hM left right)
  }

/-- Production specialization: physical face labels stop at `K`, while all
boundary-link channels live in the fusion-complete `6*K` window. -/
def adjacentEvenProductionFixedFaceChannelGramRep
    (K radius : Nat)
    (channelState : Nat → Z4Link → Nat)
    (hchannel : ∀ configuration link,
      channelState configuration link ≤ linkAuxiliaryCutoff K) :
    GramRep (adjacentEvenGlobalFixedFaceChannelMatrix
      K radius channelState) :=
  adjacentEvenGlobalFixedFaceChannelGramRep
    K (linkAuxiliaryCutoff K) radius channelState hchannel

/-- Concrete inhabitance witness for the production channel hypothesis. -/
def adjacentEvenZeroChannelState : Nat → Z4Link → Nat :=
  fun _ _ => 0

theorem adjacentEvenZeroChannelState_bounded (K : Nat) :
    ∀ configuration link,
      adjacentEvenZeroChannelState configuration link ≤
        linkAuxiliaryCutoff K := by
  intro _ _
  exact Nat.zero_le _

/-- The production fixed-face Gram carrier is therefore explicitly inhabited,
already on the all-vacuum open-channel configuration. -/
def adjacentEvenZeroProductionFixedFaceChannelGramRep
    (K radius : Nat) :
    GramRep (adjacentEvenGlobalFixedFaceChannelMatrix
      K radius adjacentEvenZeroChannelState) :=
  adjacentEvenProductionFixedFaceChannelGramRep K radius
    adjacentEvenZeroChannelState
    (adjacentEvenZeroChannelState_bounded K)

#print axioms adjacentEvenFixedFaceLinks_length
#print axioms adjacentEvenFixedFaceLink_mem_fixedSlabLinks
#print axioms adjacentEvenFixedFaceId_mem_linkIncidence
#print axioms adjacentEvenFixedFaceIds_nodup
#print axioms boundedLabelling_product_fubini
#print axioms adjacentEvenGlobalFixedFaceChannelKernel_eqv_blockProduct
#print axioms fourChannels_mem_fourChannelSpace_of_le
#print axioms faceListNetwork_eqv_blockProduct
#print axioms adjacentEvenGlobalFixedFaceChannelKernel_eqv_anchorNetwork
#print axioms adjacentEvenGlobalFixedFaceChannelGramRep
#print axioms adjacentEvenProductionFixedFaceChannelGramRep
#print axioms adjacentEvenZeroChannelState_bounded
#print axioms adjacentEvenZeroProductionFixedFaceChannelGramRep

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
