/-
# A positive BF4 row outside the closed-binary-sheet semigroup

The finite row-mass search decides binary-multicover existence, but the
universal positive-row normality statement is false.  This file gives a
literal corrected-slab counterexample at physical cutoff two.

Seventeen displayed plaquettes carry twice-spin label two.  Every touched
link sees either two or three such faces, so the local SU(2) invariant
multiplicity is positive.  Four displayed `x2` links form a binary
coboundary whose odd intersection with the seventeen-face support is the
single distinguished `p12` face.  Every closed binary sheet intersects a
coboundary evenly.  Therefore no closed sheet contained in the positive
support can contain the distinguished face, whereas reconstruction would
have to cover it twice.

Thus the all-positive-row integral multicover theorem cannot inhabit the
physical BF4 carrier.  A successful joint-carrier construction must retain
more local intertwiner/channel data than closed binary face sheets.

## Axiom gate

Finite list recursion, exact natural arithmetic, and kernel-checked concrete
geometry only.  No `Classical.*`, `sorry`, `native_decide`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
import YMGap.Continuum.BF4SU2OuterBinaryMulticoverDecision

namespace YMGap.Continuum.BF4SU2OuterBinaryMulticoverNoGo

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverDecision
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Literal positive cutoff-two row -/

/-- The seventeen-face support found by the exact cocircuit scout. -/
def normalityCounterSupport : List Z4Plaq :=
  [((0, 0, 0, 0), .p01),
   ((0, 0, 0, 0), .p02),
   ((0, 0, 0, 0), .p13),
   ((0, 0, 0, 0), .p23),
   ((0, 0, 0, 1), .p01),
   ((0, 0, 0, 1), .p02),
   ((0, 0, 1, 0), .p01),
   ((0, 0, 1, 0), .p13),
   ((0, 0, 1, 1), .p01),
   ((0, 1, 0, 0), .p02),
   ((0, 1, 0, 0), .p23),
   ((0, 1, 0, 1), .p02),
   ((1, 0, 0, 0), .p12),
   ((1, 0, 0, 0), .p13),
   ((1, 0, 0, 0), .p23),
   ((1, 0, 1, 0), .p13),
   ((1, 1, 0, 0), .p23)]

def normalityCounterIndicator : EdgeLabelling :=
  slabBinarySupportLabelling 3 normalityCounterSupport

def normalityCounterState : EdgeLabelling :=
  addEdgeLabelling
    normalityCounterIndicator normalityCounterIndicator

theorem normalityCounterSupport_nodup :
    normalityCounterSupport.Nodup := by
  decide

theorem normalityCounterSupport_subset_slab_three :
    ∀ plaquette, plaquette ∈ normalityCounterSupport →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  simp only [normalityCounterSupport, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem normalityCounterIndicator_mem_cutoff_one :
    normalityCounterIndicator ∈
      boundedEdgeLabellings
        1 (slabPhysicalFaceEdges 3) :=
  slabBinarySupportLabelling_mem
    (by decide) normalityCounterSupport

theorem normalityCounterState_mem :
    normalityCounterState ∈
      counterScalePair.fine.physicalLabellings := by
  change normalityCounterState ∈
    boundedEdgeLabellings
      2 (slabPhysicalFaceEdges 3)
  exact addEdgeLabelling_mem_bounded
    (leftCutoff := 1) (rightCutoff := 1)
    (left := normalityCounterIndicator)
    (right := normalityCounterIndicator)
    (slabPhysicalFaceEdges 3)
    normalityCounterIndicator_mem_cutoff_one
    normalityCounterIndicator_mem_cutoff_one

def normalityCounterTouchedLinks : List Z4Link :=
  [((0, 0, 0, 0), .x0),
   ((0, 0, 0, 0), .x1),
   ((0, 1, 0, 0), .x0),
   ((1, 0, 0, 0), .x1),
   ((0, 0, 0, 0), .x2),
   ((0, 0, 1, 0), .x0),
   ((1, 0, 0, 0), .x2),
   ((0, 0, 0, 0), .x3),
   ((0, 0, 0, 1), .x1),
   ((0, 1, 0, 0), .x3),
   ((0, 0, 0, 1), .x2),
   ((0, 0, 1, 0), .x3),
   ((0, 0, 0, 1), .x0),
   ((0, 1, 0, 1), .x0),
   ((1, 0, 0, 1), .x1),
   ((0, 0, 1, 1), .x0),
   ((1, 0, 0, 1), .x2),
   ((0, 0, 1, 0), .x1),
   ((0, 1, 1, 0), .x0),
   ((1, 0, 1, 0), .x1),
   ((0, 0, 1, 1), .x1),
   ((0, 1, 1, 0), .x3),
   ((0, 1, 1, 1), .x0),
   ((1, 0, 1, 1), .x1),
   ((0, 1, 0, 0), .x2),
   ((1, 1, 0, 0), .x2),
   ((0, 1, 0, 1), .x2),
   ((1, 1, 0, 1), .x2),
   ((1, 0, 0, 0), .x3),
   ((1, 1, 0, 0), .x3),
   ((1, 0, 1, 0), .x3),
   ((1, 1, 1, 0), .x3)]

theorem normalityCounterTouchedLinks_complete :
    normalityCounterTouchedLinks =
      supportBoundaryLinks normalityCounterSupport := by
  rfl

/-- Only the 32 touched links require a non-vacuum local calculation. -/
theorem normalityCounterTouchedLinks_length :
    normalityCounterTouchedLinks.length = 32 := by
  decide

def normalityCounterIncidentSpins (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds 3 link).map normalityCounterState

def normalityCounterActiveSpins (link : Z4Link) : List Nat :=
  (normalityCounterIncidentSpins link).filter
    (fun spin => decide (spin ≠ 0))

/-- Every touched link has geometric support degree two or three.  This is
the complete concrete calculation; the passage from incidence counts to
spin words is proved structurally below. -/
theorem normalityCounterTouchedIncidence_shape :
    normalityCounterTouchedLinks.all
        (fun link =>
          decide
            (faceIncidenceCount link normalityCounterSupport = 2 ∨
              faceIncidenceCount link normalityCounterSupport = 3)) =
      true := by
  decide

private theorem zeroExtension_filter_nonzero :
    ∀ spins : List Nat,
      ZeroExtension
        (spins.filter (fun spin => decide (spin ≠ 0)))
        spins
  | [] => ZeroExtension.nil
  | head :: tail => by
      by_cases hhead : head = 0
      · subst head
        simpa using ZeroExtension.insertZero
          (zeroExtension_filter_nonzero tail)
      · simp only [ne_eq, hhead, not_false_eq_true,
          decide_true, List.filter_cons_of_pos]
        exact ZeroExtension.keep head
          (zeroExtension_filter_nonzero tail)

private theorem natListSum_filter_nonzero :
    ∀ spins : List Nat,
      natListSum
          (spins.filter (fun spin => decide (spin ≠ 0))) =
        natListSum spins
  | [] => rfl
  | head :: tail => by
      by_cases hhead : head = 0
      · subst head
        simpa [natListSum] using
          natListSum_filter_nonzero tail
      · simp only [ne_eq, hhead, not_false_eq_true,
          decide_true, List.filter_cons_of_pos,
          natListSum, natListSum_filter_nonzero tail]

private theorem localExternalSpinSum_eq_natListSum :
    ∀ spins : List Nat,
      localExternalSpinSum spins.length
          (externalSpinsOfList spins) =
        natListSum spins
  | [] => rfl
  | head :: tail => by
      change
        natListSum
            ((List.range (tail.length + 1)).map
              (externalSpinsOfList (head :: tail))) =
          natListSum (head :: tail)
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, natListSum, List.map_map]
      change head +
          natListSum
            ((List.range tail.length).map
              (externalSpinsOfList tail)) =
        head + natListSum tail
      exact congrArg (fun value => head + value)
        (localExternalSpinSum_eq_natListSum tail)

private theorem natListSum_map_double :
    ∀ spins : List Nat,
      natListSum (spins.map (fun spin => spin + spin)) =
        2 * natListSum spins
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, natListSum,
        natListSum_map_double tail]
      omega

private theorem natListSum_replicate_two :
    ∀ count : Nat,
      natListSum (List.replicate count 2) = 2 * count
  | 0 => rfl
  | count + 1 => by
      simp only [List.replicate_succ, natListSum,
        natListSum_replicate_two count]
      omega

private theorem list_eq_replicate_of_pointwise
    (value : Nat) :
    ∀ entries : List Nat,
      (∀ entry, entry ∈ entries → entry = value) →
        entries = List.replicate entries.length value
  | [], _ => rfl
  | head :: tail, hpointwise => by
      have hhead := hpointwise head List.mem_cons_self
      have htail :
          ∀ entry, entry ∈ tail → entry = value := by
        intro entry hentry
        exact hpointwise entry
          (List.mem_cons_of_mem head hentry)
      subst head
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons value)
        (list_eq_replicate_of_pointwise value tail htail)

private theorem normalityCounterState_eq_double_indicator
    (id : Nat) :
    normalityCounterState id =
      normalityCounterIndicator id +
        normalityCounterIndicator id := rfl

private theorem normalityCounterActiveSpins_pointwise
    (link : Z4Link) :
    ∀ spin, spin ∈ normalityCounterActiveSpins link →
      spin = 2 := by
  intro spin hspin
  have hparts := List.mem_filter.mp hspin
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp hparts.1
  have hle :=
    slabBinarySupportLabelling_le_one
      3 normalityCounterSupport id
  change normalityCounterIndicator id ≤ 1 at hle
  have hne :
      normalityCounterState id ≠ 0 := by
    simpa only [decide_eq_true_eq] using hparts.2
  rw [normalityCounterState_eq_double_indicator] at hne ⊢
  omega

private theorem normalityCounterIncidentSpins_sum
    (link : Z4Link) :
    natListSum (normalityCounterIncidentSpins link) =
      2 * faceIncidenceCount
        link normalityCounterSupport := by
  let binarySpins :=
    (slabIncidentPlaqIds 3 link).map
      normalityCounterIndicator
  have hbinary :=
    slabBinarySupport_localExternalSpinSum
      normalityCounterSupport_subset_slab_three
      normalityCounterSupport_nodup link
  have hbinarySum :
      natListSum binarySpins =
        faceIncidenceCount
          link normalityCounterSupport := by
    unfold binarySpins normalityCounterIndicator
    rw [← localExternalSpinSum_eq_natListSum
      ((slabIncidentPlaqIds 3 link).map
        (slabBinarySupportLabelling
          3 normalityCounterSupport))]
    simpa only [List.length_map] using hbinary
  have hspins :
      normalityCounterIncidentSpins link =
        binarySpins.map (fun spin => spin + spin) := by
    unfold normalityCounterIncidentSpins binarySpins
      normalityCounterState normalityCounterIndicator
    rw [List.map_map]
    rfl
  rw [hspins, natListSum_map_double, hbinarySum]

private theorem normalityCounterActiveSpins_length
    (link : Z4Link) :
    (normalityCounterActiveSpins link).length =
      faceIncidenceCount
        link normalityCounterSupport := by
  have hreplicate :=
    list_eq_replicate_of_pointwise 2
      (normalityCounterActiveSpins link)
      (normalityCounterActiveSpins_pointwise link)
  have hsumFilter :=
    natListSum_filter_nonzero
      (normalityCounterIncidentSpins link)
  change
    natListSum (normalityCounterActiveSpins link) =
      natListSum (normalityCounterIncidentSpins link)
      at hsumFilter
  rw [hreplicate, natListSum_replicate_two,
    normalityCounterIncidentSpins_sum] at hsumFilter
  omega

private theorem normalityCounterTouchedActiveSpins_shape_at
    (link : Z4Link)
    (hlink : link ∈ normalityCounterTouchedLinks) :
    normalityCounterActiveSpins link = [2, 2] ∨
      normalityCounterActiveSpins link = [2, 2, 2] := by
  have hcount :
      faceIncidenceCount link normalityCounterSupport = 2 ∨
        faceIncidenceCount link normalityCounterSupport = 3 :=
    of_decide_eq_true
      (List.all_eq_true.mp
        normalityCounterTouchedIncidence_shape link hlink)
  have hreplicate :=
    list_eq_replicate_of_pointwise 2
      (normalityCounterActiveSpins link)
      (normalityCounterActiveSpins_pointwise link)
  rw [normalityCounterActiveSpins_length] at hreplicate
  rcases hcount with htwo | hthree
  · left
    simpa only [htwo] using hreplicate
  · right
    simpa only [hthree] using hreplicate

private theorem normalityCounterTouchedLinkMultiplicity_pos
    (link : Z4Link)
    (hlink : link ∈ normalityCounterTouchedLinks) :
    0 < slabExplicitLinkMultiplicity
      2 3 normalityCounterState link := by
  let spins := normalityCounterIncidentSpins link
  let active := normalityCounterActiveSpins link
  have hzero : ZeroExtension active spins := by
    unfold active normalityCounterActiveSpins spins
      normalityCounterIncidentSpins
    exact zeroExtension_filter_nonzero
      ((slabIncidentPlaqIds 3 link).map normalityCounterState)
  have htargetLength : spins.length ≤ 6 := by
    unfold spins normalityCounterIncidentSpins
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 3 link
  rcases normalityCounterTouchedActiveSpins_shape_at
      link hlink with htwo | hthree
  · have hsourceLength : active.length ≤ 6 := by
      dsimp only [active]
      rw [htwo]
      decide
    have hsourceBounded :
        SpinsBounded (linkAuxiliaryCutoff 2) active := by
      dsimp only [active]
      rw [htwo]
      intro spin hspin
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hspin
      rcases hspin with rfl | rfl
      all_goals decide
    unfold slabExplicitLinkMultiplicity
    change
      0 < explicitValenceMultiplicity
        (linkAuxiliaryCutoff 2) spins.length
        (externalSpinsOfList spins)
    rw [← explicitValenceMultiplicity_zeroExtension
      hzero hsourceLength htargetLength hsourceBounded]
    dsimp only [active]
    rw [htwo]
    decide
  · have hsourceLength : active.length ≤ 6 := by
      dsimp only [active]
      rw [hthree]
      decide
    have hsourceBounded :
        SpinsBounded (linkAuxiliaryCutoff 2) active := by
      dsimp only [active]
      rw [hthree]
      intro spin hspin
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hspin
      rcases hspin with rfl | rfl | rfl
      all_goals decide
    unfold slabExplicitLinkMultiplicity
    change
      0 < explicitValenceMultiplicity
        (linkAuxiliaryCutoff 2) spins.length
        (externalSpinsOfList spins)
    rw [← explicitValenceMultiplicity_zeroExtension
      hzero hsourceLength htargetLength hsourceBounded]
    dsimp only [active]
    rw [hthree]
    decide

private theorem listMap_congr_on {A B : Type}
    (left right : A → B) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → left x = right x) →
        xs.map left = xs.map right
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons]
      rw [hagree head List.mem_cons_self,
        listMap_congr_on left right tail
          (fun x hx =>
            hagree x (List.mem_cons_of_mem head hx))]

private theorem slabExplicitLinkMultiplicity_congr_incident
    (K extent : Nat) (left right : EdgeLabelling)
    (link : Z4Link)
    (hagree :
      ∀ id, id ∈ slabIncidentPlaqIds extent link →
        left id = right id) :
    slabExplicitLinkMultiplicity K extent left link =
      slabExplicitLinkMultiplicity K extent right link := by
  unfold slabExplicitLinkMultiplicity
  rw [listMap_congr_on left right
    (slabIncidentPlaqIds extent link) hagree]

private theorem normalityCounterState_eq_zero_on_untouched
    (link : Z4Link)
    (hlink : link ∉ normalityCounterTouchedLinks) :
    ∀ id, id ∈ slabIncidentPlaqIds 3 link →
      normalityCounterState id = zeroEdgeLabelling id := by
  intro id hid
  obtain ⟨plaquette, hindexed, hincident⟩ :=
    mem_slabIncidentPlaqIds.mp hid
  have hphysical :=
    slabIncidentPlaqId_physical hid
  have hlookup :
      slabPlaquetteAt 3 id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem
      fallbackPlaquette hindexed
  have hnotSupport :
      plaquette ∉ normalityCounterSupport := by
    intro hsupport
    apply hlink
    rw [normalityCounterTouchedLinks_complete]
    unfold supportBoundaryLinks
    rw [List.mem_eraseDups]
    apply List.mem_flatMap.mpr
    exact ⟨plaquette, hsupport, hincident⟩
  unfold normalityCounterState normalityCounterIndicator
    addEdgeLabelling zeroEdgeLabelling
  rw [slabBinarySupportLabelling_eq_indicator
    hphysical, hlookup]
  simp [hnotSupport]

private theorem normalityCounterLinkMultiplicity_pos
    (link : Z4Link) :
    0 < slabExplicitLinkMultiplicity
      2 3 normalityCounterState link := by
  by_cases htouched :
      link ∈ normalityCounterTouchedLinks
  · exact normalityCounterTouchedLinkMultiplicity_pos
      link htouched
  · rw [slabExplicitLinkMultiplicity_congr_incident
      2 3 normalityCounterState zeroEdgeLabelling
      link
      (normalityCounterState_eq_zero_on_untouched
        link htouched)]
    rw [slabExplicitLinkMultiplicity_zero_eq_one]
    omega

private theorem natListProduct_pos_of_pointwise {A : Type}
    (value : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → 0 < value item) →
        0 < natListProduct value items
  | [], _ => by
      change 0 < 1
      omega
  | head :: tail, hvalue => by
      rw [natListProduct]
      exact Nat.mul_pos
        (hvalue head List.mem_cons_self)
        (natListProduct_pos_of_pointwise value tail
          (fun item hitem =>
            hvalue item
              (List.mem_cons_of_mem head hitem)))

/-- Strict positivity of the complete actual corrected-slab link product. -/
theorem normalityCounterState_linkProduct_pos :
    0 < slabExplicitLinkMultiplicityProduct
      2 3 normalityCounterState := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_pos_of_pointwise
    (slabExplicitLinkMultiplicity
      2 3 normalityCounterState)
    (boundaryCompleteSlabLinks 3)
    (fun link _ =>
      normalityCounterLinkMultiplicity_pos link)

private theorem eliminateLinks_pos_local
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') < value id) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by
      show (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head)
        (eliminateLinks_pos_local value hvalue tail)

theorem normalityCounterState_faceFactor_pos :
    (0 : Q') <
      slabParametricKPhysicalFaceFactor
        1 2 3 normalityCounterState := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_pos_local
  intro id
  have hspin : normalityCounterState id < 2 + 1 := by
    unfold normalityCounterState normalityCounterIndicator
      addEdgeLabelling
    have hleft :=
      slabBinarySupportLabelling_le_one
        3 normalityCounterSupport id
    omega
  rw [coeffAt_heatKernelPacket hspin]
  exact
    YMGap.Continuum.FusionResidualBound.coeffW_pos
      (by decide) (normalityCounterState id)

private theorem qOfNat_pos_of_pos
    (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  show (0 : Int) * ((Q'.ofNat value).den : Int) <
    (Q'.ofNat value).num * (1 : Int)
  rw [Int.zero_mul, Q'.ofNat_num_cast, Int.mul_one]
  exact Int.ofNat_lt.mpr hvalue

/-- The counterexample is an actual strictly positive physical BF4 row. -/
theorem normalityCounterState_physicalTerm_pos :
    (0 : Q') <
      counterScalePair.fine.physicalTerm
        normalityCounterState := by
  change
    (0 : Q') <
      slabParametricKPhysicalFaceFactor
          1 2 3 normalityCounterState *
        Q'.ofNat
          (slabExplicitLinkMultiplicityProduct
            2 3 normalityCounterState)
  exact Q'.mul_pos
    normalityCounterState_faceFactor_pos
    (qOfNat_pos_of_pos _
      normalityCounterState_linkProduct_pos)

/-! ## 2. Sparse coboundary certificate -/

def normalityCounterDistinguishedFace : Z4Plaq :=
  ((1, 0, 0, 0), .p12)

def normalityCounterCutLink0 : Z4Link :=
  ((0, 1, 0, 0), .x2)

def normalityCounterCutLink1 : Z4Link :=
  ((0, 1, 0, 1), .x2)

def normalityCounterCutLink2 : Z4Link :=
  ((1, 1, 0, 0), .x2)

def normalityCounterCutLink3 : Z4Link :=
  ((1, 1, 0, 1), .x2)

/-- Number of the four certificate links lying on one plaquette boundary. -/
def normalityCounterCutFaceCount (plaquette : Z4Plaq) : Nat :=
  (if normalityCounterCutLink0 ∈ edgesOf plaquette then 1 else 0) +
  (if normalityCounterCutLink1 ∈ edgesOf plaquette then 1 else 0) +
  (if normalityCounterCutLink2 ∈ edgesOf plaquette then 1 else 0) +
  (if normalityCounterCutLink3 ∈ edgesOf plaquette then 1 else 0)

/-- On the positive support, the coboundary has odd incidence exactly at the
distinguished face. -/
theorem normalityCounterSupport_cut_parity
    (plaquette : Z4Plaq)
    (hplaquette :
      plaquette ∈ normalityCounterSupport) :
    normalityCounterCutFaceCount plaquette % 2 =
      if plaquette =
          normalityCounterDistinguishedFace then 1 else 0 := by
  simp only [normalityCounterSupport, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Double-count the incidences between an arbitrary support and the four
certificate links. -/
theorem normalityCounterCut_double_count :
    ∀ support : List Z4Plaq,
      natListSum
          (support.map normalityCounterCutFaceCount) =
        faceIncidenceCount
            normalityCounterCutLink0 support +
          faceIncidenceCount
            normalityCounterCutLink1 support +
          faceIncidenceCount
            normalityCounterCutLink2 support +
          faceIncidenceCount
            normalityCounterCutLink3 support
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, natListSum,
        normalityCounterCutFaceCount, faceIncidenceCount]
      rw [normalityCounterCut_double_count tail]
      omega

private theorem normalityCounterCut_sum_parity
    (support : List Z4Plaq)
    (hnodup : support.Nodup)
    (hsubset :
      ∀ plaquette, plaquette ∈ support →
        plaquette ∈ normalityCounterSupport) :
    natListSum
        (support.map normalityCounterCutFaceCount) % 2 =
      if normalityCounterDistinguishedFace ∈ support
        then 1 else 0 := by
  induction support with
  | nil => rfl
  | cons head tail ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hhead :=
        normalityCounterSupport_cut_parity head
          (hsubset head List.mem_cons_self)
      have htailSubset :
          ∀ plaquette, plaquette ∈ tail →
            plaquette ∈ normalityCounterSupport := by
        intro plaquette hplaquette
        exact hsubset plaquette
          (List.mem_cons_of_mem head hplaquette)
      have htail := ih hparts.2 htailSubset
      simp only [List.map_cons, natListSum]
      rw [Nat.add_mod, hhead, htail]
      by_cases heq :
          head = normalityCounterDistinguishedFace
      · subst head
        have hnotTail :
            normalityCounterDistinguishedFace ∉ tail :=
          hparts.1
        simp [hnotTail]
      · have hreverse :
            normalityCounterDistinguishedFace ≠ head := by
          intro h
          exact heq h.symm
        by_cases htailMem :
            normalityCounterDistinguishedFace ∈ tail
        · simp [heq, hreverse, htailMem]
        · simp [heq, hreverse, htailMem]

/-- No even-incidence binary support contained in the positive support can
contain the distinguished face. -/
theorem distinguished_not_mem_even_subsupport
    (support : List Z4Plaq)
    (hnodup : support.Nodup)
    (heven : EvenFaceIncidence support)
    (hsubset :
      ∀ plaquette, plaquette ∈ support →
        plaquette ∈ normalityCounterSupport) :
    normalityCounterDistinguishedFace ∉ support := by
  intro hdistinguished
  have hsumParity :=
    normalityCounterCut_sum_parity
      support hnodup hsubset
  rw [if_pos hdistinguished] at hsumParity
  have hdouble :=
    normalityCounterCut_double_count support
  have h0 := heven normalityCounterCutLink0
  have h1 := heven normalityCounterCutLink1
  have h2 := heven normalityCounterCutLink2
  have h3 := heven normalityCounterCutLink3
  omega

/-! ## 3. Every alleged layer misses the distinguished face -/

private theorem layer_state_le_sum_of_mem
    {S : SlabScalePair} :
    ∀ (layers : List (BinaryEvenSlabLayer S))
      (layer : BinaryEvenSlabLayer S),
      layer ∈ layers →
        ∀ faceId, layer.state faceId ≤
          sumLayerStates layers faceId
  | [], layer, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, layer, hmem, faceId => by
      rcases List.mem_cons.mp hmem with heq | htail
      · rw [heq]
        simp only [sumLayerStates, addEdgeLabelling]
        omega
      · have ih :=
          layer_state_le_sum_of_mem
            tail layer htail faceId
        simp only [sumLayerStates, addEdgeLabelling]
        omega

private theorem supportCode_subset_counterSupport
    (multicover :
      BinaryEvenSlabMulticover
        counterScalePair normalityCounterState)
    (layer : BinaryEvenSlabLayer counterScalePair)
    (hlayer : layer ∈ multicover.layers) :
    ∀ plaquette,
      plaquette ∈ (supportCodeOfLayer layer).support →
        plaquette ∈ normalityCounterSupport := by
  intro plaquette hplaquette
  have hslab :=
    (supportCodeOfLayer layer).subset
      plaquette hplaquette
  let faceId :=
    listIndexOf plaquette
      (boundaryCompleteSlabPlaquettes 3)
  have hfaceId :
      faceId ∈ slabPhysicalFaceEdges 3 := by
    unfold faceId slabPhysicalFaceEdges
    exact List.mem_range.mpr
      (listIndexOf_lt_of_mem plaquette
        (boundaryCompleteSlabPlaquettes 3) hslab)
  have hlookup :
      slabPlaquetteAt 3 faceId = plaquette := by
    unfold faceId slabPlaquetteAt
    exact getD_listIndexOf_of_mem
      fallbackPlaquette plaquette
      (boundaryCompleteSlabPlaquettes 3) hslab
  have hcodeState :
      (supportCodeOfLayer layer).toLayer.state faceId = 1 := by
    change
      slabBinarySupportLabelling
          3 (supportCodeOfLayer layer).support faceId = 1
    rw [slabBinarySupportLabelling_eq_indicator
      hfaceId, hlookup]
    simp [hplaquette]
  have hlayerState : layer.state faceId = 1 := by
    rw [← supportCodeOfLayer_toLayer_state layer]
    exact hcodeState
  have hle :=
    layer_state_le_sum_of_mem
      multicover.layers layer hlayer faceId
  rw [multicover.reconstruct] at hle
  by_cases hmem :
      plaquette ∈ normalityCounterSupport
  · exact hmem
  · have hcounterZero :
        normalityCounterState faceId = 0 := by
      unfold normalityCounterState normalityCounterIndicator
        addEdgeLabelling
      rw [slabBinarySupportLabelling_eq_indicator
        hfaceId, hlookup]
      simp [hmem]
    rw [hlayerState, hcounterZero] at hle
    exact False.elim (by omega)

def normalityCounterDistinguishedFaceId : Nat :=
  listIndexOf normalityCounterDistinguishedFace
    (boundaryCompleteSlabPlaquettes 3)

theorem normalityCounterDistinguishedFace_mem_support :
    normalityCounterDistinguishedFace ∈
      normalityCounterSupport := by
  decide

theorem normalityCounterDistinguishedFaceId_physical :
    normalityCounterDistinguishedFaceId ∈
      slabPhysicalFaceEdges 3 := by
  unfold normalityCounterDistinguishedFaceId
    slabPhysicalFaceEdges
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact normalityCounterSupport_subset_slab_three
    normalityCounterDistinguishedFace
    normalityCounterDistinguishedFace_mem_support

theorem normalityCounterDistinguishedFaceId_lookup :
    slabPlaquetteAt 3 normalityCounterDistinguishedFaceId =
      normalityCounterDistinguishedFace := by
  unfold normalityCounterDistinguishedFaceId slabPlaquetteAt
  exact getD_listIndexOf_of_mem
    fallbackPlaquette normalityCounterDistinguishedFace
    (boundaryCompleteSlabPlaquettes 3)
    (normalityCounterSupport_subset_slab_three
      normalityCounterDistinguishedFace
      normalityCounterDistinguishedFace_mem_support)

theorem normalityCounterState_distinguished :
    normalityCounterState
        normalityCounterDistinguishedFaceId = 2 := by
  unfold normalityCounterState normalityCounterIndicator
    addEdgeLabelling
  rw [slabBinarySupportLabelling_eq_indicator
    normalityCounterDistinguishedFaceId_physical,
    normalityCounterDistinguishedFaceId_lookup]
  simp [normalityCounterDistinguishedFace_mem_support]

private theorem alleged_layer_distinguished_zero
    (multicover :
      BinaryEvenSlabMulticover
        counterScalePair normalityCounterState)
    (layer : BinaryEvenSlabLayer counterScalePair)
    (hlayer : layer ∈ multicover.layers) :
    layer.state normalityCounterDistinguishedFaceId = 0 := by
  let code := supportCodeOfLayer layer
  have hnot :
      normalityCounterDistinguishedFace ∉ code.support := by
    apply distinguished_not_mem_even_subsupport
    · exact code.nodup
    · exact code.even
    · exact supportCode_subset_counterSupport
        multicover layer hlayer
  have hcode :
      code.toLayer.state
          normalityCounterDistinguishedFaceId = 0 := by
    change
      slabBinarySupportLabelling
          3 code.support
          normalityCounterDistinguishedFaceId = 0
    rw [slabBinarySupportLabelling_eq_indicator
      normalityCounterDistinguishedFaceId_physical,
      normalityCounterDistinguishedFaceId_lookup]
    simp [hnot]
  rw [← supportCodeOfLayer_toLayer_state layer]
  exact hcode

private theorem alleged_layers_distinguished_sum_zero
    (multicover :
      BinaryEvenSlabMulticover
        counterScalePair normalityCounterState) :
    ∀ layers : List (BinaryEvenSlabLayer counterScalePair),
      (∀ layer, layer ∈ layers →
        layer ∈ multicover.layers) →
      sumLayerStates layers
          normalityCounterDistinguishedFaceId = 0
  | [], _ => rfl
  | head :: tail, hsubset => by
      have hhead :=
        alleged_layer_distinguished_zero
          multicover head
          (hsubset head List.mem_cons_self)
      have htail :
          ∀ layer, layer ∈ tail →
            layer ∈ multicover.layers := by
        intro layer hlayer
        exact hsubset layer
          (List.mem_cons_of_mem head hlayer)
      simp only [sumLayerStates, addEdgeLabelling,
        hhead,
        alleged_layers_distinguished_sum_zero
          multicover tail htail,
        Nat.zero_add]

/-! ## 4. The positive-row multicover theorem is false -/

theorem normalityCounterState_no_multicover :
    BinaryEvenSlabMulticover
        counterScalePair normalityCounterState →
      False := by
  intro multicover
  have hzero :=
    alleged_layers_distinguished_sum_zero
      multicover multicover.layers
      (fun layer hlayer => hlayer)
  have hreconstruct :=
    congrFun multicover.reconstruct
      normalityCounterDistinguishedFaceId
  rw [hzero,
    normalityCounterState_distinguished] at hreconstruct
  cases hreconstruct

/-- The complete row-mass decision procedure necessarily takes its negative
branch on this literal positive row. -/
def normalityCounterDecision :
    BinaryMulticoverDecision
      counterScalePair normalityCounterState :=
  decideBinaryMulticover
    counterScalePair normalityCounterState
    normalityCounterState_mem

#print axioms normalityCounterSupport_nodup
#print axioms normalityCounterSupport_subset_slab_three
#print axioms normalityCounterState_mem
#print axioms normalityCounterState_linkProduct_pos
#print axioms normalityCounterState_physicalTerm_pos
#print axioms normalityCounterSupport_cut_parity
#print axioms normalityCounterCut_double_count
#print axioms distinguished_not_mem_even_subsupport
#print axioms normalityCounterState_no_multicover
#print axioms normalityCounterDecision

end YMGap.Continuum.BF4SU2OuterBinaryMulticoverNoGo
