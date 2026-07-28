/-
# Additive closure of finite SU(2) fusion support

The Clebsch--Gordan support relation is closed under componentwise addition:
if `s` occurs in `a ⊗ b` and `s'` occurs in `a' ⊗ b'`, then `s+s'`
occurs in `(a+a') ⊗ (b+b')`.  In ladder coordinates this is the literal
addition of the two contraction-order witnesses.

This module lifts that elementary fact through the production canonical
link resolver.  Two accepted auxiliary fusion fields add pointwise to an
accepted field for the sum of their external labels.  Their finite Cartesian
cutoffs add as well.  Hence positive canonical and explicit valence-0-through-6
multiplicities are preserved by componentwise addition.

The final theorem specializes this to one boundary-complete corrected-slab
link.  Positive production multiplicities for two face labellings imply a
positive production multiplicity for their pointwise sum at cutoff `K + L`;
if the inputs are physically bounded by `K` and `L`, the summed labelling is
simultaneously bounded by `K + L`.

## Axiom gate

Finite `Nat` and `List` recursion only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.FusionBratteli
import YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
import YMGap.Continuum.Z4FusionPathZeroInsertion
import YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

namespace YMGap.Continuum.SU2FusionSupportAddition

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. The binary Clebsch--Gordan support monoid -/

def addEdgeLabelling
    (left right : EdgeLabelling) : EdgeLabelling :=
  fun edge => left edge + right edge

/-- Addition of the two ladder witnesses proves additive closure of SU(2)
fusion support. -/
theorem fusionOK_add
    {a b s a' b' s' : Nat}
    (hleft : fusionOK a b s = true)
    (hright : fusionOK a' b' s' = true) :
    fusionOK (a + a') (b + b') (s + s') = true := by
  obtain ⟨k, hka, hkb, hsum⟩ :=
    (fusionOK_iff_ladder a b s).mp hleft
  obtain ⟨k', hka', hkb', hsum'⟩ :=
    (fusionOK_iff_ladder a' b' s').mp hright
  apply (fusionOK_iff_ladder
    (a + a') (b + b') (s + s')).mpr
  refine ⟨k + k', ?_, ?_, ?_⟩ <;> omega

/-! ## 2. Trivalent graphs and canonical resolvers -/

theorem verticesAdmissibleB_cons_true_iff
    (vertex : TrivalentVertex)
    (rest : List TrivalentVertex)
    (label : EdgeLabelling) :
    verticesAdmissibleB (vertex :: rest) label = true ↔
      fusionOK (label vertex.1)
          (label vertex.2.1) (label vertex.2.2) = true ∧
        verticesAdmissibleB rest label = true := by
  cases hfusion :
      fusionOK (label vertex.1)
        (label vertex.2.1) (label vertex.2.2) <;>
    simp [verticesAdmissibleB, hfusion]

/-- Every fixed trivalent graph has additively closed admissible support. -/
theorem verticesAdmissibleB_add :
    ∀ (vertices : List TrivalentVertex)
      (left right : EdgeLabelling),
      verticesAdmissibleB vertices left = true →
      verticesAdmissibleB vertices right = true →
      verticesAdmissibleB vertices
        (addEdgeLabelling left right) = true
  | [], _, _, _, _ => rfl
  | vertex :: rest, left, right, hleft, hright => by
      have hleftParts :=
        (verticesAdmissibleB_cons_true_iff
          vertex rest left).mp hleft
      have hrightParts :=
        (verticesAdmissibleB_cons_true_iff
          vertex rest right).mp hright
      apply
        (verticesAdmissibleB_cons_true_iff
          vertex rest (addEdgeLabelling left right)).mpr
      constructor
      · exact fusionOK_add hleftParts.1 hrightParts.1
      · exact verticesAdmissibleB_add rest left right
          hleftParts.2 hrightParts.2

theorem overlayOn_add
    (edges : List Nat)
    (leftOuter rightOuter leftInner rightInner : EdgeLabelling) :
    overlayOn edges
        (addEdgeLabelling leftOuter rightOuter)
        (addEdgeLabelling leftInner rightInner) =
      addEdgeLabelling
        (overlayOn edges leftOuter leftInner)
        (overlayOn edges rightOuter rightInner) := by
  funext edge
  by_cases hedge : edge ∈ edges <;>
    simp [overlayOn, addEdgeLabelling, hedge]

/-- The canonical fixed-external resolver is closed under pointwise
addition, including its forced vacuum terminator. -/
theorem canonicalLinkConditionalAllowedB_add
    (degree : Nat)
    (leftExternal rightExternal leftAuxiliary rightAuxiliary :
      EdgeLabelling)
    (hleft :
      canonicalLinkConditionalAllowedB
        degree leftExternal leftAuxiliary = true)
    (hright :
      canonicalLinkConditionalAllowedB
        degree rightExternal rightAuxiliary = true) :
    canonicalLinkConditionalAllowedB degree
      (addEdgeLabelling leftExternal rightExternal)
      (addEdgeLabelling leftAuxiliary rightAuxiliary) = true := by
  let vertices :=
    fuseLabels degree (degree + 1) (List.range degree)
  let leftLabel :=
    overlayOn (List.range degree) leftExternal leftAuxiliary
  let rightLabel :=
    overlayOn (List.range degree) rightExternal rightAuxiliary
  let sumLabel :=
    overlayOn (List.range degree)
      (addEdgeLabelling leftExternal rightExternal)
      (addEdgeLabelling leftAuxiliary rightAuxiliary)
  have hleftParts :
      verticesAdmissibleB vertices leftLabel = true ∧
        (canonicalUsedAuxiliaryCoordinates degree).all
          (canonicalAuxiliaryEdgeAllowedB degree leftLabel) = true := by
    simpa only [canonicalLinkConditionalAllowedB,
      Bool.and_eq_true] using hleft
  have hrightParts :
      verticesAdmissibleB vertices rightLabel = true ∧
        (canonicalUsedAuxiliaryCoordinates degree).all
          (canonicalAuxiliaryEdgeAllowedB degree rightLabel) = true := by
    simpa only [canonicalLinkConditionalAllowedB,
      Bool.and_eq_true] using hright
  have hsumLabel :
      sumLabel = addEdgeLabelling leftLabel rightLabel := by
    exact overlayOn_add
      (List.range degree)
      leftExternal rightExternal leftAuxiliary rightAuxiliary
  unfold canonicalLinkConditionalAllowedB
  rw [Bool.and_eq_true]
  constructor
  · change verticesAdmissibleB vertices sumLabel = true
    rw [hsumLabel]
    exact verticesAdmissibleB_add vertices leftLabel rightLabel
      hleftParts.1 hrightParts.1
  · apply List.all_eq_true.mpr
    intro edge hedge
    have hleftEdge :=
      List.all_eq_true.mp hleftParts.2 edge hedge
    have hrightEdge :=
      List.all_eq_true.mp hrightParts.2 edge hedge
    change canonicalAuxiliaryEdgeAllowedB
      degree sumLabel edge = true
    rw [hsumLabel]
    unfold canonicalAuxiliaryEdgeAllowedB at hleftEdge
    unfold canonicalAuxiliaryEdgeAllowedB at hrightEdge
    unfold canonicalAuxiliaryEdgeAllowedB
    by_cases heq : edge = degree
    · rw [if_pos heq] at hleftEdge hrightEdge ⊢
      simp only [decide_eq_true_eq] at hleftEdge hrightEdge ⊢
      unfold addEdgeLabelling
      rw [hleftEdge, hrightEdge]
    · rw [if_neg heq] at hleftEdge hrightEdge ⊢

/-! ## 3. Addition inside the finite Cartesian auxiliary window -/

theorem addEdgeLabelling_mem_bounded
    {leftCutoff rightCutoff : Nat}
    (edges : List Nat)
    {left right : EdgeLabelling}
    (hleft :
      left ∈ boundedEdgeLabellings leftCutoff edges)
    (hright :
      right ∈ boundedEdgeLabellings rightCutoff edges) :
    addEdgeLabelling left right ∈
      boundedEdgeLabellings (leftCutoff + rightCutoff) edges := by
  have hleftSound :=
    boundedEdgeLabellings_sound
      leftCutoff edges left hleft
  have hrightSound :=
    boundedEdgeLabellings_sound
      rightCutoff edges right hright
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    unfold addEdgeLabelling
    have hl := hleftSound.1 edge hedge
    have hr := hrightSound.1 edge hedge
    omega
  · intro edge hedge
    unfold addEdgeLabelling
    rw [hleftSound.2 edge hedge, hrightSound.2 edge hedge]

private theorem list_has_member_of_length_pos {A : Type} :
    ∀ (items : List A), 0 < items.length →
      ∃ item, item ∈ items
  | [], hpositive =>
      False.elim (Nat.not_lt_zero 0 hpositive)
  | head :: _, _ => ⟨head, List.mem_cons_self⟩

/-- Positive canonical link multiplicities form an additive support monoid.
The target auxiliary cutoff is the literal sum of the two source cutoffs. -/
theorem canonicalLinkInvariantMultiplicityCount_add_pos
    {leftCutoff rightCutoff degree : Nat}
    {leftExternal rightExternal : EdgeLabelling}
    (hleft :
      0 < canonicalLinkInvariantMultiplicityCount
        leftCutoff degree leftExternal)
    (hright :
      0 < canonicalLinkInvariantMultiplicityCount
        rightCutoff degree rightExternal) :
    0 < canonicalLinkInvariantMultiplicityCount
      (leftCutoff + rightCutoff) degree
      (addEdgeLabelling leftExternal rightExternal) := by
  unfold canonicalLinkInvariantMultiplicityCount at hleft hright ⊢
  obtain ⟨leftAuxiliary, hleftAuxiliary⟩ :=
    list_has_member_of_length_pos _ hleft
  obtain ⟨rightAuxiliary, hrightAuxiliary⟩ :=
    list_has_member_of_length_pos _ hright
  have hleftParts := List.mem_filter.mp hleftAuxiliary
  have hrightParts := List.mem_filter.mp hrightAuxiliary
  apply List.length_pos_of_mem
  apply List.mem_filter.mpr
  constructor
  · exact addEdgeLabelling_mem_bounded
      (canonicalUsedAuxiliaryCoordinates degree)
      hleftParts.1 hrightParts.1
  · exact canonicalLinkConditionalAllowedB_add
      degree leftExternal rightExternal
      leftAuxiliary rightAuxiliary
      hleftParts.2 hrightParts.2

/-- Through geometric degree six, the literal explicit multiplicity inherits
the same additive support law. -/
theorem explicitValenceMultiplicity_add_pos
    {leftCutoff rightCutoff degree : Nat}
    {leftExternal rightExternal : EdgeLabelling}
    (hdegree : degree ≤ 6)
    (hleft :
      0 < explicitValenceMultiplicity
        leftCutoff degree leftExternal)
    (hright :
      0 < explicitValenceMultiplicity
        rightCutoff degree rightExternal) :
    0 < explicitValenceMultiplicity
      (leftCutoff + rightCutoff) degree
      (addEdgeLabelling leftExternal rightExternal) := by
  rw [← canonicalMultiplicity_eq_explicit
    leftExternal hdegree] at hleft
  rw [← canonicalMultiplicity_eq_explicit
    rightExternal hdegree] at hright
  have hsum :=
    canonicalLinkInvariantMultiplicityCount_add_pos
      hleft hright
  rw [canonicalMultiplicity_eq_explicit
    (addEdgeLabelling leftExternal rightExternal) hdegree] at hsum
  exact hsum

theorem linkAuxiliaryCutoff_add (K L : Nat) :
    linkAuxiliaryCutoff (K + L) =
      linkAuxiliaryCutoff K + linkAuxiliaryCutoff L := by
  unfold linkAuxiliaryCutoff linkIncidenceBound
  omega

/-! ## 4. Production corrected-slab link specialization -/

theorem externalSpinsOfList_map_add
    (ids : List Nat) (left right : EdgeLabelling) :
    externalSpinsOfList
        (ids.map (addEdgeLabelling left right)) =
      addEdgeLabelling
        (externalSpinsOfList (ids.map left))
        (externalSpinsOfList (ids.map right)) := by
  funext position
  induction ids generalizing position with
  | nil =>
      simp [externalSpinsOfList, addEdgeLabelling]
  | cons head tail ih =>
      cases position with
      | zero =>
          simp [externalSpinsOfList, addEdgeLabelling]
      | succ position =>
          simpa [externalSpinsOfList, addEdgeLabelling] using
            ih position

/-- Positive production multiplicities at one corrected-slab link are
preserved by pointwise addition of physical face labels. -/
theorem slabExplicitLinkMultiplicity_add_pos
    {K L extent : Nat}
    {left right : EdgeLabelling}
    (link : Z4Link)
    (hleft :
      0 < slabExplicitLinkMultiplicity K extent left link)
    (hright :
      0 < slabExplicitLinkMultiplicity L extent right link) :
    0 < slabExplicitLinkMultiplicity (K + L) extent
      (addEdgeLabelling left right) link := by
  let ids := slabIncidentPlaqIds extent link
  have hdegree : ids.length ≤ 6 := by
    exact slabIncidentPlaqIds_length_le_six extent link
  unfold slabExplicitLinkMultiplicity at hleft hright ⊢
  simp only [List.length_map] at hleft hright ⊢
  rw [linkAuxiliaryCutoff_add]
  have hsum :=
    explicitValenceMultiplicity_add_pos
      hdegree hleft hright
  have hexternal :
      externalSpinsOfList
          (ids.map (addEdgeLabelling left right)) =
        addEdgeLabelling
          (externalSpinsOfList (ids.map left))
          (externalSpinsOfList (ids.map right)) :=
    externalSpinsOfList_map_add ids left right
  rw [hexternal]
  exact hsum

theorem slabFaceLabellingBounded_add
    {K L extent : Nat}
    {left right : EdgeLabelling}
    (hleft : SlabFaceLabellingBounded K extent left)
    (hright : SlabFaceLabellingBounded L extent right) :
    SlabFaceLabellingBounded (K + L) extent
      (addEdgeLabelling left right) := by
  intro faceId hface
  unfold addEdgeLabelling
  exact Nat.add_le_add
    (hleft faceId hface) (hright faceId hface)

/-- Binary-layer aggregation at one link: the summed physical face field is
bounded by the summed face cutoff and retains a positive local invariant
multiplicity in the production `6*(K+L)` auxiliary window. -/
theorem slabBounded_add_and_linkMultiplicity_pos
    {K L extent : Nat}
    {left right : EdgeLabelling}
    (link : Z4Link)
    (hleftBounded : SlabFaceLabellingBounded K extent left)
    (hrightBounded : SlabFaceLabellingBounded L extent right)
    (hleft :
      0 < slabExplicitLinkMultiplicity K extent left link)
    (hright :
      0 < slabExplicitLinkMultiplicity L extent right link) :
    SlabFaceLabellingBounded (K + L) extent
        (addEdgeLabelling left right) ∧
      0 < slabExplicitLinkMultiplicity (K + L) extent
        (addEdgeLabelling left right) link :=
  ⟨slabFaceLabellingBounded_add hleftBounded hrightBounded,
    slabExplicitLinkMultiplicity_add_pos link hleft hright⟩

private theorem natListProduct_factor_pos {A : Type}
    (value : A → Nat) :
    ∀ (items : List A),
      0 < natListProduct value items →
      ∀ item, item ∈ items → 0 < value item
  | [], _, item, hitem =>
      False.elim (List.not_mem_nil hitem)
  | head :: tail, hproduct, item, hitem => by
      rcases List.mem_cons.mp hitem with hhead | htail
      · subst item
        have hne : value head ≠ 0 := by
          intro hzero
          rw [natListProduct, hzero, Nat.zero_mul] at hproduct
          exact Nat.not_lt_zero 0 hproduct
        omega
      · have htailProduct :
            0 < natListProduct value tail := by
          have hne : natListProduct value tail ≠ 0 := by
            intro hzero
            rw [natListProduct, hzero, Nat.mul_zero] at hproduct
            exact Nat.not_lt_zero 0 hproduct
          omega
        exact natListProduct_factor_pos
          value tail htailProduct item htail

private theorem natListProduct_pos_of_pointwise {A : Type}
    (value : A → Nat) :
    ∀ (items : List A),
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
            hvalue item (List.mem_cons_of_mem head hitem)))

/-- The local additive law assembles over every boundary-complete slab link:
positive complete link products are closed under pointwise addition. -/
theorem slabExplicitLinkMultiplicityProduct_add_pos
    {K L extent : Nat}
    {left right : EdgeLabelling}
    (hleft :
      0 < slabExplicitLinkMultiplicityProduct K extent left)
    (hright :
      0 < slabExplicitLinkMultiplicityProduct L extent right) :
    0 < slabExplicitLinkMultiplicityProduct (K + L) extent
      (addEdgeLabelling left right) := by
  unfold slabExplicitLinkMultiplicityProduct at hleft hright ⊢
  apply natListProduct_pos_of_pointwise
  intro link hlink
  exact slabExplicitLinkMultiplicity_add_pos link
    (natListProduct_factor_pos
      (slabExplicitLinkMultiplicity K extent left)
      (boundaryCompleteSlabLinks extent)
      hleft link hlink)
    (natListProduct_factor_pos
      (slabExplicitLinkMultiplicity L extent right)
      (boundaryCompleteSlabLinks extent)
      hright link hlink)

/-- Whole-link binary aggregation with the physical cutoff budget carried
alongside the global nonvanishing conclusion. -/
theorem slabBounded_add_and_linkProduct_pos
    {K L extent : Nat}
    {left right : EdgeLabelling}
    (hleftBounded : SlabFaceLabellingBounded K extent left)
    (hrightBounded : SlabFaceLabellingBounded L extent right)
    (hleft :
      0 < slabExplicitLinkMultiplicityProduct K extent left)
    (hright :
      0 < slabExplicitLinkMultiplicityProduct L extent right) :
    SlabFaceLabellingBounded (K + L) extent
        (addEdgeLabelling left right) ∧
      0 < slabExplicitLinkMultiplicityProduct (K + L) extent
        (addEdgeLabelling left right) :=
  ⟨slabFaceLabellingBounded_add hleftBounded hrightBounded,
    slabExplicitLinkMultiplicityProduct_add_pos hleft hright⟩

#print axioms fusionOK_add
#print axioms verticesAdmissibleB_add
#print axioms canonicalLinkConditionalAllowedB_add
#print axioms addEdgeLabelling_mem_bounded
#print axioms canonicalLinkInvariantMultiplicityCount_add_pos
#print axioms explicitValenceMultiplicity_add_pos
#print axioms externalSpinsOfList_map_add
#print axioms slabExplicitLinkMultiplicity_add_pos
#print axioms slabFaceLabellingBounded_add
#print axioms slabBounded_add_and_linkMultiplicity_pos
#print axioms slabExplicitLinkMultiplicityProduct_add_pos
#print axioms slabBounded_add_and_linkProduct_pos

end YMGap.Continuum.SU2FusionSupportAddition
