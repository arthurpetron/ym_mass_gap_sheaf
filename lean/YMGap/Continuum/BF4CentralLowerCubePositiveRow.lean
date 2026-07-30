/-
# A genuine non-vacuum positive row in the central BF4 carrier

At half-extent zero, the lower spatial slice contains the boundary of one
literal unit cube.  Its six plaquette identifiers are

    [0, 1, 3, 9, 19, 39].

Every touched link is incident on exactly two fundamental faces.  This file
checks the cutoff-one link product by kernel reduction, transports that
identity to every production cutoff `K >= 1` using the proved local cutoff
independence theorem, and proves strict positivity of the corresponding
physical reflected summand for every `w > 0`.

Consequently the central physical Markov carrier contains a concrete
non-vacuum row at every such cutoff.  This is a genuine first ingredient for
an upper bound on the vacuum marginal.  It does not yet prove a quantitative
lower bound on this row relative to the complete vacuum row and therefore
does not by itself establish `pi(0) <= 5/6`.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
import YMGap.Continuum.FusionResidualBound
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
import YMGap.Continuum.Z4ValenceFusionCutoffIndependence

namespace YMGap.Continuum.BF4CentralLowerCubePositiveRow

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal six-face lower cube -/

/-- The six lower-slice plaquette identifiers forming the boundary of the
spatial unit cube at the origin. -/
def centralLowerCubeFaceIds : List Nat :=
  [0, 1, 3, 9, 19, 39]

/-- Fundamental spin on the six cube faces and vacuum elsewhere. -/
def centralLowerCubeState :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  componentLabel centralLowerCubeFaceIds

/-- The complete reflected-slab labelling obtained from the cube source and
vacuum fixed/target data. -/
def centralLowerCubePhysical :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  assembleReflectedSlabLabelling 0 centralLowerCubeState
    zeroEdgeLabelling zeroEdgeLabelling

theorem centralLowerCubeFaceIds_subset_lower :
    ∀ id, id ∈ centralLowerCubeFaceIds →
      id ∈ centralLowerFaceIds 0 := by
  decide

theorem centralLowerCubeState_le_one (id : Nat) :
    centralLowerCubeState id ≤ 1 := by
  unfold centralLowerCubeState componentLabel
  by_cases hcube : id ∈ centralLowerCubeFaceIds <;> simp [hcube]

theorem centralLowerCubePhysical_le_one (id : Nat) :
    centralLowerCubePhysical id ≤ 1 := by
  unfold centralLowerCubePhysical assembleReflectedSlabLabelling
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · rw [if_pos hid]
    cases hside :
        plaquetteHalfSide 0
          (slabPlaquetteAt (centralExtent 0) id)
    · unfold centralLowerCubeState componentLabel
      by_cases hcube : id ∈ centralLowerCubeFaceIds <;> simp [hcube]
    · change 0 ≤ 1
      omega
    · change 0 ≤ 1
      omega
  · rw [if_neg hid]
    omega

/-- The assembled source/vacuum/vacuum labelling is exactly the six-face
indicator on every numerical plaquette coordinate. -/
theorem centralLowerCubePhysical_eq_componentLabel :
    centralLowerCubePhysical =
      componentLabel centralLowerCubeFaceIds := by
  funext id
  unfold centralLowerCubePhysical assembleReflectedSlabLabelling
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent 0)
  · rw [if_pos hid]
    cases hside :
        plaquetteHalfSide 0
          (slabPlaquetteAt (centralExtent 0) id)
    · rfl
    · change 0 = componentLabel centralLowerCubeFaceIds id
      symm
      apply componentLabel_eq_zero_of_not_mem
      intro hcube
      have hlower :=
        (mem_centralLowerFaceIds.mp
          (centralLowerCubeFaceIds_subset_lower id hcube)).2
      rw [hside] at hlower
      contradiction
    · change 0 = componentLabel centralLowerCubeFaceIds id
      symm
      apply componentLabel_eq_zero_of_not_mem
      intro hcube
      have hlower :=
        (mem_centralLowerFaceIds.mp
          (centralLowerCubeFaceIds_subset_lower id hcube)).2
      rw [hside] at hlower
      contradiction
  · rw [if_neg hid]
    change 0 = componentLabel centralLowerCubeFaceIds id
    symm
    apply componentLabel_eq_zero_of_not_mem
    intro hcube
    exact hid
      (mem_centralLowerFaceIds.mp
        (centralLowerCubeFaceIds_subset_lower id hcube)).1

/-- Closed computation of the local fusion audit at cutoff one. -/
theorem centralLowerCubeMultiplicityProduct_one :
    slabExplicitLinkMultiplicityProduct
        1 1 centralLowerCubePhysical = 1 := by
  rfl

/-! ## 2. Transport of the link audit to every cutoff -/

private theorem externalSpinsOfList_bound_one
    (spins : List Nat)
    (hspins : ∀ spin, spin ∈ spins → spin ≤ 1) :
    ExternalSpinsBounded 1 spins.length
      (externalSpinsOfList spins) := by
  intro position hposition
  unfold externalSpinsOfList
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hposition]
  exact hspins _ (List.getElem_mem hposition)

theorem centralLowerCubeMultiplicity_eq_one
    {K : Nat} (hK : 1 ≤ K)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    slabExplicitLinkMultiplicity
        K 1 centralLowerCubePhysical link = 1 := by
  let spins :=
    (slabIncidentPlaqIds 1 link).map centralLowerCubePhysical
  have hdegree : spins.length ≤ linkIncidenceBound := by
    unfold spins linkIncidenceBound
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have hspins :
      ∀ spin, spin ∈ spins → spin ≤ 1 := by
    intro spin hspin
    obtain ⟨id, _, rfl⟩ := List.mem_map.mp hspin
    exact centralLowerCubePhysical_le_one id
  have hcutoff :
      linkAuxiliaryCutoff 1 ≤ linkAuxiliaryCutoff K := by
    unfold linkAuxiliaryCutoff linkIncidenceBound
    omega
  unfold slabExplicitLinkMultiplicity
  change
    explicitValenceMultiplicity
        (linkAuxiliaryCutoff K) spins.length
        (externalSpinsOfList spins) = 1
  rw [explicitValenceMultiplicity_cutoff_independent
    (externalSpinsOfList spins) hcutoff hdegree
    (externalSpinsOfList_bound_one spins hspins)]
  change
    slabExplicitLinkMultiplicity
        1 1 centralLowerCubePhysical link = 1
  have hcheck :
      (boundaryCompleteSlabLinks 1).all
          (fun candidate =>
            decide
              (slabExplicitLinkMultiplicity
                1 1 centralLowerCubePhysical candidate = 1)) = true := by
    rfl
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck link hlink)

theorem centralLowerCubeMultiplicityProduct_eq_one
    {K : Nat} (hK : 1 ≤ K) :
    slabExplicitLinkMultiplicityProduct
        K 1 centralLowerCubePhysical = 1 := by
  unfold slabExplicitLinkMultiplicityProduct
  calc
    natListProduct
        (slabExplicitLinkMultiplicity K 1 centralLowerCubePhysical)
        (boundaryCompleteSlabLinks 1) =
      natListProduct
        (slabExplicitLinkMultiplicity 1 1 centralLowerCubePhysical)
        (boundaryCompleteSlabLinks 1) := by
          apply natListProduct_congr
          intro link hlink
          rw [centralLowerCubeMultiplicity_eq_one hK link hlink,
            centralLowerCubeMultiplicity_eq_one
              (K := 1) (by decide) link hlink]
    _ = 1 := centralLowerCubeMultiplicityProduct_one

/-! ## 3. Strict positivity of the genuine physical row -/

private theorem eliminateLinks_pos
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') < value id) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids := by
  intro ids
  induction ids with
  | nil =>
      change (0 : Q') < 1
      decide
  | cons head tail ih =>
      exact Q'.mul_pos (hvalue head) ih

/-- Multiplicative congruence in the rational setoid. -/
private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id ≈ right id) →
        eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl _
  | id :: rest, hagree =>
      qmul_congr
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem eliminateLinks_indicator_pow
    (selected : List Nat) (coefficient : Q') :
    ∀ ids : List Nat,
      eliminateLinks
          (fun id =>
            if id ∈ selected then coefficient else 1)
          ids ≈
        coefficient ^
          (ids.filter
            (fun id => decide (id ∈ selected))).length
  | [] => Q'.eqv_refl _
  | id :: rest => by
      by_cases hselected : id ∈ selected
      · simp only [eliminateLinks, hselected, if_pos,
          List.filter_cons, decide_true, List.length_cons,
          Q'.pow_succ]
        exact qmul_congr (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow selected coefficient rest)
      · simp only [eliminateLinks, hselected,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow
              selected coefficient rest))
          (Q'.one_mul_eqv _)

/-- The exact face activity of the lower cube.  All other slab plaquettes
carry the vacuum coefficient one. -/
theorem centralLowerCubePhysicalFaceFactor_eqv
    (w : Q') {K : Nat} (hK : 1 ≤ K) :
    slabParametricKPhysicalFaceFactor
        w K 1 centralLowerCubePhysical ≈
      (coeffW w 1) ^ 6 := by
  unfold slabParametricKPhysicalFaceFactor
  have hcoeff :
      eliminateLinks
          (fun id =>
            coeffAt (heatKernelPacket K w)
              (centralLowerCubePhysical id))
          (slabPhysicalFaceEdges 1) ≈
        eliminateLinks
          (fun id =>
            if id ∈ centralLowerCubeFaceIds
            then coeffW w 1 else 1)
          (slabPhysicalFaceEdges 1) := by
    apply eliminateLinks_congr_on
    intro id _
    rw [centralLowerCubePhysical_eq_componentLabel]
    by_cases hcube : id ∈ centralLowerCubeFaceIds
    · rw [componentLabel_eq_one_iff.mpr hcube,
        coeffAt_heatKernelPacket (by omega),
        if_pos hcube]
      exact Q'.eqv_refl _
    · rw [componentLabel_eq_zero_of_not_mem hcube,
        coeffAt_heatKernelPacket (Nat.succ_pos K),
        coeffW_zero, if_neg hcube]
      exact Q'.eqv_refl _
  have hpower :=
    eliminateLinks_indicator_pow
      centralLowerCubeFaceIds (coeffW w 1)
      (slabPhysicalFaceEdges 1)
  have hcount :
      ((slabPhysicalFaceEdges 1).filter
        (fun id =>
          decide (id ∈ centralLowerCubeFaceIds))).length = 6 := by
    decide
  rw [hcount] at hpower
  exact Q'.eqv_trans _ _ _ hcoeff hpower

/-- Exact non-vacuum production activity of the closed six-face cube. -/
theorem centralLowerCubePhysicalTerm_eqv
    (w : Q') {K : Nat} (hK : 1 ≤ K) :
    slabParametricKPhysicalTerm
        w K 1 centralLowerCubePhysical ≈
      (coeffW w 1) ^ 6 := by
  unfold slabParametricKPhysicalTerm
  rw [centralLowerCubeMultiplicityProduct_eq_one hK]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ 1
      (centralLowerCubePhysicalFaceFactor_eqv w hK))
    (Q'.mul_one_eqv _)

theorem centralLowerCubePhysicalTerm_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    (0 : Q') <
      slabParametricKPhysicalTerm
        w K 1 centralLowerCubePhysical := by
  have hface :
      (0 : Q') <
        slabParametricKPhysicalFaceFactor
          w K 1 centralLowerCubePhysical := by
    unfold slabParametricKPhysicalFaceFactor
    apply eliminateLinks_pos
    intro id
    have hspin : centralLowerCubePhysical id < K + 1 := by
      have hle := centralLowerCubePhysical_le_one id
      omega
    rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_pos hw _
  unfold slabParametricKPhysicalTerm
  rw [centralLowerCubeMultiplicityProduct_eq_one hK]
  exact Q'.mul_pos hface (by decide)

theorem centralLowerCubeState_mem_centralHalfStates
    {K : Nat} (hK : 1 ≤ K) :
    centralLowerCubeState ∈ centralHalfStates K 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro id _
    exact Nat.lt_succ_of_le
      (Nat.le_trans (centralLowerCubeState_le_one id) hK)
  · intro id hid
    exact componentLabel_eq_zero_of_not_mem (by
      intro hcube
      exact hid
        (centralLowerCubeFaceIds_subset_lower id hcube))

theorem centralLowerCubeState_ne_zero :
    centralLowerCubeState ≠ zeroEdgeLabelling := by
  intro heq
  have hvalue := congrFun heq 0
  change 1 = 0 at hvalue
  omega

private theorem zero_mem_bounded (K : Nat) :
    ∀ ids : List Nat,
      zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih :=
          listQSum_member_le value hvalue tail htail
        have hmono :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have h :=
            Q'.add_le_add_right
              (0 : Q') (value head)
              (listQSum value tail)
              (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

theorem centralLowerCubePhysicalReflectedKernel_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    (0 : Q') <
      centralPhysicalReflectedKernel
        w K 0 centralLowerCubeState zeroEdgeLabelling := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling
        0 centralLowerCubeState boundary zeroEdgeLabelling)
  have hmember :
      value zeroEdgeLabelling ≤
        listQSum value (centralBoundaryChannels K 0) :=
    listQSum_member_le value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          (Q'.le_of_lt hw) K 1
          (assembleReflectedSlabLabelling
            0 centralLowerCubeState boundary zeroEdgeLabelling))
      (centralBoundaryChannels K 0)
      (zero_mem_bounded K (centralFixedFaceIds 0))
  have hchosen : (0 : Q') < value zeroEdgeLabelling :=
    centralLowerCubePhysicalTerm_pos hw hK
  unfold centralPhysicalReflectedKernel
  exact Q'.pos_of_lt_of_le hchosen hmember

/-- The complete raw reflected row contains the exact six-face activity. -/
theorem centralLowerCubeActivity_le_reflectedKernel
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K : Nat} (hK : 1 ≤ K) :
    (coeffW w 1) ^ 6 ≤
      centralPhysicalReflectedKernel
        w K 0 centralLowerCubeState zeroEdgeLabelling := by
  let value := fun boundary =>
    slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling
        0 centralLowerCubeState boundary zeroEdgeLabelling)
  have hmember :
      value zeroEdgeLabelling ≤
        listQSum value (centralBoundaryChannels K 0) :=
    listQSum_member_le value
      (fun boundary =>
        slabParametricKPhysicalTerm_nonnegative
          hw K 1
          (assembleReflectedSlabLabelling
            0 centralLowerCubeState boundary zeroEdgeLabelling))
      (centralBoundaryChannels K 0)
      (zero_mem_bounded K (centralFixedFaceIds 0))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (centralLowerCubePhysicalTerm_eqv w hK))
    hmember

theorem centralLowerCubeNormalizedJoint_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    (0 : Q') <
      centralNormalizedPhysicalReflectedKernel
        w (Q'.le_of_lt hw) K 0
        centralLowerCubeState zeroEdgeLabelling := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  exact Q'.mul_pos
    (centralLowerCubePhysicalReflectedKernel_pos hw hK)
    (Q'.recipPos_pos _ _)

theorem centralLowerCubeRowMarginal_pos
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    (0 : Q') <
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState := by
  unfold centralPhysicalRowMarginal
  have hmember :=
    listQSum_member_le
      (centralNormalizedPhysicalReflectedKernel
        w (Q'.le_of_lt hw) K 0 centralLowerCubeState)
      (fun target =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K 0 centralLowerCubeState target)
      (centralHalfStates K 0)
      (zero_mem_bounded K (centralLowerFaceIds 0))
  exact Q'.pos_of_lt_of_le
    (centralLowerCubeNormalizedJoint_pos hw hK)
    hmember

theorem centralLowerCubeState_mem_centralPositiveHalfStates
    {w : Q'} (hw : (0 : Q') < w)
    {K : Nat} (hK : 1 ≤ K) :
    centralLowerCubeState ∈
      centralPositiveHalfStates
        w (Q'.le_of_lt hw) K 0 := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨centralLowerCubeState_mem_centralHalfStates hK,
      centralLowerCubeRowMarginal_pos hw hK⟩

/-! ## 4. The spacing-dependent all-label cutoff retains the cube -/

theorem one_le_spacingLabelCutoff
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    1 ≤ spacingLabelCutoff w := by
  have hpower := spacingLabelCutoff_power_le hw0 hw1
  by_cases hpositive : 1 ≤ spacingLabelCutoff w
  · exact hpositive
  · have hzero : spacingLabelCutoff w = 0 := by omega
    rw [hzero] at hpower
    have himpossible :
        ¬ ((1 : Q') ≤ eighth) := by decide
    exact False.elim (himpossible hpower)

/-- The genuine non-vacuum cube row is present on the exact moving
all-label heat cutoff, not merely on a fixed cutoff-one surrogate. -/
theorem centralLowerCubeState_mem_spacingPositiveHalfStates
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    centralLowerCubeState ∈
      centralPositiveHalfStates
        w (Q'.le_of_lt hw0)
        (spacingLabelCutoff w) 0 :=
  centralLowerCubeState_mem_centralPositiveHalfStates
    hw0 (one_le_spacingLabelCutoff hw0 hw1)

end YMGap.Continuum.BF4CentralLowerCubePositiveRow

#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeMultiplicityProduct_one
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubePhysical_eq_componentLabel
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeMultiplicity_eq_one
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeMultiplicityProduct_eq_one
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubePhysicalFaceFactor_eqv
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubePhysicalTerm_eqv
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubePhysicalTerm_pos
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeState_ne_zero
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubePhysicalReflectedKernel_pos
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeActivity_le_reflectedKernel
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeNormalizedJoint_pos
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeRowMarginal_pos
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeState_mem_centralPositiveHalfStates
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.one_le_spacingLabelCutoff
#print axioms YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeState_mem_spacingPositiveHalfStates
