/-
# Exact spin-cube classification of BF4 vacuum-root spokes

The cutoff-independent active lower-link constraint hypergraph has a rigid
solution set.  Eighteen of its twenty-four lower-face variables occur in a
one-valent constraint and are therefore forced to the vacuum label.  Two
binary and three vacuum-padded ternary constraints then propagate one common
label across the six faces of the central lower cube.

Consequently, among retained half states, the active local constraints hold
exactly for the uniform central spin cubes.  This is an arbitrary-cutoff
classification; it is not yet an indexed-carrier enumeration, routing load
bound, spectral gap, continuum limit, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
import YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
import YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier
import YMGap.Continuum.Z4CanonicalPolymerUniverse

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeActiveScopeClassifier
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLinkMultiplicityClassifier
open YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeLocalConstraintClassifier
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open scoped List

/-! ## 1. Small-valence vacuum constraints -/

theorem explicitValenceMultiplicity_singleton_pos_iff_zero
    (cutoff spin : Nat) :
    0 < explicitValenceMultiplicity cutoff [spin].length
        (externalSpinsOfList [spin]) ↔
      spin = 0 := by
  change 0 < oneValentMultiplicity cutoff spin ↔ spin = 0
  rw [oneValentMultiplicity_eq_bool_zero]
  by_cases hspin : spin = 0 <;> simp [boolMultiplicity, hspin]

theorem explicitValenceMultiplicity_pair_pos_iff_eq
    (cutoff left right : Nat) :
    0 < explicitValenceMultiplicity cutoff [left, right].length
        (externalSpinsOfList [left, right]) ↔
      left = right := by
  change 0 < twoValentMultiplicity cutoff left right ↔ left = right
  rw [twoValentMultiplicity_eq_bool_zero_output,
    fusionOK_zero_output_eq_decide]
  by_cases heq : left = right <;> simp [boolMultiplicity, heq]

theorem explicitValenceMultiplicity_pair_zero_pos_iff_eq
    (cutoff left right : Nat) :
    0 < explicitValenceMultiplicity cutoff [left, right, 0].length
        (externalSpinsOfList [left, right, 0]) ↔
      left = right := by
  change 0 < boolMultiplicity (fusionOK left right 0) ↔ left = right
  rw [fusionOK_zero_output_eq_decide]
  by_cases heq : left = right <;> simp [boolMultiplicity, heq]

theorem explicitValenceMultiplicity_middle_zero_pos_iff_eq
    (cutoff left right : Nat) :
    0 < explicitValenceMultiplicity cutoff [left, 0, right].length
        (externalSpinsOfList [left, 0, right]) ↔
      left = right := by
  change 0 < boolMultiplicity (fusionOK left 0 right) ↔ left = right
  rw [fusionOK_zero_right_eq_decide]
  by_cases heq : left = right <;>
    simp [boolMultiplicity, heq, eq_comm]

/-! ## 2. A finite unary-pin certificate -/

private def fallbackLowerLink : Z4Link := ((0, 0, 0, 0), .x0)

private def centralVacuumLowerActiveLinkAt (index : Nat) : Z4Link :=
  (centralLowerLinks 0).getD index fallbackLowerLink

private def centralVacuumLowerUnaryPinLinkIndex (faceId : Nat) : Nat :=
  match faceId with
  | 10 => 12
  | 12 => 14
  | 18 => 17
  | 21 => 21
  | 27 => 22
  | 28 => 24
  | 30 => 26
  | 36 => 30
  | 37 => 32
  | 45 => 34
  | 46 => 35
  | 48 => 37
  | 54 => 38
  | 55 => 40
  | 57 => 41
  | 63 => 42
  | 64 => 44
  | 66 => 46
  | _ => 0

private theorem centralLowerFaceIds_zero_checked :
    centralLowerFaceIds 0 =
      [0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30,
        36, 37, 39, 45, 46, 48, 54, 55, 57, 63, 64, 66] := by
  decide

/-- Every lower face outside the central cube has a certified one-valent
active link whose sole source coordinate is that face. -/
theorem centralVacuumLower_unaryPinLink_sound
    (faceId : Nat) (hlower : faceId ∈ centralLowerFaceIds 0)
    (hoffCube : faceId ∉ centralLowerCubeFaceIds) :
    let link := centralVacuumLowerActiveLinkAt
      (centralVacuumLowerUnaryPinLinkIndex faceId)
    link ∈ centralLowerLinks 0 ∧
      centralVacuumLowerActiveIncidentFaceIds link = [faceId] := by
  rw [centralLowerFaceIds_zero_checked] at hlower
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlower
  rcases hlower with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (hoffCube (by decide)) | decide

/-! ## 3. Constraint propagation -/

private theorem centralVacuumLowerActiveSpins_eq_of_scope
    (source : EdgeLabelling) (link : Z4Link) (ids : List Nat)
    (hscope : centralVacuumLowerActiveIncidentFaceIds link = ids) :
    centralVacuumLowerActiveSpins source link = ids.map source := by
  unfold centralVacuumLowerActiveSpins
  rw [hscope]

theorem centralVacuumLower_source_eq_zero_off_cube
    (K : Nat) (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0)
    (hadmissible :
      centralVacuumLowerActiveScopesAdmissibleB K source = true)
    (faceId : Nat) (hoffCube : faceId ∉ centralLowerCubeFaceIds) :
    source faceId = 0 := by
  have hsourceSound :=
    boundedEdgeLabellings_sound K (centralLowerFaceIds 0) source hsource
  by_cases hlower : faceId ∈ centralLowerFaceIds 0
  · let link := centralVacuumLowerActiveLinkAt
      (centralVacuumLowerUnaryPinLinkIndex faceId)
    have hwitness := centralVacuumLower_unaryPinLink_sound
      faceId hlower hoffCube
    have hpositive :
        0 < centralVacuumLowerActiveMultiplicity K source link :=
      of_decide_eq_true
        (List.all_eq_true.mp hadmissible link hwitness.1)
    have hspins :
        centralVacuumLowerActiveSpins source link = [source faceId] := by
      exact centralVacuumLowerActiveSpins_eq_of_scope
        source link [faceId] hwitness.2
    unfold centralVacuumLowerActiveMultiplicity at hpositive
    rw [hspins] at hpositive
    exact (explicitValenceMultiplicity_singleton_pos_iff_zero
      (linkAuxiliaryCutoff K) (source faceId)).mp hpositive
  · exact hsourceSound.2 faceId hlower

private theorem centralVacuumLower_binaryScope01 :
    let link := centralVacuumLowerActiveLinkAt 0
    link ∈ centralLowerLinks 0 ∧
      centralVacuumLowerActiveIncidentFaceIds link = [0, 1] := by
  decide

private theorem centralVacuumLower_binaryScope03 :
    let link := centralVacuumLowerActiveLinkAt 1
    link ∈ centralLowerLinks 0 ∧
      centralVacuumLowerActiveIncidentFaceIds link = [0, 3] := by
  decide

private theorem centralVacuumLower_paddedScope19 :
    let link := centralVacuumLowerActiveLinkAt 5
    link ∈ centralLowerLinks 0 ∧
      centralVacuumLowerActiveIncidentFaceIds link = [1, 9, 10] := by
  decide

private theorem centralVacuumLower_paddedScope319 :
    let link := centralVacuumLowerActiveLinkAt 8
    link ∈ centralLowerLinks 0 ∧
      centralVacuumLowerActiveIncidentFaceIds link = [3, 19, 21] := by
  decide

private theorem centralVacuumLower_paddedScope039 :
    let link := centralVacuumLowerActiveLinkAt 3
    link ∈ centralLowerLinks 0 ∧
      centralVacuumLowerActiveIncidentFaceIds link = [0, 36, 39] := by
  decide

/-- The active lower-link CSP is rigid: every retained admissible source is
the uniform central spin cube labelled by its value on face zero. -/
theorem centralVacuumLowerActiveScopesAdmissibleB_true_implies_spinCube
    (K : Nat) (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0)
    (hadmissible :
      centralVacuumLowerActiveScopesAdmissibleB K source = true) :
    source = centralLowerSpinCubeState (source 0) := by
  have hpositive := fun (link : Z4Link) (hlink : link ∈ centralLowerLinks 0) =>
    of_decide_eq_true (List.all_eq_true.mp hadmissible link hlink)
  have h01 : source 0 = source 1 := by
    let link := centralVacuumLowerActiveLinkAt 0
    have hwitness := centralVacuumLower_binaryScope01
    have hpos := hpositive link hwitness.1
    have hspins : centralVacuumLowerActiveSpins source link =
        [source 0, source 1] :=
      centralVacuumLowerActiveSpins_eq_of_scope
        source link [0, 1] hwitness.2
    unfold centralVacuumLowerActiveMultiplicity at hpos
    rw [hspins] at hpos
    exact (explicitValenceMultiplicity_pair_pos_iff_eq
      (linkAuxiliaryCutoff K) (source 0) (source 1)).mp hpos
  have h03 : source 0 = source 3 := by
    let link := centralVacuumLowerActiveLinkAt 1
    have hwitness := centralVacuumLower_binaryScope03
    have hpos := hpositive link hwitness.1
    have hspins : centralVacuumLowerActiveSpins source link =
        [source 0, source 3] :=
      centralVacuumLowerActiveSpins_eq_of_scope
        source link [0, 3] hwitness.2
    unfold centralVacuumLowerActiveMultiplicity at hpos
    rw [hspins] at hpos
    exact (explicitValenceMultiplicity_pair_pos_iff_eq
      (linkAuxiliaryCutoff K) (source 0) (source 3)).mp hpos
  have h10 : source 10 = 0 :=
    centralVacuumLower_source_eq_zero_off_cube
      K source hsource hadmissible 10 (by decide)
  have h19 : source 1 = source 9 := by
    let link := centralVacuumLowerActiveLinkAt 5
    have hwitness := centralVacuumLower_paddedScope19
    have hpos := hpositive link hwitness.1
    have hspins : centralVacuumLowerActiveSpins source link =
        [source 1, source 9, source 10] :=
      centralVacuumLowerActiveSpins_eq_of_scope
        source link [1, 9, 10] hwitness.2
    unfold centralVacuumLowerActiveMultiplicity at hpos
    rw [hspins, h10] at hpos
    exact (explicitValenceMultiplicity_pair_zero_pos_iff_eq
      (linkAuxiliaryCutoff K) (source 1) (source 9)).mp hpos
  have h21 : source 21 = 0 :=
    centralVacuumLower_source_eq_zero_off_cube
      K source hsource hadmissible 21 (by decide)
  have h319 : source 3 = source 19 := by
    let link := centralVacuumLowerActiveLinkAt 8
    have hwitness := centralVacuumLower_paddedScope319
    have hpos := hpositive link hwitness.1
    have hspins : centralVacuumLowerActiveSpins source link =
        [source 3, source 19, source 21] :=
      centralVacuumLowerActiveSpins_eq_of_scope
        source link [3, 19, 21] hwitness.2
    unfold centralVacuumLowerActiveMultiplicity at hpos
    rw [hspins, h21] at hpos
    exact (explicitValenceMultiplicity_pair_zero_pos_iff_eq
      (linkAuxiliaryCutoff K) (source 3) (source 19)).mp hpos
  have h36 : source 36 = 0 :=
    centralVacuumLower_source_eq_zero_off_cube
      K source hsource hadmissible 36 (by decide)
  have h039 : source 0 = source 39 := by
    let link := centralVacuumLowerActiveLinkAt 3
    have hwitness := centralVacuumLower_paddedScope039
    have hpos := hpositive link hwitness.1
    have hspins : centralVacuumLowerActiveSpins source link =
        [source 0, source 36, source 39] :=
      centralVacuumLowerActiveSpins_eq_of_scope
        source link [0, 36, 39] hwitness.2
    unfold centralVacuumLowerActiveMultiplicity at hpos
    rw [hspins, h36] at hpos
    exact (explicitValenceMultiplicity_middle_zero_pos_iff_eq
      (linkAuxiliaryCutoff K) (source 0) (source 39)).mp hpos
  have h1 : source 1 = source 0 := h01.symm
  have h3 : source 3 = source 0 := h03.symm
  have h9 : source 9 = source 0 := h19.symm.trans h1
  have h19' : source 19 = source 0 := h319.symm.trans h3
  have h39 : source 39 = source 0 := h039.symm
  funext faceId
  by_cases hcube : faceId ∈ centralLowerCubeFaceIds
  · simp only [centralLowerCubeFaceIds, List.mem_cons,
      List.not_mem_nil, or_false] at hcube
    rcases hcube with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [centralLowerSpinCubeState, centralLowerCubeFaceIds]
    · simpa [centralLowerSpinCubeState, centralLowerCubeFaceIds] using h1
    · simpa [centralLowerSpinCubeState, centralLowerCubeFaceIds] using h3
    · simpa [centralLowerSpinCubeState, centralLowerCubeFaceIds] using h9
    · simpa [centralLowerSpinCubeState, centralLowerCubeFaceIds] using h19'
    · simpa [centralLowerSpinCubeState, centralLowerCubeFaceIds] using h39
  · rw [centralLowerSpinCubeState_eq_zero_off_cube (source 0) hcube]
    exact centralVacuumLower_source_eq_zero_off_cube
      K source hsource hadmissible faceId hcube

/-! ## 4. Exact arbitrary-cutoff classifier -/

/-- Among retained half states, the active lower-link constraints hold
exactly for the uniform central spin cube determined by face zero. -/
theorem centralVacuumLowerActiveScopesAdmissibleB_true_iff_spinCube
    (K : Nat) (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    centralVacuumLowerActiveScopesAdmissibleB K source = true ↔
      source = centralLowerSpinCubeState (source 0) := by
  constructor
  · exact centralVacuumLowerActiveScopesAdmissibleB_true_implies_spinCube
      K source hsource
  · intro hcube
    have hsourceSound :=
      boundedEdgeLabellings_sound K (centralLowerFaceIds 0) source hsource
    have hzeroLower : 0 ∈ centralLowerFaceIds 0 := by decide
    have hspin : source 0 ≤ K := by
      have hlt := hsourceSound.1 0 hzeroLower
      omega
    have hfull :
        centralVacuumLowerLinksAdmissibleB K
          (centralLowerSpinCubeState (source 0)) = true := by
      apply (centralVacuumLowerLinksAdmissibleB_true_iff
        K (centralLowerSpinCubeState (source 0))).mpr
      intro link hlink
      have hpos := centralLowerSpinCube_linkMultiplicity_pos
        hspin link (mem_centralLowerLinks.mp hlink).1
      simpa [centralVacuumLowerPhysical, centralLowerSpinCubePhysical,
        centralExtent] using hpos
    have heq := centralVacuumLowerLinksAdmissibleB_eq_activeScopes
      K (centralLowerSpinCubeState (source 0))
      (centralLowerSpinCubeState_mem_centralHalfStates hspin)
    rw [heq] at hfull
    rw [hcube]
    exact hfull

/-! ## 5. Exact indexed root-spoke carrier and count -/

/-- The computable spin-cube carrier indices are injective on the complete
cutoff-admitted label range. -/
theorem centralLowerSpinCubeIndex_injective_on
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') < w)
    {K left right : Nat} (hleft : left ≤ K) (hright : right ≤ K)
    (heq : centralLowerSpinCubeIndex w (YMGap.Constructive.Q'.le_of_lt hw)
        K left =
      centralLowerSpinCubeIndex w (YMGap.Constructive.Q'.le_of_lt hw)
        K right) :
    left = right := by
  have hstates : centralLowerSpinCubeState left =
      centralLowerSpinCubeState right := by
    rw [← centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hleft,
      ← centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hright,
      heq]
  exact centralLowerSpinCubeState_injective hstates

/-- A finite-sector vertex is a positive predecessor of the vacuum root
exactly when it is the computable carrier index of one admitted spin cube. -/
theorem mem_centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_iff_spinCubeIndex
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') < w)
    {K source : Nat} :
    source ∈ centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
        w (YMGap.Constructive.Q'.le_of_lt hw) K ↔
      ∃ spin, spin ≤ K ∧
        source = centralLowerSpinCubeIndex
          w (YMGap.Constructive.Q'.le_of_lt hw) K spin := by
  rw [centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_activeScopes
    (YMGap.Constructive.Q'.le_of_lt hw) hw K]
  constructor
  · intro hsource
    have hparts := List.mem_filter.mp hsource
    have hsectorState :
        centralPhysicalFiniteStateAt w
            (YMGap.Constructive.Q'.le_of_lt hw) K 0 source ∈
          centralPhysicalFiniteVacuumSectorStates
            w (YMGap.Constructive.Q'.le_of_lt hw) K 0 :=
      centralPhysicalFiniteVacuumSectorState_mem_of_index
        w (YMGap.Constructive.Q'.le_of_lt hw) K 0 hparts.1 rfl
    have hhalf := centralPhysicalFiniteVacuumSectorState_mem_halfStates
      w (YMGap.Constructive.Q'.le_of_lt hw) K 0 hsectorState
    have hcube :=
      (centralVacuumLowerActiveScopesAdmissibleB_true_iff_spinCube
        K (centralPhysicalFiniteStateAt w
          (YMGap.Constructive.Q'.le_of_lt hw) K 0 source) hhalf).mp
        hparts.2
    let spin := centralPhysicalFiniteStateAt w
      (YMGap.Constructive.Q'.le_of_lt hw) K 0 source 0
    have hspin : spin ≤ K := by
      have hsound := boundedEdgeLabellings_sound K
        (centralLowerFaceIds 0)
        (centralPhysicalFiniteStateAt w
          (YMGap.Constructive.Q'.le_of_lt hw) K 0 source) hhalf
      have hlt := hsound.1 0 (by decide : 0 ∈ centralLowerFaceIds 0)
      unfold spin
      omega
    refine ⟨spin, hspin, ?_⟩
    apply centralPhysicalFiniteStateAt_injective_of_lt
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w (YMGap.Constructive.Q'.le_of_lt hw) K 0 hparts.1)
      (centralLowerSpinCubeIndex_lt hw hspin)
    rw [centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin]
    exact hcube
  · rintro ⟨spin, hspin, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨centralLowerSpinCubeIndex_mem_vacuumSector hw hspin, ?_⟩
    rw [centralPhysicalFiniteStateAt_spinCubeIndex_eq hw hspin]
    apply (centralVacuumLowerActiveScopesAdmissibleB_true_iff_spinCube
      K (centralLowerSpinCubeState spin)
      (centralLowerSpinCubeState_mem_centralHalfStates hspin)).mpr
    have hfaceZero : centralLowerSpinCubeState spin 0 = spin :=
      centralLowerSpinCubeState_eq_spin_on_cube spin (by decide)
    rw [hfaceZero]

/-- The explicit list of all cutoff-admitted spin-cube root spokes. -/
def centralLowerSpinCubeRootIndices
    (w : YMGap.Constructive.Q')
    (hw : (0 : YMGap.Constructive.Q') ≤ w) (K : Nat) : List Nat :=
  (List.range (K + 1)).map (centralLowerSpinCubeIndex w hw K)

theorem centralLowerSpinCubeRootIndices_length
    (w : YMGap.Constructive.Q')
    (hw : (0 : YMGap.Constructive.Q') ≤ w) (K : Nat) :
    (centralLowerSpinCubeRootIndices w hw K).length = K + 1 := by
  simp [centralLowerSpinCubeRootIndices]

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

theorem centralLowerSpinCubeRootIndices_nodup
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') < w) (K : Nat) :
    (centralLowerSpinCubeRootIndices
      w (YMGap.Constructive.Q'.le_of_lt hw) K).Nodup := by
  unfold centralLowerSpinCubeRootIndices
  apply nodup_map_of_injOn
  · exact rangeNodupLocal _
  · intro left hleft right hright heq
    exact centralLowerSpinCubeIndex_injective_on hw
      (by have hlt := List.mem_range.mp hleft; omega)
      (by have hlt := List.mem_range.mp hright; omega) heq

/-- The production positive root-predecessor list is, up to its inherited
finite-sector ordering, exactly the `K + 1` spin-cube indices. -/
theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_perm_spinCubeRootIndices
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') < w) (K : Nat) :
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
      w (YMGap.Constructive.Q'.le_of_lt hw) K).Perm
      (centralLowerSpinCubeRootIndices
        w (YMGap.Constructive.Q'.le_of_lt hw) K) := by
  apply perm_of_nodup_mem_iff
  · unfold centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
    exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (YMGap.Constructive.Q'.le_of_lt hw) K 0)
  · exact centralLowerSpinCubeRootIndices_nodup hw K
  · intro source
    constructor
    · intro hsource
      obtain ⟨spin, hspin, rfl⟩ :=
        (mem_centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_iff_spinCubeIndex
          hw).mp hsource
      unfold centralLowerSpinCubeRootIndices
      apply List.mem_map.mpr
      exact ⟨spin, List.mem_range.mpr (by omega), rfl⟩
    · intro hsource
      unfold centralLowerSpinCubeRootIndices at hsource
      obtain ⟨spin, hspin, heq⟩ := List.mem_map.mp hsource
      apply
        (mem_centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_iff_spinCubeIndex
          hw).mpr
      exact ⟨spin, by have hlt := List.mem_range.mp hspin; omega, heq.symm⟩

/-- There are exactly `K + 1` positive production spokes entering the vacuum
root at every cutoff and every strictly positive coupling. -/
theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_cutoff_succ
    {w : YMGap.Constructive.Q'}
    (hw : (0 : YMGap.Constructive.Q') < w) (K : Nat) :
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
      w (YMGap.Constructive.Q'.le_of_lt hw) K).length = K + 1 := by
  rw [(centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_perm_spinCubeRootIndices
      hw K).length_eq,
    centralLowerSpinCubeRootIndices_length]

end YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.explicitValenceMultiplicity_singleton_pos_iff_zero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.centralVacuumLower_unaryPinLink_sound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.centralVacuumLower_source_eq_zero_off_cube
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.centralVacuumLowerActiveScopesAdmissibleB_true_implies_spinCube
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.centralVacuumLowerActiveScopesAdmissibleB_true_iff_spinCube
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.mem_centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_iff_spinCubeIndex
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_perm_spinCubeRootIndices
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeSpinCubeClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_cutoff_succ
