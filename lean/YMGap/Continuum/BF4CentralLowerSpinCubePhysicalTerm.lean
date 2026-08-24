/-
# Exact selected physical term of an arbitrary spin cube

For the closed lower cube labelled by an arbitrary cutoff-admitted spin,
every touched link sees exactly one equal pair and otherwise only vacuum
labels.  Vacuum insertion and permutation invariance reduce its local fusion
multiplicity to the two-valent singlet count, which is exactly one.

Consequently the complete link product is one and the selected zero-boundary
physical term is exactly the sixth power of the heat-kernel coefficient of
the spin.  This makes the remaining raw-row ceiling fully explicit; it does
not prove that ceiling, a full-sector gap, a continuum theory, or the Clay
conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

namespace YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Equal pair plus vacuum labels has one fusion path -/

private theorem zeroExtension_nil_of_all_zero :
    ∀ spins : List Nat,
      (∀ spin, spin ∈ spins → spin = 0) →
      ZeroExtension [] spins
  | [], _hzero => ZeroExtension.nil
  | head :: tail, hzero => by
      have hhead : head = 0 := hzero head List.mem_cons_self
      subst head
      exact ZeroExtension.insertZero
        (zeroExtension_nil_of_all_zero tail
          (fun spin hspin =>
            hzero spin (List.mem_cons_of_mem 0 hspin)))

private theorem equalPair_zeroExtension
    (spin : Nat) (rest : List Nat)
    (hrest : ∀ value, value ∈ rest → value = 0) :
    ZeroExtension [spin, spin] (spin :: spin :: rest) :=
  ZeroExtension.keep spin
    (ZeroExtension.keep spin
      (zeroExtension_nil_of_all_zero rest hrest))

private theorem fusionPathMultiplicity_equalPair_eq_one
    (cutoff spin : Nat) :
    fusionPathMultiplicity cutoff [spin, spin] = 1 := by
  rw [fusionPathMultiplicity_two,
    fusionOK_zero_output_eq_decide]
  simp [boolMultiplicity]

private theorem fusionPathMultiplicity_equalPair_zeros_eq_one
    {cutoff spin : Nat} (hspin : spin ≤ cutoff)
    (rest : List Nat)
    (hrest : ∀ value, value ∈ rest → value = 0) :
    fusionPathMultiplicity cutoff (spin :: spin :: rest) = 1 := by
  have hpairBounded : SpinsBounded cutoff [spin, spin] := by
    intro value hvalue
    have hvalueSpin : value = spin := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self]
        using hvalue
    subst value
    exact hspin
  exact Eq.trans
    (fusionPathMultiplicity_zeroExtension
      (equalPair_zeroExtension spin rest hrest) hpairBounded).symm
    (fusionPathMultiplicity_equalPair_eq_one cutoff spin)

/-! ## 2. Every local selected-cube multiplicity is exactly one -/

private theorem spinCubePhysical_bounded_local
    {K spin : Nat} (hspin : spin ≤ K) :
    SlabFaceLabellingBounded K 1
      (centralLowerSpinCubePhysical spin) := by
  intro id _hid
  exact Nat.le_trans (centralLowerSpinCubePhysical_le spin id) hspin

private theorem mapped_zero_values
    (ids : List Nat) :
    ∀ value,
      value ∈ ids.map zeroEdgeLabelling → value = 0 := by
  intro value hvalue
  obtain ⟨id, _hid, hvalue⟩ := List.mem_map.mp hvalue
  exact hvalue.symm

theorem centralLowerSpinCube_linkMultiplicity_eq_one
    {K spin : Nat} (hspin : spin ≤ K)
    (link : YMGap.Continuum.ClusterCount4DProgress.Z4Link)
    (hlink : link ∈ boundaryCompleteSlabLinks 1) :
    slabExplicitLinkMultiplicity K 1
        (centralLowerSpinCubePhysical spin) link = 1 := by
  let actual :=
    (slabIncidentPlaqIds 1 link).map
      (centralLowerSpinCubePhysical spin)
  let vacuum :=
    (slabIncidentPlaqIds 1 link).map zeroEdgeLabelling
  let rest :=
    (centralLowerCubeUnselectedIncidentIds link).map zeroEdgeLabelling
  have hactualLength : actual.length ≤ 6 := by
    unfold actual
    simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six 1 link
  have hactualBounded : SpinsBounded K actual :=
    slabIncidentSpins_bounded
      (spinCubePhysical_bounded_local hspin) link
  have hvacuumPerm :=
    zero_incident_spins_perm_selected_remainder link
  have hactualPerm :=
    spinCube_incident_spins_perm_selected_remainder spin link
  rcases centralLowerCube_selected_length_zero_or_two link hlink
      with hzero | htwo
  · rw [hzero] at hvacuumPerm hactualPerm
    simp only [List.replicate_zero, List.nil_append] at hvacuumPerm
    simp only [List.replicate_zero, List.nil_append] at hactualPerm
    unfold slabExplicitLinkMultiplicity
    exact Eq.trans
      (explicitValenceMultiplicity_physical_perm
        (hactualPerm.trans hvacuumPerm.symm)
        hactualLength hactualBounded)
      (by
        change slabExplicitLinkMultiplicity K 1
          zeroEdgeLabelling link = 1
        exact slabExplicitLinkMultiplicity_zero_eq_one K 1 link)
  · rw [htwo] at hactualPerm
    simp only [List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append] at hactualPerm
    let canonical := spin :: spin :: rest
    have hcanonicalLength : canonical.length ≤ 6 := by
      rw [← hactualPerm.length_eq]
      exact hactualLength
    have hcanonicalBounded : SpinsBounded K canonical :=
      spinsBounded_of_perm hactualPerm hactualBounded
    have hcanonicalAux : SpinsBounded
        (linkAuxiliaryCutoff K) canonical := by
      intro value hvalue
      exact Nat.le_trans (hcanonicalBounded value hvalue)
        (externalCutoff_le_linkAuxiliaryCutoff K)
    have hspinAux : spin ≤ linkAuxiliaryCutoff K :=
      Nat.le_trans hspin (externalCutoff_le_linkAuxiliaryCutoff K)
    have hcanonicalMultiplicity :
        explicitValenceMultiplicity
            (linkAuxiliaryCutoff K) canonical.length
            (externalSpinsOfList canonical) = 1 := by
      rw [← fusionPathMultiplicity_eq_explicit_of_length_le_six
        canonical hcanonicalLength hcanonicalAux]
      exact fusionPathMultiplicity_equalPair_zeros_eq_one
        hspinAux rest (mapped_zero_values _)
    unfold slabExplicitLinkMultiplicity
    exact Eq.trans
      (explicitValenceMultiplicity_physical_perm
        hactualPerm hactualLength hactualBounded)
      hcanonicalMultiplicity

private theorem natListProduct_spinCube_eq_one
    {K spin : Nat} (hspin : spin ≤ K) :
    ∀ links : List YMGap.Continuum.ClusterCount4DProgress.Z4Link,
      (∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks 1) →
      natListProduct
        (slabExplicitLinkMultiplicity K 1
          (centralLowerSpinCubePhysical spin)) links = 1
  | [], _hlinks => rfl
  | head :: tail, hlinks => by
      simp only [natListProduct]
      rw [centralLowerSpinCube_linkMultiplicity_eq_one
        hspin head (hlinks head List.mem_cons_self),
        natListProduct_spinCube_eq_one hspin tail
          (fun link hlink =>
            hlinks link (List.mem_cons_of_mem head hlink))]

theorem centralLowerSpinCube_linkProduct_eq_one
    {K spin : Nat} (hspin : spin ≤ K) :
    slabExplicitLinkMultiplicityProduct K 1
      (centralLowerSpinCubePhysical spin) = 1 := by
  unfold slabExplicitLinkMultiplicityProduct
  exact natListProduct_spinCube_eq_one hspin
    (boundaryCompleteSlabLinks 1) (fun _link hlink => hlink)

/-! ## 3. The selected term is exactly the sixth heat coefficient power -/

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem eliminateLinks_congr_on_local
    (left right : Nat → Q') :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _hagree => Q'.eqv_refl _
  | id :: rest, hagree =>
      qmul_congr_local
        (hagree id List.mem_cons_self)
        (eliminateLinks_congr_on_local left right rest
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem id hitem)))

private theorem eliminateLinks_indicator_pow_local
    (selected : List Nat) (coefficient : Q') :
    ∀ ids : List Nat,
      eliminateLinks
          (fun id => if id ∈ selected then coefficient else 1)
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
        exact qmul_congr_local (Q'.eqv_refl _)
          (eliminateLinks_indicator_pow_local
            selected coefficient rest)
      · simp only [eliminateLinks, hselected,
          List.filter_cons, decide_false]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left 1 _ _
            (eliminateLinks_indicator_pow_local
              selected coefficient rest))
          (Q'.one_mul_eqv _)

theorem centralLowerSpinCubePhysicalFaceFactor_eqv
    (w : Q') {K spin : Nat} (hspin : spin ≤ K) :
    slabParametricKPhysicalFaceFactor w K 1
        (centralLowerSpinCubePhysical spin) ≈
      (coeffW w spin) ^ 6 := by
  unfold slabParametricKPhysicalFaceFactor
  have hcoeff :
      eliminateLinks
          (fun id =>
            coeffAt (heatKernelPacket K w)
              (centralLowerSpinCubePhysical spin id))
          (slabPhysicalFaceEdges 1) ≈
        eliminateLinks
          (fun id =>
            if id ∈ centralLowerCubeFaceIds
            then coeffW w spin else 1)
          (slabPhysicalFaceEdges 1) := by
    apply eliminateLinks_congr_on_local
    intro id _hid
    by_cases hcube : id ∈ centralLowerCubeFaceIds
    · rw [centralLowerSpinCubePhysical_eq_state,
        centralLowerSpinCubeState_eq_spin_on_cube spin hcube,
        coeffAt_heatKernelPacket (Nat.lt_succ_of_le hspin),
        if_pos hcube]
      exact Q'.eqv_refl _
    · rw [centralLowerSpinCubePhysical_eq_state,
        centralLowerSpinCubeState_eq_zero_off_cube spin hcube,
        coeffAt_heatKernelPacket (Nat.zero_lt_succ K),
        coeffW_zero, if_neg hcube]
      exact Q'.eqv_refl _
  have hpower := eliminateLinks_indicator_pow_local
    centralLowerCubeFaceIds (coeffW w spin)
    (slabPhysicalFaceEdges 1)
  have hcount :
      ((slabPhysicalFaceEdges 1).filter
        (fun id => decide (id ∈ centralLowerCubeFaceIds))).length = 6 := by
    decide
  rw [hcount] at hpower
  exact Q'.eqv_trans _ _ _ hcoeff hpower

theorem centralLowerSpinCubePhysicalTerm_eqv
    (w : Q') {K spin : Nat} (hspin : spin ≤ K) :
    slabParametricKPhysicalTerm w K 1
        (centralLowerSpinCubePhysical spin) ≈
      (coeffW w spin) ^ 6 := by
  unfold slabParametricKPhysicalTerm
  rw [centralLowerSpinCube_linkProduct_eq_one hspin]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ 1
      (centralLowerSpinCubePhysicalFaceFactor_eqv w hspin))
    (Q'.mul_one_eqv _)

end YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm.centralLowerSpinCube_linkMultiplicity_eq_one
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm.centralLowerSpinCube_linkProduct_eq_one
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm.centralLowerSpinCubePhysicalFaceFactor_eqv
#print axioms YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm.centralLowerSpinCubePhysicalTerm_eqv
