/-
# Total cutoff-one whole-slab recoupling kernel

The globally recoupled row is canonically normalized whenever the fine Gibbs
term is strictly positive.  A finite Markov kernel, however, must also be
defined on the enumerated rows whose physical Gibbs weight is exactly zero.
This module supplies a reflection-equivariant stochastic completion on those
null rows and packages the result as the literal `FiniteSlabKernel`.

The completion is deliberately separated from the physical content:

* positive Gibbs rows use `wholeSlabRecouplingConditionalKernel`;
* nonpositive rows use a deterministic supported Dirac row;
* nonnegativity of the Gibbs summand makes every nonpositive listed row a
  zero-mass row, so the completion cannot alter the physical pushforward.

Two one-plaquette rows certify source dependence of the total matrix.  Their
odd incidence makes their physical Gibbs terms nonpositive (indeed exactly
zero), so this witness is bookkeeping and is not advertised as positive-mass
source dependence.

## Axiom gate

Finite exact-rational algebra and previously audited corrected-slab geometry
only.  No `Classical.*`, `sorry`, `native_decide`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
import YMGap.Continuum.CompactDualWholeSlabConditionalReflection
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.CompactDualCutoffOneTotalKernel

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabConditionalReflection
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Two canonical one-plaquette rows -/

/-- A temporal plaquette crossing the reflection plane. -/
def centralFixedPlaquette (half : Nat) : Z4Plaq :=
  ((0, 0, 0, half), .p03)

/-- A spatial plaquette on the bottom boundary slice. -/
def bottomPlaquette : Z4Plaq :=
  ((0, 0, 0, 0), .p01)

theorem centralFixedPlaquette_mem_slab (half : Nat) :
    centralFixedPlaquette half ∈
      boundaryCompleteSlabPlaquettes (centralExtent half) := by
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · simp [mem_boxPlaquettes, centralFixedPlaquette, centralExtent] <;> omega
  · simp [centralFixedPlaquette, plaquetteTimeAdmissible, centralExtent] <;>
      omega

theorem bottomPlaquette_mem_slab (half : Nat) :
    bottomPlaquette ∈
      boundaryCompleteSlabPlaquettes (centralExtent half) := by
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · simp [mem_boxPlaquettes, bottomPlaquette, centralExtent]
  · simp [bottomPlaquette, plaquetteTimeAdmissible, centralExtent]

theorem centralFixedPlaquette_reflection (half : Nat) :
    timeReflectPlaquette (centralExtent half)
        (centralFixedPlaquette half) =
      centralFixedPlaquette half := by
  simp [centralFixedPlaquette, centralExtent, timeReflectPlaquette]

theorem centralFixedPlaquette_ne_bottom (half : Nat) :
    centralFixedPlaquette half ≠ bottomPlaquette := by
  intro heq
  have hplane := congrArg Prod.snd heq
  cases hplane

def fixedSingletonLabelling (D : SlabPhysicalData) : EdgeLabelling :=
  slabBinarySupportLabelling D.extent [centralFixedPlaquette D.half]

def bottomSingletonLabelling (D : SlabPhysicalData) : EdgeLabelling :=
  slabBinarySupportLabelling D.extent [bottomPlaquette]

theorem fixedSingletonLabelling_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff) :
    fixedSingletonLabelling D ∈ D.physicalLabellings := by
  exact slabBinarySupportLabelling_mem hcutoff _

theorem bottomSingletonLabelling_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff) :
    bottomSingletonLabelling D ∈ D.physicalLabellings := by
  exact slabBinarySupportLabelling_mem hcutoff _

private theorem exists_physical_id_of_slab_mem
    {extent : Nat} {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boundaryCompleteSlabPlaquettes extent) :
    ∃ id, id ∈ slabPhysicalFaceEdges extent ∧
      slabPlaquetteAt extent id = plaquette := by
  obtain ⟨id, hindexed⟩ := exists_mem_enumerate hplaquette
  refine ⟨id, ?_, ?_⟩
  · unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr (enumerate_index_lt hindexed)
  · exact enumerate_getD_of_mem fallbackPlaquette hindexed

theorem fixedSingletonLabelling_ne_zero (D : SlabPhysicalData) :
    fixedSingletonLabelling D ≠ zeroEdgeLabelling := by
  obtain ⟨id, hid, hlookup⟩ :=
    exists_physical_id_of_slab_mem
      (centralFixedPlaquette_mem_slab D.half)
  intro heq
  have hpoint := congrArg (fun label => label id) heq
  simp only [fixedSingletonLabelling, SlabPhysicalData.extent] at hpoint
  rw [slabBinarySupportLabelling_eq_indicator hid, hlookup] at hpoint
  simp [zeroEdgeLabelling] at hpoint

theorem bottomSingletonLabelling_ne_fixed
    (D : SlabPhysicalData) :
    bottomSingletonLabelling D ≠ fixedSingletonLabelling D := by
  obtain ⟨id, hid, hlookup⟩ :=
    exists_physical_id_of_slab_mem
      (centralFixedPlaquette_mem_slab D.half)
  intro heq
  have hpoint := congrArg (fun label => label id) heq
  simp only [bottomSingletonLabelling, fixedSingletonLabelling,
    SlabPhysicalData.extent] at hpoint
  rw [slabBinarySupportLabelling_eq_indicator hid,
    slabBinarySupportLabelling_eq_indicator hid, hlookup] at hpoint
  simp [centralFixedPlaquette_ne_bottom D.half] at hpoint

/-! ## 2. Supported finite Dirac rows without function-space decidable equality -/

def supportedLabellingEqB
    (ids : List Nat) (left right : EdgeLabelling) : Bool :=
  ids.all fun id => decide (left id = right id)

theorem supportedLabellingEqB_true_of_eq
    (ids : List Nat) {left right : EdgeLabelling}
    (heq : left = right) :
    supportedLabellingEqB ids left right = true := by
  subst right
  unfold supportedLabellingEqB
  apply List.all_eq_true.mpr
  intro id _
  simp

theorem edgeLabelling_eq_of_eq_on_supported
    {ids : List Nat} {left right : EdgeLabelling}
    (hleft : ∀ id, id ∉ ids → left id = 0)
    (hright : ∀ id, id ∉ ids → right id = 0)
    (hagree : ∀ id, id ∈ ids → left id = right id) :
    left = right := by
  funext id
  by_cases hid : id ∈ ids
  · exact hagree id hid
  · rw [hleft id hid, hright id hid]

theorem supportedLabellingEqB_true_iff
    {K : Nat} {ids : List Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K ids)
    (hright : right ∈ boundedEdgeLabellings K ids) :
    supportedLabellingEqB ids left right = true ↔ left = right := by
  constructor
  · intro hall
    apply edgeLabelling_eq_of_eq_on_supported
      (boundedEdgeLabellings_sound K ids left hleft).2
      (boundedEdgeLabellings_sound K ids right hright).2
    intro id hid
    have hdecision :=
      List.all_eq_true.mp hall id hid
    simpa only [decide_eq_true_eq] using hdecision
  · exact supportedLabellingEqB_true_of_eq ids

def supportedDirac
    (ids : List Nat) (selected target : EdgeLabelling) : Q' :=
  if supportedLabellingEqB ids target selected then 1 else 0

theorem supportedDirac_nonnegative
    (ids : List Nat) (selected target : EdgeLabelling) :
    (0 : Q') ≤ supportedDirac ids selected target := by
  unfold supportedDirac
  split
  · exact Q'.zero_le_one
  · exact Q'.le_refl' 0

private theorem listQSum_boolDirac_zero_of_not_mem {A : Type}
    (selected : A) (predicate : A → Bool) :
    ∀ targets : List A, selected ∉ targets →
      (∀ target, target ∈ targets →
        predicate target = true → target = selected) →
      listQSum
          (fun target => if predicate target then (1 : Q') else 0)
          targets ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hnot, hunique => by
      have hheadNe : head ≠ selected := by
        intro heq
        subst head
        exact hnot List.mem_cons_self
      have htailNot : selected ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hheadFalse : predicate head = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact hheadNe
          (hunique head List.mem_cons_self htrue)
      rw [listQSum, hheadFalse]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0)
          (listQSum_boolDirac_zero_of_not_mem
            selected predicate tail htailNot
            (fun target htarget =>
              hunique target (List.mem_cons_of_mem head htarget))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_boolDirac_one_of_unique {A : Type}
    (selected : A) (predicate : A → Bool) :
    ∀ targets : List A, targets.Nodup → selected ∈ targets →
      (∀ target, target ∈ targets →
        (predicate target = true ↔ target = selected)) →
      listQSum
          (fun target => if predicate target then (1 : Q') else 0)
          targets ≈ 1
  | [], _, hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, hnodup, hmem, hunique => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        have hselectedTrue :
            predicate selected = true :=
          ((hunique selected) List.mem_cons_self).mpr rfl
        rw [listQSum, hselectedTrue]
        have htailZero :
            listQSum
                (fun target =>
                  if predicate target then (1 : Q') else 0)
                tail ≈ 0 := by
          exact listQSum_boolDirac_zero_of_not_mem
            selected predicate tail hparts.1
            (fun target htarget htrue =>
              ((hunique target)
                (List.mem_cons_of_mem selected htarget)).mp htrue)
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 1) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' 1))
      · have hheadNe : head ≠ selected := by
          intro heq
          subst head
          exact hparts.1 htail
        have hheadFalse : predicate head = false := by
          apply Bool.eq_false_iff.mpr
          intro htrue
          exact hheadNe
            (((hunique head) List.mem_cons_self).mp htrue)
        rw [listQSum, hheadFalse]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (listQSum_boolDirac_one_of_unique selected predicate tail
              hparts.2 htail
              (fun target htarget =>
                (hunique target)
                  (List.mem_cons_of_mem head htarget))))
          (Q'.eqv_of_eq (Q'.zero_add' 1))

private theorem listQSum_supportedDirac_eq_one
    {K : Nat} {ids : List Nat} {selected : EdgeLabelling}
    (hids : ids.Nodup)
    (hselected : selected ∈ boundedEdgeLabellings K ids) :
    listQSum (supportedDirac ids selected)
        (boundedEdgeLabellings K ids) ≈ 1 := by
  let targets := boundedEdgeLabellings K ids
  have htargetsNodup : targets.Nodup :=
    boundedEdgeLabellings_nodup K ids hids
  exact listQSum_boolDirac_one_of_unique selected
    (fun target => supportedLabellingEqB ids target selected)
    targets htargetsNodup hselected
    (fun target htarget =>
      @supportedLabellingEqB_true_iff K ids target selected
        htarget hselected)

/-! ## 3. Reflection-fixed supported point masses -/

theorem fixedSingletonLabelling_reflection (D : SlabPhysicalData) :
    D.reflectLabelling (fixedSingletonLabelling D) =
      fixedSingletonLabelling D := by
  unfold SlabPhysicalData.reflectLabelling fixedSingletonLabelling
    SlabPhysicalData.extent
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent D.half)
  ·
    rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
    unfold reflectSlabFaceLabelling
    rw [slabBinarySupportLabelling_eq_indicator
      (slabFaceReflectId_physical hid)]
    rw [slabPlaquetteAt_slabFaceReflectId hid]
    rw [slabBinarySupportLabelling_eq_indicator hid]
    have hadmissible :
        plaquetteTimeAdmissible (centralExtent D.half)
          (slabPlaquetteAt (centralExtent D.half) id) :=
      ((mem_boundaryCompleteSlabPlaquettes _ _).mp
        (slabPlaquetteAt_mem hid)).2
    have hreflectedMem :
        timeReflectPlaquette (centralExtent D.half)
            (slabPlaquetteAt (centralExtent D.half) id) ∈
              [centralFixedPlaquette D.half] ↔
          slabPlaquetteAt (centralExtent D.half) id ∈
              [centralFixedPlaquette D.half] := by
      simp only [List.mem_singleton]
      constructor
      · intro hreflected
        have hback := congrArg
          (timeReflectPlaquette (centralExtent D.half)) hreflected
        rw [timeReflectPlaquette_involutive _ _ hadmissible,
          centralFixedPlaquette_reflection] at hback
        exact hback
      · intro hsource
        rw [hsource, centralFixedPlaquette_reflection]
    by_cases hsource :
        slabPlaquetteAt (centralExtent D.half) id ∈
          [centralFixedPlaquette D.half]
    · have hreflected := hreflectedMem.mpr hsource
      simp [hsource, hreflected]
    · have hreflected :
          timeReflectPlaquette (centralExtent D.half)
              (slabPlaquetteAt (centralExtent D.half) id) ∉
            [centralFixedPlaquette D.half] := by
        intro hmem
        exact hsource (hreflectedMem.mp hmem)
      simp [hsource, hreflected]
  ·
    rw [reflectSupportedSlabFaceLabelling_zero_off_physical _ _ hid]
    exact (slabBinarySupportLabelling_eq_zero_of_not_physical hid).symm

theorem zeroEdgeLabelling_mem_slab (D : SlabPhysicalData) :
    zeroEdgeLabelling ∈ D.physicalLabellings := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    simp [zeroEdgeLabelling]
  · intro _ _
    rfl

theorem zeroEdgeLabelling_reflection (D : SlabPhysicalData) :
    D.reflectLabelling zeroEdgeLabelling = zeroEdgeLabelling := by
  funext id
  by_cases hid : id ∈ D.faceEdges
  · unfold SlabPhysicalData.reflectLabelling
    rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
    rfl
  · unfold SlabPhysicalData.reflectLabelling
    rw [reflectSupportedSlabFaceLabelling_zero_off_physical _ _ hid]
    rfl

theorem supportedDirac_reflection
    (D : SlabPhysicalData) {selected target : EdgeLabelling}
    (hselected : selected ∈ D.physicalLabellings)
    (htarget : target ∈ D.physicalLabellings)
    (hselectedFixed : D.reflectLabelling selected = selected) :
    supportedDirac D.faceEdges selected (D.reflectLabelling target) =
      supportedDirac D.faceEdges selected target := by
  unfold supportedDirac
  have hreflectedMem :=
    reflectSupportedSlabFaceLabelling_mem htarget
  by_cases heq : target = selected
  · subst target
    rw [hselectedFixed]
  · have hreflectedNe :
      D.reflectLabelling target ≠ selected := by
      intro hreflected
      have hback := congrArg D.reflectLabelling hreflected
      have hsupport :=
        (boundedEdgeLabellings_sound D.cutoff D.faceEdges target htarget).2
      unfold SlabPhysicalData.reflectLabelling at hback
      rw [reflectSupportedSlabFaceLabelling_involutive
          D.extent target hsupport,
        show reflectSupportedSlabFaceLabelling D.extent selected = selected
          from hselectedFixed] at hback
      exact heq hback
    have htargetFalse :
        supportedLabellingEqB D.faceEdges target selected = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact heq ((supportedLabellingEqB_true_iff
        htarget hselected).mp htrue)
    have hreflectedFalse :
        supportedLabellingEqB D.faceEdges
            (D.reflectLabelling target) selected = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hreflectedNe ((supportedLabellingEqB_true_iff
        hreflectedMem hselected).mp htrue)
    rw [htargetFalse, hreflectedFalse]

/-! ## 4. One-plaquette rows are Gibbs-null -/

def firstPlaquetteBoundaryLink (plaquette : Z4Plaq) : Z4Link :=
  (plaquette.1, (dirsOf plaquette.2).1)

theorem firstPlaquetteBoundaryLink_mem_edges
    (plaquette : Z4Plaq) :
    firstPlaquetteBoundaryLink plaquette ∈ edgesOf plaquette := by
  exact List.mem_cons_self

theorem singleton_faceIncidenceCount_first_eq_one
    (plaquette : Z4Plaq) :
    faceIncidenceCount (firstPlaquetteBoundaryLink plaquette)
        [plaquette] = 1 := by
  unfold faceIncidenceCount
  rw [if_pos (firstPlaquetteBoundaryLink_mem_edges plaquette)]
  rfl

/-- Every binary one-face corrected-slab row has a vanishing local Haar
projector.  The theorem is stated as failure of strict positivity, exactly
the branch condition needed by the total kernel. -/
theorem singletonPhysicalTerm_not_positive
    (D : SlabPhysicalData) {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ boundaryCompleteSlabPlaquettes D.extent) :
    ¬ (0 : Q') <
      D.physicalTerm
        (slabBinarySupportLabelling D.extent [plaquette]) := by
  intro hpositive
  let link := firstPlaquetteBoundaryLink plaquette
  have hlink :
      link ∈ boundaryCompleteSlabLinks D.extent := by
    apply (mem_boundaryCompleteSlabLinks_iff _ _).mpr
    exact ⟨plaquette, hplaquette,
      firstPlaquetteBoundaryLink_mem_edges plaquette⟩
  have hnonzero :=
    positivePhysicalTerm_localMultiplicity_ne_zero
      D (slabBinarySupportLabelling D.extent [plaquette])
      hpositive hlink
  apply hnonzero
  unfold slabExplicitLinkMultiplicity
  apply explicitValenceMultiplicity_eq_zero_of_odd_sum
  · simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six D.extent link
  · have hsum :=
      slabBinarySupport_localExternalSpinSum
        (extent := D.extent) (support := [plaquette])
        (fun face hmem => by
          have heq := List.mem_singleton.mp hmem
          simpa [heq] using hplaquette)
        (by simp) link
    simp only [List.length_map]
    rw [hsum]
    change
      faceIncidenceCount
          (firstPlaquetteBoundaryLink plaquette) [plaquette] % 2 = 1
    rw [singleton_faceIncidenceCount_first_eq_one]

theorem fixedSingletonPhysicalTerm_not_positive
    (D : SlabPhysicalData) :
    ¬ (0 : Q') < D.physicalTerm (fixedSingletonLabelling D) := by
  unfold fixedSingletonLabelling
  exact singletonPhysicalTerm_not_positive D
    (by
      unfold SlabPhysicalData.extent
      exact centralFixedPlaquette_mem_slab D.half)

theorem bottomSingletonPhysicalTerm_not_positive
    (D : SlabPhysicalData) :
    ¬ (0 : Q') < D.physicalTerm (bottomSingletonLabelling D) := by
  unfold bottomSingletonLabelling
  exact singletonPhysicalTerm_not_positive D
    (by
      unfold SlabPhysicalData.extent
      exact bottomPlaquette_mem_slab D.half)

/-! ## 5. Reflection-equivariant completion on null rows -/

private theorem rangeNodup : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodup n,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl n) (List.mem_range.mp hleft)

theorem slabFaceEdges_nodup (D : SlabPhysicalData) :
    D.faceEdges.Nodup := by
  unfold SlabPhysicalData.faceEdges slabPhysicalFaceEdges
  exact rangeNodup _

theorem supportedDirac_slab_row_normalized
    (D : SlabPhysicalData) {selected : EdgeLabelling}
    (hselected : selected ∈ D.physicalLabellings) :
    listQSum (supportedDirac D.faceEdges selected)
      D.physicalLabellings ≈ 1 := by
  exact listQSum_supportedDirac_eq_one
    (slabFaceEdges_nodup D) hselected

def nullCompletionKernel
    (S : SlabScalePair)
    (fineState coarseState : EdgeLabelling) : Q' :=
  if supportedLabellingEqB S.fine.faceEdges fineState
      (fixedSingletonLabelling S.fine) then
    supportedDirac S.coarse.faceEdges
      (fixedSingletonLabelling S.coarse) coarseState
  else
    supportedDirac S.coarse.faceEdges zeroEdgeLabelling coarseState

theorem nullCompletionKernel_nonnegative
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling) :
    (0 : Q') ≤ nullCompletionKernel S fineState coarseState := by
  unfold nullCompletionKernel
  split
  · exact supportedDirac_nonnegative _ _ _
  · exact supportedDirac_nonnegative _ _ _

theorem nullCompletionKernel_row_normalized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (fineState : EdgeLabelling) :
    listQSum (nullCompletionKernel S fineState)
        S.coarse.physicalLabellings ≈ 1 := by
  have hcoarseCutoff : 1 ≤ S.coarse.cutoff := by
    rw [S.coarse_cutoff, hfineCutoff]
    omega
  unfold nullCompletionKernel
  split
  · exact supportedDirac_slab_row_normalized S.coarse
      (fixedSingletonLabelling_mem S.coarse hcoarseCutoff)
  · exact supportedDirac_slab_row_normalized S.coarse
      (zeroEdgeLabelling_mem_slab S.coarse)

theorem supportedLabellingEqB_reflection_fixed
    (D : SlabPhysicalData) {physical selected : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings)
    (hselected : selected ∈ D.physicalLabellings)
    (hselectedFixed : D.reflectLabelling selected = selected) :
    supportedLabellingEqB D.faceEdges
        (D.reflectLabelling physical) selected =
      supportedLabellingEqB D.faceEdges physical selected := by
  have hreflectedMem :=
    reflectSupportedSlabFaceLabelling_mem hphysical
  by_cases heq : physical = selected
  · subst physical
    rw [hselectedFixed]
  · have hreflectedNe : D.reflectLabelling physical ≠ selected := by
      intro hreflected
      have hback := congrArg D.reflectLabelling hreflected
      have hsupport :=
        (boundedEdgeLabellings_sound D.cutoff D.faceEdges
          physical hphysical).2
      unfold SlabPhysicalData.reflectLabelling at hback
      rw [reflectSupportedSlabFaceLabelling_involutive
          D.extent physical hsupport,
        show reflectSupportedSlabFaceLabelling D.extent selected = selected
          from hselectedFixed] at hback
      exact heq hback
    have hsourceFalse :
        supportedLabellingEqB D.faceEdges physical selected = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact heq ((supportedLabellingEqB_true_iff
        hphysical hselected).mp htrue)
    have hreflectedFalse :
        supportedLabellingEqB D.faceEdges
            (D.reflectLabelling physical) selected = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hreflectedNe ((supportedLabellingEqB_true_iff
        hreflectedMem hselected).mp htrue)
    rw [hsourceFalse, hreflectedFalse]

theorem nullCompletionKernel_reflection
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    nullCompletionKernel S
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState) =
      nullCompletionKernel S fineState coarseState := by
  have hfixedFineMem :
      fixedSingletonLabelling S.fine ∈ S.fine.physicalLabellings :=
    fixedSingletonLabelling_mem S.fine (by omega)
  have hsource :=
    supportedLabellingEqB_reflection_fixed S.fine
      hfine hfixedFineMem
      (fixedSingletonLabelling_reflection S.fine)
  unfold nullCompletionKernel
  rw [hsource]
  split
  · exact supportedDirac_reflection S.coarse
      (fixedSingletonLabelling_mem S.coarse (by
        rw [S.coarse_cutoff, hfineCutoff]
        omega))
      hcoarse (fixedSingletonLabelling_reflection S.coarse)
  · exact supportedDirac_reflection S.coarse
      (zeroEdgeLabelling_mem_slab S.coarse)
      hcoarse (zeroEdgeLabelling_reflection S.coarse)

/-! ## 6. Canonical support restriction and the total kernel -/

def restrictToSlabSupport
    (D : SlabPhysicalData) (physical : EdgeLabelling) : EdgeLabelling :=
  fun id => if id ∈ D.faceEdges then physical id else 0

def slabCoordinatesBoundedB
    (D : SlabPhysicalData) (physical : EdgeLabelling) : Bool :=
  D.faceEdges.all fun id => decide (physical id < D.cutoff + 1)

theorem slabCoordinatesBoundedB_true_of_mem
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    slabCoordinatesBoundedB D physical = true := by
  unfold slabCoordinatesBoundedB
  apply List.all_eq_true.mpr
  intro id hid
  simpa only [decide_eq_true_eq] using
    (boundedEdgeLabellings_sound D.cutoff D.faceEdges
      physical hphysical).1 id hid

theorem restrictToSlabSupport_eq_of_mem
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    restrictToSlabSupport D physical = physical := by
  have hsound :=
    boundedEdgeLabellings_sound D.cutoff D.faceEdges physical hphysical
  funext id
  by_cases hid : id ∈ D.faceEdges
  · simp [restrictToSlabSupport, hid]
  · simp [restrictToSlabSupport, hid, hsound.2 id hid]

theorem restrictToSlabSupport_mem_of_bounded
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hbounded : slabCoordinatesBoundedB D physical = true) :
    restrictToSlabSupport D physical ∈ D.physicalLabellings := by
  apply boundedEdgeLabellings_complete
  · intro id hid
    unfold restrictToSlabSupport
    rw [if_pos hid]
    have hdecision :=
      List.all_eq_true.mp hbounded id hid
    simpa only [decide_eq_true_eq] using hdecision
  · intro id hid
    unfold restrictToSlabSupport
    rw [if_neg hid]

def positiveCoherentSource
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineState : EdgeLabelling)
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    CoherentSlabRecouplingSource S :=
  (CutoffOnePositivePhysicalSource.mk
    fineState hfine hfineCutoff hpositive hcoarseCoupling
  ).toCoherentSlabRecouplingSource

theorem wholeSlabConditionalKernel_eq_of_fineState_eq
    {S : SlabScalePair}
    (left right : CoherentSlabRecouplingSource S)
    (hstate : left.fineState = right.fineState)
    (target : EdgeLabelling) :
    wholeSlabRecouplingConditionalKernel left target ≈
      wholeSlabRecouplingConditionalKernel right target := by
  unfold wholeSlabRecouplingConditionalKernel
    wholeSlabRecouplingPartition
  rw [hstate]
  exact Q'.eqv_refl _

def cutoffOneWholeSlabKernel
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineState coarseState : EdgeLabelling) : Q' :=
  if hbounded : slabCoordinatesBoundedB S.fine fineState = true then
    let restricted := restrictToSlabSupport S.fine fineState
    let hrestricted :=
      restrictToSlabSupport_mem_of_bounded S.fine hbounded
    if hpositive : (0 : Q') <
        S.fine.physicalTerm restricted then
      wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          restricted hrestricted hpositive)
        coarseState
    else
      nullCompletionKernel S restricted coarseState
  else
    nullCompletionKernel S fineState coarseState

theorem cutoffOneWholeSlabKernel_eq_positive
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (coarseState : EdgeLabelling) :
    cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        fineState coarseState ≈
      wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          fineState hfine hpositive)
        coarseState := by
  unfold cutoffOneWholeSlabKernel
  rw [dif_pos (slabCoordinatesBoundedB_true_of_mem S.fine hfine)]
  have hrestrict :=
    restrictToSlabSupport_eq_of_mem S.fine hfine
  simp only [hrestrict]
  rw [dif_pos hpositive]
  exact Q'.eqv_refl _

theorem cutoffOneWholeSlabKernel_eq_null
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hnotPositive : ¬ (0 : Q') < S.fine.physicalTerm fineState)
    (coarseState : EdgeLabelling) :
    cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        fineState coarseState =
      nullCompletionKernel S fineState coarseState := by
  unfold cutoffOneWholeSlabKernel
  rw [dif_pos (slabCoordinatesBoundedB_true_of_mem S.fine hfine)]
  have hrestrict :=
    restrictToSlabSupport_eq_of_mem S.fine hfine
  simp only [hrestrict]
  rw [dif_neg hnotPositive]

/-! ## 7. Stochasticity and reflection of the total row -/

theorem physicalTerm_reflection_positive_iff
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    (0 : Q') < D.physicalTerm (D.reflectLabelling physical) ↔
      (0 : Q') < D.physicalTerm physical := by
  have hreflection := D.physicalTerm_reflection hphysical
  constructor
  · intro hpositive
    exact Q'.pos_of_lt_of_le hpositive
      (Q'.le_of_eqv hreflection)
  · intro hpositive
    exact Q'.pos_of_lt_of_le hpositive
      (Q'.ge_of_eqv hreflection)

theorem positiveCoherentConditionalKernel_reflection
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          (S.fine.reflectLabelling fineState)
          (reflectSupportedSlabFaceLabelling_mem hfine)
          ((physicalTerm_reflection_positive_iff S.fine hfine).mpr
            hpositive))
        (S.coarse.reflectLabelling coarseState) ≈
      wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          fineState hfine hpositive)
        coarseState := by
  let source :=
    positiveCoherentSource S hfineCutoff hcoarseCoupling
      fineState hfine hpositive
  let reflectedSource :=
    positiveCoherentSource S hfineCutoff hcoarseCoupling
      (S.fine.reflectLabelling fineState)
      (reflectSupportedSlabFaceLabelling_mem hfine)
      ((physicalTerm_reflection_positive_iff S.fine hfine).mpr
        hpositive)
  refine Q'.eqv_trans _
    (wholeSlabRecouplingConditionalKernel
      (reflectCoherentSlabRecouplingSource source)
      (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
  · apply wholeSlabConditionalKernel_eq_of_fineState_eq
    rfl
  · exact wholeSlabRecouplingConditionalKernel_reflection
      source hcoarse

theorem cutoffOneWholeSlabKernel_nonnegative
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (_hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    (0 : Q') ≤
      cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        fineState coarseState := by
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · have heq :=
      cutoffOneWholeSlabKernel_eq_positive S hfineCutoff
        hcoarseCoupling hfine hpositive coarseState
    exact Q'.le_trans' _ _ _
      (wholeSlabRecouplingConditionalKernel_nonnegative
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          fineState hfine hpositive) coarseState)
      (Q'.ge_of_eqv heq)
  · rw [cutoffOneWholeSlabKernel_eq_null S hfineCutoff
      hcoarseCoupling hfine hpositive coarseState]
    exact nullCompletionKernel_nonnegative S fineState coarseState

theorem cutoffOneWholeSlabKernel_row_normalized
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings) :
    listQSum
        (cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
          fineState)
        S.coarse.physicalLabellings ≈ 1 := by
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · refine Q'.eqv_trans _
      (listQSum
        (wholeSlabRecouplingConditionalKernel
          (positiveCoherentSource S hfineCutoff hcoarseCoupling
            fineState hfine hpositive))
        S.coarse.physicalLabellings) _ ?_ ?_
    · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
        (fun coarseState _ =>
          cutoffOneWholeSlabKernel_eq_positive S hfineCutoff
            hcoarseCoupling hfine hpositive coarseState)
    · exact wholeSlabRecouplingConditionalKernel_row_normalized _
  · refine Q'.eqv_trans _
      (listQSum (nullCompletionKernel S fineState)
        S.coarse.physicalLabellings) _ ?_ ?_
    · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
        (fun coarseState _ =>
          Q'.eqv_of_eq
            (cutoffOneWholeSlabKernel_eq_null S hfineCutoff
              hcoarseCoupling hfine hpositive coarseState))
    · exact nullCompletionKernel_row_normalized
        S hfineCutoff fineState

theorem cutoffOneWholeSlabKernel_reflection
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {fineState coarseState : EdgeLabelling}
    (hfine : fineState ∈ S.fine.physicalLabellings)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        (S.fine.reflectLabelling fineState)
        (S.coarse.reflectLabelling coarseState) ≈
      cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        fineState coarseState := by
  have hreflectedFine :=
    reflectSupportedSlabFaceLabelling_mem hfine
  by_cases hpositive :
      (0 : Q') < S.fine.physicalTerm fineState
  · have hreflectedPositive :=
      (physicalTerm_reflection_positive_iff S.fine hfine).mpr
        hpositive
    refine Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          (S.fine.reflectLabelling fineState)
          hreflectedFine hreflectedPositive)
        (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
    · exact cutoffOneWholeSlabKernel_eq_positive
        S hfineCutoff hcoarseCoupling hreflectedFine
        hreflectedPositive _
    refine Q'.eqv_trans _
      (wholeSlabRecouplingConditionalKernel
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          fineState hfine hpositive)
        coarseState) _ ?_ ?_
    · exact positiveCoherentConditionalKernel_reflection
        S hfineCutoff hcoarseCoupling hfine hcoarse hpositive
    · exact Q'.eqv_symm
        (cutoffOneWholeSlabKernel_eq_positive
          S hfineCutoff hcoarseCoupling hfine hpositive _)
  · have hreflectedNotPositive :
        ¬ (0 : Q') <
          S.fine.physicalTerm
            (S.fine.reflectLabelling fineState) := by
      intro hreflectedPositive
      exact hpositive
        ((physicalTerm_reflection_positive_iff S.fine hfine).mp
          hreflectedPositive)
    rw [cutoffOneWholeSlabKernel_eq_null S hfineCutoff
      hcoarseCoupling hreflectedFine hreflectedNotPositive]
    rw [cutoffOneWholeSlabKernel_eq_null S hfineCutoff
      hcoarseCoupling hfine hpositive]
    exact Q'.eqv_of_eq
      (nullCompletionKernel_reflection
        S hfineCutoff hfine hcoarse)

/-! ## 8. Source dependence and the packaged finite kernel -/

theorem cutoffOneWholeSlabKernel_fixed_eq_one
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        (fixedSingletonLabelling S.fine)
        (fixedSingletonLabelling S.coarse) = 1 := by
  have hfineMem :=
    fixedSingletonLabelling_mem S.fine (by
      rw [hfineCutoff]
      omega)
  rw [cutoffOneWholeSlabKernel_eq_null S hfineCutoff
    hcoarseCoupling hfineMem
    (fixedSingletonPhysicalTerm_not_positive S.fine)]
  unfold nullCompletionKernel
  have hsource :
      supportedLabellingEqB S.fine.faceEdges
          (fixedSingletonLabelling S.fine)
          (fixedSingletonLabelling S.fine) = true :=
    supportedLabellingEqB_true_of_eq _ rfl
  rw [hsource]
  unfold supportedDirac
  have htarget :
      supportedLabellingEqB S.coarse.faceEdges
          (fixedSingletonLabelling S.coarse)
          (fixedSingletonLabelling S.coarse) = true :=
    supportedLabellingEqB_true_of_eq _ rfl
  rw [htarget]

theorem cutoffOneWholeSlabKernel_bottom_eq_zero
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
        (bottomSingletonLabelling S.fine)
        (fixedSingletonLabelling S.coarse) = 0 := by
  have hfineMem :=
    bottomSingletonLabelling_mem S.fine (by
      rw [hfineCutoff]
      omega)
  have hfixedFineMem :=
    fixedSingletonLabelling_mem S.fine (by
      rw [hfineCutoff]
      omega)
  have hcoarseCutoff : 1 ≤ S.coarse.cutoff := by
    rw [S.coarse_cutoff, hfineCutoff]
    omega
  have hfixedCoarseMem :=
    fixedSingletonLabelling_mem S.coarse hcoarseCutoff
  have hvacuumCoarseMem :=
    zeroEdgeLabelling_mem_slab S.coarse
  rw [cutoffOneWholeSlabKernel_eq_null S hfineCutoff
    hcoarseCoupling hfineMem
    (bottomSingletonPhysicalTerm_not_positive S.fine)]
  unfold nullCompletionKernel
  have hsource :
      supportedLabellingEqB S.fine.faceEdges
          (bottomSingletonLabelling S.fine)
          (fixedSingletonLabelling S.fine) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact bottomSingletonLabelling_ne_fixed S.fine
      ((supportedLabellingEqB_true_iff
        hfineMem hfixedFineMem).mp htrue)
  rw [hsource]
  unfold supportedDirac
  have htarget :
      supportedLabellingEqB S.coarse.faceEdges
          (fixedSingletonLabelling S.coarse)
          zeroEdgeLabelling = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact fixedSingletonLabelling_ne_zero S.coarse
      ((supportedLabellingEqB_true_iff
        hfixedCoarseMem hvacuumCoarseMem).mp htrue)
  rw [htarget]

/-- The total cutoff-one whole-slab kernel.  Positive Gibbs rows are the
globally link-glued recoupling law; its source-dependence witness lies on
Gibbs-null singleton rows and therefore only certifies that the total matrix
is not a constant stochastic completion. -/
def cutoffOneWholeSlabFiniteKernel
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    S.FiniteSlabKernel where
  kernel :=
    cutoffOneWholeSlabKernel S hfineCutoff hcoarseCoupling
  nonnegative := by
    intro fineState coarseState hfine hcoarse
    exact cutoffOneWholeSlabKernel_nonnegative
      S hfineCutoff hcoarseCoupling hfine hcoarse
  row_normalized := by
    intro fineState hfine
    exact cutoffOneWholeSlabKernel_row_normalized
      S hfineCutoff hcoarseCoupling hfine
  reflection_intertwines := by
    intro fineState coarseState hfine hcoarse
    exact cutoffOneWholeSlabKernel_reflection
      S hfineCutoff hcoarseCoupling hfine hcoarse
  source_dependent := by
    refine ⟨fixedSingletonLabelling S.fine,
      bottomSingletonLabelling S.fine,
      fixedSingletonLabelling S.coarse, ?_, ?_, ?_, ?_⟩
    · exact fixedSingletonLabelling_mem S.fine (by
        rw [hfineCutoff]
        omega)
    · exact bottomSingletonLabelling_mem S.fine (by
        rw [hfineCutoff]
        omega)
    · exact fixedSingletonLabelling_mem S.coarse (by
        rw [S.coarse_cutoff, hfineCutoff]
        omega)
    · rw [cutoffOneWholeSlabKernel_fixed_eq_one
        S hfineCutoff hcoarseCoupling]
      rw [cutoffOneWholeSlabKernel_bottom_eq_zero
        S hfineCutoff hcoarseCoupling]
      exact (by decide : ¬ ((1 : Q') ≈ 0))

#print axioms singletonPhysicalTerm_not_positive
#print axioms nullCompletionKernel_reflection
#print axioms cutoffOneWholeSlabKernel_eq_positive
#print axioms cutoffOneWholeSlabKernel_row_normalized
#print axioms cutoffOneWholeSlabKernel_reflection
#print axioms cutoffOneWholeSlabFiniteKernel

end YMGap.Continuum.CompactDualCutoffOneTotalKernel
