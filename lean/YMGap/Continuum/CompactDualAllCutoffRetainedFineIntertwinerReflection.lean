/-
# Reflection covariance of the lossless all-cutoff enriched kernel

The lossless all-cutoff target is a disjoint sum.  Ordinary coarse states
reflect geometrically; retained fine states reflect their physical labels
geometrically and their exact SU(2) intertwiner assignment by the equal-rank
involution constructed in the preceding module.

This module proves that the resulting target map preserves the literal finite
carrier and is involutive there.  It then checks every row branch of the
enriched stochastic kernel.  Coherent rows use whole-slab recoupling
reflection, incoherent rows use equal-cardinality Haar-fibre reflection, and
Gibbs-null rows use the reflected null completion.  Hence the complete
source-to-target kernel commutes with reflection exactly.

Pushed-law reflection and reflection positivity are subsequent layers.  In
particular kernel covariance alone is not presented as OS positivity, a
strict form bound, a continuum limit, or the Clay theorem.

## Axiom gate

Finite carrier reindexing and existing exact reflection identities only.  No
classical choice, placeholder, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Constructive.CRealLogRatCongruence
import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
import YMGap.Continuum.CompactDualRetainedFineIntertwinerReflection

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabConditionalReflection
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Reflection on the disjoint enriched carrier -/

theorem allCutoffRetainedCoarseTarget_mem_iff
    (S : SlabScalePair) (coarseState : EdgeLabelling) :
    (Sum.inl coarseState : AllCutoffRetainedTarget) ∈
        allCutoffRetainedTargets S ↔
      coarseState ∈ S.coarse.physicalLabellings := by
  unfold allCutoffRetainedTargets
  constructor
  · intro htarget
    rcases List.mem_append.mp htarget with hcoarse | hretained
    · obtain ⟨state, hstate, heq⟩ := List.mem_map.mp hcoarse
      injection heq with heq'
      exact heq' ▸ hstate
    · obtain ⟨retained, _, heq⟩ := List.mem_map.mp hretained
      cases heq
  · intro hcoarse
    apply List.mem_append.mpr
    exact Or.inl (List.mem_map.mpr ⟨coarseState, hcoarse, rfl⟩)

theorem allCutoffRetainedFineTarget_mem_iff
    (S : SlabScalePair)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment) :
    (Sum.inr retained : AllCutoffRetainedTarget) ∈
        allCutoffRetainedTargets S ↔
      retained ∈ slabExpandedFineSources S.fine := by
  unfold allCutoffRetainedTargets
  constructor
  · intro htarget
    rcases List.mem_append.mp htarget with hcoarse | hretained
    · obtain ⟨coarseState, _, heq⟩ := List.mem_map.mp hcoarse
      cases heq
    · obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hretained
      injection heq with heq'
      exact heq' ▸ hsource
  · intro hretained
    apply List.mem_append.mpr
    exact Or.inr (List.mem_map.mpr ⟨retained, hretained, rfl⟩)

/-- Geometric reflection on the coarse summand and equal-rank fibre
reflection on the retained fine summand. -/
def reflectAllCutoffRetainedTarget
    (S : SlabScalePair) :
    AllCutoffRetainedTarget → AllCutoffRetainedTarget
  | .inl coarseState => .inl (S.coarse.reflectLabelling coarseState)
  | .inr retained =>
      .inr
        (S.fine.reflectLabelling retained.1,
          reflectRetainedFineIntertwiner
            S.fine retained.1 retained.2)

theorem slabPhysicalReflectLabelling_involutive_on
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    D.reflectLabelling (D.reflectLabelling physical) = physical := by
  unfold SlabPhysicalData.reflectLabelling
  apply reflectSupportedSlabFaceLabelling_involutive
  intro id hid
  exact (boundedEdgeLabellings_sound
    D.cutoff D.faceEdges physical hphysical).2 id hid

/-- The enriched reflection stays in the literal disjoint target carrier. -/
theorem reflectAllCutoffRetainedTarget_mem
    (S : SlabScalePair) {target : AllCutoffRetainedTarget}
    (htarget : target ∈ allCutoffRetainedTargets S) :
    reflectAllCutoffRetainedTarget S target ∈
      allCutoffRetainedTargets S := by
  cases target with
  | inl coarseState =>
      apply (allCutoffRetainedCoarseTarget_mem_iff S _).mpr
      exact reflectSupportedSlabFaceLabelling_mem
        ((allCutoffRetainedCoarseTarget_mem_iff S coarseState).mp htarget)
  | inr retained =>
      have hparts := mem_slabExpandedFineSources_iff.mp
        ((allCutoffRetainedFineTarget_mem_iff S retained).mp htarget)
      apply (allCutoffRetainedFineTarget_mem_iff S _).mpr
      apply mem_slabExpandedFineSources_iff.mpr
      exact ⟨reflectSupportedSlabFaceLabelling_mem hparts.1,
        reflectRetainedFineIntertwiner_mem
          S.fine hparts.1 hparts.2⟩

/-- The enriched target reflection is involutive on its finite carrier. -/
theorem reflectAllCutoffRetainedTarget_involutive
    (S : SlabScalePair) {target : AllCutoffRetainedTarget}
    (htarget : target ∈ allCutoffRetainedTargets S) :
    reflectAllCutoffRetainedTarget S
        (reflectAllCutoffRetainedTarget S target) = target := by
  cases target with
  | inl coarseState =>
      have hcoarse :=
        (allCutoffRetainedCoarseTarget_mem_iff S coarseState).mp htarget
      unfold reflectAllCutoffRetainedTarget
      exact congrArg Sum.inl
        (slabPhysicalReflectLabelling_involutive_on S.coarse hcoarse)
  | inr retained =>
      have hparts := mem_slabExpandedFineSources_iff.mp
        ((allCutoffRetainedFineTarget_mem_iff S retained).mp htarget)
      unfold reflectAllCutoffRetainedTarget
      apply congrArg Sum.inr
      apply Prod.ext
      · exact slabPhysicalReflectLabelling_involutive_on
          S.fine hparts.1
      · exact reflectRetainedFineIntertwiner_involutive
          S.fine hparts.1 hparts.2

/-! ## 2. Reflection of the retained Haar row -/

theorem retainedFineIntertwinerPartition_reflection
    (D : SlabPhysicalData) {physical : EdgeLabelling}
    (hphysical : physical ∈ D.physicalLabellings) :
    retainedFineIntertwinerPartition
        D (D.reflectLabelling physical) ≈
      retainedFineIntertwinerPartition D physical := by
  refine Q'.eqv_trans _
    (Q'.ofNat
      (slabExplicitLinkMultiplicityProduct
        D.cutoff D.extent (D.reflectLabelling physical))) _ ?_ ?_
  · exact retainedFineIntertwinerPartition_eqv_linkMultiplicity
      D (D.reflectLabelling physical)
  · rw [YMGap.Continuum.CompactDualWholeSlabRecouplingReflection.slabLinkMultiplicityProduct_supported_reflection
      D hphysical]
    exact Q'.eqv_symm
      (retainedFineIntertwinerPartition_eqv_linkMultiplicity D physical)

/-- Unit-counting Haar conditionals are reflection invariant after equal-rank
transport of their retained assignment. -/
def reflectRetainedFineIntertwinerSource
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D) :
    RetainedFineIntertwinerSource D :=
  { fineState := D.reflectLabelling source.fineState
    fineState_mem :=
      reflectSupportedSlabFaceLabelling_mem source.fineState_mem
    physicalTerm_pos :=
      (physicalTerm_reflection_positive_iff
        D source.fineState_mem).mpr source.physicalTerm_pos }

theorem retainedFineIntertwinerConditionalKernel_reflection
    {D : SlabPhysicalData}
    (source : RetainedFineIntertwinerSource D)
    (assignment : SlabFusionWitnessAssignment) :
    retainedFineIntertwinerConditionalKernel
        (reflectRetainedFineIntertwinerSource source)
        (reflectRetainedFineIntertwiner
          D source.fineState assignment) ≈
      retainedFineIntertwinerConditionalKernel source assignment := by
  unfold retainedFineIntertwinerConditionalKernel
    retainedFineIntertwinerRawWeight Q'.divPos
    reflectRetainedFineIntertwinerSource
  apply Q'.mul_eqv_congr_left 1
  exact Q'.recipPos_eqv_congr _ _ _ _
    (retainedFineIntertwinerPartition_reflection
      D source.fineState_mem)

theorem slabPhysicalStateCode_reflection_eq_iff
    (D : SlabPhysicalData) {left right : EdgeLabelling}
    (hleft : left ∈ D.physicalLabellings)
    (hright : right ∈ D.physicalLabellings) :
    slabPhysicalStateCode D (D.reflectLabelling left) =
        slabPhysicalStateCode D (D.reflectLabelling right) ↔
      slabPhysicalStateCode D left = slabPhysicalStateCode D right := by
  constructor
  · intro hcode
    have hreflected :
        D.reflectLabelling left = D.reflectLabelling right :=
      slabPhysicalStateCode_injective_on_carrier
        (reflectSupportedSlabFaceLabelling_mem hleft)
        (reflectSupportedSlabFaceLabelling_mem hright) hcode
    have heq := congrArg D.reflectLabelling hreflected
    rw [slabPhysicalReflectLabelling_involutive_on D hleft,
      slabPhysicalReflectLabelling_involutive_on D hright] at heq
    rw [heq]
  · intro hcode
    have heq : left = right :=
      slabPhysicalStateCode_injective_on_carrier hleft hright hcode
    rw [heq]

/-- The zero-extended retained row commutes with physical and equal-rank
assignment reflection. -/
theorem retainedSamePhysicalStateKernel_reflection
    (D : SlabPhysicalData)
    (source : SlabPhysicalSourceEntry D)
    (hpositive : (0 : Q') < D.physicalTerm source.1)
    (target : EdgeLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈ slabExpandedFineSources D) :
    retainedSamePhysicalStateKernel
        ⟨D.reflectLabelling source.1,
          reflectSupportedSlabFaceLabelling_mem source.2⟩
        ((physicalTerm_reflection_positive_iff D source.2).mpr hpositive)
        (D.reflectLabelling target.1,
          reflectRetainedFineIntertwiner D target.1 target.2) ≈
      retainedSamePhysicalStateKernel source hpositive target := by
  rcases target with ⟨targetPhysical, targetAssignment⟩
  have htargetParts := mem_slabExpandedFineSources_iff.mp htarget
  have hcodeIff := slabPhysicalStateCode_reflection_eq_iff
    D htargetParts.1 source.2
  by_cases hcode :
      slabPhysicalStateCode D targetPhysical =
        slabPhysicalStateCode D source.1
  · unfold retainedSamePhysicalStateKernel
    rw [if_pos hcode, if_pos (hcodeIff.mpr hcode)]
    let retainedSource :=
      retainedSourceOfPhysicalEntry source hpositive
    change retainedFineIntertwinerConditionalKernel
        (reflectRetainedFineIntertwinerSource retainedSource)
          (reflectRetainedFineIntertwiner
            D targetPhysical targetAssignment) ≈
      retainedFineIntertwinerConditionalKernel
        retainedSource targetAssignment
    have hphysicalEq : targetPhysical = source.1 :=
      slabPhysicalStateCode_injective_on_carrier
        htargetParts.1 source.2 hcode
    subst targetPhysical
    exact retainedFineIntertwinerConditionalKernel_reflection
      retainedSource targetAssignment
  · have hreflectedCode :
        slabPhysicalStateCode D (D.reflectLabelling targetPhysical) ≠
          slabPhysicalStateCode D (D.reflectLabelling source.1) :=
      fun heq => hcode (hcodeIff.mp heq)
    unfold retainedSamePhysicalStateKernel
    rw [if_neg hcode, if_neg hreflectedCode]
    exact Q'.eqv_refl 0

/-! ## 3. Reflection covariance of every enriched kernel branch -/

/-- Reflect a physical source entry without changing its carrier. -/
def reflectSlabPhysicalSourceEntry
    {D : SlabPhysicalData} (source : SlabPhysicalSourceEntry D) :
    SlabPhysicalSourceEntry D :=
  ⟨D.reflectLabelling source.1,
    reflectSupportedSlabFaceLabelling_mem source.2⟩

/-- The dependent retained-incoherent branch, isolated behind an exact
intermediate Haar row so later proofs need not normalize the complete kernel
while matching proof-bearing sources. -/
theorem allCutoffRetainedFineIntertwinerKernel_reflection_incoherent_retained
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : (0 : Q') < S.fine.physicalTerm source.1)
    (hpartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S source.1)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment)
    (hretained : retained ∈ slabExpandedFineSources S.fine) :
    allCutoffRetainedFineIntertwinerKernel S
        (reflectSlabPhysicalSourceEntry source)
        (.inr
          (S.fine.reflectLabelling retained.1,
            reflectRetainedFineIntertwiner
              S.fine retained.1 retained.2)) ≈
      allCutoffRetainedFineIntertwinerKernel S source (.inr retained) := by
  have hreflectedPositive :
      (0 : Q') < S.fine.physicalTerm
        (S.fine.reflectLabelling source.1) :=
    (physicalTerm_reflection_positive_iff S.fine source.2).mpr
      hpositive
  have hreflectedNotPartition :
      ¬ (0 : Q') < wholeSlabRawRowPartition S
        (S.fine.reflectLabelling source.1) := by
    intro hreflected
    exact hpartition
      ((wholeSlabRawRowPartition_reflection_pos_iff
        S source.1).mp hreflected)
  refine Q'.eqv_trans _
    (retainedSamePhysicalStateKernel
      (reflectSlabPhysicalSourceEntry source)
      hreflectedPositive
      (S.fine.reflectLabelling retained.1,
        reflectRetainedFineIntertwiner
          S.fine retained.1 retained.2)) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
        S (reflectSlabPhysicalSourceEntry source)
          hreflectedPositive hreflectedNotPartition _)
  refine Q'.eqv_trans _
    (retainedSamePhysicalStateKernel source hpositive retained) _
    (retainedSamePhysicalStateKernel_reflection
      S.fine source hpositive retained hretained) ?_
  exact Q'.eqv_symm (Q'.eqv_of_eq
    (allCutoffRetainedFineIntertwinerKernel_eq_retained_of_incoherent
      S source hpositive hpartition retained))

/-- On a Gibbs-null source and a coarse target, the enriched row is exactly
the already-reflected total whole-slab row. -/
theorem allCutoffRetainedFineIntertwinerKernel_eq_total_of_not_positive
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : ¬ (0 : Q') < S.fine.physicalTerm source.1)
    (coarseState : EdgeLabelling) :
    allCutoffRetainedFineIntertwinerKernel
        S source (.inl coarseState) =
      allCutoffWholeSlabKernel S source.1 coarseState := by
  rw [allCutoffWholeSlabKernel_eq_null_of_not_physical_positive
    S source.2 hpositive coarseState]
  unfold allCutoffRetainedFineIntertwinerKernel
  rw [dif_neg hpositive]

/-- A Gibbs-null source has no retained-summand output. -/
theorem allCutoffRetainedFineIntertwinerKernel_retained_zero_of_not_positive
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : ¬ (0 : Q') < S.fine.physicalTerm source.1)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment) :
    allCutoffRetainedFineIntertwinerKernel
        S source (.inr retained) = 0 := by
  unfold allCutoffRetainedFineIntertwinerKernel
  rw [dif_neg hpositive]

/-- Reflection covariance of the Gibbs-null coarse branch, kept opaque so the
complete dependent kernel is not normalized by its consumers. -/
theorem allCutoffRetainedFineIntertwinerKernel_reflection_not_positive_coarse
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : ¬ (0 : Q') < S.fine.physicalTerm source.1)
    (coarseState : EdgeLabelling)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    allCutoffRetainedFineIntertwinerKernel S
        (reflectSlabPhysicalSourceEntry source)
        (.inl (S.coarse.reflectLabelling coarseState)) ≈
      allCutoffRetainedFineIntertwinerKernel
        S source (.inl coarseState) := by
  have hreflectedNotPositive :
      ¬ (0 : Q') < S.fine.physicalTerm
        (S.fine.reflectLabelling source.1) := by
    intro hreflected
    exact hpositive
      ((physicalTerm_reflection_positive_iff S.fine source.2).mp
        hreflected)
  refine Q'.eqv_trans _
    (nullCompletionKernel S
      (S.fine.reflectLabelling source.1)
      (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
  · exact Q'.eqv_of_eq (by
      unfold allCutoffRetainedFineIntertwinerKernel
        reflectSlabPhysicalSourceEntry
      rw [dif_neg hreflectedNotPositive])
  refine Q'.eqv_trans _
    (nullCompletionKernel S source.1 coarseState) _
    (Q'.eqv_of_eq
      (allCutoffNullCompletionKernel_reflection
        S hfineCutoff source.2 hcoarse)) ?_
  exact Q'.eqv_symm (Q'.eqv_of_eq (by
    unfold allCutoffRetainedFineIntertwinerKernel
    rw [dif_neg hpositive]))

/-- Reflection covariance of the Gibbs-null retained branch. -/
theorem allCutoffRetainedFineIntertwinerKernel_reflection_not_positive_retained
    (S : SlabScalePair)
    (source : SlabPhysicalSourceEntry S.fine)
    (hpositive : ¬ (0 : Q') < S.fine.physicalTerm source.1)
    (retained : EdgeLabelling × SlabFusionWitnessAssignment) :
    allCutoffRetainedFineIntertwinerKernel S
        (reflectSlabPhysicalSourceEntry source)
        (.inr
          (S.fine.reflectLabelling retained.1,
            reflectRetainedFineIntertwiner
              S.fine retained.1 retained.2)) ≈
      allCutoffRetainedFineIntertwinerKernel
        S source (.inr retained) := by
  have hreflectedNotPositive :
      ¬ (0 : Q') < S.fine.physicalTerm
        (S.fine.reflectLabelling source.1) := by
    intro hreflected
    exact hpositive
      ((physicalTerm_reflection_positive_iff S.fine source.2).mp
        hreflected)
  rw [allCutoffRetainedFineIntertwinerKernel_retained_zero_of_not_positive
    S (reflectSlabPhysicalSourceEntry source) hreflectedNotPositive]
  rw [allCutoffRetainedFineIntertwinerKernel_retained_zero_of_not_positive
    S source hpositive]
  exact Q'.eqv_refl 0

/-- The complete lossless all-cutoff stochastic row commutes with reflection.
The proof branches explicitly over coherent, retained-incoherent, and
Gibbs-null sources. -/
theorem allCutoffRetainedFineIntertwinerKernel_reflection
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (source : SlabPhysicalSourceEntry S.fine)
    (target : AllCutoffRetainedTarget)
    (htarget : target ∈ allCutoffRetainedTargets S) :
    allCutoffRetainedFineIntertwinerKernel S
        (reflectSlabPhysicalSourceEntry source)
        (reflectAllCutoffRetainedTarget S target) ≈
      allCutoffRetainedFineIntertwinerKernel S source target := by
  have hreflectedFine : S.fine.reflectLabelling source.1 ∈
      S.fine.physicalLabellings :=
    reflectSupportedSlabFaceLabelling_mem source.2
  by_cases hpositive : (0 : Q') < S.fine.physicalTerm source.1
  · have hreflectedPositive :
        (0 : Q') < S.fine.physicalTerm
          (S.fine.reflectLabelling source.1) :=
      (physicalTerm_reflection_positive_iff S.fine source.2).mpr
        hpositive
    by_cases hpartition :
        (0 : Q') < wholeSlabRawRowPartition S source.1
    · have hreflectedPartition :
          (0 : Q') < wholeSlabRawRowPartition S
            (S.fine.reflectLabelling source.1) :=
        (wholeSlabRawRowPartition_reflection_pos_iff
          S source.1).mpr hpartition
      cases target with
      | inl coarseState =>
          simp only [reflectAllCutoffRetainedTarget]
          have hcoarse :=
            (allCutoffRetainedCoarseTarget_mem_iff S coarseState).mp
              htarget
          let original := coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1 source.2 hpartition
          let reflected := coherentSlabRecouplingSourceOfRawPartitionPos
            S (S.fine.reflectLabelling source.1)
              hreflectedFine hreflectedPartition
          refine Q'.eqv_trans _
            (wholeSlabRecouplingConditionalKernel reflected
              (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
          · exact Q'.eqv_of_eq
              (allCutoffRetainedFineIntertwinerKernel_eq_recoupling
                S (reflectSlabPhysicalSourceEntry source)
                hreflectedPositive hreflectedPartition _)
          refine Q'.eqv_trans _
            (wholeSlabRecouplingConditionalKernel
              (reflectCoherentSlabRecouplingSource original)
              (S.coarse.reflectLabelling coarseState)) _ ?_ ?_
          · exact wholeSlabConditionalKernel_eq_of_fineState_eq
              reflected (reflectCoherentSlabRecouplingSource original)
              rfl _
          refine Q'.eqv_trans _
            (wholeSlabRecouplingConditionalKernel original coarseState) _
            (wholeSlabRecouplingConditionalKernel_reflection
              original hcoarse) ?_
          exact Q'.eqv_symm (Q'.eqv_of_eq
            (allCutoffRetainedFineIntertwinerKernel_eq_recoupling
              S source hpositive hpartition coarseState))
      | inr retained =>
          simp only [reflectAllCutoffRetainedTarget]
          unfold allCutoffRetainedFineIntertwinerKernel
            reflectSlabPhysicalSourceEntry
          rw [dif_pos hreflectedPositive, dif_pos hreflectedPartition,
            dif_pos hpositive, dif_pos hpartition]
          exact Q'.eqv_refl 0
    · have hreflectedNotPartition :
          ¬ (0 : Q') < wholeSlabRawRowPartition S
            (S.fine.reflectLabelling source.1) := by
        intro hreflected
        exact hpartition
          ((wholeSlabRawRowPartition_reflection_pos_iff
            S source.1).mp hreflected)
      cases target with
      | inl coarseState =>
          simp only [reflectAllCutoffRetainedTarget]
          unfold allCutoffRetainedFineIntertwinerKernel
            reflectSlabPhysicalSourceEntry
          rw [dif_pos hreflectedPositive, dif_neg hreflectedNotPartition,
            dif_pos hpositive, dif_neg hpartition]
          exact Q'.eqv_refl 0
      | inr retained =>
          simp only [reflectAllCutoffRetainedTarget]
          have hretained :=
            (allCutoffRetainedFineTarget_mem_iff S retained).mp htarget
          exact
            allCutoffRetainedFineIntertwinerKernel_reflection_incoherent_retained
              S source hpositive hpartition retained hretained
  · have hreflectedNotPositive :
        ¬ (0 : Q') < S.fine.physicalTerm
          (S.fine.reflectLabelling source.1) := by
      intro hreflected
      exact hpositive
        ((physicalTerm_reflection_positive_iff S.fine source.2).mp
          hreflected)
    cases target with
    | inl coarseState =>
        simp only [reflectAllCutoffRetainedTarget]
        have hcoarse :=
          (allCutoffRetainedCoarseTarget_mem_iff S coarseState).mp htarget
        exact
          allCutoffRetainedFineIntertwinerKernel_reflection_not_positive_coarse
            S hfineCutoff source hpositive coarseState hcoarse
    | inr retained =>
        simp only [reflectAllCutoffRetainedTarget]
        exact
          allCutoffRetainedFineIntertwinerKernel_reflection_not_positive_retained
            S source hpositive retained

/-! ## Axiom audit -/

#print axioms reflectAllCutoffRetainedTarget_mem
#print axioms reflectAllCutoffRetainedTarget_involutive
#print axioms retainedFineIntertwinerPartition_reflection
#print axioms retainedFineIntertwinerConditionalKernel_reflection
#print axioms retainedSamePhysicalStateKernel_reflection
#print axioms allCutoffRetainedFineIntertwinerKernel_reflection

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
