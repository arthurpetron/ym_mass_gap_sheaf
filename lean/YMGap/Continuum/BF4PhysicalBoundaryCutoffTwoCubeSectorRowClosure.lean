/-
# Exact cutoff-two 65-sector row closure

The literal 65-state sector is closed under support of the genuine physical
reflected kernel at cutoff two.  For the fundamental cube this follows from
the checked CSP classifier directly.  For each doubled-spin subset source,
the source-support containment theorem first supplies the fundamental cube on
the same boundary word, after which the same classifier applies.

This is an exact finite-volume, finite-cutoff row-closure theorem.  It is not
a cutoff-uniform, infinite-volume, or continuum mass-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetSourceSupport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact sector lies in the physical half-state carrier -/

theorem cutoffTwoCubeSectorState_mem_halfStates
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    state ∈ centralHalfStates 2 0 := by
  rcases List.mem_cons.mp hstate with hcube | hdoubled
  · subst state
    exact centralLowerCubeState_mem_centralHalfStates (by decide)
  · have hsemantics :=
      (mem_cutoffTwoDoubledCubeSubsetStates_iff state).mp hdoubled
    unfold centralHalfStates
    apply boundedEdgeLabellings_complete
    · intro id _
      have hcubeDecision : Decidable (id ∈ centralLowerCubeFaceIds) :=
        List.instDecidableMemOfLawfulBEq id centralLowerCubeFaceIds
      cases hcubeDecision with
      | isTrue hcube =>
        rcases hsemantics.1 id hcube with hzero | htwo
        · rw [hzero]
          decide
        · rw [htwo]
          decide
      | isFalse hcube =>
        rw [hsemantics.2 id hcube]
        decide
    · intro id hnotLower
      apply hsemantics.2 id
      intro hcube
      exact hnotLower (centralLowerCubeFaceIds_subset_lower id hcube)

/-! ## 2. Shared support forces the target into the sector -/

theorem target_mem_sector_of_shared_halfAmplitude_support
    (source target boundary : EdgeLabelling)
    (hsource : source ∈ cutoffTwoCubeSectorStates)
    (htarget : target ∈ centralHalfStates 2 0)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (hsourceNonzero : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary) 0)
    (htargetNonzero : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target boundary) 0) :
    target ∈ cutoffTwoCubeSectorStates := by
  have hcubeNonzero : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        centralLowerCubeState boundary) 0 := by
    rcases List.mem_cons.mp hsource with hcube | hdoubled
    · subst source
      exact hsourceNonzero
    · exact
        cube_halfAmplitude_ne_zero_of_doubledSubset_halfAmplitude_ne_zero
          source boundary hdoubled hboundary hsourceNonzero
  have hclassifier :=
    cutoffTwoCubeSubsetState_of_shared_halfAmplitude_support
      target boundary htarget hboundary hcubeNonzero htargetNonzero
  exact (cutoffTwoCubeSubsetState_iff_mem_sector htarget).mp hclassifier

theorem target_halfAmplitude_eqv_zero_of_not_mem_sector
    (source target boundary : EdgeLabelling)
    (hsource : source ∈ cutoffTwoCubeSectorStates)
    (htarget : target ∈ centralHalfStates 2 0)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (houtside : target ∉ cutoffTwoCubeSectorStates)
    (hsourceNonzero : ¬ Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary) 0) :
    Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target boundary) 0 := by
  let targetAmplitude :=
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target boundary
  have hdecidable : Decidable (Q'.eqv targetAmplitude 0) := by
    unfold Q'.eqv
    infer_instance
  cases hdecidable with
  | isTrue hzero => exact hzero
  | isFalse htargetNonzero =>
    exact False.elim (houtside
      (target_mem_sector_of_shared_halfAmplitude_support
        source target boundary hsource htarget hboundary
        hsourceNonzero htargetNonzero))

/-! ## 3. Pointwise vanishing and exact weighted-Gram row closure -/

theorem halfAmplitude_pair_eqv_zero_of_target_not_mem_sector
    (source target boundary : EdgeLabelling)
    (hsource : source ∈ cutoffTwoCubeSectorStates)
    (htarget : target ∈ centralHalfStates 2 0)
    (hboundary : boundary ∈ centralBoundaryChannels 2 0)
    (houtside : target ∉ cutoffTwoCubeSectorStates) :
    Q'.eqv
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target boundary) 0 := by
  let sourceAmplitude :=
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary
  let targetAmplitude :=
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target boundary
  have hdecidable : Decidable (Q'.eqv sourceAmplitude 0) := by
    unfold Q'.eqv
    infer_instance
  cases hdecidable with
  | isTrue hsourceZero =>
    exact Q'.eqv_trans _ (0 * targetAmplitude) _
      (Q'.mul_eqv_congr_right sourceAmplitude 0
        targetAmplitude hsourceZero)
      (Q'.zero_mul_eqv targetAmplitude)
  | isFalse hsourceNonzero =>
    have htargetZero :=
      target_halfAmplitude_eqv_zero_of_not_mem_sector
        source target boundary hsource htarget hboundary
        houtside hsourceNonzero
    exact Q'.eqv_trans _ (sourceAmplitude * 0) _
      (Q'.mul_eqv_congr_left sourceAmplitude targetAmplitude 0
        htargetZero)
      (Q'.mul_zero_eqv sourceAmplitude)

private theorem listQSum_eqv_zero_on {A : Type} (value : A → Q') :
    ∀ items : List A,
    (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_on value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

theorem weightedGram_cutoffTwo_cubeSector_eqv_zero_of_target_not_mem
    (source target : EdgeLabelling)
    (hsource : source ∈ cutoffTwoCubeSectorStates)
    (htarget : target ∈ centralHalfStates 2 0)
    (houtside : target ∉ cutoffTwoCubeSectorStates) :
    weightedGram (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0)
        source target ≈ 0 := by
  unfold weightedGram
  apply listQSum_eqv_zero_on
  intro boundary hboundary
  have hpair := halfAmplitude_pair_eqv_zero_of_target_not_mem_sector
    source target boundary hsource htarget hboundary houtside
  exact Q'.eqv_trans _
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary * 0) _
    (Q'.mul_eqv_congr_left
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary)
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source boundary *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target boundary)
      0 hpair)
    (Q'.mul_zero_eqv
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary))

/-- Exact genuine physical-kernel row closure of the literal 65-state
sector at cutoff two and half extent zero. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
    (source target : EdgeLabelling)
    (hsource : source ∈ cutoffTwoCubeSectorStates)
    (htarget : target ∈ centralHalfStates 2 0)
    (houtside : target ∉ cutoffTwoCubeSectorStates) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      source target ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_eq_weightedGram
      cutoffTwoHalfCoupling
      (cutoffTwoCubeSectorState_mem_halfStates hsource) htarget)
    (weightedGram_cutoffTwo_cubeSector_eqv_zero_of_target_not_mem
      source target hsource htarget houtside)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure.target_mem_sector_of_shared_halfAmplitude_support
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure.centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
