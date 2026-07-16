/-
# Global finite-state pushforward for the SU(2) parity shadow

The cellular parity construction already supplies one coarse cutoff-one
labelling for every fine SU(2) labelling.  This module upgrades that local
coefficient map to a single normalized kernel on the full finite coarse
labelling space.  It then defines the exact finite fibre-summed fine weight
induced by the kernel.

No equality with the physical coarse Yang--Mills weight is asserted.  The
global information-loss fence at the end records why such an equality needs
a new summed-amplitude argument: two distinct bounded fine-spin states lie in
the same deterministic parity fibre and have identical global kernel rows.
-/

import YMGap.Continuum.Z4DyadicSU2ParitySpinKernel
import YMGap.Continuum.Z4CutoffOneSupportBijection
import YMGap.Continuum.Z4ExplicitSpinFoamBounds
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParitySpinKernel
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite, injective key for cutoff-one coarse labellings -/

/-- The canonical support key of the parity-shadow target labelling. -/
def dyadicParityTargetSupportIds (n : Nat)
    (finePhysical : EdgeLabelling) : List Nat :=
  excitedPlaquetteIds n
    (coarseParityPhysicalLabelling n finePhysical)

theorem dyadicParityTargetSupportIds_mem (n : Nat)
    (finePhysical : EdgeLabelling) :
    dyadicParityTargetSupportIds n finePhysical ∈
      cutoffOneFaceSupports n := by
  have htarget :=
    coarseParityPhysicalLabelling_mem_cutoff_one n finePhysical
  have htargetMap : coarseParityPhysicalLabelling n finePhysical ∈
      (cutoffOneFaceSupports n).map componentLabel := by
    rw [← explicitPhysicalLabellings_one_eq_supportIndicators]
    exact htarget
  obtain ⟨support, hsupport, heq⟩ := List.mem_map.mp htargetMap
  have hids := excitedPlaquetteIds_componentLabel_eq_support hsupport
  unfold dyadicParityTargetSupportIds
  rw [← heq, hids]
  exact hsupport

/-- On the enumerated cutoff-one state space, the support key determines the
whole function-valued edge labelling. -/
theorem cutoffOne_supportIds_injective
    {n : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ explicitPhysicalLabellings 1 n)
    (hright : right ∈ explicitPhysicalLabellings 1 n)
    (hids : excitedPlaquetteIds n left =
      excitedPlaquetteIds n right) :
    left = right := by
  have hleftMap : left ∈
      (cutoffOneFaceSupports n).map componentLabel := by
    rw [← explicitPhysicalLabellings_one_eq_supportIndicators]
    exact hleft
  have hrightMap : right ∈
      (cutoffOneFaceSupports n).map componentLabel := by
    rw [← explicitPhysicalLabellings_one_eq_supportIndicators]
    exact hright
  obtain ⟨leftSupport, hleftSupport, hleftEq⟩ :=
    List.mem_map.mp hleftMap
  obtain ⟨rightSupport, hrightSupport, hrightEq⟩ :=
    List.mem_map.mp hrightMap
  have hleftIds : excitedPlaquetteIds n left = leftSupport := by
    rw [← hleftEq]
    exact excitedPlaquetteIds_componentLabel_eq_support hleftSupport
  have hrightIds : excitedPlaquetteIds n right = rightSupport := by
    rw [← hrightEq]
    exact excitedPlaquetteIds_componentLabel_eq_support hrightSupport
  have hsupport : leftSupport = rightSupport := by
    rw [← hleftIds, ← hrightIds]
    exact hids
  exact hleftEq.symm.trans
    ((congrArg componentLabel hsupport).trans hrightEq)

/-! ## 2. One global deterministic kernel row -/

/-- The global 0/1 kernel from a fine SU(2) labelling to the finite
cutoff-one coarse labelling space.  Equality is decided through the canonical
finite support key, not through function extensionality. -/
def dyadicParityGlobalKernel (n : Nat)
    (finePhysical coarsePhysical : EdgeLabelling) : Q' :=
  deterministicKernel (dyadicParityTargetSupportIds n) finePhysical
    (excitedPlaquetteIds n coarsePhysical)

theorem dyadicParityGlobalKernel_nonnegative
    (n : Nat) (finePhysical coarsePhysical : EdgeLabelling) :
    (0 : Q') ≤
      dyadicParityGlobalKernel n finePhysical coarsePhysical := by
  exact deterministicKernel_nonnegative
    (dyadicParityTargetSupportIds n) finePhysical
    (excitedPlaquetteIds n coarsePhysical)

theorem dyadicParityGlobalKernel_on_image
    (n : Nat) (finePhysical : EdgeLabelling) :
    dyadicParityGlobalKernel n finePhysical
      (coarseParityPhysicalLabelling n finePhysical) = 1 := by
  exact deterministicKernel_on_image
    (dyadicParityTargetSupportIds n) finePhysical

theorem dyadicParityGlobalKernel_off_support_key
    {n : Nat} {finePhysical coarsePhysical : EdgeLabelling}
    (hne : excitedPlaquetteIds n coarsePhysical ≠
      dyadicParityTargetSupportIds n finePhysical) :
    dyadicParityGlobalKernel n finePhysical coarsePhysical = 0 := by
  exact deterministicKernel_off_image hne

/-- Within the finite coarse state space, nonzero kernel mass identifies the
unique target labelling, not merely a support-equivalent representative. -/
theorem dyadicParityGlobalKernel_nonzero_target_eq
    {n : Nat} {finePhysical coarsePhysical : EdgeLabelling}
    (hcoarse : coarsePhysical ∈ explicitPhysicalLabellings 1 n)
    (hnonzero : dyadicParityGlobalKernel n finePhysical coarsePhysical ≠ 0) :
    coarsePhysical = coarseParityPhysicalLabelling n finePhysical := by
  have hkey : excitedPlaquetteIds n coarsePhysical =
      dyadicParityTargetSupportIds n finePhysical := by
    by_cases h : excitedPlaquetteIds n coarsePhysical =
        dyadicParityTargetSupportIds n finePhysical
    · exact h
    · exact absurd (dyadicParityGlobalKernel_off_support_key h) hnonzero
  apply cutoffOne_supportIds_injective hcoarse
    (coarseParityPhysicalLabelling_mem_cutoff_one n finePhysical)
  unfold dyadicParityTargetSupportIds at hkey
  exact hkey

private theorem listQSum_map_local {A B : Type}
    (f : B → Q') (g : A → B) : ∀ xs : List A,
    listQSum f (xs.map g) =
      listQSum (fun x => f (g x)) xs
  | [] => rfl
  | _ :: xs => congrArg (fun tail => f (g _) + tail)
      (listQSum_map_local f g xs)

/-- Every global kernel row has exact total mass one over the full finite
coarse cutoff-one labelling enumeration. -/
theorem dyadicParityGlobalKernel_row_normalized
    (n : Nat) (finePhysical : EdgeLabelling) :
    listQSum (dyadicParityGlobalKernel n finePhysical)
      (explicitPhysicalLabellings 1 n) ≈ 1 := by
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  rw [listQSum_map_local]
  refine Q'.eqv_trans _
    (listQSum
      (deterministicKernel (dyadicParityTargetSupportIds n) finePhysical)
      (cutoffOneFaceSupports n)) _ ?_ ?_
  · apply
      FiniteDeterministicKernelPushforward.listQSum_congr_on
    intro support hsupport
    unfold dyadicParityGlobalKernel
    rw [excitedPlaquetteIds_componentLabel_eq_support hsupport]
    exact Q'.eqv_refl _
  · exact deterministicKernel_row_normalized
      (dyadicParityTargetSupportIds n) finePhysical
      (cutoffOneFaceSupports n)
      (cutoffOneFaceSupports_nodup n)
      (dyadicParityTargetSupportIds_mem n finePhysical)

/-! ## 3. Exact finite fibre-summed fine weight -/

def dyadicParityFineStateSpace (K n : Nat) : List EdgeLabelling :=
  explicitPhysicalLabellings K (2 * n)

def dyadicParityFibreB (n : Nat) (coarsePhysical finePhysical : EdgeLabelling) :
    Bool :=
  decide (excitedPlaquetteIds n coarsePhysical =
    dyadicParityTargetSupportIds n finePhysical)

def dyadicParityFineFibre (K n : Nat)
    (coarsePhysical : EdgeLabelling) : List EdgeLabelling :=
  (dyadicParityFineStateSpace K n).filter
    (dyadicParityFibreB n coarsePhysical)

/-- Exact finite fibre sum written directly as a kernel pushforward. -/
def dyadicParityKernelPushforwardWeight (K n : Nat)
    (coarsePhysical : EdgeLabelling) : Q' :=
  kernelPushforwardWeight (dyadicParityFineStateSpace K n)
    (explicitSpinFoamWeight K (2 * n))
    (dyadicParityTargetSupportIds n)
    (excitedPlaquetteIds n coarsePhysical)

/-- The same exact finite fibre sum written as a filtered source sum. -/
def dyadicParityFilteredPushforwardWeight (K n : Nat)
    (coarsePhysical : EdgeLabelling) : Q' :=
  fiberWeight (dyadicParityFineStateSpace K n)
    (explicitSpinFoamWeight K (2 * n))
    (dyadicParityTargetSupportIds n)
    (excitedPlaquetteIds n coarsePhysical)

theorem dyadicParityFilteredPushforwardWeight_eq_fibre_list
    (K n : Nat) (coarsePhysical : EdgeLabelling) :
    dyadicParityFilteredPushforwardWeight K n coarsePhysical =
      listQSum (explicitSpinFoamWeight K (2 * n))
        (dyadicParityFineFibre K n coarsePhysical) := by
  rfl

theorem dyadicParityKernelPushforwardWeight_eq_filtered
    (K n : Nat) (coarsePhysical : EdgeLabelling) :
    dyadicParityKernelPushforwardWeight K n coarsePhysical ≈
      dyadicParityFilteredPushforwardWeight K n coarsePhysical := by
  exact kernelPushforwardWeight_eqv_fiberWeight
    (explicitSpinFoamWeight K (2 * n))
    (dyadicParityTargetSupportIds n)
    (excitedPlaquetteIds n coarsePhysical)
    (dyadicParityFineStateSpace K n)

theorem dyadicParityKernelPushforwardWeight_nonnegative
    (K n : Nat) (coarsePhysical : EdgeLabelling) :
    (0 : Q') ≤
      dyadicParityKernelPushforwardWeight K n coarsePhysical := by
  apply kernelPushforwardWeight_nonnegative
  intro finePhysical _
  simpa [explicitSpinFoamWeight] using
    explicitSpinFoamSummand_nonnegative K (2 * n) finePhysical

theorem dyadicParityFilteredPushforwardWeight_nonnegative
    (K n : Nat) (coarsePhysical : EdgeLabelling) :
    (0 : Q') ≤
      dyadicParityFilteredPushforwardWeight K n coarsePhysical := by
  apply fiberWeight_nonnegative
  intro finePhysical _
  simpa [explicitSpinFoamWeight] using
    explicitSpinFoamSummand_nonnegative K (2 * n) finePhysical

/-- Summing the exact fibre weights over the canonical finite support keys
preserves the complete fine finite-box partition. -/
theorem dyadicParitySupportPushforward_total (K n : Nat) :
    listQSum
        (kernelPushforwardWeight (dyadicParityFineStateSpace K n)
          (explicitSpinFoamWeight K (2 * n))
          (dyadicParityTargetSupportIds n))
        (cutoffOneFaceSupports n) ≈
      explicitPhysicalSpinFoamPartition K (2 * n) := by
  unfold explicitPhysicalSpinFoamPartition dyadicParityFineStateSpace
  exact kernelPushforwardWeight_total
    (explicitPhysicalLabellings K (2 * n))
    (explicitSpinFoamWeight K (2 * n))
    (dyadicParityTargetSupportIds n)
    (cutoffOneFaceSupports n)
    (cutoffOneFaceSupports_nodup n)
    (fun finePhysical _ =>
      dyadicParityTargetSupportIds_mem n finePhysical)

/-- The same partition-preservation identity, now indexed by the full
function-valued coarse labelling enumeration rather than by support keys. -/
theorem dyadicParityKernelPushforward_partition_preserved (K n : Nat) :
    listQSum (dyadicParityKernelPushforwardWeight K n)
        (explicitPhysicalLabellings 1 n) ≈
      explicitPhysicalSpinFoamPartition K (2 * n) := by
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  rw [listQSum_map_local]
  refine Q'.eqv_trans _
    (listQSum
      (kernelPushforwardWeight (dyadicParityFineStateSpace K n)
        (explicitSpinFoamWeight K (2 * n))
        (dyadicParityTargetSupportIds n))
      (cutoffOneFaceSupports n)) _ ?_ ?_
  · apply
      FiniteDeterministicKernelPushforward.listQSum_congr_on
    intro support hsupport
    unfold dyadicParityKernelPushforwardWeight
    rw [excitedPlaquetteIds_componentLabel_eq_support hsupport]
    exact Q'.eqv_refl _
  · exact dyadicParitySupportPushforward_total K n

/-! ## 4. Global information-loss fence -/

theorem oddPhysicalPlaquettes_zeroEdgeLabelling (n : Nat) :
    oddPhysicalPlaquettes n zeroEdgeLabelling = [] := by
  unfold oddPhysicalPlaquettes
  generalize enumerate
      (YMGap.Continuum.Z4FiniteBoxExhaustion.boxPlaquettes n) = entries
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filter_cons]
      have hfalse :
          decide (zeroEdgeLabelling head.1 % 2 = 1) = false := by
        rfl
      rw [hfalse]
      exact ih

theorem coarseParityPhysicalLabelling_zeroEdgeLabelling (n : Nat) :
    coarseParityPhysicalLabelling n zeroEdgeLabelling =
      zeroEdgeLabelling := by
  funext coarseId
  unfold coarseParityPhysicalLabelling
  change (if coarseId < plaquetteEdgeCount n then
      dyadicParitySpinCoefficient n zeroEdgeLabelling
        (YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.boxPlaquetteAt
          n coarseId)
    else 0) = 0
  by_cases hlt : coarseId < plaquetteEdgeCount n
  · rw [if_pos hlt]
    unfold dyadicParitySpinCoefficient
    rw [oddPhysicalPlaquettes_zeroEdgeLabelling]
    have hfalse :
        YMGap.Continuum.Z4DyadicModTwoCellularKernel.dyadicFacePushforward
          (YMGap.Continuum.Z4DyadicModTwoCellularKernel.supportCoefficient [])
          (YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.boxPlaquetteAt
            n coarseId) = false := by
      unfold
        YMGap.Continuum.Z4DyadicModTwoCellularKernel.dyadicFacePushforward
      generalize
        YMGap.Continuum.Z4DyadicModTwoCellularKernel.dyadicFacePreimages
          (YMGap.Continuum.Z4CanonicalPolymerAnimalBridge.boxPlaquetteAt
            n coarseId) = faces
      induction faces with
      | nil => rfl
      | cons head tail ih =>
          unfold
            YMGap.Continuum.Z4DyadicModTwoCellularKernel.xorList
          have hcoefficient :
              YMGap.Continuum.Z4DyadicModTwoCellularKernel.supportCoefficient
                [] head = false := by
            rfl
          rw [hcoefficient, ih]
          rfl
    rw [hfalse]
    rfl
  · rw [if_neg hlt]

theorem dyadicParityTargetSupportIds_zeroEdgeLabelling (n : Nat) :
    dyadicParityTargetSupportIds n zeroEdgeLabelling = [] := by
  unfold dyadicParityTargetSupportIds
  rw [coarseParityPhysicalLabelling_zeroEdgeLabelling]
  unfold excitedPlaquetteIds
  generalize physicalFaceEdges n = edges
  induction edges with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filter_cons]
      have hfalse : decide (1 ≤ zeroEdgeLabelling head) = false := by
        rfl
      rw [hfalse]
      exact ih

theorem dyadicParityGlobalKernel_information_loss
    (n : Nat) (coarsePhysical : EdgeLabelling) :
    dyadicParityGlobalKernel n evenTwoPhysical coarsePhysical =
      dyadicParityGlobalKernel n zeroEdgeLabelling coarsePhysical := by
  unfold dyadicParityGlobalKernel deterministicKernel
    dyadicParityTargetSupportIds
  rw [coarseParityPhysicalLabelling_information_loss]

theorem boundedGlobalKernel_information_loss_fence (n : Nat) :
    zeroEdgeLabelling ∈
        dyadicParityFineStateSpace 2 (n + 1) ∧
      evenTwoPhysical ∈
        dyadicParityFineStateSpace 2 (n + 1) ∧
      zeroEdgeLabelling ≠ evenTwoPhysical ∧
      (∀ coarsePhysical,
        dyadicParityGlobalKernel (n + 1) zeroEdgeLabelling coarsePhysical =
          dyadicParityGlobalKernel (n + 1) evenTwoPhysical
            coarsePhysical) := by
  have hfence := boundedSpin_information_loss_fence n
  exact ⟨hfence.1, hfence.2.1, hfence.2.2.1,
    fun coarsePhysical =>
      (dyadicParityGlobalKernel_information_loss
        (n + 1) coarsePhysical).symm⟩

/-- Two distinct bounded fine-spin states occur in one global parity fibre.
This is an exact finite obstruction to treating the parity target as a
lossless reindexing of the SU(2) state space. -/
theorem boundedParityFibre_contains_distinct_pair (n : Nat) :
    let coarseTarget :=
      coarseParityPhysicalLabelling (n + 1) zeroEdgeLabelling
    zeroEdgeLabelling ∈
        dyadicParityFineFibre 2 (n + 1) coarseTarget ∧
      evenTwoPhysical ∈
        dyadicParityFineFibre 2 (n + 1) coarseTarget ∧
      zeroEdgeLabelling ≠ evenTwoPhysical := by
  dsimp only
  have hfence := boundedSpin_information_loss_fence n
  constructor
  · apply List.mem_filter.mpr
    constructor
    · exact hfence.1
    · simp [dyadicParityFibreB, dyadicParityTargetSupportIds]
  · constructor
    · apply List.mem_filter.mpr
      constructor
      · exact hfence.2.1
      · unfold dyadicParityFibreB dyadicParityTargetSupportIds
        rw [← hfence.2.2.2]
        simp
    · exact hfence.2.2.1

/-! ## Axiom gates -/

#print axioms dyadicParityTargetSupportIds_mem
#print axioms cutoffOne_supportIds_injective
#print axioms dyadicParityGlobalKernel_nonnegative
#print axioms dyadicParityGlobalKernel_on_image
#print axioms dyadicParityGlobalKernel_nonzero_target_eq
#print axioms dyadicParityGlobalKernel_row_normalized
#print axioms dyadicParityFilteredPushforwardWeight_eq_fibre_list
#print axioms dyadicParityKernelPushforwardWeight_eq_filtered
#print axioms dyadicParityKernelPushforwardWeight_nonnegative
#print axioms dyadicParityFilteredPushforwardWeight_nonnegative
#print axioms dyadicParitySupportPushforward_total
#print axioms dyadicParityKernelPushforward_partition_preserved
#print axioms oddPhysicalPlaquettes_zeroEdgeLabelling
#print axioms coarseParityPhysicalLabelling_zeroEdgeLabelling
#print axioms dyadicParityTargetSupportIds_zeroEdgeLabelling
#print axioms dyadicParityGlobalKernel_information_loss
#print axioms boundedGlobalKernel_information_loss_fence
#print axioms boundedParityFibre_contains_distinct_pair

end YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
