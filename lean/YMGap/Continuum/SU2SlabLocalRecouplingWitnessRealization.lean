/-
# Local physical realization of complete crossed recoupling targets

At each actual slab link, the complete crossed bistochastic matrix has a
right-tree target carrier and a left-tree source carrier of the same finite
size.  Equal written rank therefore recodes every target as one complete
left carrier.  The canonical reconstruction theorem then turns that carrier
into two literal accepted production auxiliary labellings.

This is deliberately a finite carrier reindexing.  It does not identify a
right-associated vector with a left-associated vector, and it makes no
global collision or column-capacity claim.

Constructive contract: explicit finite rank, literal witness membership, no
choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticRankReindex
import YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
import YMGap.Continuum.SU2CompleteCarrierDecidableEquality
import YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel

namespace YMGap.Continuum.SU2SlabLocalRecouplingWitnessRealization

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2CompleteCarrierDecidableEquality
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler
open YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Every written target carrier is complete -/

theorem physicalSchurTensorTargets_complete
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (target : FixedRightCGChannel a₁ b₁ c₁ d₁ ×
      FixedRightCGChannel a₂ b₂ c₂ d₂) :
    target ∈
      (tensor
        (physicalSchurBistochasticKernel a₁ b₁ c₁ d₁)
        (physicalSchurBistochasticKernel a₂ b₂ c₂ d₂)).targets := by
  exact (mem_cartesian_iff _ _ target).mpr
    ⟨fixedRightChannels_complete target.1,
      fixedRightChannels_complete target.2⟩

theorem valenceFiveTensorTargets_complete
    {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : Nat}
    (target : ValenceFiveRightCarrier a₁ b₁ c₁ d₁ e₁ ×
      ValenceFiveRightCarrier a₂ b₂ c₂ d₂ e₂) :
    target ∈
      (tensor
        (valenceFiveBistochasticKernel a₁ b₁ c₁ d₁ e₁)
        (valenceFiveBistochasticKernel a₂ b₂ c₂ d₂ e₂)).targets := by
  exact (mem_cartesian_iff _ _ target).mpr
    ⟨valenceFiveRightCarriers_complete target.1,
      valenceFiveRightCarriers_complete target.2⟩

theorem valenceSixTensorTargets_complete
    {a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂ : Nat}
    (target : ValenceSixRightCarrier a₁ b₁ c₁ d₁ e₁ f₁ ×
      ValenceSixRightCarrier a₂ b₂ c₂ d₂ e₂ f₂) :
    target ∈
      (tensor
        (valenceSixBistochasticKernel a₁ b₁ c₁ d₁ e₁ f₁)
        (valenceSixBistochasticKernel a₂ b₂ c₂ d₂ e₂ f₂)).targets := by
  exact (mem_cartesian_iff _ _ target).mpr
    ⟨valenceSixRightCarriers_complete target.1,
      valenceSixRightCarriers_complete target.2⟩

theorem crossedSchurBistochasticTarget_complete {K extent : Nat}
    (D : ValenceFourCrossReplicaSwitchData K extent)
    (target : CrossedSchurTarget D) :
    target ∈ (crossedSchurBistochasticKernel D).targets :=
  physicalSchurTensorTargets_complete target

theorem crossedValenceFiveBistochasticTarget_complete {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 5)
    (target : CrossedValenceFiveMatrixTarget D) :
    target ∈ (crossedValenceFiveBistochasticKernel D).targets :=
  valenceFiveTensorTargets_complete target

theorem crossedValenceSixBistochasticTarget_complete {K extent : Nat}
    (D : CrossedSlabSwitchData K extent 6)
    (target : CrossedValenceSixMatrixTarget D) :
    target ∈ (crossedValenceSixBistochasticKernel D).targets :=
  valenceSixTensorTargets_complete target

def crossedLinkBistochasticTargetDecidableEq {K extent : Nat} :
    (degree : Nat) → (D : CrossedSlabSwitchData K extent degree) →
      DecidableEq (crossedLinkBistochasticKernelPackage degree D).Target
  | 0, _ => by
      simp only [crossedLinkBistochasticKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 1, _ => by
      simp only [crossedLinkBistochasticKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 2, _ => by
      simp only [crossedLinkBistochasticKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 3, _ => by
      simp only [crossedLinkBistochasticKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 4, _ => by
      simp only [crossedLinkBistochasticKernelPackage]
      infer_instance
  | 5, _ => by
      simp only [crossedLinkBistochasticKernelPackage]
      infer_instance
  | 6, _ => by
      simp only [crossedLinkBistochasticKernelPackage]
      infer_instance
  | degree + 7, D => False.elim (by
      have hdegree := CrossedSlabSwitchData.degree_le_six D
      omega)

def crossedLinkBistochasticTarget_mem {K extent : Nat} :
    (degree : Nat) → (D : CrossedSlabSwitchData K extent degree) →
      (target :
        (crossedLinkBistochasticKernelPackage degree D).Target) →
      target ∈
        (crossedLinkBistochasticKernelPackage degree D).kernel.targets
  | 0, _, () => List.mem_cons_self
  | 1, _, () => List.mem_cons_self
  | 2, _, () => List.mem_cons_self
  | 3, _, () => List.mem_cons_self
  | 4, D, target => by
      let D₄ := CrossedSlabSwitchData.toValenceFour D
      exact crossedSchurBistochasticTarget_complete D₄ target
  | 5, D, target =>
      crossedValenceFiveBistochasticTarget_complete D target
  | 6, D, target =>
      crossedValenceSixBistochasticTarget_complete D target
  | degree + 7, D, _ => False.elim (by
      have hdegree := CrossedSlabSwitchData.degree_le_six D
      omega)

/-! ## 2. Complete left carriers become literal production witnesses -/

structure CrossedProductionWitnessPair {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) where
  leftAuxiliary : SlabLabelling
  rightAuxiliary : SlabLabelling
  left_mem : leftAuxiliary ∈
    slabLinkFusionWitnesses K extent (higherCrossedLeftPhysical D) D.link
  right_mem : rightAuxiliary ∈
    slabLinkFusionWitnesses K extent (higherCrossedRightPhysical D) D.link

def crossedProductionWitnessPairOfSource {K extent : Nat} :
    (degree : Nat) → (D : CrossedSlabSwitchData K extent degree) →
      (source : (crossedLinkBistochasticKernelPackage degree D).Source) →
      CrossedProductionWitnessPair D
  | 0, D, _ =>
      ⟨higherCrossedLeftAuxiliary D, higherCrossedRightAuxiliary D,
        higherCrossedLeftAuxiliary_mem D,
        higherCrossedRightAuxiliary_mem D⟩
  | 1, D, _ =>
      ⟨higherCrossedLeftAuxiliary D, higherCrossedRightAuxiliary D,
        higherCrossedLeftAuxiliary_mem D,
        higherCrossedRightAuxiliary_mem D⟩
  | 2, D, _ =>
      ⟨higherCrossedLeftAuxiliary D, higherCrossedRightAuxiliary D,
        higherCrossedLeftAuxiliary_mem D,
        higherCrossedRightAuxiliary_mem D⟩
  | 3, D, _ =>
      ⟨higherCrossedLeftAuxiliary D, higherCrossedRightAuxiliary D,
        higherCrossedLeftAuxiliary_mem D,
        higherCrossedRightAuxiliary_mem D⟩
  | 4, D, source => by
      let leftBounded : SlabFaceLabellingBounded K extent
          (higherCrossedLeftPhysical D) :=
        twoReplicaFaceSwapLeft_bounded D.mask D.leftBounded D.rightBounded
      let rightBounded : SlabFaceLabellingBounded K extent
          (higherCrossedRightPhysical D) :=
        twoReplicaFaceSwapRight_bounded D.mask D.leftBounded D.rightBounded
      exact
        ⟨valenceFourLeftAuxiliary source.1,
          valenceFourLeftAuxiliary source.2,
          valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
            leftBounded D.degree_eq source.1,
          valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
            rightBounded D.degree_eq source.2⟩
  | 5, D, source => by
      let leftBounded : SlabFaceLabellingBounded K extent
          (higherCrossedLeftPhysical D) :=
        twoReplicaFaceSwapLeft_bounded D.mask D.leftBounded D.rightBounded
      let rightBounded : SlabFaceLabellingBounded K extent
          (higherCrossedRightPhysical D) :=
        twoReplicaFaceSwapRight_bounded D.mask D.leftBounded D.rightBounded
      exact
        ⟨valenceFiveLeftAuxiliary source.1,
          valenceFiveLeftAuxiliary source.2,
          valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
            leftBounded D.degree_eq source.1,
          valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
            rightBounded D.degree_eq source.2⟩
  | 6, D, source => by
      let leftBounded : SlabFaceLabellingBounded K extent
          (higherCrossedLeftPhysical D) :=
        twoReplicaFaceSwapLeft_bounded D.mask D.leftBounded D.rightBounded
      let rightBounded : SlabFaceLabellingBounded K extent
          (higherCrossedRightPhysical D) :=
        twoReplicaFaceSwapRight_bounded D.mask D.leftBounded D.rightBounded
      exact
        ⟨valenceSixLeftAuxiliary source.1,
          valenceSixLeftAuxiliary source.2,
          valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
            leftBounded D.degree_eq source.1,
          valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
            rightBounded D.degree_eq source.2⟩
  | degree + 7, D, _ => False.elim (by
      have hdegree := CrossedSlabSwitchData.degree_le_six D
      omega)

/-! ## 3. Every local right-tree target has a physical realization -/

def crossedLinkTargetToProductionSourceAtEqualRank
    {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree)
    (target : (crossedLinkBistochasticKernelPackage degree D).Target) :
    (crossedLinkBistochasticKernelPackage degree D).Source := by
  letI := crossedLinkBistochasticTargetDecidableEq degree D
  exact
    FiniteBistochasticRankReindex.FiniteBistochasticQKernel.targetToSourceAtEqualRank
      (crossedLinkBistochasticKernelPackage degree D).kernel
      (crossedLinkBistochasticProductionSource degree D) target

theorem crossedLinkTargetToProductionSourceAtEqualRank_mem
    {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree)
    (target : (crossedLinkBistochasticKernelPackage degree D).Target) :
    crossedLinkTargetToProductionSourceAtEqualRank D target ∈
      (crossedLinkBistochasticKernelPackage degree D).kernel.sources := by
  letI := crossedLinkBistochasticTargetDecidableEq degree D
  exact
    FiniteBistochasticRankReindex.FiniteBistochasticQKernel.targetToSourceAtEqualRank_mem
      (crossedLinkBistochasticKernelPackage degree D).kernel
      (crossedLinkBistochasticProductionSource degree D) target
      (crossedLinkBistochasticTarget_mem degree D target)

/-- **Every complete local right-tree target is constructively realized by
two accepted production witnesses at the crossed physical fields.** -/
def crossedLinkTargetProductionWitnessPair
    {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree)
    (target : (crossedLinkBistochasticKernelPackage degree D).Target) :
    CrossedProductionWitnessPair D :=
  crossedProductionWitnessPairOfSource degree D
    (crossedLinkTargetToProductionSourceAtEqualRank D target)

#print axioms crossedLinkBistochasticTarget_mem
#print axioms crossedProductionWitnessPairOfSource
#print axioms crossedLinkTargetToProductionSourceAtEqualRank_mem
#print axioms crossedLinkTargetProductionWitnessPair

end YMGap.Continuum.SU2SlabLocalRecouplingWitnessRealization
