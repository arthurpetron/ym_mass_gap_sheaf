/-
# Literal witness realization of physical-pair recoupling columns

Every target column of the complete physical-pair matrix has the same finite
rank as its source carrier.  Rank reindexing first recodes a target as one
complete left carrier.  Canonical left-carrier reconstruction then produces
two literal accepted auxiliary labellings over the fixed physical fields.

The construction needs one accepted production row to anchor the finite rank
reindexing.  At degrees zero through three that row is also the realized
witness.  At degrees four through six the complete left carrier itself
determines the reconstructed auxiliary labels.

Constructive contract: explicit finite ranks and literal witness membership;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
import YMGap.Continuum.SU2SlabLocalRecouplingWitnessRealization

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2CompleteCarrierDecidableEquality
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabLocalRecouplingWitnessRealization
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Complete target carriers -/

def slabPhysicalPairRecouplingTargetDecidableEq {extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      DecidableEq (slabPhysicalPairRecouplingKernelPackage degree D).Target
  | 0, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 1, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 2, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 3, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage,
        unitFiniteBistochasticQKernelPackage]
      infer_instance
  | 4, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage]
      infer_instance
  | 5, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage]
      infer_instance
  | 6, _ => by
      simp only [slabPhysicalPairRecouplingKernelPackage]
      infer_instance
  | degree + 7, D => False.elim (by
      have hdegree := D.degree_le_six
      have hseven_le_six : 7 ≤ 6 :=
        Nat.le_trans (Nat.le_add_left 7 degree) hdegree
      exact Nat.not_succ_le_self 6 hseven_le_six)

def slabPhysicalPairRecouplingTarget_mem {extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      (target :
        (slabPhysicalPairRecouplingKernelPackage degree D).Target) →
      target ∈
        (slabPhysicalPairRecouplingKernelPackage degree D).kernel.targets
  | 0, _, () => List.mem_cons_self
  | 1, _, () => List.mem_cons_self
  | 2, _, () => List.mem_cons_self
  | 3, _, () => List.mem_cons_self
  | 4, _, target => physicalSchurTensorTargets_complete target
  | 5, _, target => valenceFiveTensorTargets_complete target
  | 6, _, target => valenceSixTensorTargets_complete target
  | degree + 7, D, _ => False.elim (by
      have hdegree := D.degree_le_six
      have hseven_le_six : 7 ≤ 6 :=
        Nat.le_trans (Nat.le_add_left 7 degree) hdegree
      exact Nat.not_succ_le_self 6 hseven_le_six)

/-! ## 2. Complete left carriers reconstruct accepted witnesses -/

structure SlabPhysicalPairProductionWitnessPair
    (K : Nat) {extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree) where
  leftAuxiliary : SlabLabelling
  rightAuxiliary : SlabLabelling
  left_mem : leftAuxiliary ∈
    slabLinkFusionWitnesses K extent D.leftPhysical D.link
  right_mem : rightAuxiliary ∈
    slabLinkFusionWitnesses K extent D.rightPhysical D.link

def slabPhysicalPairProductionWitnessPairOfSource
    {K extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      (W : SlabPhysicalPairRecouplingWitnessData K D) →
      SlabFaceLabellingBounded K extent D.leftPhysical →
      SlabFaceLabellingBounded K extent D.rightPhysical →
      (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source) →
      SlabPhysicalPairProductionWitnessPair K D
  | 0, _, W, _, _, _ =>
      ⟨W.leftAuxiliary, W.rightAuxiliary, W.left_mem, W.right_mem⟩
  | 1, _, W, _, _, _ =>
      ⟨W.leftAuxiliary, W.rightAuxiliary, W.left_mem, W.right_mem⟩
  | 2, _, W, _, _, _ =>
      ⟨W.leftAuxiliary, W.rightAuxiliary, W.left_mem, W.right_mem⟩
  | 3, _, W, _, _, _ =>
      ⟨W.leftAuxiliary, W.rightAuxiliary, W.left_mem, W.right_mem⟩
  | 4, D, _, leftBounded, rightBounded, source =>
      ⟨valenceFourLeftAuxiliary source.1,
        valenceFourLeftAuxiliary source.2,
        valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
          leftBounded D.degree_eq source.1,
        valenceFourLeftAuxiliary_mem_slabLinkFusionWitnesses
          rightBounded D.degree_eq source.2⟩
  | 5, D, _, leftBounded, rightBounded, source =>
      ⟨valenceFiveLeftAuxiliary source.1,
        valenceFiveLeftAuxiliary source.2,
        valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
          leftBounded D.degree_eq source.1,
        valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
          rightBounded D.degree_eq source.2⟩
  | 6, D, _, leftBounded, rightBounded, source =>
      ⟨valenceSixLeftAuxiliary source.1,
        valenceSixLeftAuxiliary source.2,
        valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
          leftBounded D.degree_eq source.1,
        valenceSixLeftAuxiliary_mem_slabLinkFusionWitnesses
          rightBounded D.degree_eq source.2⟩
  | degree + 7, D, _, _, _, _ => False.elim (by
      have hdegree := D.degree_le_six
      have hseven_le_six : 7 ≤ 6 :=
        Nat.le_trans (Nat.le_add_left 7 degree) hdegree
      exact Nat.not_succ_le_self 6 hseven_le_six)

/-! ## 3. Every target column has a literal witness pair -/

def slabPhysicalPairTargetToProductionSourceAtEqualRank
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (W : SlabPhysicalPairRecouplingWitnessData K D)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    (slabPhysicalPairRecouplingKernelPackage degree D).Source := by
  letI := slabPhysicalPairRecouplingTargetDecidableEq degree D
  exact
    FiniteBistochasticQKernel.targetToSourceAtEqualRank
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel
      (slabPhysicalPairRecouplingProductionSource degree D W) target

theorem slabPhysicalPairTargetToProductionSourceAtEqualRank_mem
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (W : SlabPhysicalPairRecouplingWitnessData K D)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank D W target ∈
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel.sources := by
  letI := slabPhysicalPairRecouplingTargetDecidableEq degree D
  exact
    FiniteBistochasticQKernel.targetToSourceAtEqualRank_mem
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel
      (slabPhysicalPairRecouplingProductionSource degree D W) target
      (slabPhysicalPairRecouplingTarget_mem degree D target)

/-- **Every complete local target column is represented by two literal
accepted production witnesses over the fixed physical pair.** -/
def slabPhysicalPairTargetProductionWitnessPair
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (W : SlabPhysicalPairRecouplingWitnessData K D)
    (leftBounded : SlabFaceLabellingBounded K extent D.leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent D.rightPhysical)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    SlabPhysicalPairProductionWitnessPair K D :=
  slabPhysicalPairProductionWitnessPairOfSource degree D W
    leftBounded rightBounded
    (slabPhysicalPairTargetToProductionSourceAtEqualRank D W target)

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization.slabPhysicalPairRecouplingTarget_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization.slabPhysicalPairProductionWitnessPairOfSource
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization.slabPhysicalPairTargetToProductionSourceAtEqualRank_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization.slabPhysicalPairTargetProductionWitnessPair
