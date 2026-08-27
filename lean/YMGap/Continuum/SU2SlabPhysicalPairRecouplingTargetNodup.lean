/-
# Duplicate-free whole-slab physical-pair target carriers

Every local physical-only recoupling matrix has a duplicate-free written
target list.  The unit cases are immediate; valence four is the Cartesian
product of canonical right-channel lists; valence five uses the complete
right-carrier enumeration; and valence six is the indexed final Schur target
carrier.  Heterogeneous Cartesian products then preserve duplicate freedom
over the whole slab.

This is the finite multiplicity input needed by the dependent pushforward:
one source row cannot contain the same abstract target column twice.

Constructive contract: structural finite lists only; no choice, `Classical`,
`sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
import YMGap.Continuum.SU2DirectRightFixedOutputEnumeration

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Local target lists -/

theorem valenceSixRightCarriers_nodup (a b c d e f : Nat) :
    (valenceSixBistochasticKernel a b c d e f).targets.Nodup := by
  change (indexedTargets
    (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)).Nodup
  exact indexedTargets_nodup
    (valenceSixInnerPairs b c d)
    (valenceSixInnerPairs_nodup b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    (fun pair => fixedRightChannels_nodup a pair.n e f)

theorem physicalSchurTensorTargets_nodup
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat} :
    (tensor
      (physicalSchurBistochasticKernel a₁ b₁ c₁ d₁)
      (physicalSchurBistochasticKernel a₂ b₂ c₂ d₂)).targets.Nodup :=
  cartesian_nodup _ _
    (fixedRightChannels_nodup a₁ b₁ c₁ d₁)
    (fixedRightChannels_nodup a₂ b₂ c₂ d₂)

theorem slabPhysicalPairRecouplingKernelPackageFour_targets_nodup
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4) :
    (slabPhysicalPairRecouplingKernelPackageFour D).kernel.targets.Nodup := by
  exact physicalSchurTensorTargets_nodup

theorem valenceFiveTensorTargets_nodup
    {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : Nat} :
    (tensor
      (valenceFiveBistochasticKernel a₁ b₁ c₁ d₁ e₁)
      (valenceFiveBistochasticKernel a₂ b₂ c₂ d₂ e₂)).targets.Nodup :=
  cartesian_nodup _ _
    (valenceFiveRightCarriers_nodup a₁ b₁ c₁ d₁ e₁)
    (valenceFiveRightCarriers_nodup a₂ b₂ c₂ d₂ e₂)

theorem slabPhysicalPairRecouplingKernelPackageFive_targets_nodup
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5) :
    (slabPhysicalPairRecouplingKernelPackageFive D).kernel.targets.Nodup := by
  exact valenceFiveTensorTargets_nodup

theorem valenceSixTensorTargets_nodup
    {a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂ : Nat} :
    (tensor
      (valenceSixBistochasticKernel a₁ b₁ c₁ d₁ e₁ f₁)
      (valenceSixBistochasticKernel a₂ b₂ c₂ d₂ e₂ f₂)).targets.Nodup :=
  cartesian_nodup _ _
    (valenceSixRightCarriers_nodup a₁ b₁ c₁ d₁ e₁ f₁)
    (valenceSixRightCarriers_nodup a₂ b₂ c₂ d₂ e₂ f₂)

theorem slabPhysicalPairRecouplingKernelPackageSix_targets_nodup
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 6) :
    (slabPhysicalPairRecouplingKernelPackageSix D).kernel.targets.Nodup := by
  exact valenceSixTensorTargets_nodup

theorem slabPhysicalPairRecouplingKernelPackage_targets_nodup
    {extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel.targets.Nodup
  | 0, _ => by
      change [()].Nodup
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 1, _ => by
      change [()].Nodup
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 2, _ => by
      change [()].Nodup
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 3, _ => by
      change [()].Nodup
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 4, D => slabPhysicalPairRecouplingKernelPackageFour_targets_nodup D
  | 5, D => slabPhysicalPairRecouplingKernelPackageFive_targets_nodup D
  | 6, D => slabPhysicalPairRecouplingKernelPackageSix_targets_nodup D
  | degree + 7, D => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-! ## 2. Heterogeneous whole-slab products -/

theorem finiteBistochasticTargetAssignments_nodup
    (packages : List FiniteBistochasticQKernelPackage)
    (hlocal : ∀ package, package ∈ packages →
      package.kernel.targets.Nodup) :
    (finiteBistochasticTargetAssignments packages).Nodup := by
  induction packages with
  | nil =>
      change [()].Nodup
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons package packages ih =>
      change (cartesian package.kernel.targets
        (finiteBistochasticTargetAssignments packages)).Nodup
      exact cartesian_nodup _ _
        (hlocal package List.mem_cons_self)
        (ih (fun next hnext => hlocal next
          (List.mem_cons_of_mem package hnext)))

theorem slabPhysicalPairRecouplingKernel_targets_nodup
    (extent : Nat) (leftPhysical rightPhysical : SlabLabelling) :
    (slabPhysicalPairRecouplingKernel
      extent leftPhysical rightPhysical).targets.Nodup := by
  apply finiteBistochasticTargetAssignments_nodup
  intro package hpackage
  unfold slabPhysicalPairRecouplingPackages at hpackage
  obtain ⟨linked, _, rfl⟩ := List.mem_map.mp hpackage
  exact slabPhysicalPairRecouplingKernelPackage_targets_nodup
    (slabIncidentPlaqIds extent linked.1).length
    (slabPhysicalPairRecouplingDataAtLink
      extent leftPhysical rightPhysical linked)

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup.valenceSixRightCarriers_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup.slabPhysicalPairRecouplingKernelPackage_targets_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup.finiteBistochasticTargetAssignments_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup.slabPhysicalPairRecouplingKernel_targets_nodup
