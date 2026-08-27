/-
# Duplicate-free sources for physical-pair recoupling packages

The complete left-carrier lists at valences four, five, and six are duplicate
free.  Their Cartesian two-replica source lists are therefore duplicate free,
and the same conclusion holds uniformly for every geometrically possible slab
link degree.

The fixed-valence statements are kept separate from the final dependent
wrapper so that each carrier calculation is elaborated once and then used
opaquely.

Constructive contract: explicit finite carrier lists only; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup

set_option autoImplicit false

open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

/-! ## 1. Fixed valences -/

theorem physicalSchurTensorSources_nodup
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat} :
    (tensor
      (physicalSchurBistochasticKernel a₁ b₁ c₁ d₁)
      (physicalSchurBistochasticKernel a₂ b₂ c₂ d₂)).sources.Nodup :=
  cartesian_nodup _ _
    (fixedLeftChannels_nodup a₁ b₁ c₁ d₁)
    (fixedLeftChannels_nodup a₂ b₂ c₂ d₂)

theorem slabPhysicalPairRecouplingKernelPackageFour_sources_nodup
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4) :
    (slabPhysicalPairRecouplingKernelPackageFour D).kernel.sources.Nodup := by
  exact physicalSchurTensorSources_nodup

theorem valenceFiveTensorSources_nodup
    {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : Nat} :
    (tensor
      (valenceFiveBistochasticKernel a₁ b₁ c₁ d₁ e₁)
      (valenceFiveBistochasticKernel a₂ b₂ c₂ d₂ e₂)).sources.Nodup :=
  cartesian_nodup _ _
    (valenceFiveLeftCarriers_nodup a₁ b₁ c₁ d₁ e₁)
    (valenceFiveLeftCarriers_nodup a₂ b₂ c₂ d₂ e₂)

theorem slabPhysicalPairRecouplingKernelPackageFive_sources_nodup
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5) :
    (slabPhysicalPairRecouplingKernelPackageFive D).kernel.sources.Nodup := by
  exact valenceFiveTensorSources_nodup

theorem valenceSixTensorSources_nodup
    {a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂ : Nat} :
    (tensor
      (valenceSixBistochasticKernel a₁ b₁ c₁ d₁ e₁ f₁)
      (valenceSixBistochasticKernel a₂ b₂ c₂ d₂ e₂ f₂)).sources.Nodup :=
  cartesian_nodup _ _
    (valenceSixLeftCarriers_nodup a₁ b₁ c₁ d₁ e₁ f₁)
    (valenceSixLeftCarriers_nodup a₂ b₂ c₂ d₂ e₂ f₂)

theorem slabPhysicalPairRecouplingKernelPackageSix_sources_nodup
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 6) :
    (slabPhysicalPairRecouplingKernelPackageSix D).kernel.sources.Nodup := by
  exact valenceSixTensorSources_nodup

/-! ## 2. Every geometrically possible degree -/

/-- The written source carrier of every local physical-pair recoupling matrix
is duplicate free. -/
theorem slabPhysicalPairRecouplingKernelPackage_sources_nodup
    {extent : Nat} :
    (degree : Nat) -> (D : SlabPhysicalPairRecouplingData extent degree) ->
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel.sources.Nodup
  | 0, _ =>
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 1, _ =>
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 2, _ =>
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 3, _ =>
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | 4, D =>
      slabPhysicalPairRecouplingKernelPackageFour_sources_nodup D
  | 5, D =>
      slabPhysicalPairRecouplingKernelPackageFive_sources_nodup D
  | 6, D =>
      slabPhysicalPairRecouplingKernelPackageSix_sources_nodup D
  | degree + 7, D => False.elim (by
      have hdegree := D.degree_le_six
      omega)

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup.slabPhysicalPairRecouplingKernelPackageFour_sources_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup.slabPhysicalPairRecouplingKernelPackageFive_sources_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup.slabPhysicalPairRecouplingKernelPackageSix_sources_nodup
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup.slabPhysicalPairRecouplingKernelPackage_sources_nodup
