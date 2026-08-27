/-
# Injectivity of physical-pair recoupling target realization

Equal-rank recoding sends distinct complete target columns to distinct complete
source carriers because the written source list is duplicate free.  Canonical
auxiliary reconstruction is a left inverse on those source carriers, so two
target columns that realize the same accepted witness pair are equal.

This is the local faithfulness statement required before whole-slab target
realization can be used in a column-capacity argument.

Constructive contract: finite rank recoding and canonical SU(2) witness
coordinates only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetInjectivity

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingPackageSourceNodup
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetFaithfulness
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Equal-rank target codes are injective -/

theorem slabPhysicalPairTargetToProductionSourceAtEqualRank_injective
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (anchor : SlabPhysicalPairRecouplingWitnessData K D)
    {left right :
      (slabPhysicalPairRecouplingKernelPackage degree D).Target}
    (heq : slabPhysicalPairTargetToProductionSourceAtEqualRank
        D anchor left =
      slabPhysicalPairTargetToProductionSourceAtEqualRank
        D anchor right) :
    left = right := by
  letI := slabPhysicalPairRecouplingKernelPackageSourceDecidableEq degree D
  letI := slabPhysicalPairRecouplingTargetDecidableEq degree D
  exact FiniteBistochasticQKernel.targetToSourceAtEqualRank_injective
    (slabPhysicalPairRecouplingKernelPackage degree D).kernel
    (slabPhysicalPairRecouplingProductionSource degree D anchor)
    (slabPhysicalPairRecouplingKernelPackage_sources_nodup degree D)
    (slabPhysicalPairRecouplingTarget_mem degree D left)
    (slabPhysicalPairRecouplingTarget_mem degree D right)
    heq

/-! ## 2. Literal reconstructed witnesses retain the target column -/

theorem SlabPhysicalPairProductionWitnessPair.eq_of_auxiliaries_eq
    {K extent degree : Nat}
    {D : SlabPhysicalPairRecouplingData extent degree}
    {left right : SlabPhysicalPairProductionWitnessPair K D}
    (hleft : left.leftAuxiliary = right.leftAuxiliary)
    (hright : left.rightAuxiliary = right.rightAuxiliary) :
    left = right := by
  cases left
  cases right
  cases hleft
  cases hright
  rfl

/-- Distinct complete local target columns realize distinct pairs of accepted
auxiliary labellings. -/
theorem slabPhysicalPairTargetProductionWitnessPair_injective
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (anchor : SlabPhysicalPairRecouplingWitnessData K D)
    (leftBounded : SlabFaceLabellingBounded K extent D.leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent D.rightPhysical)
    {left right :
      (slabPhysicalPairRecouplingKernelPackage degree D).Target}
    (hleft :
      (slabPhysicalPairTargetProductionWitnessPair
        D anchor leftBounded rightBounded left).leftAuxiliary =
      (slabPhysicalPairTargetProductionWitnessPair
        D anchor leftBounded rightBounded right).leftAuxiliary)
    (hright :
      (slabPhysicalPairTargetProductionWitnessPair
        D anchor leftBounded rightBounded left).rightAuxiliary =
      (slabPhysicalPairTargetProductionWitnessPair
        D anchor leftBounded rightBounded right).rightAuxiliary) :
    left = right := by
  let leftResult := slabPhysicalPairTargetProductionWitnessPair
    D anchor leftBounded rightBounded left
  let rightResult := slabPhysicalPairTargetProductionWitnessPair
    D anchor leftBounded rightBounded right
  have hpairs : leftResult = rightResult :=
    SlabPhysicalPairProductionWitnessPair.eq_of_auxiliaries_eq hleft hright
  have hdata :
      SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
          leftResult =
        SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
          rightResult :=
    congrArg
      SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
      hpairs
  have hdataCanonical :
      SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
          (slabPhysicalPairProductionWitnessPairOfSource degree D anchor
            leftBounded rightBounded
            (slabPhysicalPairTargetToProductionSourceAtEqualRank
              D anchor left)) =
        SU2SlabPhysicalPairRecouplingTargetFaithfulness.SlabPhysicalPairProductionWitnessPair.toWitnessData
          (slabPhysicalPairProductionWitnessPairOfSource degree D anchor
            leftBounded rightBounded
            (slabPhysicalPairTargetToProductionSourceAtEqualRank
              D anchor right)) := by
    simpa only [leftResult, rightResult,
      slabPhysicalPairTargetProductionWitnessPair] using hdata
  have hleftRoundtrip :=
    slabPhysicalPairProductionWitnessPairOfSource_roundtrip
      degree D leftBounded rightBounded anchor
      (slabPhysicalPairTargetToProductionSourceAtEqualRank D anchor left)
  have hrightRoundtrip :=
    slabPhysicalPairProductionWitnessPairOfSource_roundtrip
      degree D leftBounded rightBounded anchor
      (slabPhysicalPairTargetToProductionSourceAtEqualRank D anchor right)
  have hsource :
      slabPhysicalPairTargetToProductionSourceAtEqualRank D anchor left =
        slabPhysicalPairTargetToProductionSourceAtEqualRank D anchor right := by
    rw [<- hleftRoundtrip, <- hrightRoundtrip, hdataCanonical]
  exact slabPhysicalPairTargetToProductionSourceAtEqualRank_injective
    D anchor hsource

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetInjectivity

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetInjectivity.slabPhysicalPairTargetToProductionSourceAtEqualRank_injective
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetInjectivity.SlabPhysicalPairProductionWitnessPair.eq_of_auxiliaries_eq
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetInjectivity.slabPhysicalPairTargetProductionWitnessPair_injective
