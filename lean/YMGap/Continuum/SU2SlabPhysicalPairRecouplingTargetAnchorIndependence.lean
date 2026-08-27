/-
# Source-anchor independence of physical-pair target realization

The complete physical-pair target carrier is recoded into the source carrier
by equal written rank.  Its accepted production row is supplied only as the
total lookup fallback.  Every literal target has an in-range rank, so that
fallback is never inspected.

Consequently the source carrier selected by one target column is independent
of the accepted auxiliary pair used to anchor the construction.  At degrees
zero through three all accepted local witnesses are unique; at degrees four
through six the selected complete source carrier itself determines the two
reconstructed witnesses.  Thus the realized local witness pair is canonical
for the fixed physical fields and target column.

Constructive contract: finite ranks and the existing accepted-witness
decoder only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The equal-rank source code is anchor independent -/

theorem slabPhysicalPairTargetToProductionSourceAtEqualRank_anchor_independent
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (leftAnchor rightAnchor : SlabPhysicalPairRecouplingWitnessData K D)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    slabPhysicalPairTargetToProductionSourceAtEqualRank
        D leftAnchor target =
      slabPhysicalPairTargetToProductionSourceAtEqualRank
        D rightAnchor target := by
  letI := slabPhysicalPairRecouplingTargetDecidableEq degree D
  exact
    FiniteBistochasticQKernel.targetToSourceAtEqualRank_fallback_independent
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel
      (slabPhysicalPairRecouplingProductionSource degree D leftAnchor)
      (slabPhysicalPairRecouplingProductionSource degree D rightAnchor)
      target (slabPhysicalPairRecouplingTarget_mem degree D target)

/-! ## 2. The two reconstructed production witnesses are canonical -/

theorem slabPhysicalPairTargetProductionWitnessPair_anchor_independent
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (leftAnchor rightAnchor : SlabPhysicalPairRecouplingWitnessData K D)
    (leftBounded : SlabFaceLabellingBounded K extent D.leftPhysical)
    (rightBounded : SlabFaceLabellingBounded K extent D.rightPhysical)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    let leftResult := slabPhysicalPairTargetProductionWitnessPair
      D leftAnchor leftBounded rightBounded target
    let rightResult := slabPhysicalPairTargetProductionWitnessPair
      D rightAnchor leftBounded rightBounded target
    leftResult.leftAuxiliary = rightResult.leftAuxiliary ∧
      leftResult.rightAuxiliary = rightResult.rightAuxiliary := by
  cases degree with
  | zero =>
      exact slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
        D leftAnchor rightAnchor rfl
  | succ degree =>
      cases degree with
      | zero =>
          exact slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
            D leftAnchor rightAnchor rfl
      | succ degree =>
          cases degree with
          | zero =>
              exact slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
                D leftAnchor rightAnchor rfl
          | succ degree =>
              cases degree with
              | zero =>
                  exact slabPhysicalPairRecouplingProductionSource_auxiliaries_injective
                    D leftAnchor rightAnchor rfl
              | succ degree =>
                  cases degree with
                  | zero =>
                      have hsource :=
                        slabPhysicalPairTargetToProductionSourceAtEqualRank_anchor_independent
                          D leftAnchor rightAnchor target
                      simp only [slabPhysicalPairTargetProductionWitnessPair,
                        slabPhysicalPairProductionWitnessPairOfSource]
                      rw [hsource]
                      exact ⟨rfl, rfl⟩
                  | succ degree =>
                      cases degree with
                      | zero =>
                          have hsource :=
                            slabPhysicalPairTargetToProductionSourceAtEqualRank_anchor_independent
                              D leftAnchor rightAnchor target
                          simp only [slabPhysicalPairTargetProductionWitnessPair,
                            slabPhysicalPairProductionWitnessPairOfSource]
                          rw [hsource]
                          exact ⟨rfl, rfl⟩
                      | succ degree =>
                          cases degree with
                          | zero =>
                              have hsource :=
                                slabPhysicalPairTargetToProductionSourceAtEqualRank_anchor_independent
                                  D leftAnchor rightAnchor target
                              simp only [slabPhysicalPairTargetProductionWitnessPair,
                                slabPhysicalPairProductionWitnessPairOfSource]
                              rw [hsource]
                              exact ⟨rfl, rfl⟩
                          | succ degree =>
                              exact False.elim (by
                                have hdegree := D.degree_le_six
                                have hseven :
                                    7 ≤ degree + 1 + 1 + 1 + 1 + 1 + 1 + 1 :=
                                  Nat.succ_le_succ
                                    (Nat.succ_le_succ
                                      (Nat.succ_le_succ
                                        (Nat.succ_le_succ
                                          (Nat.succ_le_succ
                                            (Nat.succ_le_succ
                                              (Nat.succ_le_succ
                                                (Nat.zero_le degree)))))))
                                exact Nat.not_succ_le_self 6
                                  (Nat.le_trans hseven hdegree))

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence.slabPhysicalPairTargetToProductionSourceAtEqualRank_anchor_independent
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetAnchorIndependence.slabPhysicalPairTargetProductionWitnessPair_anchor_independent
