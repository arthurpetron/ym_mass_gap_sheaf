/-
# Forgetting the retained blocked law recovers the old blocked law

The retained all-cutoff kernel and its forgetting kernel already form an
exact row-level commuting square.  This module lifts that square through the
normalized fine Gibbs law.  Finite Fubini proves that pushing first to the
lossless coarse-or-retained carrier and then forgetting gives exactly the
blocked law of the former total four-preimage kernel.

This is a compatibility theorem between two finite probability flows.  It
does not claim that forgetting the retained sector is physically harmless:
the cutoff-two counterexample proves that the forgotten sector has positive
mass.  No reflection lift, contraction estimate, spectral gap, continuum
limit, or Clay theorem is claimed.

## Axiom gate

Finite exact-rational Fubini and the previously checked row identity only.
No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerProjection
import YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedProjection

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerProjection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Push the enriched law through the forgetting kernel -/

/-- The coarse target column obtained by forgetting the retained blocked law. -/
def allCutoffRetainedForgottenBlockedMass
    (S : SlabScalePair) (coarseState : EdgeLabelling) : Q' :=
  listQSum
    (fun retained =>
      allCutoffRetainedFineIntertwinerBlockedMass S retained *
        allCutoffRetainedForgetKernel S retained coarseState)
    (allCutoffRetainedTargets S)

theorem allCutoffRetainedForgottenBlockedMass_nonnegative
    (S : SlabScalePair) (coarseState : EdgeLabelling) :
    (0 : Q') ≤
      allCutoffRetainedForgottenBlockedMass S coarseState := by
  unfold allCutoffRetainedForgottenBlockedMass
  apply listQSum_nonnegative_on
  intro retained _
  exact Q'.mul_nonneg _ _
    (allCutoffRetainedFineIntertwinerBlockedMass_nonnegative S retained)
    (allCutoffRetainedForgetKernel_nonnegative S retained coarseState)

/-! ## 2. The blocked-law commuting square -/

/-- Forgetting after the lossless enriched pushforward is exactly the old
all-cutoff blocked law, target by target. -/
theorem allCutoffRetainedForgottenBlockedMass_eqv_oldBlockedMass
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (coarseState : EdgeLabelling)
    (hcoarse : coarseState ∈ S.coarse.physicalLabellings) :
    allCutoffRetainedForgottenBlockedMass S coarseState ≈
      (allCutoffPhysicalKernel S hfineCutoff).blockedMass coarseState := by
  unfold allCutoffRetainedForgottenBlockedMass
    allCutoffRetainedFineIntertwinerBlockedMass
  refine Q'.eqv_trans _
    (listQSum
      (fun retained =>
        listQSum
          (fun source : SlabPhysicalSourceEntry S.fine =>
            (S.fine.normalizedMass source.1 *
                allCutoffRetainedFineIntertwinerKernel S source retained) *
              allCutoffRetainedForgetKernel S retained coarseState)
          (slabPhysicalSourceEntries S.fine))
      (allCutoffRetainedTargets S)) _ ?_ ?_
  · apply listQSum_congr_on _ _ (allCutoffRetainedTargets S)
    intro retained _
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun source : SlabPhysicalSourceEntry S.fine =>
          S.fine.normalizedMass source.1 *
            allCutoffRetainedFineIntertwinerKernel S source retained)
        (allCutoffRetainedForgetKernel S retained coarseState)
        (slabPhysicalSourceEntries S.fine))
  refine Q'.eqv_trans _
    (listQSum
      (fun source : SlabPhysicalSourceEntry S.fine =>
        listQSum
          (fun retained =>
            (S.fine.normalizedMass source.1 *
                allCutoffRetainedFineIntertwinerKernel S source retained) *
              allCutoffRetainedForgetKernel S retained coarseState)
          (allCutoffRetainedTargets S))
      (slabPhysicalSourceEntries S.fine)) _ ?_ ?_
  · exact listQSum_swap
      (fun source : SlabPhysicalSourceEntry S.fine =>
        fun retained : AllCutoffRetainedTarget =>
          (S.fine.normalizedMass source.1 *
              allCutoffRetainedFineIntertwinerKernel S source retained) *
            allCutoffRetainedForgetKernel S retained coarseState)
      (slabPhysicalSourceEntries S.fine)
      (allCutoffRetainedTargets S)
  refine Q'.eqv_trans _
    (listQSum
      (fun source : SlabPhysicalSourceEntry S.fine =>
        S.fine.normalizedMass source.1 *
          allCutoffWholeSlabKernel S source.1 coarseState)
      (slabPhysicalSourceEntries S.fine)) _ ?_ ?_
  · apply listQSum_congr_on _ _ (slabPhysicalSourceEntries S.fine)
    intro source _
    refine Q'.eqv_trans _
      (listQSum
        (fun retained =>
          S.fine.normalizedMass source.1 *
            (allCutoffRetainedFineIntertwinerKernel S source retained *
              allCutoffRetainedForgetKernel S retained coarseState))
        (allCutoffRetainedTargets S)) _ ?_ ?_
    · apply listQSum_congr_on _ _ (allCutoffRetainedTargets S)
      intro retained _
      exact Q'.mul_assoc_eqv _ _ _
    refine Q'.eqv_trans _
      (S.fine.normalizedMass source.1 *
        allCutoffRetainedForgottenKernel S source coarseState) _ ?_ ?_
    · exact listQSum_mul_left
        (S.fine.normalizedMass source.1)
        (fun retained =>
          allCutoffRetainedFineIntertwinerKernel S source retained *
            allCutoffRetainedForgetKernel S retained coarseState)
        (allCutoffRetainedTargets S)
    · exact Q'.mul_eqv_congr_left
        (S.fine.normalizedMass source.1) _ _
        (allCutoffRetainedForgottenKernel_eqv_allCutoffWholeSlabKernel
          S source coarseState hcoarse)
  unfold SlabScalePair.FiniteSlabKernel.blockedMass
    allCutoffPhysicalKernel
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (listQSum_attach
        (fun source =>
          S.fine.normalizedMass source *
            allCutoffWholeSlabKernel S source coarseState)
        S.fine.physicalLabellings))
    (Q'.eqv_refl _)

/-! ## Axiom audit -/

#print axioms allCutoffRetainedForgottenBlockedMass_nonnegative
#print axioms allCutoffRetainedForgottenBlockedMass_eqv_oldBlockedMass

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerBlockedProjection
