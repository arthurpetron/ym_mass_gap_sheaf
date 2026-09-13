/-
# Probe-rooted resummation of both ORIGINAL actions at once

The already proved ambient-order fiber bijection is reused with the mixed
partition functional. All detached faces, including exterior faces, are
summed before absolute values. Each actual fixed-core family is exactly
its mixed coefficient times Z_detached * Z_inside-detached. The root carries
only the probe support; no exterior selection is attached to it.
-/

import YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization
import YMGap.Continuum.BF4ExactSlabRootedFamilyResummation

namespace YMGap.Continuum.BF4ExactSlabMixedRootedResummation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def mixedFamily (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (links : List Z4Link)
    (ambient anchor : List Nat) : Q' :=
  fiberWeight (selections ambient) (mixedCoefficient w K extent keep p) (core extent links) anchor

theorem mixedNumerator_family_expansion (w : Q') (K extent : Nat) (keep : Nat → Bool)
    (p : RatPoly) (links : List Z4Link) (ambient : List Nat) (hn : ambient.Nodup) :
    mixedNumerator w K extent keep p ambient ≈
      listQSum (mixedFamily w K extent keep p links ambient) (selections ambient) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (reconstruct _ _))
    (Q'.eqv_symm (fiberWeight_total _ _ _ _ (selections_nodup ambient hn)
      (fun ids hi => sublist_selected ((selected_sublist (core_selected extent links ids)).trans (selected_sublist hi)))))

theorem mixedFamily_zero_of_not_fixed (w : Q') (K extent : Nat) (keep : Nat → Bool)
    (p : RatPoly) (links : List Z4Link) (ambient anchor : List Nat) (hf : core extent links anchor ≠ anchor) :
    mixedFamily w K extent keep p links ambient anchor ≈ 0 := by
  change listQSum _ (familySelections extent links ambient anchor) ≈ 0
  rw [family_empty_of_not_fixed hf]
  exact Q'.eqv_refl 0

section Local

variable (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (links : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hl : LinkLocal extent links p)

include hp hl

theorem mixedFamily_factorizes (ambient anchor : List Nat) :
    mixedFamily w K extent keep p links ambient anchor ≈ mixedCoefficient w K extent keep p anchor *
      listQSum (fun ids => mixedPartitionCoefficient w K extent keep (spectators extent links ids))
        (familySelections extent links ambient anchor) := by
  refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ids hi => ?_)) (listQSum_mul_left _ _ _)
  have hc : anchor = core extent links ids := of_decide_eq_true (List.mem_filter.mp hi).2
  have h := mixedCoefficient_rooted_pin w K extent keep p links hp hl ids
  rw [← hc] at h
  exact h

theorem mixedFamily_resummed (ambient anchor : List Nat) (hn : ambient.Nodup)
    (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor) :
    mixedFamily w K extent keep p links ambient anchor ≈ mixedCoefficient w K extent keep p anchor *
      mixedPartition w K extent keep (detachedIds extent links anchor ambient) := by
  refine Q'.eqv_trans _ _ _ (mixedFamily_factorizes w K extent keep p links hp hl ambient anchor)
    (Q'.mul_eqv_congr_left _ _ _ ?_)
  rw [← FiniteSelectionMobius.sum_map]
  exact Q'.eqv_trans _ _ _ (listQSum_perm _ (family_spectators_perm hn ha hf)) (reconstruct _ _)

/-- All original faces are grouped together, so exterior spectators are also resummed. -/
theorem mixedNumerator_rooted_expansion (ambient : List Nat) (hn : ambient.Nodup) :
    mixedNumerator w K extent keep p ambient ≈
      listQSum (fun anchor => mixedCoefficient w K extent keep p anchor *
        mixedPartition w K extent keep (detachedIds extent links anchor ambient)) (rootedAnchors extent links ambient) :=
  Q'.eqv_trans _ _ _ (mixedNumerator_family_expansion w K extent keep p links ambient hn)
    (Q'.eqv_trans _ _ _ (sum_filter_zero _ (fixedTest extent links) _
      (fun anchor _ hf => mixedFamily_zero_of_not_fixed w K extent keep p links ambient anchor (of_decide_eq_false hf)))
      (listQSum_congr_on _ _ _ (fun anchor ha => mixedFamily_resummed w K extent keep p links hp hl
        ambient anchor hn (List.mem_filter.mp ha).1 (of_decide_eq_true (List.mem_filter.mp ha).2))))

end Local

end YMGap.Continuum.BF4ExactSlabMixedRootedResummation

#print axioms YMGap.Continuum.BF4ExactSlabMixedRootedResummation.mixedFamily
#print axioms YMGap.Continuum.BF4ExactSlabMixedRootedResummation.mixedNumerator_family_expansion
#print axioms YMGap.Continuum.BF4ExactSlabMixedRootedResummation.mixedFamily_zero_of_not_fixed
#print axioms YMGap.Continuum.BF4ExactSlabMixedRootedResummation.mixedFamily_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabMixedRootedResummation.mixedFamily_resummed
#print axioms YMGap.Continuum.BF4ExactSlabMixedRootedResummation.mixedNumerator_rooted_expansion
