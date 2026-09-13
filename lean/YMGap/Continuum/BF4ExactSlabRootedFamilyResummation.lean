/-
# Exact saturation and resummation of ACTUAL original rooted families

The two computed maps are ambient-order merging and spectator decoding.
They are inverse on each fixed-core fiber. Their duplicate-free enumerations
are therefore permutations, so the ACTUAL signed spectator weight is exactly the
partition square on all detached ambient faces. Non-fixed keys have empty
fibers and are removed by a computed test. This gives a full original
connected-numerator expansion with no absolute spectator majorant.

No small-nome guard is needed for these finite identities. They assert no
normalized estimate, geometric decay or continuum passage.
-/

import YMGap.Continuum.BF4ExactSlabRootedSelectionStability
import YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
import YMGap.Continuum.Z4CanonicalPolymerRange

namespace YMGap.Continuum.BF4ExactSlabRootedFamilyResummation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedSelectionStability
open YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMerge
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def fixedTest (extent : Nat) (links : List Z4Link) (anchor : List Nat) : Bool :=
  decide (core extent links anchor = anchor)

def rootedAnchors (extent : Nat) (links : List Z4Link) (ambient : List Nat) : List (List Nat) :=
  (selections ambient).filter (fixedTest extent links)

theorem fixed_of_family {extent : Nat} {links : List Z4Link} {ambient anchor ids : List Nat}
    (hi : ids ∈ familySelections extent links ambient anchor) : core extent links anchor = anchor := by
  have hc : anchor = core extent links ids := of_decide_eq_true (List.mem_filter.mp hi).2
  rw [hc]
  exact core_idempotent extent links ids

theorem family_merge_mem {extent : Nat} {links : List Z4Link} {ambient anchor extra : List Nat}
    (hn : ambient.Nodup) (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor)
    (he : extra ∈ selections (detachedIds extent links anchor ambient)) :
    merge ambient anchor extra ∈ familySelections extent links ambient anchor :=
  List.mem_filter.mpr ⟨merge_selected _ _ _, decide_eq_true (core_merge hn ha hf he).symm⟩

theorem family_spectators_selected {extent : Nat} {links : List Z4Link} {ambient anchor ids : List Nat}
    (hi : ids ∈ familySelections extent links ambient anchor) :
    spectators extent links ids ∈ selections (detachedIds extent links anchor ambient) := by
  have hc : anchor = core extent links ids := of_decide_eq_true (List.mem_filter.mp hi).2
  rw [spectators_eq_detached, ← hc]
  exact sublist_selected (List.Sublist.filter _ (selected_sublist (List.mem_filter.mp hi).1))

/-- The encoder is a literal inverse, not just an equality of supports. -/
theorem merge_family_recovers {extent : Nat} {links : List Z4Link} {ambient anchor ids : List Nat}
    (hn : ambient.Nodup) (hi : ids ∈ familySelections extent links ambient anchor) :
    merge ambient anchor (spectators extent links ids) = ids := by
  have hc : anchor = core extent links ids := of_decide_eq_true (List.mem_filter.mp hi).2
  apply merge_recovers hn (List.mem_filter.mp hi).1
  intro id
  rw [hc]
  exact (split_perm extent links ids).mem_iff.symm.trans List.mem_append

theorem family_spectators_injective {extent : Nat} {links : List Z4Link} {ambient anchor xs ys : List Nat}
    (hn : ambient.Nodup) (hx : xs ∈ familySelections extent links ambient anchor)
    (hy : ys ∈ familySelections extent links ambient anchor)
    (he : spectators extent links xs = spectators extent links ys) : xs = ys := by
  rw [← merge_family_recovers hn hx, ← merge_family_recovers hn hy, he]

/-- Full range and injectivity, with both enumerations duplicate-free. -/
theorem family_spectators_perm {extent : Nat} {links : List Z4Link} {ambient anchor : List Nat}
    (hn : ambient.Nodup) (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor) :
    ((familySelections extent links ambient anchor).map (spectators extent links)).Perm
      (selections (detachedIds extent links anchor ambient)) := by
  apply perm_of_nodup_mem_iff _ _
    (nodup_map_of_injOn _ _ (familySelections_nodup extent links ambient anchor hn)
      (fun _ hx _ hy he => family_spectators_injective hn hx hy he))
    (selections_nodup _ (List.filter_sublist.nodup hn))
  intro extra
  constructor
  · intro he
    obtain ⟨ids, hi, rfl⟩ := List.mem_map.mp he
    exact family_spectators_selected hi
  · intro he
    exact List.mem_map.mpr ⟨merge ambient anchor extra, family_merge_mem hn ha hf he,
      spectators_merge hn ha hf he⟩

theorem spectatorWeight_pin (w : Q') (K extent : Nat) (links : List Z4Link) (ambient anchor : List Nat)
    (hn : ambient.Nodup) (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor) :
    spectatorWeight w K extent links ambient anchor ≈
      partitionSquare w K extent (detachedIds extent links anchor ambient) := by
  unfold spectatorWeight
  rw [← FiniteSelectionMobius.sum_map]
  exact Q'.eqv_trans _ _ _ (listQSum_perm _ (family_spectators_perm hn ha hf))
    (partitionSquareCoefficient_sum w K extent _)

theorem family_empty_of_not_fixed {extent : Nat} {links : List Z4Link} {ambient anchor : List Nat}
    (hf : core extent links anchor ≠ anchor) : familySelections extent links ambient anchor = [] := by
  cases he : familySelections extent links ambient anchor with
  | nil => rfl
  | cons ids rest =>
      have hi : ids ∈ familySelections extent links ambient anchor := by
        rw [he]
        exact List.mem_cons_self
      exact False.elim (hf (fixed_of_family hi))

theorem rootedFamily_zero_of_not_fixed (w : Q') (K extent : Nat) (p q : RatPoly)
    (links : List Z4Link) (ambient anchor : List Nat) (hf : core extent links anchor ≠ anchor) :
    rootedFamily w K extent p q links ambient anchor ≈ 0 := by
  change listQSum _ (familySelections extent links ambient anchor) ≈ 0
  rw [family_empty_of_not_fixed hf]
  exact Q'.eqv_refl 0

section Local

variable (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
  (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q)

include hp hq hlp hlq

theorem rootedFamily_resummed (ambient anchor : List Nat) (hn : ambient.Nodup)
    (ha : anchor ∈ selections ambient) (hf : core extent links anchor = anchor) :
    rootedFamily w K extent p q links ambient anchor ≈ connectedCoefficient w K extent p q anchor *
      partitionSquare w K extent (detachedIds extent links anchor ambient) :=
  Q'.eqv_trans _ _ _ (rootedFamily_factorizes w K extent p q links hp hq hlp hlq ambient anchor)
    (Q'.mul_eqv_congr_left _ _ _ (spectatorWeight_pin w K extent links ambient anchor hn ha hf))

theorem connectedNumerator_resummed_expansion (ambient : List Nat) (hn : ambient.Nodup) :
    connectedNumerator w K extent ambient p q ≈
      listQSum (fun anchor => connectedCoefficient w K extent p q anchor *
        partitionSquare w K extent (detachedIds extent links anchor ambient)) (rootedAnchors extent links ambient) :=
  Q'.eqv_trans _ _ _ (connectedNumerator_family_expansion w K extent p q links ambient hn)
    (Q'.eqv_trans _ _ _ (sum_filter_zero _ (fixedTest extent links) _
      (fun anchor _ hf => rootedFamily_zero_of_not_fixed w K extent p q links ambient anchor (of_decide_eq_false hf)))
      (listQSum_congr_on _ _ _ (fun anchor ha => rootedFamily_resummed w K extent p q links hp hq hlp hlq
        ambient anchor hn (List.mem_filter.mp ha).1 (of_decide_eq_true (List.mem_filter.mp ha).2))))

end Local

end YMGap.Continuum.BF4ExactSlabRootedFamilyResummation

#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.fixedTest
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.rootedAnchors
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.fixed_of_family
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.family_merge_mem
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.family_spectators_selected
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.merge_family_recovers
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.family_spectators_injective
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.family_spectators_perm
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.spectatorWeight_pin
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.family_empty_of_not_fixed
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.rootedFamily_zero_of_not_fixed
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.rootedFamily_resummed
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyResummation.connectedNumerator_resummed_expansion
