/-
# Rooted spectator resummation for a rational original-face functional

A permutation-invariant list functional factors across an actual disjoint
spectator region by a second functional G. Its finite Mobius coefficients
therefore factor across the same split. The existing rooted selections and
proved spectator-fiber permutation resum those coefficients to G evaluated
on the complete detached face list.

This is finite algebra with explicit factorization premises. It introduces
no new enumeration, component geometry, analytic estimate, or frontier
structure. In the original connected-response application, the separately
proved spectator factor is the fourth power of the same partition function.
-/

import YMGap.Continuum.BF4ExactSlabRootedFamilyResummation

namespace YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionMobiusFactorization
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerRange

local infix:50 " ≈ " => Q'.eqv

private theorem coefficient_rooted (extent : Nat) (links : List Z4Link)
    (F G : List Nat → Q')
    (hperm : ∀ {xs ys : List Nat}, xs.Perm ys → F xs ≈ F ys)
    (hfactor : ∀ a b : List Nat,
      LinksDisjoint (links++faceLinks extent a) (faceLinks extent b) → F (a++b) ≈ F a * G b)
    (ids : List Nat) :
    coefficient F ids ≈ coefficient F (core extent links ids) * coefficient G (spectators extent links ids) :=
  Q'.eqv_trans _ _ _
    (coefficient_perm (split_perm extent links ids).symm F (fun _ _ h => hperm h))
    (coefficient_factorizes F F G _ _ (fun a ha b hb =>
      hfactor a b (disjoint_subfaces (split_disjoint extent links ids)
        (fun id hi => selected_mem ha id hi) (fun id hi => selected_mem hb id hi))))

/-- Exact resummation on the ALREADY constructed rooted anchors. No sign or
positivity premise is needed, and G need not be permutation invariant. -/
theorem rooted_functional_resummed_expansion (extent : Nat) (links : List Z4Link)
    (F G : List Nat → Q')
    (hperm : ∀ {xs ys : List Nat}, xs.Perm ys → F xs ≈ F ys)
    (hfactor : ∀ a b : List Nat,
      LinksDisjoint (links++faceLinks extent a) (faceLinks extent b) → F (a++b) ≈ F a * G b)
    (ambient : List Nat) (hn : ambient.Nodup) :
    F ambient ≈ listQSum
      (fun anchor => coefficient F anchor * G (detachedIds extent links anchor ambient))
      (rootedAnchors extent links ambient) := by
  let family : List Nat → Q' :=
    fiberWeight (selections ambient) (coefficient F) (core extent links)
  have hgroup : F ambient ≈ listQSum family (selections ambient) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (reconstruct F ambient))
      (Q'.eqv_symm (fiberWeight_total _ _ _ _ (selections_nodup ambient hn)
        (fun ids hi => sublist_selected ((selected_sublist (core_selected extent links ids)).trans
          (selected_sublist hi)))))
  have hzero (anchor : List Nat) (hf : core extent links anchor ≠ anchor) : family anchor ≈ 0 := by
    change listQSum (coefficient F) (familySelections extent links ambient anchor) ≈ 0
    rw [family_empty_of_not_fixed hf]
    exact Q'.eqv_refl 0
  have hresum (anchor : List Nat) (ha : anchor ∈ selections ambient)
      (hf : core extent links anchor = anchor) :
      family anchor ≈ coefficient F anchor * G (detachedIds extent links anchor ambient) := by
    have hsplit : family anchor ≈ coefficient F anchor *
        listQSum (fun ids => coefficient G (spectators extent links ids))
          (familySelections extent links ambient anchor) := by
      change listQSum (coefficient F) (familySelections extent links ambient anchor) ≈ _
      refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ids hi => ?_)) (listQSum_mul_left _ _ _)
      have he : anchor = core extent links ids := of_decide_eq_true (List.mem_filter.mp hi).2
      have hc := coefficient_rooted extent links F G hperm hfactor ids
      rw [← he] at hc
      exact hc
    have hspectators :
        listQSum (fun ids => coefficient G (spectators extent links ids))
          (familySelections extent links ambient anchor) ≈ G (detachedIds extent links anchor ambient) := by
      rw [← FiniteSelectionMobius.sum_map]
      exact Q'.eqv_trans _ _ _ (listQSum_perm _ (family_spectators_perm hn ha hf))
        (reconstruct G _)
    exact Q'.eqv_trans _ _ _ hsplit (Q'.mul_eqv_congr_left _ _ _ hspectators)
  exact Q'.eqv_trans _ _ _ hgroup
    (Q'.eqv_trans _ _ _
      (sum_filter_zero family (fixedTest extent links) (selections ambient)
        (fun anchor _ hf => hzero anchor (of_decide_eq_false hf)))
      (listQSum_congr_on _ _ _ (fun anchor ha => hresum anchor
        (List.mem_filter.mp ha).1 (of_decide_eq_true (List.mem_filter.mp ha).2))))

end YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation

#print axioms YMGap.Continuum.BF4ExactSlabRootedFunctionalResummation.rooted_functional_resummed_expansion
