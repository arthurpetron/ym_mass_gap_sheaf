/-
# Exact canonical rooted families of the ORIGINAL connected numerator

The original coefficient is permutation invariant. Its computed rooted
split therefore factors into the SAME core coefficient and spectator
partition-square coefficient. Grouping all ordered selections by their
computed core is exact and counts every selection once for duplicate-free
ambient faces. Signed spectator coefficients are retained inside each fiber.

The fiber weight below is still an explicit filtered sum. Identifying it
with the partition square of ALL detached ambient faces requires the
additional fiber-saturation/bijection theorem; that is not assumed here.
-/

import YMGap.Continuum.BF4ExactSlabRootedSelection
import YMGap.Continuum.BF4ExactSlabSpectatorResummation

namespace YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem connectedCoefficient_perm (w : Q') (K extent : Nat) (p q : RatPoly)
    {xs ys : List Nat} (h : xs.Perm ys) :
    connectedCoefficient w K extent p q xs ≈ connectedCoefficient w K extent p q ys :=
  coefficient_perm h _ (fun _ _ hp => connectedNumerator_perm w K extent hp p q)

def familySelections (extent : Nat) (links : List Z4Link) (ambient anchor : List Nat) : List (List Nat) :=
  (selections ambient).filter (fun ids => decide (anchor = core extent links ids))

def rootedFamily (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link)
    (ambient anchor : List Nat) : Q' :=
  fiberWeight (selections ambient) (connectedCoefficient w K extent p q) (core extent links) anchor

/-- No positivity or full-detached-partition identity is built into this weight. -/
def spectatorWeight (w : Q') (K extent : Nat) (links : List Z4Link) (ambient anchor : List Nat) : Q' :=
  listQSum (fun ids => partitionSquareCoefficient w K extent (spectators extent links ids))
    (familySelections extent links ambient anchor)

theorem family_code_unique {extent : Nat} {links : List Z4Link} {ambient anchor other ids : List Nat}
    (ha : ids ∈ familySelections extent links ambient anchor)
    (hb : ids ∈ familySelections extent links ambient other) : anchor = other :=
  (of_decide_eq_true (List.mem_filter.mp ha).2).trans
    (of_decide_eq_true (List.mem_filter.mp hb).2).symm

theorem familySelections_nodup (extent : Nat) (links : List Z4Link) (ambient anchor : List Nat)
    (hn : ambient.Nodup) : (familySelections extent links ambient anchor).Nodup :=
  List.filter_sublist.nodup (selections_nodup ambient hn)

/-- Exact global grouping, before any absolute value or analytic estimate. -/
theorem connectedNumerator_family_expansion (w : Q') (K extent : Nat) (p q : RatPoly)
    (links : List Z4Link) (ambient : List Nat) (hn : ambient.Nodup) :
    connectedNumerator w K extent ambient p q ≈
      listQSum (rootedFamily w K extent p q links ambient) (selections ambient) :=
  Q'.eqv_trans _ _ _ (connectedNumerator_expansion w K extent p q ambient)
    (Q'.eqv_symm (fiberWeight_total _ _ _ _ (selections_nodup ambient hn)
      (fun ids hi => sublist_selected ((selected_sublist (core_selected extent links ids)).trans
        (selected_sublist hi)))))

section Local

variable (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
  (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q)

include hp hq hlp hlq

theorem coefficient_rooted_pin (ids : List Nat) :
    connectedCoefficient w K extent p q ids ≈
      connectedCoefficient w K extent p q (core extent links ids) *
        partitionSquareCoefficient w K extent (spectators extent links ids) :=
  Q'.eqv_trans _ _ _ (connectedCoefficient_perm w K extent p q (split_perm extent links ids).symm)
    (coefficient_spectator_factorizes w K extent p q links hp hq hlp hlq _ _ (split_disjoint extent links ids))

theorem rootedFamily_factorizes (ambient anchor : List Nat) :
    rootedFamily w K extent p q links ambient anchor ≈
      connectedCoefficient w K extent p q anchor * spectatorWeight w K extent links ambient anchor := by
  refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ids hi => ?_)) (listQSum_mul_left _ _ _)
  have he : anchor = core extent links ids := of_decide_eq_true (List.mem_filter.mp hi).2
  have hf := coefficient_rooted_pin w K extent p q links hp hq hlp hlq ids
  rw [← he] at hf
  exact hf

end Local

def rootedResponse (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link) (ambient : List Nat) : Q' :=
  listQSum (fun anchor => connectedCoefficient w K extent p q anchor *
    spectatorWeight w K extent links ambient anchor) (selections ambient)

theorem connectedNumerator_rooted_expansion (w : Q') (K extent : Nat) (p q : RatPoly)
    (links : List Z4Link) (ambient : List Nat) (hn : ambient.Nodup)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q) :
    connectedNumerator w K extent ambient p q ≈ rootedResponse w K extent p q links ambient :=
  Q'.eqv_trans _ _ _ (connectedNumerator_family_expansion w K extent p q links ambient hn)
    (listQSum_congr_on _ _ _ (fun anchor _ => rootedFamily_factorizes w K extent p q links hp hq hlp hlq ambient anchor))

end YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion

#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.connectedCoefficient_perm
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.familySelections
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.rootedFamily
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.spectatorWeight
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.family_code_unique
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.familySelections_nodup
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.connectedNumerator_family_expansion
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.coefficient_rooted_pin
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.rootedFamily_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.rootedResponse
#print axioms YMGap.Continuum.BF4ExactSlabRootedFamilyExpansion.connectedNumerator_rooted_expansion
