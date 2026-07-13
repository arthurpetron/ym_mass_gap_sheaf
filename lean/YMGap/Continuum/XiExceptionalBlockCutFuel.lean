/-
# Additive block-cut fuel for pair-bounced ears

An occurrence carrier has only `Gamma.length` chain fuel.  Repeating an ear
therefore has to be budgeted before any codes are composed.  A block records
the adjacent interior pairs on the selected arm and on its unselected reserve
arm.  A binary block-cut tree adds these quantities over its children.

The exact invariant is sharp: the selected pair total fits precisely when it
does not exceed the reserve pair total.  Consequently both complementary
square codes fit precisely when the two totals are equal.  This exposes the
capacity condition needed by a multicode allocator rather than burying it in
a later target-membership proof.
-/

import YMGap.Continuum.XiExceptionalEarOccurrenceCarrier

namespace YMGap.Continuum.XiExceptionalBlockCutFuel

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalEarOccurrenceCarrier

/-- Fuel data for a block-cut tree.  `selected` counts adjacent interior
pairs on the arm encoded by a square code; `reserve` counts the unused arm.
Each fork also carries its own block before its two child subtrees. -/
inductive BlockCutFuel
  | leaf (selected reserve : Nat)
  | fork (selected reserve : Nat) (left right : BlockCutFuel)
deriving DecidableEq

namespace BlockCutFuel

def blockCount : BlockCutFuel → Nat
  | .leaf _ _ => 1
  | .fork _ _ left right => 1 + left.blockCount + right.blockCount

def selectedPairs : BlockCutFuel → Nat
  | .leaf selected _ => selected
  | .fork selected _ left right =>
      selected + left.selectedPairs + right.selectedPairs

def reservePairs : BlockCutFuel → Nat
  | .leaf _ reserve => reserve
  | .fork _ reserve left right =>
      reserve + left.reservePairs + right.reservePairs

/-- Edge occurrences used after pair-bouncing every selected arm.  The
unrepeated base edge of every block contributes one. -/
def repeatedEdgeCost : BlockCutFuel → Nat
  | .leaf selected _ => 1 + 4 * selected
  | .fork selected _ left right =>
      1 + 4 * selected + left.repeatedEdgeCost + right.repeatedEdgeCost

/-- Available distinct-occurrence edge budget: one base edge per block and
two interior vertices for every pair on either arm. -/
def availableEdgeBudget : BlockCutFuel → Nat
  | .leaf selected reserve => 1 + 2 * (selected + reserve)
  | .fork selected reserve left right =>
      1 + 2 * (selected + reserve) + left.availableEdgeBudget +
        right.availableEdgeBudget

def bouncedVertexLength (tree : BlockCutFuel) : Nat :=
  tree.repeatedEdgeCost + 1

def availableOccurrenceCount (tree : BlockCutFuel) : Nat :=
  tree.availableEdgeBudget + 1

/-- Every local selected arm has enough reserve in its own block. -/
def LocallyFits : BlockCutFuel → Prop
  | .leaf selected reserve => selected ≤ reserve
  | .fork selected reserve left right =>
      selected ≤ reserve ∧ left.LocallyFits ∧ right.LocallyFits

def swap : BlockCutFuel → BlockCutFuel
  | .leaf selected reserve => .leaf reserve selected
  | .fork selected reserve left right =>
      .fork reserve selected left.swap right.swap

/-! ## Exact additive identities -/

theorem repeatedEdgeCost_eq : ∀ tree : BlockCutFuel,
    tree.repeatedEdgeCost = tree.blockCount + 4 * tree.selectedPairs
  | .leaf selected reserve => by
      simp [repeatedEdgeCost, blockCount, selectedPairs]
  | .fork selected reserve left right => by
      simp only [repeatedEdgeCost, blockCount, selectedPairs]
      rw [repeatedEdgeCost_eq left, repeatedEdgeCost_eq right]
      omega

theorem availableEdgeBudget_eq : ∀ tree : BlockCutFuel,
    tree.availableEdgeBudget = tree.blockCount +
      2 * (tree.selectedPairs + tree.reservePairs)
  | .leaf selected reserve => by
      simp [availableEdgeBudget, blockCount, selectedPairs, reservePairs]
  | .fork selected reserve left right => by
      simp only [availableEdgeBudget, blockCount, selectedPairs, reservePairs]
      rw [availableEdgeBudget_eq left, availableEdgeBudget_eq right]
      omega

theorem fork_repeated_cost_additive
    (selected reserve : Nat) (left right : BlockCutFuel) :
    (BlockCutFuel.fork selected reserve left right).repeatedEdgeCost =
      1 + 4 * selected + left.repeatedEdgeCost + right.repeatedEdgeCost :=
  rfl

theorem fork_available_budget_additive
    (selected reserve : Nat) (left right : BlockCutFuel) :
    (BlockCutFuel.fork selected reserve left right).availableEdgeBudget =
      1 + 2 * (selected + reserve) + left.availableEdgeBudget +
        right.availableEdgeBudget :=
  rfl

/-! ## Structural budget induction -/

theorem selected_le_reserve_of_locallyFits : ∀ tree : BlockCutFuel,
    tree.LocallyFits → tree.selectedPairs ≤ tree.reservePairs
  | .leaf selected reserve, h => h
  | .fork selected reserve left right, h => by
      have hlocal : selected ≤ reserve := h.1
      have hleft : left.selectedPairs ≤ left.reservePairs :=
        selected_le_reserve_of_locallyFits left h.2.1
      have hright : right.selectedPairs ≤ right.reservePairs :=
        selected_le_reserve_of_locallyFits right h.2.2
      simp only [selectedPairs, reservePairs]
      omega

theorem global_occurrence_budget_of_locallyFits (tree : BlockCutFuel)
    (hfit : tree.LocallyFits) :
    tree.bouncedVertexLength ≤ tree.availableOccurrenceCount := by
  have htot := selected_le_reserve_of_locallyFits tree hfit
  unfold bouncedVertexLength availableOccurrenceCount
  rw [repeatedEdgeCost_eq, availableEdgeBudget_eq]
  omega

theorem global_occurrence_budget_iff (tree : BlockCutFuel) :
    tree.bouncedVertexLength ≤ tree.availableOccurrenceCount ↔
      tree.selectedPairs ≤ tree.reservePairs := by
  unfold bouncedVertexLength availableOccurrenceCount
  rw [repeatedEdgeCost_eq, availableEdgeBudget_eq]
  constructor <;> intro h <;> omega

/-! ## Complementary-code capacity -/

theorem swap_blockCount : ∀ tree : BlockCutFuel,
    tree.swap.blockCount = tree.blockCount
  | .leaf selected reserve => rfl
  | .fork selected reserve left right => by
      simp only [swap, blockCount]
      rw [swap_blockCount left, swap_blockCount right]

theorem swap_selectedPairs : ∀ tree : BlockCutFuel,
    tree.swap.selectedPairs = tree.reservePairs
  | .leaf selected reserve => rfl
  | .fork selected reserve left right => by
      simp only [swap, selectedPairs, reservePairs]
      rw [swap_selectedPairs left, swap_selectedPairs right]

theorem swap_reservePairs : ∀ tree : BlockCutFuel,
    tree.swap.reservePairs = tree.selectedPairs
  | .leaf selected reserve => rfl
  | .fork selected reserve left right => by
      simp only [swap, reservePairs, selectedPairs]
      rw [swap_reservePairs left, swap_reservePairs right]

/-- Sharp global capacity test for the two complementary square codes. -/
theorem both_complementary_codes_fit_iff_balanced (tree : BlockCutFuel) :
    (tree.bouncedVertexLength ≤ tree.availableOccurrenceCount ∧
      tree.swap.bouncedVertexLength ≤ tree.swap.availableOccurrenceCount) ↔
        tree.selectedPairs = tree.reservePairs := by
  constructor
  · intro h
    have hforward := (global_occurrence_budget_iff tree).mp h.1
    have hreverse := (global_occurrence_budget_iff tree.swap).mp h.2
    rw [swap_selectedPairs, swap_reservePairs] at hreverse
    exact Nat.le_antisymm hforward hreverse
  · intro h
    constructor
    · exact (global_occurrence_budget_iff tree).mpr (Nat.le_of_eq h)
    · apply (global_occurrence_budget_iff tree.swap).mpr
      rw [swap_selectedPairs, swap_reservePairs]
      exact Nat.le_of_eq h.symm

/-! ## Connection to the occurrence target constructor -/

variable {L : Lattice} [DecidableEq L.Plaquette]

theorem leaf_bouncedVertexLength {edge : Nat → Nat → Bool}
    {i j : Nat} (path : PairedPath edge i j) (reserve : Nat) :
    (BlockCutFuel.leaf path.pairCount reserve).bouncedVertexLength =
      2 + 4 * path.pairCount := by
  simp only [bouncedVertexLength, repeatedEdgeCost]
  omega

/-- A locally budgeted leaf is a genuine target code once its available
occurrence count is the ambient list length and its vertices are in range. -/
theorem pairedBounceCarrierCode_mem_of_leaf_budget
    (Gamma : List (Polymer L))
    {edge : Nat → Nat → Bool} {i j : Nat}
    (path : PairedPath edge i j)
    (hsymm : ∀ x y, edge x y = true → edge y x = true)
    (background external : OccBitVec Gamma.length)
    (reserve : Nat)
    (hfit : path.pairCount ≤ reserve)
    (hcount :
      (BlockCutFuel.leaf path.pairCount reserve).availableOccurrenceCount =
        Gamma.length)
    (hi : i < Gamma.length)
    (hbound : ∀ k, k ∈ (path.bounceWalk hsymm).vertices →
      k < Gamma.length) :
    pairedBounceCarrierCode Gamma path hsymm background external ∈
      occurrenceCarrierXiCodes Gamma := by
  apply pairedBounceCarrierCode_mem Gamma path hsymm background external hi
  · rw [← leaf_bouncedVertexLength path reserve, ← hcount]
    exact global_occurrence_budget_of_locallyFits
      (.leaf path.pairCount reserve) hfit
  · exact hbound

#print axioms repeatedEdgeCost_eq
#print axioms availableEdgeBudget_eq
#print axioms selected_le_reserve_of_locallyFits
#print axioms global_occurrence_budget_of_locallyFits
#print axioms global_occurrence_budget_iff
#print axioms both_complementary_codes_fit_iff_balanced
#print axioms pairedBounceCarrierCode_mem_of_leaf_budget

end BlockCutFuel

end YMGap.Continuum.XiExceptionalBlockCutFuel
