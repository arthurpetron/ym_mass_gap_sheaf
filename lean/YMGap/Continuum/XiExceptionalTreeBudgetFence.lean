/-
# Raw occurrence-tree majorant versus the accepted chain budget

The finite occurrence-tree list deliberately enumerates both `prepend` and
`attach` presentations.  It is therefore a safe ambient carrier, but its raw
sum is not bounded by the previously accepted connecting-chain majorant.

This closed two-occurrence example uses the derived rational coupling
`w = 1/2` and the nontrivial constant representation label `1`.  The raw tree
majorant is `1/32`, whereas the chain majorant is only `21/1024`.  Hence a
successful accepted-budget comparison must first quotient or canonically
restrict the raw tree presentations; the unqualified pointwise comparison is
kernel-refuted.
-/

import YMGap.Continuum.XiExceptionalSourceTreeAnalytic

namespace YMGap.Continuum.XiExceptionalTreeBudgetFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant

local infix:50 " ≈ " => Q'.eqv

private abbrev TL := toyLattice

private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)
private def X : Polymer TL := [p]
private def Y : Polymer TL := [p, q]
private def Gamma : List (Polymer TL) := [X, Y]
private def qAll : Polymer TL → Bool := fun _ => true
private def bX : Polymer TL → Bool := fun Z => decide (Z = X)
private def bY : Polymer TL → Bool := fun Z => decide (Z = Y)
private def labelOne : TL.Plaquette → Rep := fun _ => 1
private def half : Q' := Q'.mkPos 1 2 (by decide)

theorem raw_tree_majorant_eqv_one_over_32 :
    occurrenceTreeMajorant half Gamma qAll bX bY labelOne Gamma.length ≈
      Q'.mkPos 1 32 (by decide) := by
  decide

theorem chain_majorant_eqv_21_over_1024 :
    connectingChainMajorant half qAll bX bY Gamma labelOne ≈
      Q'.mkPos 21 1024 (by decide) := by
  decide

/-- The raw tree enumeration cannot be absorbed into the accepted chain
majorant without an additional canonicalization or fibre payment. -/
theorem raw_tree_majorant_not_le_chain_majorant :
    ¬ (occurrenceTreeMajorant half Gamma qAll bX bY labelOne Gamma.length ≤
      connectingChainMajorant half qAll bX bY Gamma labelOne) := by
  decide

#print axioms raw_tree_majorant_eqv_one_over_32
#print axioms chain_majorant_eqv_21_over_1024
#print axioms raw_tree_majorant_not_le_chain_majorant

end YMGap.Continuum.XiExceptionalTreeBudgetFence
