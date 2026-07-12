/-
The complete-graph Ursell pin is a useful exact model, but it is not a generic
replacement for the Ursell coefficient of a physical incompatibility graph.

`UrsellPinComplete.ursellPinComplete` uses `K_n` for every polymer of size `n`.
This file banks the smallest kernel-checked obstruction to identifying that pin
with an arbitrary connected adjacency graph.  On three vertices, the complete
graph `K₃` and the path `P₃` are both connected, but at hard-core Mayer weight
`c = -1` their signed connected-subgraph sums are respectively `2` and `1`.
After the common `3!` normalization, their absolute Ursell coefficients are
therefore `1/3` and `1/6`.

This does not refute the complete-graph theorem.  It refutes only the attempted
physical substitution

    adjacency graph of Y  :=  K_(|Y|).

Consequently `treeGraphBoundHardCore` cannot by itself discharge the physical
tree-graph atom: a physical route must construct the actual incompatibility
edge list and pin `phiT` to its connected-subgraph sum.  The fence is finite,
exact, Mathlib-free, and proved by kernel reduction (`decide`), with no measured
constant and no classical principle.
-/

import YMGap.Continuum.UrsellPinComplete

namespace YMGap.Continuum.UrsellCompleteGraphFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseConstWeightDC
open YMGap.Continuum.PenroseConstInRange
open YMGap.Continuum.CayleyMaxBound
open YMGap.Continuum.CayleyLooseReduction
open YMGap.Continuum.CubicEulerBoundProof
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.UrsellPinComplete

/-- The connected three-vertex path `0--1--2`. -/
def pathEdges3 : List Edge := [(0, 1), (1, 2)]

/-- Both comparison graphs span all three vertices. -/
theorem comparison_graphs_span :
    spans 3 (completeEdges 3) = true ∧ spans 3 pathEdges3 = true := by
  decide

/-- Their spanning-tree counts differ: `K₃` has three and `P₃` has one. -/
theorem comparison_tree_counts :
    treeCount 3 (completeEdges 3) = 3 ∧ treeCount 3 pathEdges3 = 1 := by
  decide

/-- Exact hard-core signed connected-subgraph sums: `C(K₃)=2`, `C(P₃)=1`. -/
theorem hardCore_connected_sums :
    (Csum (wConst (-1)) 3 (completeEdges 3)).eqv 2 ∧
      (Csum (wConst (-1)) 3 pathEdges3).eqv 1 := by
  decide

/-- The normalized absolute Ursell coefficient attached to a finite edge list. -/
def hardCoreUrsell3 (edges : List Edge) : Q' :=
  Q'.abs (Csum (wConst (-1)) 3 edges) * Q'.mkPos 1 6 (by decide)

/-- Exact normalized coefficients: `|C(K₃)|/3! = 1/3`, while
`|C(P₃)|/3! = 1/6`. -/
theorem hardCore_ursell_values :
    (hardCoreUrsell3 (completeEdges 3)).eqv (Q'.mkPos 1 3 (by decide)) ∧
      (hardCoreUrsell3 pathEdges3).eqv (Q'.mkPos 1 6 (by decide)) := by
  decide

/-- **Dead-route fence.**  The complete-graph hard-core pin is not the path-graph
hard-core pin, even though both graphs are connected and have the same vertex
count.  Thus size and connectedness do not determine the physical Ursell
coefficient. -/
theorem completeGraph_pin_ne_path_pin :
    ¬ (hardCoreUrsell3 (completeEdges 3)).eqv (hardCoreUrsell3 pathEdges3) := by
  decide

/-- A formulation directly exposing the failed size-only substitution: no
coefficient depending only on vertex count can equal both exact graph
coefficients at `n = 3`. -/
theorem no_size_only_pin_at_three (u : Q')
    (hK : u.eqv (hardCoreUrsell3 (completeEdges 3)))
    (hP : u.eqv (hardCoreUrsell3 pathEdges3)) : False := by
  have hKP : (hardCoreUrsell3 (completeEdges 3)).eqv (hardCoreUrsell3 pathEdges3) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hK) hP
  exact completeGraph_pin_ne_path_pin hKP

/-! ## Graph-sensitive repair

The finite Penrose inequality does not require a complete graph.  The correct
constructive interface is an explicit simple edge list for each polymer.  The
next constructor pins `phiT` to that graph's exact connected-subgraph sum. -/

/-- Construct the exact const-weight Ursell pin from an explicit simple
incompatibility graph for every polymer.  Unlike `ursellPinComplete`, this does
not replace the supplied graph by `K_(|Y|)`. -/
def ursellPinOfSimpleGraphs (S : SepLattice) (c : Q')
    (edges : Polymer S.toLattice → List Edge)
    (hsimple : ∀ Y, SimpleEdges (Polymer.size Y) (edges Y)) :
    UrsellPinConst S c where
  adjN := fun Y => Polymer.size Y
  adjE := edges
  adjInRange := by
    intro Y e he
    have h := (hsimple Y).2 e he
    exact ⟨Nat.lt_trans h.1 h.2, h.2⟩
  phiT := fun Y =>
    Q'.abs (Csum (wConst c) (Polymer.size Y) (edges Y)) *
      Q'.mkPos 1 (fact (Polymer.size Y)) (fact_pos _)
  phiT_nonneg := fun Y =>
    Q'.mul_nonneg _ _ (Q'.abs_nonneg _)
      (mkPos_recip_nonneg _ (fact_pos _))
  treeCountF := fun Y => treeCount (Polymer.size Y) (edges Y)
  ursell := fun Y =>
    ofNat_mul_recip_cancel _ (fact (Polymer.size Y)) (fact_pos _)
  countPin := fun _ => rfl

/-- **Strict graph-sensitive reduction.**  An explicit simple incompatibility
graph family yields the exact const-weight `TreeGraphBound`; no complete-graph
substitution and no new analytic hypothesis is used.  A physical application
must still prove that `edges Y` is the actual incompatibility graph of `Y`.
That identification is the honest residual isolated by the three-vertex fence. -/
def treeGraphBoundOfSimpleGraphs (S : SepLattice) (w : Q') (r : Rep)
    (c : Q') (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q'))
    (edges : Polymer S.toLattice → List Edge)
    (hsimple : ∀ Y, SimpleEdges (Polymer.size Y) (edges Y)) :
    TreeGraphBound S w r :=
  let P := ursellPinOfSimpleGraphs S c edges hsimple
  let red : TreeGraphReductionLoose S w r := {
    phiT := P.phiT
    phiT_nonneg := P.phiT_nonneg
    treeCount := P.treeCountF
    penroseDom := fun Y => penroseDomConst_of_pin hc1 hc2 P Y
    cayleyMaxLoose := fun Y =>
      CayleyParentInj.cayleyLooseBound_closed
        (Polymer.size Y) (edges Y) (hsimple Y)
  }
  red.toBoundLoose cubicEulerBound

/-- Hard-core specialization of the graph-sensitive repair. -/
def treeGraphBoundHardCoreOfSimpleGraphs (S : SepLattice) (w : Q') (r : Rep)
    (edges : Polymer S.toLattice → List Edge)
    (hsimple : ∀ Y, SimpleEdges (Polymer.size Y) (edges Y)) :
    TreeGraphBound S w r :=
  treeGraphBoundOfSimpleGraphs S w r (-1) (by decide) (by decide) edges hsimple

end YMGap.Continuum.UrsellCompleteGraphFence

#print axioms YMGap.Continuum.UrsellCompleteGraphFence.comparison_graphs_span
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.comparison_tree_counts
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.hardCore_connected_sums
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.hardCore_ursell_values
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.completeGraph_pin_ne_path_pin
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.no_size_only_pin_at_three
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.ursellPinOfSimpleGraphs
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.treeGraphBoundOfSimpleGraphs
#print axioms YMGap.Continuum.UrsellCompleteGraphFence.treeGraphBoundHardCoreOfSimpleGraphs
