/-
# Branch-return articulation normalization fence

A depth-first carrier that leaves an articulation to visit a branch and then
returns must contain the articulation twice.  Its activity monomial therefore
contains the square of the articulation activity.  This is not a uniform
upper replacement for the source monomial: at activity `1/2`, the returned
walk contributes `1/4`, strictly below the once-counted source contribution
`1/2`.

Thus parallel block-cut children cannot be converted into one carrier merely
by inserting return excursions.  A valid branch allocator needs an additional
multicode inequality or a routing field that preserves the once-counted
articulation normalization.
-/

import YMGap.Continuum.XiExceptionalPairedSpine

namespace YMGap.Continuum.XiExceptionalBranchReturnFence

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalPathExtraction

local infix:50 " ≈ " => Q'.eqv

def branchEdge (_ _ : Bool) : Bool := true

/-- The minimal leave-and-return excursion. -/
def branchReturnWalk : CWalk branchEdge false false :=
  .cons (x := false) (y := true) (by rfl)
    (.cons (x := true) (y := false) (by rfl) (.single false))

theorem branchReturn_vertices :
    branchReturnWalk.vertices = [false, true, false] := rfl

theorem branchReturn_articulation_twice :
    (branchReturnWalk.vertices.filter (fun x => x == false)).length = 2 := rfl

private def half : Q' := Q'.mkPos 1 2 (by decide)

def onceCountedBranchMonomial (articulation branch : Q') : Q' :=
  articulation * branch

def returnedBranchMonomial (articulation branch : Q') : Q' :=
  articulation * articulation * branch

theorem half_once_eqv :
    onceCountedBranchMonomial half 1 ≈ half := by decide

theorem half_returned_eqv :
    returnedBranchMonomial half 1 ≈ Q'.mkPos 1 4 (by decide) := by decide

/-- Closed rational counterexample to naive return-excursion domination. -/
theorem branch_return_not_uniformly_dominating :
    ¬ onceCountedBranchMonomial half 1 ≤
      returnedBranchMonomial half 1 := by decide

#print axioms branchReturn_vertices
#print axioms branchReturn_articulation_twice
#print axioms half_once_eqv
#print axioms half_returned_eqv
#print axioms branch_return_not_uniformly_dominating

end YMGap.Continuum.XiExceptionalBranchReturnFence
