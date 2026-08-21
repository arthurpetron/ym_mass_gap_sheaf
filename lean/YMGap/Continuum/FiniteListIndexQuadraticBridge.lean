/-
# Exact list-to-finite-index quadratic bridge

Finite rational matrix checkers use coordinates `0, ..., n-1`, while the
physical constructions in this repository use literal duplicate-free lists.
This module proves that totalized `List.getD` lookup on the exact list length
preserves the single and double `listQSum` expressions.  Out-of-range fallback
values are therefore irrelevant to every certified finite matrix quadratic.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalLDLCertificate

namespace YMGap.Continuum.FiniteListIndexQuadraticBridge

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Totalized lookup used by a finite matrix table. -/
def finiteListStateAt {State : Type}
    (states : List State) (fallback : State) (index : Nat) : State :=
  states.getD index fallback

private theorem range_succ_shift (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        List.range (Nat.succ n + 1) =
            List.range (n + 1) ++ [n + 1] := by
          simpa only [Nat.succ_eq_add_one] using
            (List.range_succ (n := n + 1))
        _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] :=
          congrArg (fun items => items ++ [n + 1]) ih
        _ = 0 :: (List.range (n + 1)).map Nat.succ := by
          simp only [List.range_succ, List.map_append, List.map,
            List.cons_append, Nat.succ_eq_add_one]

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

/-- Summing a value over totalized in-range indices is literally the original
list sum. -/
theorem finiteIndexSum_eq_listQSum
    {State : Type} (states : List State) (fallback : State)
    (value : State → Q') :
    listQSum
        (fun index => value (finiteListStateAt states fallback index))
        (List.range states.length) =
      listQSum value states := by
  induction states with
  | nil => rfl
  | cons head tail ih =>
      rw [List.length_cons, range_succ_shift]
      simp only [listQSum, finiteListStateAt, List.getD_cons_zero]
      rw [listQSum_map_local]
      simp only [List.getD_cons_succ]
      exact congrArg (fun sum => value head + sum)
        (by simpa [finiteListStateAt] using ih)

/-- The corresponding exact bridge for a double list sum. -/
theorem finiteIndexDoubleSum_eqv_listQSum
    {State : Type} (states : List State) (fallback : State)
    (value : State → State → Q') :
    listQSum
        (fun row => listQSum
          (fun column => value
            (finiteListStateAt states fallback row)
            (finiteListStateAt states fallback column))
          (List.range states.length))
        (List.range states.length) ≈
      listQSum
        (fun left => listQSum (value left) states)
        states := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum
        (fun column => value left
          (finiteListStateAt states fallback column))
        (List.range states.length))
      states) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states fallback
        (fun left => listQSum
          (fun column => value left
            (finiteListStateAt states fallback column))
          (List.range states.length)))
  · apply listQSum_congr_on
    intro left _hleft
    exact Q'.eqv_of_eq
      (finiteIndexSum_eq_listQSum states fallback (value left))

end YMGap.Continuum.FiniteListIndexQuadraticBridge

#print axioms
  YMGap.Continuum.FiniteListIndexQuadraticBridge.finiteIndexSum_eq_listQSum
#print axioms
  YMGap.Continuum.FiniteListIndexQuadraticBridge.finiteIndexDoubleSum_eqv_listQSum
