/-
# Parametric parity obstruction for adaptive long-arm coloring

The C12 first-gap construction is not fundamentally twelve-specific.  Its
exceptional full pattern is forced by path parity: a connected path with an
odd number of edges has opposite colors at its endpoints in every proper
two-coloring.  The carrier short chain forces both boundary occurrences into
the external layer, so no two-layer singleton carrier can handle such a full
component.  A missing occurrence resets the coloring, while a full odd-edge
component needs a separate multi-code payer.

This file states and proves that obstruction for arbitrary length.  C12 is
the instance with seven edges (`oddEdges 3`).
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction

/-- A recursive presentation of the positive odd numbers: `1,3,5,...`. -/
def oddEdges : Nat → Nat
  | 0 => 1
  | k + 1 => oddEdges k + 2

/-- Flip a Boolean once per traversed path edge. -/
def flipN : Nat → Bool → Bool
  | 0, b => b
  | n + 1, b => !(flipN n b)

theorem flipN_add_two (n : Nat) (b : Bool) :
    flipN (n + 2) b = flipN n b := by
  simp [flipN]

theorem flipN_oddEdges (k : Nat) (b : Bool) :
    flipN (oddEdges k) b = !b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      unfold oddEdges
      rw [flipN_add_two, ih]

/-- Abstract data of a proper two-coloring of a path with `edges` edges.
Only the local alternation law is retained; no finite enumeration appears. -/
structure PathTwoColoring (edges : Nat) where
  color : Nat → Bool
  step : ∀ i, i < edges → color (i + 1) = !(color i)

theorem PathTwoColoring.color_eq_flipN {edges : Nat}
    (C : PathTwoColoring edges) :
    ∀ i, i ≤ edges → C.color i = flipN i (C.color 0)
  | 0, _ => rfl
  | i + 1, hi => by
      rw [C.step i (Nat.lt_of_succ_le hi),
        C.color_eq_flipN i (Nat.le_trans (Nat.le_succ i) hi)]
      rfl

/-- On every odd-edge path, the endpoint color is the negation of the start
color. -/
theorem odd_path_endpoint_flip (k : Nat)
    (C : PathTwoColoring (oddEdges k)) :
    C.color (oddEdges k) = !(C.color 0) := by
  rw [C.color_eq_flipN (oddEdges k) (Nat.le_refl _), flipN_oddEdges]

/-- Therefore both endpoints cannot be assigned to the same (external)
layer.  This is the general obstruction met by the full C12 off-path arm. -/
theorem no_odd_path_both_external (k : Nat)
    (C : PathTwoColoring (oddEdges k)) :
    ¬ (C.color 0 = false ∧ C.color (oddEdges k) = false) := by
  intro h
  have hend := odd_path_endpoint_flip k C
  rw [h.1, h.2] at hend
  cases hend

theorem oddEdges_three : oddEdges 3 = 7 := by rfl

/-- Kernel-checked C12 specialization: the eight vertices `V4,...,V11`
form a seven-edge component, so a compatible two-layer coloring cannot put
both forced boundary vertices in the external layer. -/
theorem no_c12_full_component_two_layer
    (C : PathTwoColoring 7) :
    ¬ (C.color 0 = false ∧ C.color 7 = false) := by
  change ¬ (C.color 0 = false ∧ C.color (oddEdges 3) = false)
  exact no_odd_path_both_external 3 C

end YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction.flipN_oddEdges
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction.PathTwoColoring.color_eq_flipN
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction.odd_path_endpoint_flip
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction.no_odd_path_both_external
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction.no_c12_full_component_two_layer
