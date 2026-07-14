import YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction

namespace YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveBreakNecessity

open YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveParityObstruction

theorem bool_ne_eq_not {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

/-- Equal forced endpoint layers on a full odd-edge component require a
non-alternating edge.  Thus a uniform payer needs an explicit cut/reset (or
several carrier codes); the existing two hard-core masks alone cannot do it. -/
theorem same_endpoint_requires_break (k : Nat) (color : Nat → Bool)
    (hend : color (oddEdges k) = color 0) :
    ¬ (∀ i, i < oddEdges k → color (i + 1) ≠ color i) := by
  intro hproper
  let C : PathTwoColoring (oddEdges k) :=
    { color := color
      step := fun i hi => bool_ne_eq_not (fun h => hproper i hi h.symm) }
  have hflip := odd_path_endpoint_flip k C
  change color (oddEdges k) = !(color 0) at hflip
  rw [hend] at hflip
  cases h : color 0 <;> simp [h] at hflip

theorem c12_same_endpoint_requires_break (color : Nat → Bool)
    (hend : color 7 = color 0) :
    ¬ (∀ i, i < 7 → color (i + 1) ≠ color i) := by
  change ¬ (∀ i, i < oddEdges 3 → color (i + 1) ≠ color i)
  exact same_endpoint_requires_break 3 color hend

end YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveBreakNecessity

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveBreakNecessity.same_endpoint_requires_break
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmAdaptiveBreakNecessity.c12_same_endpoint_requires_break
