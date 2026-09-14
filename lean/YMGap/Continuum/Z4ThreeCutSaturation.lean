/-
# Saturated three-cut area leaves no off-window plaquette

The three temporal cuts are disjoint filters of the actual face list.
Their total count equals the count of their computed union. Equality
with the full face count therefore forces every face into the window.
This is a finite counting theorem, not a response or sign estimate.
-/

import YMGap.Continuum.Z4TemporalCutParityMinimum

namespace YMGap.Continuum.Z4ThreeCutSaturation

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalCutParityMinimum

def window (time : Nat) (face : Z4Plaq) : Bool :=
  crosses time face || crosses (time+1) face || crosses (time+2) face

theorem crosses_unique {time other : Nat} {face : Z4Plaq}
    (h : crosses time face = true) (k : crosses other face = true) : time = other :=
  (of_decide_eq_true h).2.symm.trans (of_decide_eq_true k).2

theorem window_count (time : Nat) : ∀ faces : List Z4Plaq,
    (faces.filter (window time)).length =
      (cut time faces).length + (cut (time+1) faces).length + (cut (time+2) faces).length
  | [] => rfl
  | f::fs => by
    have ih := window_count time fs
    have h01 : ¬(crosses time f = true ∧ crosses (time+1) f = true) := by
      intro h; have hh := crosses_unique h.1 h.2; omega
    have h02 : ¬(crosses time f = true ∧ crosses (time+2) f = true) := by
      intro h; have hh := crosses_unique h.1 h.2; omega
    have h12 : ¬(crosses (time+1) f = true ∧ crosses (time+2) f = true) := by
      intro h; have hh := crosses_unique h.1 h.2; omega
    cases h0 : crosses time f <;> cases h1 : crosses (time+1) f <;> cases h2 : crosses (time+2) f
    all_goals simp_all only [window, cut, List.filter_cons, List.length_map, List.length_cons,
      Bool.false_or, Bool.true_or, Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte]
    all_goals omega

theorem saturated_in_window (time : Nat) (faces : List Z4Plaq)
    (h : (cut time faces).length + (cut (time+1) faces).length +
      (cut (time+2) faces).length = faces.length) :
    ∀ f, f ∈ faces → window time f = true :=
  List.length_filter_eq_length_iff.mp ((window_count time faces).trans h)

theorem window_temporal {time : Nat} {face : Z4Plaq} (h : window time face = true) :
    (dirsOf face.2).2 = Dir4.x3 := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact (of_decide_eq_true h).1
    · exact (of_decide_eq_true h).1
  · exact (of_decide_eq_true h).1

theorem window_times {time : Nat} {face : Z4Plaq} (h : window time face = true) :
    face.1.2.2.2 = time ∨ face.1.2.2.2 = time+1 ∨ face.1.2.2.2 = time+2 := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inl (of_decide_eq_true h).2
    · exact Or.inr (Or.inl (of_decide_eq_true h).2)
  · exact Or.inr (Or.inr (of_decide_eq_true h).2)

end YMGap.Continuum.Z4ThreeCutSaturation

#print axioms YMGap.Continuum.Z4ThreeCutSaturation.window
#print axioms YMGap.Continuum.Z4ThreeCutSaturation.crosses_unique
#print axioms YMGap.Continuum.Z4ThreeCutSaturation.window_count
#print axioms YMGap.Continuum.Z4ThreeCutSaturation.saturated_in_window
#print axioms YMGap.Continuum.Z4ThreeCutSaturation.window_temporal
#print axioms YMGap.Continuum.Z4ThreeCutSaturation.window_times
