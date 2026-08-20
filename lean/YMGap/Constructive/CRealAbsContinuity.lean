/-
Constructive continuity of absolute value for `CReal.ConvergesTo`.

`CReal.abs` was already proved representation-invariant, but the continuum
correlation handoff needs the corresponding sequential continuity statement:
signed sampled correlators converging to `C` imply that their absolute values
converge to `|C|`.  The proof is the rational reverse-triangle inequality at
each approximation index.  No sign decision or classical trichotomy is used.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealExp

namespace YMGap.Constructive.CReal

/-- Absolute value preserves constructive-real sequential convergence. -/
theorem convergesTo_abs {s : Nat -> CReal} {L : CReal}
    (h : ConvergesTo s L) :
    ConvergesTo (fun k => abs (s k)) (abs L) := by
  intro ε hε
  obtain ⟨Nstage, hstage⟩ := h ε hε
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx, hapx⟩ := hstage N hN
  refine ⟨Napx, fun n hn => ?_⟩
  obtain ⟨hSL, hLS⟩ := hapx n hn
  have hdiffSL :
      Q'.abs ((s N).approx n + -(L.approx n)) ≤ ε :=
    CReal.abs_sub_le_of_bounds hSL hLS
  have hdiffLS :
      Q'.abs (L.approx n + -((s N).approx n)) ≤ ε :=
    CReal.abs_sub_le_of_bounds hLS hSL
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.abs_le_abs_add_abs_sub ((s N).approx n) (L.approx n))
      (Q'.add_le_add_left _ _ ε hdiffSL)
  · exact Q'.le_trans' _ _ _
      (Q'.abs_le_abs_add_abs_sub (L.approx n) ((s N).approx n))
      (Q'.add_le_add_left _ _ ε hdiffLS)

end YMGap.Constructive.CReal

#print axioms YMGap.Constructive.CReal.convergesTo_abs
