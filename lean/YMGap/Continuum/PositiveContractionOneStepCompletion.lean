/-
# The completed one-step form and the canonical norm-decreasing map

A positive contraction induces its own completed one-step form, and its same
action descends there. The identity on representatives gives a continuous map
from the original completion, with unchanged Cauchy moduli, intertwining the
two actions. Its inner product is exactly one original transfer insertion.
No inverse or equivalence of norms is claimed.
-/

import YMGap.Continuum.PositiveContractionOneStepForm
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.PositiveContractionOneStepCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.PositiveContractionOneStepForm

local infix:50 " ≈ " => Q'.eqv

def actionIterate {V : Type} (F : V → V) : Nat → V → V
  | 0, x => x
  | n + 1, x => F (actionIterate F n x)

variable (D : SmulGNSData) (S : DiagonalTransferSymbol D)
  (hsub : ∀ a b, D.toGNSData.veq (S.Dv (D.toGNSData.sub a b))
    (D.toGNSData.sub (S.Dv a) (S.Dv b)))
  (hsa : ∀ a b, D.toGNSData.B a (S.Dv b) ≈ D.toGNSData.B (S.Dv a) b)
  (hpos : ∀ a, (0 : Q') ≤ D.toGNSData.B a (S.Dv a))
  (hupper : ∀ a, D.toGNSData.B a (S.Dv a) ≤ D.toGNSData.B a a)

local notation "E" => oneStepSmulGNSData D S.Dv hsa hpos
local notation "T" => oneStepSymbol D S hsub hsa hpos hupper

/-- Identity on representatives; the one-step form is bounded by the original norm. -/
def comparisonCauchy (X : CauchyGNS D.toGNSData) : CauchyGNS (E).toGNSData where
  seq := X.seq
  modulus := X.modulus
  isCauchy := fun epsilon hepsilon p q hp hq =>
    Q'.le_trans' _ _ _ (hupper (D.toGNSData.sub (X.seq p) (X.seq q)))
      (X.isCauchy epsilon hepsilon p q hp hq)

theorem comparisonCauchy_null {X Y : CauchyGNS D.toGNSData}
    (h : CauchyNull D.toGNSData X Y) :
    CauchyNull (E).toGNSData (comparisonCauchy D S hsa hpos hupper X)
      (comparisonCauchy D S hsa hpos hupper Y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (hupper (D.toGNSData.sub (X.seq n) (Y.seq n))) (hN n hn)⟩

def comparison : GNSCompletionSpace D.toGNSData → GNSCompletionSpace (E).toGNSData :=
  Quotient.lift
    (fun X => Quotient.mk (cauchySetoid (E).toGNSData) (comparisonCauchy D S hsa hpos hupper X))
    (fun _ _ h => Quotient.sound (comparisonCauchy_null D S hsa hpos hupper h))

theorem comparison_embed (a : D.toGNSData.V) :
    comparison D S hsa hpos hupper (embedV D.toGNSData a) = embedV (E).toGNSData a := rfl

/-- The two completed actions commute with the same-representative map. -/
theorem comparison_intertwines (x : GNSCompletionSpace D.toGNSData) :
    comparison D S hsa hpos hupper (S.TqSymb x) =
      (T).TqSymb (comparison D S hsa hpos hupper x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

/-- The completed comparison retains the exact one-step matrix element. -/
theorem comparison_inner (x y : GNSCompletionSpace D.toGNSData) :
    (E).toGNSData.cinnerCompl (comparison D S hsa hpos hupper x)
        (comparison D S hsa hpos hupper y) =
      D.toGNSData.cinnerCompl x (S.TqSymb y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv (Q'.eqv_refl _)

theorem comparison_contraction (x : GNSCompletionSpace D.toGNSData) :
    CReal.RCle ((E).toGNSData.cinnerCompl (comparison D S hsa hpos hupper x)
        (comparison D S hsa hpos hupper x)) (D.toGNSData.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  show CReal.leEv ((E).toGNSData.cinnerRep (comparisonCauchy D S hsa hpos hupper X)
    (comparisonCauchy D S hsa hpos hupper X)) (D.toGNSData.cinnerRep X X)
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _ (hupper (X.seq n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

theorem comparison_iterates (n : Nat) (x : GNSCompletionSpace D.toGNSData) :
    comparison D S hsa hpos hupper (actionIterate S.TqSymb n x) =
      actionIterate (T).TqSymb n (comparison D S hsa hpos hupper x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change comparison D S hsa hpos hupper (S.TqSymb (actionIterate S.TqSymb n x)) = _
      rw [comparison_intertwines D S hsub hsa hpos hupper, ih]
      rfl

/-- Exact same-operator moments: one-step-form time n is original-form time n+1. -/
theorem comparison_moments (n : Nat) (x y : GNSCompletionSpace D.toGNSData) :
    (E).toGNSData.cinnerCompl (comparison D S hsa hpos hupper x)
        (actionIterate (T).TqSymb n (comparison D S hsa hpos hupper y)) =
      D.toGNSData.cinnerCompl x (actionIterate S.TqSymb (n + 1) y) := by
  rw [← comparison_iterates D S hsub hsa hpos hupper, comparison_inner D S hsa hpos hupper]
  rfl

theorem completed_selfAdjoint (x y : GNSCompletionSpace (E).toGNSData) :
    (E).toGNSData.cinnerCompl ((T).TqSymb x) y = (E).toGNSData.cinnerCompl x ((T).TqSymb y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm (hsa (X.seq n) (S.Dv (Y.seq n))))

theorem completed_positive (x : GNSCompletionSpace (E).toGNSData) :
    CReal.RCnonneg ((E).toGNSData.cinnerCompl ((T).TqSymb x) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  show CReal.leEv CReal.czero ((E).toGNSData.cinnerRep ((T).cDiagCauchy X) X)
  apply CReal.leEv_ofQ'_of_approx_ge
  intro n
  exact D.toGNSData.self_nonneg _

theorem completed_contraction (x : GNSCompletionSpace (E).toGNSData) :
    CReal.RCle ((E).toGNSData.cinnerCompl ((T).TqSymb x) ((T).TqSymb x))
      ((E).toGNSData.cinnerCompl x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  show CReal.leEv ((E).toGNSData.cinnerRep ((T).cDiagCauchy X) ((T).cDiagCauchy X))
    ((E).toGNSData.cinnerRep X X)
  refine CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _) ?_
  intro epsilon hepsilon
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (oneStep_contraction D.toGNSData S.Dv hsa hpos hupper (X.seq n))
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩

end YMGap.Continuum.PositiveContractionOneStepCompletion

#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparisonCauchy
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparisonCauchy_null
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison_embed
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison_intertwines
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison_inner
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison_contraction
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison_iterates
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.comparison_moments
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.completed_selfAdjoint
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.completed_positive
#print axioms YMGap.Continuum.PositiveContractionOneStepCompletion.completed_contraction
