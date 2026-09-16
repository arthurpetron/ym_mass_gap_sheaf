/-
# Fixed points and invariant ranges on the existing GNS completion

Self-adjointness moves the operators onto a fixed test vector. The existing
pairing continuity of the supplied Cauchy representative then passes its
termwise fixed-point identities to the SAME completion class. No new
representative, inverse, completion or modulus is selected.

The intended consumer is the original conditional projection: locality
proves its dense output independent of a second, non-neighboring link.
The final lemma extends a dense invariant-range identity by transposing
the existing operators and testing against the original dense vectors.
These are completion identities, not strict contraction or OS-gap claims.
-/

import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.GNSDenseFixedPoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws

variable {D : GNSData}

private theorem pairing_eq_of_cauchy_terms (x y : GNSCompletionSpace D)
    (X : CauchyGNS D)
    (h : ∀ n, D.cinnerCompl x (embedV D (X.seq n)) =
      D.cinnerCompl y (embedV D (X.seq n))) :
    D.cinnerCompl x (Quotient.mk (cauchySetoid D) X) =
      D.cinnerCompl y (Quotient.mk (cauchySetoid D) X) := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro U V h
  apply Quotient.sound
  exact CReal.Equiv_of_limit_of_equal
    (fun n => Quotient.exact (s := CReal.crealSetoid) (h n))
    (fixed_input_converges U X) (fixed_input_converges V X)

/-- Fixedness of every operator image of a supplied Cauchy sequence passes
to the image of its original completion class. Both maps are self-adjoint;
neither a chosen representative of an output nor a new continuity axiom is
needed. -/
theorem fixed_of_cauchy_images
    (C P : GNSCompletionSpace D → GNSCompletionSpace D)
    (hC : ∀ x y, D.cinnerCompl (C x) y = D.cinnerCompl x (C y))
    (hP : ∀ x y, D.cinnerCompl (P x) y = D.cinnerCompl x (P y))
    (X : CauchyGNS D)
    (hfix : ∀ n, C (P (embedV D (X.seq n))) = P (embedV D (X.seq n))) :
    C (P (Quotient.mk (cauchySetoid D) X)) =
      P (Quotient.mk (cauchySetoid D) X) := by
  apply eq_of_pairings_equal
  intro y
  have hweak : D.cinnerCompl (P (C y)) (Quotient.mk (cauchySetoid D) X) =
      D.cinnerCompl (P y) (Quotient.mk (cauchySetoid D) X) := by
    apply pairing_eq_of_cauchy_terms
    intro n
    calc
      D.cinnerCompl (P (C y)) (embedV D (X.seq n)) =
          D.cinnerCompl (C y) (P (embedV D (X.seq n))) := hP _ _
      _ = D.cinnerCompl (P (embedV D (X.seq n))) (C y) := D.cinnerCompl_comm _ _
      _ = D.cinnerCompl (C (P (embedV D (X.seq n)))) y := (hC _ _).symm
      _ = D.cinnerCompl (P (embedV D (X.seq n))) y :=
        congrArg (fun z => D.cinnerCompl z y) (hfix n)
      _ = D.cinnerCompl (embedV D (X.seq n)) (P y) := hP _ _
      _ = D.cinnerCompl (P y) (embedV D (X.seq n)) := D.cinnerCompl_comm _ _
  calc
    D.cinnerCompl (C (P (Quotient.mk (cauchySetoid D) X))) y =
        D.cinnerCompl (P (Quotient.mk (cauchySetoid D) X)) (C y) := hC _ _
    _ = D.cinnerCompl (Quotient.mk (cauchySetoid D) X) (P (C y)) := hP _ _
    _ = D.cinnerCompl (P (C y)) (Quotient.mk (cauchySetoid D) X) := D.cinnerCompl_comm _ _
    _ = D.cinnerCompl (P y) (Quotient.mk (cauchySetoid D) X) := hweak
    _ = D.cinnerCompl (Quotient.mk (cauchySetoid D) X) (P y) := D.cinnerCompl_comm _ _
    _ = D.cinnerCompl (P (Quotient.mk (cauchySetoid D) X)) y := (hP _ _).symm

/-- A Cauchy sequence of fixed dense vectors has a fixed completion class. -/
theorem fixed_of_cauchy_terms
    (C : GNSCompletionSpace D → GNSCompletionSpace D)
    (hC : ∀ x y, D.cinnerCompl (C x) y = D.cinnerCompl x (C y))
    (X : CauchyGNS D)
    (hfix : ∀ n, C (embedV D (X.seq n)) = embedV D (X.seq n)) :
    C (Quotient.mk (cauchySetoid D) X) = Quotient.mk (cauchySetoid D) X :=
  fixed_of_cauchy_images C (fun x => x) hC (fun _ _ => rfl) X hfix

/-- The dense invariant-range identity extends to the whole existing
completion. Transposition and dense testing suffice; no new completed map
is constructed and idempotence is not assumed by this extension step. -/
theorem invariant_range_of_dense
    (C P : GNSCompletionSpace D → GNSCompletionSpace D)
    (hC : ∀ x y, D.cinnerCompl (C x) y = D.cinnerCompl x (C y))
    (hP : ∀ x y, D.cinnerCompl (P x) y = D.cinnerCompl x (P y))
    (hdense : ∀ p : D.V, C (P (C (embedV D p))) = P (C (embedV D p))) :
    ∀ x, C (P (C x)) = P (C x) := by
  have hleft (x y : GNSCompletionSpace D) :
      D.cinnerCompl (C (P (C x))) y = D.cinnerCompl x (C (P (C y))) :=
    (hC _ _).trans ((hP _ _).trans (hC _ _))
  have hright (x y : GNSCompletionSpace D) :
      D.cinnerCompl (P (C x)) y = D.cinnerCompl x (C (P y)) :=
    (hP _ _).trans (hC _ _)
  have hdual (y : GNSCompletionSpace D) : C (P (C y)) = C (P y) := by
    apply eq_of_dense_pairings
    intro p
    calc
      D.cinnerCompl (C (P (C y))) (embedV D p) =
          D.cinnerCompl (embedV D p) (C (P (C y))) := D.cinnerCompl_comm _ _
      _ = D.cinnerCompl (C (P (C (embedV D p)))) y := (hleft _ _).symm
      _ = D.cinnerCompl (P (C (embedV D p))) y :=
        congrArg (fun z => D.cinnerCompl z y) (hdense p)
      _ = D.cinnerCompl (embedV D p) (C (P y)) := hright _ _
      _ = D.cinnerCompl (C (P y)) (embedV D p) := D.cinnerCompl_comm _ _
  intro x
  apply eq_of_pairings_equal
  intro y
  exact (hleft x y).trans
    ((congrArg (fun z => D.cinnerCompl x z) (hdual y)).trans (hright x y).symm)

end YMGap.Continuum.GNSDenseFixedPoint

#print axioms YMGap.Continuum.GNSDenseFixedPoint.fixed_of_cauchy_images
#print axioms YMGap.Continuum.GNSDenseFixedPoint.fixed_of_cauchy_terms
#print axioms YMGap.Continuum.GNSDenseFixedPoint.invariant_range_of_dense
