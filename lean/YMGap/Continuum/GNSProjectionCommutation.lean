/-
# Commutation from invariant range in a constructive GNS completion

This is a conditional Hilbert-space identity: two self-adjoint maps commute
when the first preserves the fixed range of the second in the explicit form
`Q (P (Q x)) = P (Q x)`. The argument uses only completed-pairing
nondegeneracy. Neither linearity nor idempotence is needed once that identity
is supplied. Establishing it for physical conditional projections is separate;
this module proves no decay or spectral-gap estimate.
-/

import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.GNSProjectionCommutation

set_option autoImplicit false

open YMGap.Continuum.GNSQuotient

/-- Adjointness transfers `Q P Q = P Q` to `Q P Q = Q P`. -/
theorem commute_of_invariant (D : GNSData)
    (P Q : GNSCompletionSpace D → GNSCompletionSpace D)
    (hP : ∀ x y, D.cinnerCompl (P x) y = D.cinnerCompl x (P y))
    (hQ : ∀ x y, D.cinnerCompl (Q x) y = D.cinnerCompl x (Q y))
    (hinv : ∀ x, Q (P (Q x)) = P (Q x))
    (x : GNSCompletionSpace D) : P (Q x) = Q (P x) := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro y
  calc
    D.cinnerCompl (P (Q x)) y = D.cinnerCompl (Q (P (Q x))) y :=
      congrArg (fun v => D.cinnerCompl v y) (hinv x).symm
    _ = D.cinnerCompl (P (Q x)) (Q y) := hQ _ _
    _ = D.cinnerCompl (Q x) (P (Q y)) := hP _ _
    _ = D.cinnerCompl x (Q (P (Q y))) := hQ _ _
    _ = D.cinnerCompl x (P (Q y)) := congrArg (D.cinnerCompl x) (hinv y)
    _ = D.cinnerCompl (P x) (Q y) := (hP _ _).symm
    _ = D.cinnerCompl (Q (P x)) y := (hQ _ _).symm

#print axioms commute_of_invariant

end YMGap.Continuum.GNSProjectionCommutation
