/-
# Full outer-interval closure for the guarded Hahn correction

The strict-inner first-bulk calculation is now closed on every admissible
outer coordinate.  The proof is a constructive partition of `r ≤ i` and
`r ≤ f`: the lower coordinate face `i=r`, the upper outer face `r=f`,
and the remaining lower-closed face `r<f`.  No division or choice is used.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnInnerBoundary

namespace YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnBoundary
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnUpperBoundary
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnCoordinateBoundary

/-- The three exact boundary mechanisms exhaust the admissible outer shell. -/
theorem omegaCorrectionShellAt_first_bulk_outer_closed
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hri : q.r ≤ i) (hia : i ≤ a) :
    OmegaCorrectionShellAt qm q qp hp i j l := by
  have hrf : q.r ≤ q.intermediate := (Nat.le_min.mp q.r_le).2
  rcases Nat.lt_or_eq_of_le hri with hri' | hir
  · rcases Nat.lt_or_eq_of_le hrf with hrf' | hrfEq
    · exact omegaCorrectionShellAt_first_bulk_lower_closed
        qm q qp hp hprev hnext i j l hj hl hsum hpb hpc hrf' hri' hia
    · have hr : 0 < q.r := by
        unfold FixedRightCGChannel.intermediate at hrfEq
        omega
      exact omegaCorrectionShellAt_first_bulk_upper_boundary
        qm q qp hp hprev hnext i j l hj hl hsum hpb hpc
          hr hrfEq hri' hia
  · have hr : 0 < q.r := by omega
    exact omegaCorrectionShellAt_first_bulk_lower_coordinate
      qm q qp hp hprev hnext i j l hj hl hsum hpb hpc
        hr (by omega) hia

/-- Guarded factorial correction over the full admissible outer interval. -/
theorem omegaCorrectionFactorialAt_first_bulk_outer_closed_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hri : q.r ≤ i) (hia : i ≤ a) :
    OmegaCorrectionFactorialAt qm q qp hp i j l s := by
  apply (omegaCorrectionFactorialAt_on_shell_iff_shell
    qm q qp hp hprev hnext i j l s hi hj hl hshell).2
  exact omegaCorrectionShellAt_first_bulk_outer_closed
    qm q qp hp hprev hnext i j l hi hj hl hsum hpb hpc hri hia

/-- Raw three-carrier correction over the full admissible outer interval. -/
theorem omegaCorrectionThreeCarrierAt_first_bulk_outer_closed_on_shell
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hri : q.r ≤ i) (hia : i ≤ a) :
    OmegaCorrectionThreeCarrierAt qm q qp i j l s :=
  (omegaCorrectionThreeCarrierAt_iff_factorial qm q qp hp i j l s).2
    (omegaCorrectionFactorialAt_first_bulk_outer_closed_on_shell
      qm q qp hp hprev hnext i j l s hi hj hl hshell hsum hpb hpc
        hri hia)

end YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure.omegaCorrectionShellAt_first_bulk_outer_closed
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure.omegaCorrectionFactorialAt_first_bulk_outer_closed_on_shell
#print axioms YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure.omegaCorrectionThreeCarrierAt_first_bulk_outer_closed_on_shell
