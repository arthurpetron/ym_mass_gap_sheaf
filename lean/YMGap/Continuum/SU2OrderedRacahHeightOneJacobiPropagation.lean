/-
# Strict-bulk height-one Jacobi propagation

The normalized height-one correction is the missing correction premise in
the denominator-free right-Jacobi induction step.  Combining it with either
an already lifted reduced row or the existing coordinate-family lift yields
the original-label transpose-Jacobi row.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation
import YMGap.Continuum.SU2OrderedRacahRightJacobiLift

namespace YMGap.Continuum.SU2OrderedRacahHeightOneJacobiPropagation

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction
open YMGap.Continuum.SU2OrderedRacahRightJacobiLift
open YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation

/-- A lifted lower-height Jacobi row propagates across the strict height-one
bulk.  The normalized shell theorem supplies the complete correction term. -/
theorem rightTransposeJacobiAt_height_one_strict_bulk
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hshell : s + q.r + q.p = i + j + l)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate)
    (hreduced : LiftedReducedRightTransposeJacobiAt qm q qp i j l s) :
    RightTransposeJacobiAt qm q qp i j l s := by
  apply rightTransposeJacobiAt_of_lifted_reduced_and_correction
    qm q qp hp i j l s (by omega) hreduced
  exact omegaCorrectionThreeCarrierAt_height_one_strict_bulk_on_shell
    qm q qp hp hprev hnext i j l s hshell hj hl hheight hpb hpc
      hr hri hia hrn

/-- Reusable height-induction step.  A coordinate family of Jacobi rows for
the three peeled channels lifts and propagates to the original strict
height-one row. -/
theorem rightTransposeJacobiAt_height_one_strict_bulk_of_reduced_family
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l s : Nat) (hshell : s + q.r + q.p = i + j + l)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 4 ≤ q.r) (hri : q.r + 1 ≤ i)
    (hia : i + 1 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate)
    (hreduced : ∀ u v w,
      RightTransposeJacobiAt
        (reducePositiveInnerRightChannel qm (by omega))
        (reducePositiveInnerRightChannel q hp)
        (reducePositiveInnerRightChannel qp (by omega)) u v w s) :
    RightTransposeJacobiAt qm q qp i j l s := by
  have hm : 0 < qm.p := by omega
  have hpp : 0 < qp.p := by omega
  have hlift := liftedReducedRightTransposeJacobiAt_of_reduced_family
    qm q qp hm hp hpp (by omega) i j l s (by
      intro u v w
      simpa only using hreduced u v w)
  exact rightTransposeJacobiAt_height_one_strict_bulk
    qm q qp hp hprev hnext i j l s hshell hj hl hheight hpb hpc
      hr hri hia hrn hlift

end YMGap.Continuum.SU2OrderedRacahHeightOneJacobiPropagation

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneJacobiPropagation.rightTransposeJacobiAt_height_one_strict_bulk
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneJacobiPropagation.rightTransposeJacobiAt_height_one_strict_bulk_of_reduced_family
