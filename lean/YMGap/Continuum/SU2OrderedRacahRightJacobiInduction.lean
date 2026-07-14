/-
# Denominator-free right Jacobi induction

Peeling one positive inner contraction reduces `(b,c,p)` to
`(b-1,c-1,p-1)`.  The peeled first-pair action supplies the reduced
tridiagonal row, while the Omega correction supplies exactly
`original - reduced` in all three carrier slots.  Their sum is therefore the
original transpose-Jacobi action.  This is the constructive induction
invariant behind recurrence propagation.
-/

import YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahRightJacobiInduction

set_option maxHeartbeats 2400000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeCorrectionIdentification
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def recombineLHS : PolyExpr :=
  .add
    (.add (.add (.mul (.var 0) (.var 6)) (.mul (.var 1) (.var 7)))
      (.mul (.var 2) (.var 8)))
    (.add
      (.add
        (.mul (.add (.var 3) (.neg (.var 0))) (.var 6))
        (.mul (.add (.var 4) (.neg (.var 1))) (.var 7)))
      (.mul (.add (.var 5) (.neg (.var 2))) (.var 8)))

private def recombineRHS : PolyExpr :=
  .add (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 7)))
    (.mul (.var 5) (.var 8))

private theorem recombine_normal :
    normalize recombineLHS = normalize recombineRHS := by
  decide

private theorem three_slot_difference_recombine
    (RL RD RU OL OD OU M C P : Q') :
    ((RL * M + RD * C + RU * P) +
        ((OL + -RL) * M + (OD + -RD) * C + (OU + -RU) * P)) ≈
      OL * M + OD * C + OU * P := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then RL else if r = 1 then RD else if r = 2 then RU else
    if r = 3 then OL else if r = 4 then OD else if r = 5 then OU else
    if r = 6 then M else if r = 7 then C else P
  have h := poly_identity_of_normal_eq recombineLHS recombineRHS
    recombine_normal ρ
  simpa [recombineLHS, recombineRHS, eval, ρ] using h

/-- Original transpose-Jacobi action on one right-channel monomial. -/
def RightTransposeJacobiAt {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Prop :=
  firstPairExchange3 a b
      (fun u v w => triRight a b c d q.intermediate
        (mono u) (mono v) (mono w) s) i j l ≈
    jacobiForward a b c d (q.p - 1) *
        triRight a b c d qm.intermediate
          (mono i) (mono j) (mono l) s +
      jacobiDiagonal a b c d q.p *
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s +
      jacobiBackward a b c d (q.p + 1) *
        triRight a b c d qp.intermediate
          (mono i) (mono j) (mono l) s

/-- Induction hypothesis after Omega lifting: the peeled action is already
expressed in the three original carrier slots with reduced coefficients. -/
def LiftedReducedRightTransposeJacobiAt {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Prop :=
  omegaLiftSplit b c
      (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s)) i j l ≈
    reducedLowerCoefficient a b c d q.p *
        triRight a b c d qm.intermediate
          (mono i) (mono j) (mono l) s +
      jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
        triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s +
      jacobiBackward a (b - 1) (c - 1) d q.p *
        triRight a b c d qp.intermediate
          (mono i) (mono j) (mono l) s

/-- Core denominator-free induction step: reduced row plus exact coefficient
differences equals the original row. -/
theorem rightTransposeJacobiAt_of_lifted_reduced_and_correction
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (i j l s : Nat) (hjb : j ≤ b)
    (hreduced : LiftedReducedRightTransposeJacobiAt qm q qp i j l s)
    (hcorrection : OmegaCorrectionThreeCarrierAt qm q qp i j l s) :
    RightTransposeJacobiAt qm q qp i j l s := by
  have hstep := triRight_firstPairExchange_induction_step
    q hp i j l s hjb
  unfold RightTransposeJacobiAt
  refine Q'.eqv_trans _
    (omegaLiftSplit b c
        (firstPairExchange3 a (b - 1) (peeledRightCoefficient q s)) i j l +
      triRightOmegaCorrection q i j l s) _ hstep ?_
  refine Q'.eqv_trans _
    ((reducedLowerCoefficient a b c d q.p *
          triRight a b c d qm.intermediate
            (mono i) (mono j) (mono l) s +
        jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1) *
          triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s +
        jacobiBackward a (b - 1) (c - 1) d q.p *
          triRight a b c d qp.intermediate
            (mono i) (mono j) (mono l) s) +
      (omegaCorrectionLowerCoefficient a b c d q.p *
          triRight a b c d qm.intermediate
            (mono i) (mono j) (mono l) s +
        omegaCorrectionDiagonalCoefficient a b c d q.p *
          triRight a b c d q.intermediate
            (mono i) (mono j) (mono l) s +
        omegaCorrectionUpperCoefficient a b c d q.p *
          triRight a b c d qp.intermediate
            (mono i) (mono j) (mono l) s)) _
    (Q'.add_eqv_congr' hreduced hcorrection) ?_
  simpa only [omegaCorrectionLowerCoefficient,
    omegaCorrectionDiagonalCoefficient, omegaCorrectionUpperCoefficient] using
      three_slot_difference_recombine
        (reducedLowerCoefficient a b c d q.p)
        (jacobiDiagonal a (b - 1) (c - 1) d (q.p - 1))
        (jacobiBackward a (b - 1) (c - 1) d q.p)
        (jacobiForward a b c d (q.p - 1))
        (jacobiDiagonal a b c d q.p)
        (jacobiBackward a b c d (q.p + 1))
        (triRight a b c d qm.intermediate
          (mono i) (mono j) (mono l) s)
        (triRight a b c d q.intermediate
          (mono i) (mono j) (mono l) s)
        (triRight a b c d qp.intermediate
          (mono i) (mono j) (mono l) s)

/-- The imported exact face rows discharge the correction premise throughout
the strict-inner admissible outer interval, so a lifted reduced row propagates
to the original row pointwise. -/
theorem rightTransposeJacobiAt_first_bulk_outer_closed
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1) (i j l s : Nat)
    (hi : 0 < i) (hj : 0 < j) (hl : 0 < l)
    (hshell : s + q.r + q.p = i + j + l)
    (hsum : j + l = q.p) (hpb : q.p < b) (hpc : q.p < c)
    (hri : q.r ≤ i) (hia : i ≤ a)
    (hreduced : LiftedReducedRightTransposeJacobiAt qm q qp i j l s) :
    RightTransposeJacobiAt qm q qp i j l s := by
  apply rightTransposeJacobiAt_of_lifted_reduced_and_correction
    qm q qp hp i j l s (by omega) hreduced
  exact omegaCorrectionThreeCarrierAt_first_bulk_outer_closed_on_shell
    qm q qp hp hprev hnext i j l s hi hj hl hshell hsum hpb hpc hri hia

end YMGap.Continuum.SU2OrderedRacahRightJacobiInduction

#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiInduction.rightTransposeJacobiAt_of_lifted_reduced_and_correction
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiInduction.rightTransposeJacobiAt_first_bulk_outer_closed
