/-
# A constructive inverse of I-T_2 on the ORIGINAL unit complement

The same geometric partial sums have explicit Cauchy rows. Their existing
diagonal limit is independent of the supplied representative and therefore
defines an operator on ALL classes of the original completion. Quantitative
approximation, centering and the inverse equation are proved on that carrier.
Uniqueness uses the already-proved positive-time fixed-space theorem.

No arbitrary sequence of quotient representatives is selected. Thus this
construction does not assume or claim full quotient-level completeness.
It supplies a fixed-spacing transfer resolvent, not a continuum Hamiltonian,
full observable realization, positive excited transfer response, or Clay
closure. The coupling remains the existing SU(2) nome 1/1024.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial

namespace YMGap.Continuum.BF4ExactSlabThermodynamicResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

local notation "D" => seminorm

private theorem rc_sub_add_common (a b c : RC) :
    RCsub (RCadd a b) (RCadd a c) = RCsub b c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 0) (.var 2))))
      (.add (.var 1) (.neg (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

theorem sub_add_common (a b c : Completion) :
    completedSub (completedAdd a b) (completedAdd a c) = completedSub b c := by
  apply completed_eq_of_pairings
  intro z
  rw [completedInner_sub_left, completedInner_add_left, completedInner_add_left,
    completedInner_sub_left, rc_sub_add_common]

theorem dist_add_common (a b c : Completion) :
    completedDist (completedAdd a b) (completedAdd a c) = completedDist b c := by
  unfold completedDist
  rw [sub_add_common]

/-- The limit representative retains the actual series and both layers of moduli. -/
def resolventRepresentative (X : (D).Cauchy) : (D).Cauchy := diagonalCauchy (seriesRows X)

theorem resolventRepresentative_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (resolventRepresentative X) =
      Quotient.mk (D).completionSetoid (resolventRepresentative Y) := by
  apply rowLimit_independent
  intro n
  rw [seriesRows_point, seriesRows_point, h]

/-- The reduced resolvent: R x = sum_{j>=0} T_{2j}(center x). -/
def resolvent : Completion → Completion :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (resolventRepresentative X))
    (fun X Y h => resolventRepresentative_congr X Y (Quotient.sound h))

theorem resolvent_mk (X : (D).Cauchy) :
    resolvent (Quotient.mk (D).completionSetoid X) = rowLimit (seriesRows X) := rfl

def resolventModulus (X : (D).Cauchy) : Q' → Nat := rowLimitRate (seriesRows X)

theorem partial_resolvent_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : resolventModulus X epsilon ≤ n) :
    RCle (completedDist (partialSum (Quotient.mk (D).completionSetoid X) n)
      (resolvent (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  rw [resolvent_mk, ← seriesRows_point]
  exact rowLimit_bound (seriesRows X) epsilon he n hn

theorem resolvent_centered (x : Completion) : center (resolvent x) = resolvent x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completed_eq_of_small
  intro epsilon he
  let n := resolventModulus X (quarter epsilon)
  have h := partial_resolvent_bound X (quarter epsilon) (quarter_pos he) n (Nat.le_refl _)
  have hc := center_nonexpansive (resolvent (Quotient.mk (D).completionSetoid X))
    (partialSum (Quotient.mk (D).completionSetoid X) n)
  rw [partial_centered, completedDist_symm (resolvent (Quotient.mk (D).completionSetoid X))] at hc
  exact completedDist_two_segment _ _ _ epsilon (RCle_trans hc h) h

/-- Summation solves the exact discrete Poisson equation for the SAME T_2. -/
theorem resolvent_equation (x : Completion) :
    resolvent x = completedAdd (center x) (twoStepTransfer (resolvent x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completed_eq_of_small
  intro epsilon he
  let n := resolventModulus X (quarter epsilon)
  have hn := partial_resolvent_bound X (quarter epsilon) (quarter_pos he) n (Nat.le_refl _)
  have hs := partial_resolvent_bound X (quarter epsilon) (quarter_pos he) (n+1) (Nat.le_succ _)
  rw [completedDist_symm] at hs
  have ht := completedTime_distance_contraction 2
    (partialSum (Quotient.mk (D).completionSetoid X) n) (resolvent (Quotient.mk (D).completionSetoid X))
  have hh : RCle
      (completedDist (partialSum (Quotient.mk (D).completionSetoid X) (n+1))
        (completedAdd (center (Quotient.mk (D).completionSetoid X))
          (twoStepTransfer (resolvent (Quotient.mk (D).completionSetoid X)))))
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) := by
    change RCle (completedDist (completedAdd _ _) (completedAdd _ _)) _
    rw [dist_add_common]
    exact RCle_trans ht hn
  exact completedDist_two_segment _ _ _ epsilon hs hh

/-- Uniqueness is on the whole current complement, not a chosen dense subtype. -/
theorem solution_unique (x y z : Completion)
    (hy : center y = y) (hz : center z = z)
    (hey : y = completedAdd (center x) (twoStepTransfer y))
    (hez : z = completedAdd (center x) (twoStepTransfer z)) : y = z := by
  have hdiff : completedSub y z = completedSub (twoStepTransfer y) (twoStepTransfer z) := by
    calc
      completedSub y z = completedSub (completedAdd (center x) (twoStepTransfer y))
          (completedAdd (center x) (twoStepTransfer z)) :=
        (congrArg (fun a => completedSub a z) hey).trans
          (congrArg (completedSub (completedAdd (center x) (twoStepTransfer y))) hez)
      _ = _ := sub_add_common _ _ _
  have hfixed : completedTime 2 (completedSub y z) = completedSub y z := by
    rw [completedTime_sub]
    exact hdiff.symm
  have hc := fixed_center_zero 2 (by decide) (completedSub y z) hfixed
  rw [center_sub, hy, hz] at hc
  have h := congrArg (fun a => completedAdd a z) hc
  change completedAdd (completedSub y z) z = completedAdd completedZero z at h
  rw [completedSub_add_cancel, completedZero_add] at h
  exact h

def defect (x : Completion) : Completion := completedSub x (twoStepTransfer x)

theorem resolvent_right_inverse (x : Completion) : defect (resolvent x) = center x := by
  unfold defect
  calc
    completedSub (resolvent x) (twoStepTransfer (resolvent x)) =
        completedSub (completedAdd (center x) (twoStepTransfer (resolvent x)))
          (twoStepTransfer (resolvent x)) :=
      congrArg (fun a => completedSub a (twoStepTransfer (resolvent x))) (resolvent_equation x)
    _ = center x := sub_add_right_cancel _ _

theorem center_defect (x : Completion) : center (defect x) = defect (center x) := by
  unfold defect twoStepTransfer
  rw [center_sub, ← completedTime_center]

theorem resolvent_left_inverse (x : Completion) : resolvent (defect x) = center x := by
  apply solution_unique (defect x) _ _ (resolvent_centered _) (center_idempotent x)
    (resolvent_equation _)
  rw [center_defect]
  exact (completedSub_add_cancel (center x) (twoStepTransfer (center x))).symm

/-- A witnessing solver and its convergence modulus, not a bare existence claim. -/
def solutionCertificate (X : (D).Cauchy) :
    Σ' y : UnitComplement,
      (defect y.val = center (Quotient.mk (D).completionSetoid X)) ×'
      {M : Q' → Nat // ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, M epsilon ≤ n →
        RCle (completedDist (partialSum (Quotient.mk (D).completionSetoid X) n) y.val)
          (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨⟨resolvent (Quotient.mk (D).completionSetoid X), (center_fixed_iff _).mp (resolvent_centered _)⟩,
    resolvent_right_inverse (Quotient.mk (D).completionSetoid X),
    ⟨resolventModulus X, partial_resolvent_bound X⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicResolvent

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.sub_add_common
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.dist_add_common
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolventRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolventRepresentative_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolvent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolvent_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolventModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.partial_resolvent_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolvent_centered
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolvent_equation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.solution_unique
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolvent_right_inverse
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.center_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.resolvent_left_inverse
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolvent.solutionCertificate
