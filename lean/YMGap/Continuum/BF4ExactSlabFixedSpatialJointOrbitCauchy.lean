/-
# Supplied representatives for the even Neumann orbit

This file keeps the finite Neumann approximants on the original fixed-nome,
fixed-spatial joint completion.  The representatives are built recursively
from the supplied representative of the source; no representative is chosen
from a quotient.

The final section records the sharp cross-term estimate needed by the finite
double-sum Cauchy argument.  In particular it retains the signed finite sum:
no orthogonality of distinct time translates is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "A" => completedAdd hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

/-- A representative of every finite even-orbit sum, computed from the
supplied representative of the source. -/
def evenOrbitRep (X : (D).Cauchy) : Nat → (D).Cauchy
  | 0 => (D).constant (zero width)
  | n+1 => (addition hw0 hw1 width).mapCauchy (evenOrbitRep X n)
      ((jointTimeNonexpansive hw0 hw1 width (2*n)).mapCauchy X)

/-- The computed representative presents the pre-existing quotient-level
even orbit sum. -/
theorem mk_evenOrbitRep (X : (D).Cauchy) : ∀ n : Nat,
    Quotient.mk (D).completionSetoid (evenOrbitRep hw0 hw1 width X n) =
      evenOrbitSum hw0 hw1 width (Quotient.mk (D).completionSetoid X) n
  | 0 => rfl
  | n+1 => by
      change A (Quotient.mk (D).completionSetoid (evenOrbitRep hw0 hw1 width X n))
        (T (2*n) (Quotient.mk (D).completionSetoid X)) =
          A (evenOrbitSum hw0 hw1 width (Quotient.mk (D).completionSetoid X) n)
            (T (2*n) (Quotient.mk (D).completionSetoid X))
      rw [mk_evenOrbitRep X n]

/-- Every same-source cross term in an even tail has its full geometric
weight.  This is the termwise input for the finite double-sum estimate; it
does not discard cross terms. -/
theorem even_cross_term_le (x : V) (hx : B x U = RCzero) (i j : Nat) :
    RCle (B (T (2*i) x) (T (2*j) x))
      (RCscale (q^(i+j)) (B x x)) := by
  rw [completedInner_time_sum]
  have he : 2*i + 2*j = 2*(i+j) := by omega
  rw [he, ← completedInner_even_diagonal]
  exact time_norm_decay hw0 hw1 width x hx (i+j)

/-- Diagonal specialization of the retained cross-term estimate. -/
theorem even_translate_norm_le (x : V) (hx : B x U = RCzero) (n : Nat) :
    RCle (B (T (2*n) x) (T (2*n) x))
      (RCscale (q^(2*n)) (B x x)) :=
  time_norm_decay hw0 hw1 width x hx (2*n)

/-- The literal finite tail, with no rearrangement into an unsigned norm
estimate. -/
def evenOrbitTail (x : V) (start : Nat) : Nat → V
  | 0 => completedZero hw0 hw1 width
  | n+1 => A (evenOrbitTail x start n) (T (2*(start+n)) x)

theorem evenOrbitSum_add_tail (x : V) (start : Nat) : ∀ count : Nat,
    A (evenOrbitSum hw0 hw1 width x start)
        (evenOrbitTail hw0 hw1 width x start count) =
      evenOrbitSum hw0 hw1 width x (start+count)
  | 0 => by rw [evenOrbitTail, completedAdd_zero, Nat.add_zero]
  | count+1 => by
      rw [evenOrbitTail, ← completedAdd_assoc, evenOrbitSum_add_tail x start count,
        Nat.add_succ, evenOrbitSum]

private theorem completed_sub_add_left (a b : V) :
    completedSub hw0 hw1 width (A a b) a = b := by
  calc
    completedSub hw0 hw1 width (A a b) a =
        A (A a b) (completedNeg hw0 hw1 width a) := rfl
    _ = A b (A a (completedNeg hw0 hw1 width a)) := by
      rw [completedAdd_comm hw0 hw1 width a b, completedAdd_assoc]
    _ = A b (A (completedNeg hw0 hw1 width a) a) := by
      rw [completedAdd_comm hw0 hw1 width a (completedNeg hw0 hw1 width a)]
    _ = b := by rw [completedNeg_add, completedAdd_zero]

/-- Difference of two ordered approximants is exactly the retained finite
tail.  This is the algebraic seam at which the remaining double-sum estimate
applies. -/
theorem evenOrbitSum_sub_eq_tail (x : V) (start count : Nat) :
    completedSub hw0 hw1 width
        (evenOrbitSum hw0 hw1 width x (start+count))
        (evenOrbitSum hw0 hw1 width x start) =
      evenOrbitTail hw0 hw1 width x start count := by
  rw [← evenOrbitSum_add_tail]
  exact completed_sub_add_left hw0 hw1 width _ _

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy.evenOrbitRep
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy.mk_evenOrbitRep
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy.even_cross_term_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy.even_translate_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy.evenOrbitSum_add_tail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy.evenOrbitSum_sub_eq_tail

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy
