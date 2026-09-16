/-
# Actual completed physical time and the SAME reflected inner form

The physical advance acts pointwise on the existing explicit-modulus
Cauchy representatives. The proved intrinsic time-sum identity passes
through their actual pairing limits and descends to the same quotient.
Likewise the original reflected diagonal contraction passes through the
limits. Even-time positivity is the diagonal identity at half the advance.

The embedded correlator is pinned to the original intrinsic pairing of
the literal advanced spatial-probe presentation. No completed vector laws,
one-step positivity, strict gap, cutoff removal or continuum limit are
assumed or supplied here. Nome, width and retained heat stage are fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (seminorm PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

/-- The existing representative limits retain the literal sum-of-times law.
The Cauchy index and both physical advances are independent parameters. -/
theorem representativeInner_time_sum (r s : Nat) (X Y : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 width stage
        ((timeNonexpansive hw0 hw1 width stage r).mapCauchy X)
        ((timeNonexpansive hw0 hw1 width stage s).mapCauchy Y))
      (representativeInner hw0 hw1 width stage X
        ((timeNonexpansive hw0 hw1 width stage (r+s)).mapCauchy Y)) := by
  have hleft := pairSequence_converges hw0 hw1 width stage
    ((timeNonexpansive hw0 hw1 width stage r).mapCauchy X)
    ((timeNonexpansive hw0 hw1 width stage s).mapCauchy Y)
  have hright := pairSequence_converges hw0 hw1 width stage X
    ((timeNonexpansive hw0 hw1 width stage (r+s)).mapCauchy Y)
  apply Equiv_of_limit_of_equal (hA := hleft) (hB := hright)
  intro k
  exact pairing_time_sum hw0 hw1 width r s (X.seq k).val (Y.seq k).val
    (X.seq k).property (Y.seq k).property stage

/-- Exact time balance on arbitrary vectors of the SAME Cauchy completion. -/
theorem completedInner_time_sum (r s : Nat)
    (x y : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage
        (completedTime hw0 hw1 width stage r x) (completedTime hw0 hw1 width stage s y) =
      completedInner hw0 hw1 width stage x (completedTime hw0 hw1 width stage (r+s) y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (representativeInner_time_sum hw0 hw1 width stage r s X Y)

/-- Every natural physical advance is symmetric for the completed pairing.
This is a pairing identity, not a claim of a completed Hilbert-space package. -/
theorem completedInner_time_balance (n : Nat)
    (x y : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage (completedTime hw0 hw1 width stage n x) y =
      completedInner hw0 hw1 width stage x (completedTime hw0 hw1 width stage n y) := by
  simpa only [completedTime_zero, Nat.add_zero] using
    completedInner_time_sum hw0 hw1 width stage n 0 x y

/-- Actual intrinsic contraction survives the representative scalar limit. -/
theorem representativeInner_time_contraction (n : Nat) (X : (D).Cauchy) :
    leEv
      (representativeInner hw0 hw1 width stage
        ((timeNonexpansive hw0 hw1 width stage n).mapCauchy X)
        ((timeNonexpansive hw0 hw1 width stage n).mapCauchy X))
      (representativeInner hw0 hw1 width stage X X) := by
  have hleft := pairSequence_converges hw0 hw1 width stage
    ((timeNonexpansive hw0 hw1 width stage n).mapCauchy X)
    ((timeNonexpansive hw0 hw1 width stage n).mapCauchy X)
  have hright := pairSequence_converges hw0 hw1 width stage X X
  apply leEv_of_convergesTo_le hleft hright
  intro k
  exact pairing_advance_contraction hw0 hw1 width n (X.seq k).val (X.seq k).property stage

/-- Constant-one reflected diagonal contraction on EVERY completed vector. -/
theorem completedInner_time_contraction (n : Nat) (x : Completion hw0 hw1 width stage) :
    RCle (completedInner hw0 hw1 width stage
        (completedTime hw0 hw1 width stage n x) (completedTime hw0 hw1 width stage n x))
      (completedInner hw0 hw1 width stage x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representativeInner_time_contraction hw0 hw1 width stage n X

/-- The even-time mixed form is exactly a reflected diagonal at half time. -/
theorem completedInner_even_diagonal (n : Nat) (x : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage x (completedTime hw0 hw1 width stage (2*n) x) =
      completedInner hw0 hw1 width stage
        (completedTime hw0 hw1 width stage n x) (completedTime hw0 hw1 width stage n x) := by
  simpa only [Nat.two_mul] using
    (completedInner_time_sum hw0 hw1 width stage n n x x).symm

/-- Site-reflection positivity gives the even subsemigroup, not one-step positivity. -/
theorem completedInner_even_nonnegative (n : Nat) (x : Completion hw0 hw1 width stage) :
    RCnonneg (completedInner hw0 hw1 width stage x (completedTime hw0 hw1 width stage (2*n) x)) := by
  rw [completedInner_even_diagonal]
  exact completedInner_nonnegative hw0 hw1 width stage (completedTime hw0 hw1 width stage n x)

theorem completedInner_even_le_identity (n : Nat) (x : Completion hw0 hw1 width stage) :
    RCle (completedInner hw0 hw1 width stage x (completedTime hw0 hw1 width stage (2*n) x))
      (completedInner hw0 hw1 width stage x x) := by
  rw [completedInner_even_diagonal]
  exact completedInner_time_contraction hw0 hw1 width stage n x

/-- Dense physical correlators retain the exact original intrinsic pairing
and the literal distance advance, with no change of action or normalization. -/
theorem completedTime_correlator (n : Nat) (x y : PhysicalSpan width) :
    completedInner hw0 hw1 width stage (embedSpan hw0 hw1 width stage x)
        (completedTime hw0 hw1 width stage n (embedSpan hw0 hw1 width stage y)) =
      Quotient.mk crealSetoid (pairing hw0 hw1 width x.val (advanceSpan n y.val) stage) := by
  rw [completedTime_embedSpan, completedInner_embedSpan]
  rfl

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.representativeInner_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedInner_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedInner_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.representativeInner_time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedInner_time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedInner_even_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedInner_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedInner_even_le_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm.completedTime_correlator
