/-
# Shifted constructive Jacobi uniqueness

Physical ordered-Racah channels need not begin at contraction order zero.
This module reindexes the division-free Jacobi recurrence on an arbitrary
admissible interval `lo .. lo+N`.  The lower endpoint supplies the vanished
predecessor product, and adjacent proof-carrying channels supply every
positive pivot.  Propagation then uses only cross-multiplication and positive
left cancellation.
-/

import YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahnOuterClosure
import YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer

namespace YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer
open YMGap.Continuum.SU2RacahThreeTermUniqueness

local infix:50 " ≈ " => Q'.eqv

def shiftedSequence (lo : Nat) (x : Nat → Q') (n : Nat) : Q' :=
  x (lo + n)

def shiftedForwardA (a b c d lo : Nat) (n : Nat) : Q' :=
  forwardA a b c d (lo + n)

def shiftedForwardB (a b c d e lo : Nat) (n : Nat) : Q' :=
  forwardB a b c d e (lo + n)

def shiftedForwardC (a b c d lo : Nat) (n : Nat) : Q' :=
  forwardC a b c d (lo + n)

/-- A Jacobi solution on an absolute interval becomes the exact finite
forward recurrence on offsets.  The endpoint hypothesis is already
cross-multiplied, so no inverse coefficient is introduced. -/
theorem jacobiSolutionOnInterval_to_shiftedForwardThrough
    (N lo a b c d e : Nat) (x : Nat → Q')
    (hx : ∀ p, lo ≤ p → p ≤ lo + N → JacobiSolutionAt a b c d e x p)
    (hlower : forwardC a b c d lo * x (lo - 1) ≈ 0) :
    SatisfiesForwardThreeTermThrough N
      (shiftedForwardA a b c d lo)
      (shiftedForwardB a b c d e lo)
      (shiftedForwardC a b c d lo)
      (shiftedSequence lo x) := by
  constructor
  · intro hN
    have h := (jacobiSolutionAt_iff_forward_step
      a b c d e x lo).1 (hx lo (by omega) (by omega))
    refine Q'.eqv_trans _
      (forwardB a b c d e lo * x lo +
        forwardC a b c d lo * x (lo - 1)) _ ?_ ?_
    · simpa only [shiftedForwardA, shiftedForwardB, shiftedSequence,
        Nat.add_zero, show lo + 1 = lo + 1 by rfl] using h
    · refine Q'.eqv_trans _
        (forwardB a b c d e lo * x lo + 0) _
        (Q'.add_eqv_congr_left _ _ _ hlower) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)
  · intro n hn
    have h := (jacobiSolutionAt_iff_forward_step
      a b c d e x (lo + (n + 1))).1
        (hx (lo + (n + 1)) (by omega) (by omega))
    simpa only [shiftedForwardA, shiftedForwardB, shiftedForwardC,
      shiftedSequence, Nat.add_assoc] using h

/-- Denominator-free uniqueness on an arbitrary finite interval. -/
theorem shifted_jacobi_coefficient_unique
    (N lo a b c d e : Nat) (x y : Nat → Q')
    (hA : ∀ n, n < N → (0 : Q') < forwardA a b c d (lo + n))
    (hx : ∀ p, lo ≤ p → p ≤ lo + N → JacobiSolutionAt a b c d e x p)
    (hy : ∀ p, lo ≤ p → p ≤ lo + N → JacobiSolutionAt a b c d e y p)
    (hxLower : forwardC a b c d lo * x (lo - 1) ≈ 0)
    (hyLower : forwardC a b c d lo * y (lo - 1) ≈ 0)
    (hbase : x lo ≈ y lo) :
    ∀ n, n ≤ N → x (lo + n) ≈ y (lo + n) := by
  have hx' := jacobiSolutionOnInterval_to_shiftedForwardThrough
    N lo a b c d e x hx hxLower
  have hy' := jacobiSolutionOnInterval_to_shiftedForwardThrough
    N lo a b c d e y hy hyLower
  have h := forwardThreeTermThrough_unique N
    (shiftedForwardA a b c d lo)
    (shiftedForwardB a b c d e lo)
    (shiftedForwardC a b c d lo)
    (shiftedSequence lo x) (shiftedSequence lo y)
    (by simpa only [shiftedForwardA] using hA) hx' hy'
    (by simpa only [shiftedSequence, Nat.add_zero] using hbase)
  intro n hn
  simpa only [shiftedSequence] using h n hn

/-- Proof-carrying adjacent channels discharge every shifted pivot, leaving
only the two recurrence certificates and one lower endpoint value. -/
theorem finite_shifted_jacobi_coefficient_unique
    (N lo a b c d e : Nat)
    (channel : Nat → FixedRightCGChannel a b c d)
    (hchannelP : ∀ n, n ≤ N → (channel n).p = lo + n)
    (x y : Nat → Q')
    (hx : ∀ p, lo ≤ p → p ≤ lo + N → JacobiSolutionAt a b c d e x p)
    (hy : ∀ p, lo ≤ p → p ≤ lo + N → JacobiSolutionAt a b c d e y p)
    (hxLower : forwardC a b c d lo * x (lo - 1) ≈ 0)
    (hyLower : forwardC a b c d lo * y (lo - 1) ≈ 0)
    (hbase : x lo ≈ y lo) :
    ∀ n, n ≤ N → x (lo + n) ≈ y (lo + n) := by
  apply shifted_jacobi_coefficient_unique
    N lo a b c d e x y ?_ hx hy hxLower hyLower hbase
  intro n hn
  have hadj : (channel (n + 1)).p = (channel n).p + 1 := by
    rw [hchannelP (n + 1) (by omega), hchannelP n (by omega)]
    omega
  simpa only [forwardA, hchannelP n (by omega)] using
    jacobiForward_pos_of_adjacent_channels
      (channel n) (channel (n + 1)) hadj

end YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness

#print axioms YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness.jacobiSolutionOnInterval_to_shiftedForwardThrough
#print axioms YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness.shifted_jacobi_coefficient_unique
#print axioms YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness.finite_shifted_jacobi_coefficient_unique
