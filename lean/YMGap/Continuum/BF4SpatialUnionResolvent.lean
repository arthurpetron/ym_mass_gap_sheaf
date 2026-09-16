/-
# Constructive reduced inverse for the SAME spatial-union transfer

The computed geometric partial sums converge through supplied Cauchy rows.
Their diagonal limit is independent of the original representative and
defines R on every class of the existing UnionCompletion. It is centered
and solves (I-T_2)R x = center x = R(I-T_2)x. Uniqueness uses the actual
strict unit-complement bound, not a spectral decomposition or a new premise.

The solver returns a vector and convergence modulus as data. No arbitrary
quotient-sequence representatives are selected, and no full Hilbert/OS,
continuous-time generator, continuum or physical mass result is asserted.
-/

import YMGap.Continuum.BF4SpatialUnionResolventPartial

namespace YMGap.Continuum.BF4SpatialUnionResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4SpatialUnionCompletedDistance
open YMGap.Continuum.BF4SpatialUnionCauchyRows
open YMGap.Continuum.BF4SpatialUnionResolventPartial
open YMGap.Continuum.CRealSeminormCauchyRows
open YMGap.Continuum.CRealSeminormCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem rc_sub_add_common (a b c : RC) :
    RCsub (RCadd a b) (RCadd a c) = RCsub b c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 0) (.var 2))))
      (.add (.var 1) (.neg (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "DP" => distanceData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "Sub" => completedSub hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs

theorem sub_add_common (a b c : V) : Sub (A a b) (A a c) = Sub b c := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [completedInner_sub_left, completedInner_add_left, completedInner_add_left,
    completedInner_sub_left, rc_sub_add_common]

theorem dist_add_common (a b c : V) :
    completedDist hw0 hw1 hsmall hd hs (A a b) (A a c) =
      completedDist hw0 hw1 hsmall hd hs b c := by
  unfold completedDist
  rw [sub_add_common]

def resolventRepresentative (X : (D).Cauchy) : (D).Cauchy :=
  diagonalCauchy DP (seriesRows hw0 hw1 hsmall hd hs X)

theorem resolventRepresentative_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (resolventRepresentative hw0 hw1 hsmall hd hs X) =
      Quotient.mk (D).completionSetoid (resolventRepresentative hw0 hw1 hsmall hd hs Y) := by
  apply rowLimit_independent DP
  intro n
  rw [seriesRows_point, seriesRows_point, h]

/-- R x = sum over j>=0 of the original T_(2j)(center x). -/
def resolvent : V → V :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid
    (resolventRepresentative hw0 hw1 hsmall hd hs X))
    (fun X Y h => resolventRepresentative_congr hw0 hw1 hsmall hd hs X Y (Quotient.sound h))

theorem resolvent_mk (X : (D).Cauchy) :
    resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) =
      rowLimit DP (seriesRows hw0 hw1 hsmall hd hs X) := rfl

def resolventModulus (X : (D).Cauchy) : Q' → Nat :=
  rowLimitRate DP (seriesRows hw0 hw1 hsmall hd hs X)

theorem partial_resolvent_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : resolventModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n)
      (resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  rw [resolvent_mk, ← seriesRows_point]
  exact rowLimit_bound DP (seriesRows hw0 hw1 hsmall hd hs X) epsilon he n hn

theorem resolvent_centered (x : V) : C (resolvent hw0 hw1 hsmall hd hs x) =
    resolvent hw0 hw1 hsmall hd hs x := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [resolvent_mk]
  apply (center_fixed_iff hw0 hw1 hsmall hd hs _).mpr
  apply rowLimit_orthogonal hw0 hw1 hsmall hd hs
  intro n
  rw [seriesRows_point]
  exact (center_fixed_iff hw0 hw1 hsmall hd hs _).mp
    (partial_centered hw0 hw1 hsmall hd hs _ n)

/-- Exact discrete Poisson equation, on the same carrier as its source. -/
theorem resolvent_equation (x : V) :
    resolvent hw0 hw1 hsmall hd hs x = A (C x) (T 2 (resolvent hw0 hw1 hsmall hd hs x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completed_eq_of_small DP
  intro epsilon he
  let n := resolventModulus hw0 hw1 hsmall hd hs X (quarter epsilon)
  have hn := partial_resolvent_bound hw0 hw1 hsmall hd hs X (quarter epsilon)
    (quarter_pos he) n (Nat.le_refl _)
  have hnext := partial_resolvent_bound hw0 hw1 hsmall hd hs X (quarter epsilon)
    (quarter_pos he) (n+1) (Nat.le_succ _)
  rw [completedDist_symm] at hnext
  have ht := completedDist_time_contraction hw0 hw1 hsmall hd hs 2
    (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n)
    (resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X))
  have hh : RCle (completedDist hw0 hw1 hsmall hd hs
      (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) (n+1))
      (A (C (Quotient.mk (D).completionSetoid X))
        (T 2 (resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)))))
      (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) := by
    change RCle (completedDist hw0 hw1 hsmall hd hs (A _ _) (A _ _)) _
    rw [dist_add_common]
    exact RCle_trans ht hn
  exact completedDist_two_segment DP _ _ _ epsilon hnext hh

theorem solution_unique (x y z : V)
    (hy : C y = y) (hz : C z = z)
    (hey : y = A (C x) (T 2 y)) (hez : z = A (C x) (T 2 z)) : y = z := by
  have hdiff : Sub y z = Sub (T 2 y) (T 2 z) := by
    calc
      Sub y z = Sub (A (C x) (T 2 y)) (A (C x) (T 2 z)) :=
        (congrArg (fun a => Sub a z) hey).trans
          (congrArg (Sub (A (C x) (T 2 y))) hez)
      _ = _ := sub_add_common hw0 hw1 hsmall hd hs _ _ _
  have hfixed : T 2 (Sub y z) = Sub y z := by
    rw [completedTime_sub]
    exact hdiff.symm
  have hc : C (Sub y z) = Sub y z := by rw [center_sub, hy, hz]
  have hzero := fixed_twoStep_complement_eq_zero hw0 hw1 hsmall hd hs
    ⟨Sub y z, (center_fixed_iff hw0 hw1 hsmall hd hs _).mp hc⟩ hfixed
  have h := congrArg (fun a => A a z) hzero
  change A (Sub y z) z = A Z z at h
  rw [completedSub_add_cancel, completedZero_add] at h
  exact h

def defect (x : V) : V := Sub x (T 2 x)

theorem resolvent_right_inverse (x : V) :
    defect hw0 hw1 hsmall hd hs (resolvent hw0 hw1 hsmall hd hs x) = C x := by
  unfold defect
  calc
    Sub (resolvent hw0 hw1 hsmall hd hs x) (T 2 (resolvent hw0 hw1 hsmall hd hs x)) =
        Sub (A (C x) (T 2 (resolvent hw0 hw1 hsmall hd hs x)))
          (T 2 (resolvent hw0 hw1 hsmall hd hs x)) :=
      congrArg (fun a => Sub a (T 2 (resolvent hw0 hw1 hsmall hd hs x)))
        (resolvent_equation hw0 hw1 hsmall hd hs x)
    _ = C x := sub_add_right_cancel hw0 hw1 hsmall hd hs _ _

theorem center_defect (x : V) : C (defect hw0 hw1 hsmall hd hs x) =
    defect hw0 hw1 hsmall hd hs (C x) := by
  unfold defect
  rw [center_sub, ← completedTime_center]

theorem resolvent_left_inverse (x : V) :
    resolvent hw0 hw1 hsmall hd hs (defect hw0 hw1 hsmall hd hs x) = C x := by
  apply solution_unique hw0 hw1 hsmall hd hs (defect hw0 hw1 hsmall hd hs x) _ _
    (resolvent_centered hw0 hw1 hsmall hd hs _) (center_idempotent hw0 hw1 hsmall hd hs x)
    (resolvent_equation hw0 hw1 hsmall hd hs _)
  rw [center_defect]
  exact (completedSub_add_cancel hw0 hw1 hsmall hd hs (C x) (T 2 (C x))).symm

/-- The solved vector and actual approximation modulus are returned as data. -/
def solutionCertificate (X : (D).Cauchy) :
    Σ' y : UnitComplement hw0 hw1 hsmall hd hs,
      (defect hw0 hw1 hsmall hd hs y.val = C (Quotient.mk (D).completionSetoid X)) ×'
      {M : Q' → Nat // ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, M epsilon ≤ n →
        RCle (completedDist hw0 hw1 hsmall hd hs
          (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n) y.val)
          (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨⟨resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X),
      (center_fixed_iff hw0 hw1 hsmall hd hs _).mp (resolvent_centered hw0 hw1 hsmall hd hs _)⟩,
    resolvent_right_inverse hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X),
    ⟨resolventModulus hw0 hw1 hsmall hd hs X, partial_resolvent_bound hw0 hw1 hsmall hd hs X⟩⟩

end YMGap.Continuum.BF4SpatialUnionResolvent

#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.sub_add_common
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.dist_add_common
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolventRepresentative
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolventRepresentative_congr
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolvent
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolvent_mk
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolventModulus
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.partial_resolvent_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolvent_centered
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolvent_equation
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.solution_unique
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.defect
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolvent_right_inverse
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.center_defect
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.resolvent_left_inverse
#print axioms YMGap.Continuum.BF4SpatialUnionResolvent.solutionCertificate
