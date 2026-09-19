/-
# Constructive reduced inverse on the current Wilson completion

The represented partial sums from `BF4WilsonSpatialUnionResolventPartial` have
a diagonal limit on the SAME Wilson carrier.  This file packages that limit as
an operator and proves its centered Poisson equation and left/right inverse
identities.  It remains a fixed-spacing, small-nome SU(2) construction; no
continuum, physical-mass, or full QFT conclusion is asserted.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolventPartial

namespace YMGap.Continuum.BF4WilsonSpatialUnionResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion (zeroStage)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero fixed_orthogonal_eq_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4WilsonSpatialUnionCauchyRows
open YMGap.Continuum.BF4WilsonSpatialUnionResolventPartial
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

def resolvent : V → V :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid
    (resolventRepresentative hw0 hw1 hsmall hd hs X))
    (fun X Y h => resolventRepresentative_congr hw0 hw1 hsmall hd hs X Y (Quotient.sound h))

theorem resolvent_mk (X : (D).Cauchy) :
    resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) =
      rowLimit DP (seriesRows hw0 hw1 hsmall hd hs X) := rfl

def resolventModulus (X : (D).Cauchy) : Q' → Nat :=
  rowLimitRate DP (seriesRows hw0 hw1 hsmall hd hs X)

theorem partial_resolvent_bound (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : resolventModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n)
      (resolvent hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  rw [resolvent_mk, ← seriesRows_point]
  exact rowLimit_bound DP (seriesRows hw0 hw1 hsmall hd hs X) epsilon he n hn

def centerRows (R : CauchyRows DP) : CauchyRows DP where
  row := fun n => centerCauchy hw0 hw1 hsmall hd hs (R.row n)
  modulus := R.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact RCle_trans (center_nonexpansive hw0 hw1 hsmall hd hs
      (rowPoint DP R m) (rowPoint DP R n)) (R.isCauchy epsilon he m n hm hn)

theorem centerRows_point (R : CauchyRows DP) (n : Nat) :
    rowPoint DP (centerRows hw0 hw1 hsmall hd hs R) n =
      C (rowPoint DP R n) := rfl

theorem rowLimit_center (R : CauchyRows DP) :
    rowLimit DP (centerRows hw0 hw1 hsmall hd hs R) =
      C (rowLimit DP R) := by
  apply rowLimit_eq_of_bound DP _ _ (rowLimitRate DP R)
  intro epsilon he n hn
  rw [centerRows_point]
  exact RCle_trans (center_nonexpansive hw0 hw1 hsmall hd hs
    (rowPoint DP R n) (rowLimit DP R)) (rowLimit_bound DP R epsilon he n hn)

theorem rowLimit_orthogonal (R : CauchyRows DP)
    (h : ∀ n, completedInner hw0 hw1 hsmall hd hs
      (rowPoint DP R n) (completedUnit hw0 hw1 hsmall hd hs) = RCzero) :
    completedInner hw0 hw1 hsmall hd hs (rowLimit DP R)
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero := by
  apply (center_fixed_iff hw0 hw1 hsmall hd hs _).mp
  rw [← rowLimit_center]
  apply rowLimit_independent DP
  intro n
  rw [centerRows_point]
  exact (center_fixed_iff hw0 hw1 hsmall hd hs _).mpr (h n)

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

theorem resolvent_equation (x : V) :
    resolvent hw0 hw1 hsmall hd hs x =
      A (C x) (T 2 (resolvent hw0 hw1 hsmall hd hs x)) := by
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
  have horth : completedInner hw0 hw1 hsmall hd hs (Sub y z)
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero := by
    rw [← hc]
    exact center_orthogonal hw0 hw1 hsmall hd hs _
  have hzero := fixed_orthogonal_eq_zero hw0 hw1 hsmall hd hs
    (Sub y z) horth hfixed
  have h := congrArg (fun a => A a z) hzero
  change A (Sub y z) z = A Z z at h
  rw [completedSub_add_cancel, completedZero_add] at h
  exact h

def defect (x : V) : V := Sub x (T 2 x)

theorem resolvent_right_inverse (x : V) :
    defect hw0 hw1 hsmall hd hs (resolvent hw0 hw1 hsmall hd hs x) = C x := by
  unfold defect
  calc
    Sub (resolvent hw0 hw1 hsmall hd hs x)
        (T 2 (resolvent hw0 hw1 hsmall hd hs x)) =
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

private theorem rc_sub_swap (a b c d : RC) :
    RCsub (RCsub a b) (RCsub c d) = RCsub (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro X0 Y0
  refine Quotient.inductionOn₂ c d ?_
  intro Z0 W0
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide)
      (fun | 0 => X0.approx n | 1 => Y0.approx n | 2 => Z0.approx n | _ => W0.approx n)))

theorem defect_sub (x y : V) :
    defect hw0 hw1 hsmall hd hs (Sub x y) =
      Sub (defect hw0 hw1 hsmall hd hs x) (defect hw0 hw1 hsmall hd hs y) := by
  unfold defect
  rw [completedTime_sub]
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  simp only [completedInner_sub_left]
  exact rc_sub_swap _ _ _ _

theorem centered_eq_of_defect_eq (x y : V)
    (hx : C x = x) (hy : C y = y)
    (h : defect hw0 hw1 hsmall hd hs x = defect hw0 hw1 hsmall hd hs y) : x = y := by
  have he := congrArg (resolvent hw0 hw1 hsmall hd hs) h
  rw [resolvent_left_inverse, resolvent_left_inverse, hx, hy] at he
  exact he

theorem resolvent_sub (x y : V) :
    resolvent hw0 hw1 hsmall hd hs (Sub x y) =
      Sub (resolvent hw0 hw1 hsmall hd hs x)
        (resolvent hw0 hw1 hsmall hd hs y) := by
  apply centered_eq_of_defect_eq hw0 hw1 hsmall hd hs _ _
    (resolvent_centered hw0 hw1 hsmall hd hs _)
  · rw [center_sub, resolvent_centered, resolvent_centered]
  rw [resolvent_right_inverse, defect_sub, resolvent_right_inverse,
    resolvent_right_inverse, center_sub]

end YMGap.Continuum.BF4WilsonSpatialUnionResolvent

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolvent.resolvent
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolvent.resolvent_equation
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolvent.resolvent_right_inverse
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolvent.resolvent_left_inverse
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolvent.defect_sub
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolvent.resolvent_sub
