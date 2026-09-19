/-
# Finite geometric approximate preimages on the SAME Wilson completion

The finite geometric sum of the actual two-step transfer orbit is an explicit
constructive approximate preimage for `I - T^2`.  The identity is proved on
the current completed Wilson carrier, with no inverse, choice, spectral
theorem, or auxiliary transfer.  On the existing vacuum complement the
actual approximation error is bounded by the already checked geometric norm
decay.

This is a fixed-spacing SU(2) range approximation.  It is not a completed
spectral-gap theorem, a changing-spacing estimate, a physical mass
calibration, or a continuum Yang--Mills construction.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
import YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
import YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection

namespace YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (completedCenteredScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_self)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd

/-- The finite orbit sum `x + T²x + ... + T^(2(n-1))x`. -/
def evenOrbitSum (x : V) : Nat → V
  | 0 => Z
  | n + 1 => A (evenOrbitSum x n) (T (2*n) x)

/-- The actual same-carrier defect operator whose range is approximated below. -/
def evenOrbitResidual (x : V) : V :=
  completedSub hw0 hw1 hsmall hd hs x (T 2 x)

theorem evenOrbitResidual_kernel (x : V)
    (hx : B x (completedUnit hw0 hw1 hsmall hd hs) = RCzero)
    (hr : evenOrbitResidual hw0 hw1 hsmall hd hs x = Z) :
    x = Z := by
  have hnorm : B (evenOrbitResidual hw0 hw1 hsmall hd hs x)
      (evenOrbitResidual hw0 hw1 hsmall hd hs x) = RCzero := by
    rw [hr, completedInner_zero_left]
  have hfix : x = T 2 x := by
    apply (completedSub_norm_zero_iff hw0 hw1 hsmall hd hs x (T 2 x)).mp
    exact hnorm
  exact fixed_orthogonal_eq_zero hw0 hw1 hsmall hd hs x hx hfix.symm

theorem evenOrbitResidual_center (x : V) :
    evenOrbitResidual hw0 hw1 hsmall hd hs
        (center hw0 hw1 hsmall hd hs x) =
      center hw0 hw1 hsmall hd hs
        (evenOrbitResidual hw0 hw1 hsmall hd hs x) := by
  unfold evenOrbitResidual
  rw [center_sub, completedTime_center]

/-- A representative-level version of the finite orbit sum, retaining the
    supplied Cauchy stream rather than choosing a quotient representative. -/
def evenOrbitSumCauchy (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy) : Nat →
    (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy
  | 0 => (unionSeminorm hw0 hw1 hsmall hd hs).constant zeroStage
  | n + 1 =>
      addCauchy hw0 hw1 hsmall hd hs (evenOrbitSumCauchy X n)
        ((timeNonexpansive hw0 hw1 hsmall hd hs (2*n)).mapCauchy X)

theorem evenOrbitSumCauchy_pin
    (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy) (n : Nat) :
    Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid
        (evenOrbitSumCauchy hw0 hw1 hsmall hd hs X n) =
      evenOrbitSum hw0 hw1 hsmall hd hs
        (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [evenOrbitSumCauchy, ← completedAdd_mk, ih]
      rfl

/-- The same finite orbit sum retained as a strict finite Wilson stage. -/
def evenOrbitSumStage (x : Stage) : Nat → Stage
  | 0 => zeroStage
  | n + 1 => sumStage (evenOrbitSumStage x n) (time (2*n) x)

theorem evenOrbitSumStage_pin (x : Stage) (n : Nat) :
    embedStage hw0 hw1 hsmall hd hs
        (evenOrbitSumStage x n) =
      evenOrbitSum hw0 hw1 hsmall hd hs
        (embedStage hw0 hw1 hsmall hd hs x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [evenOrbitSumStage, ← completedAdd_embedStage, ih,
        ← completedTime_embedStage]
      rfl

@[simp] theorem evenOrbitSum_zero (x : V) : evenOrbitSum hw0 hw1 hsmall hd hs x 0 = Z := rfl

@[simp] theorem evenOrbitSum_succ (x : V) (n : Nat) :
    evenOrbitSum hw0 hw1 hsmall hd hs x (n+1) =
      A (evenOrbitSum hw0 hw1 hsmall hd hs x n) (T (2*n) x) := rfl

private theorem rc_telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro repA repB repC
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun | 0 => repA.approx n | 1 => repB.approx n | _ => repC.approx n)))

private theorem rc_sub_add_exchange (a b c d : RC) :
    RCsub (RCadd a b) (RCadd c d) =
      RCadd (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro repA repB
  refine Quotient.inductionOn₂ c d ?_
  intro repC repD
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 3)))) (by decide)
      (fun | 0 => repA.approx n | 1 => repB.approx n
            | 2 => repC.approx n | _ => repD.approx n)))

private theorem rc_sub_sub_left (a b : RC) :
    RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro repA repB
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (.var 1) (by decide)
      (fun | 0 => repA.approx n | _ => repB.approx n)))

/-- The exact finite geometric resolvent identity on the current carrier. -/
theorem evenOrbitSum_sub_twoStep (x : V) (n : Nat) :
    completedSub hw0 hw1 hsmall hd hs
        (evenOrbitSum hw0 hw1 hsmall hd hs x n)
        (T 2 (evenOrbitSum hw0 hw1 hsmall hd hs x n)) =
      completedSub hw0 hw1 hsmall hd hs x (T (2*n) x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  induction n with
  | zero =>
      rw [evenOrbitSum_zero, completedInner_sub_left,
        completedInner_sub_left, completedInner_zero_left,
        completedTime_zero_vector, completedInner_zero_left,
        Nat.mul_zero, completedTime_zero, rc_sub_self]
      exact (rc_sub_self (B x test)).symm
  | succ n ih =>
      have htime : T 2 (T (2*n) x) = T (2*(n+1)) x := by
        rw [← completedTime_add]
        congr 1
        omega
      have ih' := ih
      rw [completedInner_sub_left] at ih'
      rw [evenOrbitSum_succ, completedTime_addition, htime,
        completedInner_sub_left]
      simp only [completedInner_add_left]
      rw [rc_sub_add_exchange, ih']
      rw [completedInner_sub_left, completedInner_sub_left]
      exact rc_telescope _ _ _

/-- The actual error of the explicit preimage has a directly quantified
    squared-norm bound on the same vacuum complement. -/
theorem evenOrbitSum_error_bound (x : V)
    (hx : B x (completedUnit hw0 hw1 hsmall hd hs) = RCzero) (n : Nat) :
    RCle
    (completedDist hw0 hw1 hsmall hd hs x
      (completedSub hw0 hw1 hsmall hd hs
        (evenOrbitSum hw0 hw1 hsmall hd hs x n)
        (T 2 (evenOrbitSum hw0 hw1 hsmall hd hs x n))))
      (RCscale (q^(2*n)) (B x x)) := by
  have herr : completedSub hw0 hw1 hsmall hd hs x
      (completedSub hw0 hw1 hsmall hd hs
        (evenOrbitSum hw0 hw1 hsmall hd hs x n)
        (T 2 (evenOrbitSum hw0 hw1 hsmall hd hs x n))) =
      T (2*n) x := by
    rw [evenOrbitSum_sub_twoStep]
    apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
    intro test
    rw [completedInner_sub_left, completedInner_sub_left]
    exact rc_sub_sub_left _ _
  unfold completedDist
  rw [herr]
  exact norm_decay hw0 hw1 hsmall hd hs x hx (2*n)

private theorem pow_add_eqv (a : Q') (m n : Nat) :
    Q'.eqv (a^(m+n)) (a^m * a^n) := by
  induction n with
  | zero => exact Q'.eqv_symm (Q'.mul_one_eqv (a^m))
  | succ n ih =>
      show Q'.eqv (a^(m+n+1)) (a^m * a^(n+1))
      rw [Q'.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv a (a^m) (a^n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a (a^m))) ?_
      exact Q'.mul_assoc_eqv (a^m) a (a^n)

private theorem pow_two_step (a : Q') : ∀ n : Nat, Q'.eqv (a^(2*n)) ((a*a)^n)
  | 0 => Q'.eqv_refl _
  | n+1 => by
      have hidx : 2*(n+1) = (2*n)+2 := by omega
      rw [hidx]
      have htwo : Q'.eqv (a^2) (a*a) := by
        rw [Q'.pow_succ, Q'.pow_succ]
        exact Q'.mul_eqv_congr_left a _ _ (Q'.mul_one_eqv a)
      have hpowone : Q'.eqv ((a*a)^1) (a*a) := by
        rw [Q'.pow_succ, Q'.pow_zero]
        exact Q'.mul_one_eqv (a*a)
      have htail : Q'.eqv ((a*a)^n * (a*a)^1) ((a*a)^n * (a*a)) :=
        Q'.mul_eqv_congr_left ((a*a)^n) ((a*a)^1) (a*a) hpowone
      exact Q'.eqv_trans _ _ _ (pow_add_eqv a (2*n) 2)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (a^(2*n)) ((a*a)^n) (a^2)
            (pow_two_step a n))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left ((a*a)^n) (a^2) (a*a) htwo)
            (Q'.eqv_trans _ _ _
              (Q'.eqv_symm htail)
              (Q'.eqv_symm (pow_add_eqv (a*a) n 1)))))

private theorem rcscale_congr {a b : Q'} (h : Q'.eqv a b) (v : RC) :
    RCscale a v = RCscale b v := by
  refine Quotient.inductionOn v ?_
  intro rep
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right a b (rep.approx n) h))

/-- The explicit fixed-spacing epsilon-to-index modulus for the finite
    geometric preimage error, using the existing completed representative
    norm cap. -/
def evenOrbitSum_modulus (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy)
    (epsilon : Q') : Nat :=
  geometricCutoff (q*q) (normCap hw0 hw1 hsmall hd hs X) epsilon

theorem evenOrbitSum_error_small (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy)
    (hX : B (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : evenOrbitSum_modulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle
      (completedDist hw0 hw1 hsmall hd hs
        (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
        (completedSub hw0 hw1 hsmall hd hs
          (evenOrbitSum hw0 hw1 hsmall hd hs
            (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X) n)
          (completedTime hw0 hw1 hsmall hd hs 2
            (evenOrbitSum hw0 hw1 hsmall hd hs
              (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X) n))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hq0 : (0 : Q') ≤ q := Q'.le_of_lt (twoStepRate_positive hw0 hd)
  have hq1 : q < (1 : Q') := twoStepRate_lt_one hw0 hd hs
  have hqq0 : (0 : Q') ≤ q*q := Q'.mul_nonneg q q hq0 hq0
  have hqq1 : q*q < (1 : Q') := by
    apply Q'.lt_of_le_of_lt
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_lt hq1) hq0)
        (Q'.le_of_eqv (Q'.mul_one_eqv q)))
      hq1
  have hnorm := evenOrbitSum_error_bound hw0 hw1 hsmall hd hs
    (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X) hX n
  have hnormcap := norm_le_cap hw0 hw1 hsmall hd hs X
  have hscale := RCscale_mono
    (Q'.pow_nonneg (q*q) hqq0 n) hnormcap
  have hpow := pow_two_step q n
  have hscale' : RCscale (q^(2*n))
      (B (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
        (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)) =
      RCscale ((q*q)^n)
        (B (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
          (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)) := by
    exact rcscale_congr hpow _
  have hgeom := geometric_bound hqq0 hqq1
    (normCap_nonnegative hw0 hw1 hsmall hd hs X) he n hn
  have hbound := RCle_trans hnorm (hscale' ▸ hscale)
  refine RCle_trans hbound ?_
  exact leEv_le_ofQ'_of_approx_le (fun _ => hgeom)

/-- The current fixed-spacing range consumer, with its vacuum-complement input
    retained explicitly.  The returned preimage is represented by supplied
    Cauchy data in the original union completion. -/
def evenOrbitSum_range_data
    (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy)
    (hX : B (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' Y : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy, RCle
      (completedDist hw0 hw1 hsmall hd hs
        (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
        (evenOrbitResidual hw0 hw1 hsmall hd hs
          (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid Y)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let n := evenOrbitSum_modulus hw0 hw1 hsmall hd hs X epsilon
  refine ⟨evenOrbitSumCauchy hw0 hw1 hsmall hd hs X n, ?_⟩
  have h := evenOrbitSum_error_small hw0 hw1 hsmall hd hs X hX epsilon he n
    (Nat.le_refl _)
  simpa only [evenOrbitResidual, evenOrbitSumCauchy_pin] using h

/-- Every supplied Cauchy representative has a centered same-carrier range
    witness; the centering projection is the existing one, not a new quotient. -/
def evenOrbitCentered_range_data
    (X : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' Y : (unionSeminorm hw0 hw1 hsmall hd hs).Cauchy, RCle
      (completedDist hw0 hw1 hsmall hd hs
        (center hw0 hw1 hsmall hd hs
          (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X))
        (evenOrbitResidual hw0 hw1 hsmall hd hs
          (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid Y)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hcenter : B
      (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid
        (centerCauchy hw0 hw1 hsmall hd hs X))
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero := by
    rw [← center_mk]
    exact center_orthogonal hw0 hw1 hsmall hd hs
      (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid X)
  have h := evenOrbitSum_range_data hw0 hw1 hsmall hd hs
    (centerCauchy hw0 hw1 hsmall hd hs X) hcenter epsilon he
  simpa only [center_mk] using h

/-- The same-object defect pairing is exactly the difference of the existing
    connected lag-zero and lag-two correlators. -/
theorem evenOrbitResidual_centered_pairing (x y : V) :
    B (center hw0 hw1 hsmall hd hs x)
      (evenOrbitResidual hw0 hw1 hsmall hd hs
        (center hw0 hw1 hsmall hd hs y)) =
      RCsub
        (completedCenteredScalar hw0 hw1 hsmall hd hs 0 x y)
        (completedCenteredScalar hw0 hw1 hsmall hd hs 2 x y) := by
  unfold evenOrbitResidual
  rw [completedInner_sub_right]
  calc
    RCsub
        (B (center hw0 hw1 hsmall hd hs x)
          (center hw0 hw1 hsmall hd hs y))
        (B (center hw0 hw1 hsmall hd hs x)
          (completedTime hw0 hw1 hsmall hd hs 2
            (center hw0 hw1 hsmall hd hs y))) =
      RCsub
        (B (center hw0 hw1 hsmall hd hs x)
          (completedTime hw0 hw1 hsmall hd hs 0
            (center hw0 hw1 hsmall hd hs y)))
        (B (center hw0 hw1 hsmall hd hs x)
          (completedTime hw0 hw1 hsmall hd hs 2
            (center hw0 hw1 hsmall hd hs y))) := by
            rw [completedTime_zero]
    _ = RCsub
        (completedCenteredScalar hw0 hw1 hsmall hd hs 0 x y)
        (completedCenteredScalar hw0 hw1 hsmall hd hs 2 x y) := by
          rw [centered_time_pairing, centered_time_pairing]

/-- The stage-level cutoff obtained from the constant representative of a
    strict finite Wilson stage. -/
def evenOrbitStage_modulus (x : Stage) (epsilon : Q') : Nat :=
  evenOrbitSum_modulus hw0 hw1 hsmall hd hs
    ((unionSeminorm hw0 hw1 hsmall hd hs).constant x) epsilon

theorem evenOrbitStage_error_small (x : Stage)
    (hx : B (embedStage hw0 hw1 hsmall hd hs x)
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : evenOrbitStage_modulus hw0 hw1 hsmall hd hs x epsilon ≤ n) :
    RCle
      (completedDist hw0 hw1 hsmall hd hs
        (embedStage hw0 hw1 hsmall hd hs x)
        (evenOrbitResidual hw0 hw1 hsmall hd hs
          (embedStage hw0 hw1 hsmall hd hs
            (evenOrbitSumStage x n))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  change B (Quotient.mk (unionSeminorm hw0 hw1 hsmall hd hs).completionSetoid
      ((unionSeminorm hw0 hw1 hsmall hd hs).constant x))
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero at hx
  have h := evenOrbitSum_error_small hw0 hw1 hsmall hd hs
    ((unionSeminorm hw0 hw1 hsmall hd hs).constant x) hx epsilon he n hn
  simpa only [evenOrbitResidual, evenOrbitSumStage_pin] using h

/-- A finite strict-cylinder range certificate: cutoff, stage preimage, and
    the same-carrier error proof are returned together. -/
def evenOrbitStage_range_data (x : Stage)
    (hx : B (embedStage hw0 hw1 hsmall hd hs x)
      (completedUnit hw0 hw1 hsmall hd hs) = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' n : Nat, (n = evenOrbitStage_modulus hw0 hw1 hsmall hd hs x epsilon) ×'
      Σ' y : Stage, RCle
        (completedDist hw0 hw1 hsmall hd hs
          (embedStage hw0 hw1 hsmall hd hs x)
          (evenOrbitResidual hw0 hw1 hsmall hd hs
            (embedStage hw0 hw1 hsmall hd hs y)))
        (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let n := evenOrbitStage_modulus hw0 hw1 hsmall hd hs x epsilon
  refine ⟨n, ⟨rfl, evenOrbitSumStage x n, ?_⟩⟩
  exact evenOrbitStage_error_small hw0 hw1 hsmall hd hs x hx epsilon he n
    (Nat.le_refl _)

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitResidual
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitResidual_kernel
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitResidual_center
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSumCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSumCauchy_pin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSumStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSumStage_pin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_sub_twoStep
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_error_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_modulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_error_small
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_range_data
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitCentered_range_data
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitResidual_centered_pairing
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitStage_modulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitStage_error_small
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitStage_range_data

end YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
