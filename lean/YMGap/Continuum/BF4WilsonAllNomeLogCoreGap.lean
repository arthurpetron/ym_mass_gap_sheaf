/-
# The actual transfer gap reaches the original regularized-series graph

For T the original completed time and F=sum_(k>=1)(I-T)^k T/k,
the existing strict norm contraction gives

  <T x,F x> >= (1-q)/2 * ||T x||^2

when the input T x is orthogonal to the original vacuum. The first term of
the SAME positive series suffices. Consequently F has exactly the original
time kernel on the vacuum complement; the actual boundary kernel is retained.

This is a fixed-nome, fixed-width graph-core bound, not a scalar-log
identification, continuous-time generator, or physical/scaling mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogGraph
import YMGap.Continuum.BF4WilsonAllNomeLocalResponseOrbit

namespace YMGap.Continuum.BF4WilsonAllNomeLogCoreGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4WilsonAllNomeLogSeries
open YMGap.Continuum.BF4WilsonAllNomeLogRangePositive
open YMGap.Continuum.BF4WilsonAllNomeLogGraph

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "F" => regularizedLog hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

/-- Positive rational data, still dependent on nome and width through q. -/
def coreMargin (width : Nat) : Q' :=
  HalfPow.half * (1 - twoStepRate hw0 hw1 width)

theorem coreMargin_positive : (0 : Q') < coreMargin hw0 hw1 width :=
  Q'.mul_pos (by decide) (HKPos.one_sub_pos (twoStepRate_lt_one hw0 hw1 width))

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem sub_nonnegative {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  have hb : RCsub b b = RCzero := by
    refine Quotient.inductionOn b ?_
    exact fun B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.add_neg_self_eqv (B'.approx n)))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [hb] at h'

private theorem gap_identity (rate : Q') (a b c : RC) :
    RCsub a b = RCadd (RCscale (HalfPow.half*(1-rate)) a)
      (RCscale HalfPow.half (RCadd
        (RCsub (RCsub a b) (RCsub b c)) (RCsub (RCscale rate a) c))) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 4)
        (.add (.const 1) (.neg (.var 3)))) (.var 0))
        (.mul (.var 4)
          (.add (.add (.add (.var 0) (.neg (.var 1)))
            (.neg (.add (.var 1) (.neg (.var 2)))))
            (.add (.mul (.var 3) (.var 0)) (.neg (.var 2))))))
      (.add (.mul (.var 4) (.add (.var 0) (.neg (.var 1))))
        (.mul (.var 4) (.add (.var 0) (.neg (.var 1)))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n
           | 3 => rate | _ => HalfPow.half))
      (ExpNeg.two_halves (A.approx n + -(B'.approx n))))))

/-- The existing two-step gap bounds the one-step defect without a square
root, scalar spectral theorem or new analytic input. -/
theorem completed_defect_form_gap (x : V) (hx : B U x = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width) (B x x))
      (B x (defect hw0 hw1 x)) := by
  have hgap := completed_oneStep_norm_gap hw0 hw1 width 0 x
    ((completedInner_symm hw0 hw1 x U).trans hx)
  simp only [Nat.zero_add, completedTime_zero] at hgap
  have hsquare := completedInner_nonnegative hw0 hw1 (defect hw0 hw1 x)
  rw [defect, completedInner_sub_left, completedInner_sub_right,
    completedInner_sub_right, completedInner_symm hw0 hw1 (T 1 x) x] at hsquare
  have hrem := RCscale_mono HalfPow.half_nonneg
    (RCadd_le_add hsquare (sub_nonnegative hgap))
  rw [zero_add, RCscale_RCzero] at hrem
  have h := RCadd_le_add
    (RCle_refl (RCscale (coreMargin hw0 hw1 width) (B x x))) hrem
  rw [add_zero] at h
  rw [defect, completedInner_sub_right,
    gap_identity q (B x x) (B x (T 1 x)) (B (T 1 x) (T 1 x))]
  exact h

/-- The strict bound is on the existing graph input T x, not on a replacement
carrier or an assumed inverse of T. -/
theorem core_form_gap (x : V) (hx : B U (T 1 x) = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width) (B (T 1 x) (T 1 x)))
      (B (T 1 x) (F x)) :=
  RCle_trans (completed_defect_form_gap hw0 hw1 (T 1 x) hx)
    (regularizedLog_time_firstTerm_le hw0 hw1 x)

/-- On the vacuum complement the regularized series kills precisely the
states already killed by the original time. No boundary state is discarded. -/
theorem regularizedLog_zero_iff_time_zero (x : V) (hx : B U x = RCzero) :
    F x = Z ↔ T 1 x = Z := by
  constructor
  · intro hz
    have h := core_form_gap hw0 hw1 x
      (completedTime_preserves_vacuumComplement hw0 hw1 1 x hx)
    rw [hz, completedInner_zero_right] at h
    let m := coreMargin hw0 hw1 width
    have hm : (0 : Q') < m := coreMargin_positive hw0 hw1
    have hs := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos m hm)) h
    have hr : Q'.eqv (Q'.recipPos m hm * m) 1 :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv m hm)
    rw [RCscale_RCscale, RCscale_RCzero,
      RCSignedPairBudget.scale_congr hr, RCscale_one] at hs
    exact (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width (T 1 x)).mp
      (RCle_antisymm hs (completedInner_nonnegative hw0 hw1 (T 1 x)))
  · exact regularizedLog_kernel_zero hw0 hw1 x

/-- No nonzero original time-kernel vector is a witnessed graph input.
This follows from its supplied positive-time approximants, not from deleting
the boundary kernel or assuming full-carrier injectivity. -/
theorem graph_input_time_kernel_eq_zero {x y : V}
    (G : GraphLimit hw0 hw1 x y) (hx : T 1 x = Z) : x = Z := by
  apply (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width x).mp
  apply RCle_antisymm ?_ (completedInner_nonnegative hw0 hw1 x)
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := G.modulus epsilon
  have horth : B x (T 1 (G.source n)) = RCzero := by
    rw [← completedInner_time_balance, hx, completedInner_zero_left]
  have h := RCle_trans
    (BF4WilsonAllNomeGraphDistance.norm_le_dist_of_orthogonal hw0 hw1
      x (T 1 (G.source n)) horth)
    (by
      rw [BF4WilsonAllNomeDistance.completedDist_symm]
      exact (G.bound epsilon he n (Nat.le_refl n)).1)
  rw [zero_add]
  exact h

/-- The existing witnessed graph has no nonzero zero-output state in the
original vacuum complement. No self-adjointness or physical calibration is
inferred from this kernel statement. -/
theorem graph_zero_output_iff {x y : V}
    (G : GraphLimit hw0 hw1 x y) (hx : B U x = RCzero) :
    y = Z ↔ x = Z := by
  constructor
  · intro hy
    have hpin := graph_time_pin hw0 hw1 G
    rw [hy, completedTime_zero_element] at hpin
    exact graph_input_time_kernel_eq_zero hw0 hw1 G
      ((regularizedLog_zero_iff_time_zero hw0 hw1 x hx).mp hpin.symm)
  · intro hz
    rw [hz] at G
    exact graph_zero_input hw0 hw1 G

/-- The same kernel result on the already constructed quotient domain. -/
theorem action_zero_iff_input_zero (p : Domain hw0 hw1 (width := width))
    (hp : B U (input hw0 hw1 p) = RCzero) :
    action hw0 hw1 p = Z ↔ input hw0 hw1 p = Z := by
  revert hp
  refine Quotient.inductionOn p ?_
  intro P hp
  exact graph_zero_output_iff hw0 hw1 P.2.2 hp

/-- A concrete active plaquette is not killed by the actual regularized
series. This is finite-parameter nontriviality, not continuum survival. -/
theorem plaquette_regularizedLog_ne_zero
    (face : ClusterCount4DProgress.Z4Plaq)
    (hf : face ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width)
    (hactive : ∀ l, l ∈ ClusterCount4DProgress.edgesOf face →
      (BF4ExactSlabFixedSpatialSliceCarrier.baseLinks width).idxOf l ∈
        BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks width) :
    F (BF4WilsonAllNomePlaquetteExcitation.plaquetteExcitation hw0 hw1 width face hf).val ≠ Z := by
  intro hz
  have htime := (regularizedLog_zero_iff_time_zero hw0 hw1 _
    (BF4WilsonAllNomePlaquetteExcitation.plaquetteExcitation hw0 hw1 width face hf).property).mp hz
  exact BF4WilsonAllNomeLocalResponseOrbit.plaquette_time_ne_zero
    hw0 hw1 width face hf hactive 1 htime

#print axioms coreMargin
#print axioms coreMargin_positive
#print axioms completed_defect_form_gap
#print axioms core_form_gap
#print axioms regularizedLog_zero_iff_time_zero
#print axioms graph_input_time_kernel_eq_zero
#print axioms graph_zero_output_iff
#print axioms action_zero_iff_input_zero
#print axioms plaquette_regularizedLog_ne_zero

end YMGap.Continuum.BF4WilsonAllNomeLogCoreGap
