/-
# An explicit changing-nome test of the local defect source

Use w_j=1-1/(j+2) on the EXISTING literal Wilson completion, and assign
one lattice step the candidate duration a_j=2^(-(j+1)). At n_j=2^(j+1)
steps the candidate elapsed time is exactly one. The local plaquette
defect y_j=(I-T_j)v_j has a positive norm at each index, but its squared
orbit norm divided by its OWN squared norm becomes arbitrarily small,
with an explicit modulus independent of width and plaquette placement.

This rules out a fixed positive relative response for THIS source and
THIS proposed schedule. It does not identify the schedule with Yang--Mills
physical scaling, identify different completions, or refute other sources
or continuum Yang--Mills. No all-state gap is used or asserted.
-/

import YMGap.Continuum.BF4WilsonNomeDyadicDefectSchedule

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDefectCollapse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomeRelativeDefectNormalization
open YMGap.Continuum.BF4WilsonAllNomePolynomialDefectBudget
open YMGap.Continuum.BF4WilsonNomeDyadicDefectSchedule
open YMGap.Continuum.BF4RelativePredictionNomeBudget

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- A smaller nome only improves the displayed normalization weight. -/
theorem normWeight_antitone {w W : Q'} (hw1 : w < (1 : Q'))
    (hW1 : W < (1 : Q')) (hwW : w ≤ W) : normWeight W ≤ normWeight w := by
  let a := 1 + -W
  let b := 1 + -w
  have ha : (0 : Q') ≤ a := Q'.le_of_lt (HKPos.one_sub_pos hW1)
  have hb : (0 : Q') ≤ b := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hsub : (b + -a).eqv (W + -w) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0)))
        (.neg (.add (.const 1) (.neg (.var 1)))))
      (.add (.var 1) (.neg (.var 0))) (by decide) (fun | 0 => w | _ => W)
  have hab : a ≤ b := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hwW) (Q'.ge_of_eqv hsub))
  have hc : cubicDeficit W ≤ cubicDeficit w := HKConv.mul_le_mul'
    (Q'.mul_nonneg a a ha ha) hb (HKConv.mul_le_mul' ha hb hab hab) hab
  have h4 := HKConv.pow_le_pow_base
    (Q'.le_of_lt (cubicDeficit_positive hW1)) hc 4
  exact HKConv.mul_le_mul'
    (Q'.pow_nonneg _ (Q'.le_of_lt (cubicDeficit_positive hW1)) 4)
    (Q'.pow_nonneg _ (Q'.le_of_lt (cubicDeficit_positive hw1)) 4) h4 h4

/-- The result covers ANY nome below the explicit index-dependent ceiling,
not only the particular equality schedule. No physical calibration is assumed. -/
theorem ceiling_relative_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (j width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hwj : w ≤ nome j) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hj : scaleModulus epsilon ≤ j) :
    let y := defect hw0 hw1 (plaquetteExcitation hw0 hw1 width face hf).val
    RCle (completedInner hw0 hw1 (completedTime hw0 hw1 (steps j) y)
      (completedTime hw0 hw1 (steps j) y))
      (RCscale epsilon (completedInner hw0 hw1 y y)) := by
  apply plaquette_defect_polynomial_relative_small hw0 hw1 width face hf epsilon (steps j)
  exact Q'.le_trans' _ _ _ (scalar_budget epsilon he j hj)
    (Q'.mul_le_mul_of_nonneg_left _ _ epsilon
      (normWeight_antitone hw1 (nome_lt_one j) hwj) (Q'.le_of_lt he))

variable (j width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "hw0" => nome_positive j
local notation "hw1" => nome_lt_one j
local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "y" => defect hw0 hw1 v
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- The input is a computed index cutoff, not an assumed original-action
decay estimate. The source and the norm on both sides are exactly the same. -/
theorem sampled_relative_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (hj : scaleModulus epsilon ≤ j) :
    RCle (B (T (steps j) y) (T (steps j) y)) (RCscale epsilon (B y y)) :=
  ceiling_relative_small hw0 hw1 j width face hf (Q'.le_of_eqv (Q'.eqv_refl _)) epsilon he hj

/-- Every later elapsed lattice time inherits the same relative estimate.
In particular, every positive integer multiple of candidate physical time
one is covered without a new nome or width assumption. -/
theorem later_relative_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (hj : scaleModulus epsilon ≤ j) (n : Nat) (hn : steps j ≤ n) :
    RCle (B (T n y) (T n y)) (RCscale epsilon (B y y)) := by
  have h := completedInner_time_contraction hw0 hw1 (n-steps j) (T (steps j) y)
  rw [← completedTime_add, show n-steps j+steps j=n from Nat.sub_add_cancel hn] at h
  exact RCle_trans h (sampled_relative_small j width face hf epsilon he hj)

/-- The same estimate is the SAME-source autocorrelation at twice the
elapsed time, by the existing physical-time pairing identity. -/
theorem later_autocorrelation_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (hj : scaleModulus epsilon ≤ j) (n : Nat) (hn : steps j ≤ n) :
    RCle (B y (T (n+n) y)) (RCscale epsilon (B y y)) := by
  have h := later_relative_small j width face hf epsilon he hj n hn
  rwa [completedInner_time_sum] at h

private theorem rational_scale_cancel_of_floor {a b f : Q'} {X : RC}
    (hf : (0 : Q') < f) (hfloor : RCle (Rq f) X)
    (hscaled : RCle (RCscale a X) (RCscale b X)) : a ≤ b := by
  revert hfloor hscaled
  refine Quotient.inductionOn X ?_
  intro A hfloor hscaled
  have hc : leEv (ofQ' a) (ofQ' b) :=
    YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap.leEv_cancel_mul_right_posEv
      ⟨f, hf, hfloor⟩ hscaled
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

/-- A fixed positive relative survival floor is impossible at the computed
late index, even though the actual source norm is strictly positive there. -/
theorem sampled_relative_floor_impossible (floor : Q') (hfloor : (0 : Q') < floor)
    (hj : scaleModulus (HalfPow.half*floor) ≤ j) (n : Nat) (hn : steps j ≤ n)
    (hsurvive : RCle (RCscale floor (B y y)) (B (T n y) (T n y))) : False := by
  have hsmall := later_relative_small j width face hf (HalfPow.half*floor)
    (ExpNeg.half_mul_pos floor hfloor) hj n hn
  have hbad : floor ≤ HalfPow.half*floor := rational_scale_cancel_of_floor
    (relativeDefectNormFloor_positive (nome j))
    (plaquette_relative_defect_norm_floor hw0 hw1 width face hf)
    (RCle_trans hsurvive hsmall)
  have hstrict : HalfPow.half*floor < floor :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (ClusteringImpliesGap.mul_lt_mul_of_pos_right hfloor
        (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.one_mul_eqv floor))
  exact Int.not_lt.mpr hbad hstrict

#print axioms normWeight_antitone
#print axioms ceiling_relative_small
#print axioms sampled_relative_small
#print axioms later_relative_small
#print axioms later_autocorrelation_small
#print axioms sampled_relative_floor_impossible

end YMGap.Continuum.BF4WilsonAllNomeDyadicDefectCollapse
