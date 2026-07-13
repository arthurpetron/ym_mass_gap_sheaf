/-
# Exact arbitrary-cutoff extension of the retune/Poincare window

The original arbitrary-cutoff theorem used the deliberately loose estimate
`2w^3 <= w/2`, restricting the proof to `w <= 1/2`.  This module keeps the
same global Rayleigh invariant `A_N <= c_1 D_N`, but proves the sharp rational
cubic comparison directly:

    2 w^3 <= ((1+w)/2)^3

throughout `0 <= w <= 25/38`.  The cap is very close to the exact algebraic
crossing and has the exact endpoint slack

    (1+25/38)^3 - 16(25/38)^3 = 47/54872 > 0.

Consequently the arbitrary-cutoff correlation theorem and its exact
Dirichlet/Poincare form hold on a strict extension of the old strong window.
No finite cutoff expansion or measured constant is used.
-/

import YMGap.Continuum.AllWindowCorrDirichlet

namespace YMGap.Continuum.ExtendedWindowCorrPoincare

set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.AllWindowCorrDirichlet

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-- Rational endpoint of the extended arbitrary-cutoff window. -/
def extendedCap : Q' := Q'.mkPos 25 38 (by decide)

private def q3 : Q' := Q'.ofNat 3
private def q8 : Q' := Q'.ofNat 8
private def q15 : Q' := Q'.ofNat 15
private def q16 : Q' := Q'.ofNat 16

open YMGap.Continuum.RingNormaliser

private def cubeExpandLHS : PolyExpr :=
  .mul (.mul (.add (.const 1) (.var 0)) (.add (.const 1) (.var 0)))
    (.add (.const 1) (.var 0))

private def cubeExpandRHS : PolyExpr :=
  .add (.add (.add (.const 1) (.mul (.const 3) (.var 0)))
    (.mul (.const 3) (.mul (.var 0) (.var 0))))
    (.mul (.mul (.var 0) (.var 0)) (.var 0))

private theorem cubeExpand_normal :
    normalize cubeExpandLHS = normalize cubeExpandRHS := by decide

private theorem one_add_cube_expand (w : Q') :
    ((1 : Q') + w) * ((1 : Q') + w) * ((1 : Q') + w) ≈
      (1 : Q') + q3 * w + q3 * (w * w) + (w * w * w) := by
  have h := poly_identity_of_normal_eq cubeExpandLHS cubeExpandRHS cubeExpand_normal
    (fun _ => w)
  simpa [RingNormaliser.eval, cubeExpandLHS, cubeExpandRHS,
    RingNormaliser.qpow, q3] using h

private def scaleCubeLHS : PolyExpr :=
  .mul (.const 8) (.pow (.mul (.var 0) (.var 1)) 3)

private def scaleCubeRHS : PolyExpr :=
  .mul (.mul (.const 8) (.pow (.var 0) 3)) (.pow (.var 1) 3)

private theorem scaleCube_normal :
    normalize scaleCubeLHS = normalize scaleCubeRHS := by decide

private theorem mul_eqv_both {a b c d : Q'} (hac : a ≈ c) (hbd : b ≈ d) :
    a * b ≈ c * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

private theorem scale_mul_cube_regroup (h s : Q') :
    q8 * ((h * s) * (h * s) * (h * s)) ≈
      (q8 * (h * h * h)) * (s * s * s) := by
  have H := poly_identity_of_normal_eq scaleCubeLHS scaleCubeRHS scaleCube_normal
    (fun i => if i = 0 then h else s)
  have H' : Q'.ofInt 8 * (((1 : Q') * (h * s)) * (h * s) * (h * s)) ≈
      (Q'.ofInt 8 * (((1 : Q') * h) * h * h)) *
        (((1 : Q') * s) * s * s) := by
    simpa [RingNormaliser.eval, scaleCubeLHS, scaleCubeRHS,
      RingNormaliser.qpow] using H
  have h8 : q8.eqv (Q'.ofInt 8) := by decide
  have hhs : (((1 : Q') * (h * s)) * (h * s) * (h * s)).eqv
      ((h * s) * (h * s) * (h * s)) := by
    exact Q'.mul_eqv_congr_right _ _ (h * s)
      (Q'.mul_eqv_congr_right _ _ (h * s) (Q'.one_mul_eqv (h * s)))
  have hh : (((1 : Q') * h) * h * h).eqv (h * h * h) := by
    exact Q'.mul_eqv_congr_right _ _ h
      (Q'.mul_eqv_congr_right _ _ h (Q'.one_mul_eqv h))
  have hs : (((1 : Q') * s) * s * s).eqv (s * s * s) := by
    exact Q'.mul_eqv_congr_right _ _ s
      (Q'.mul_eqv_congr_right _ _ s (Q'.one_mul_eqv s))
  refine Q'.eqv_trans _ _ _
    (mul_eqv_both h8 (Q'.eqv_symm hhs)) ?_
  refine Q'.eqv_trans _ _ _ H' ?_
  exact mul_eqv_both (mul_eqv_both (Q'.eqv_symm h8) hh) hs

private theorem qpow_three_eqv (x : Q') :
    (RGTransport.qpow x 3).eqv (x * x * x) := by
  change (((1 : Q') * x) * x) * x ≈ x * x * x
  exact Q'.mul_eqv_congr_right _ _ x
    (Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x))

/-- The positive coefficient `B = (15c-3)c-3` used by the monotone cubic
certificate. -/
private def cubicB : Q' := (q15 * extendedCap - q3) * extendedCap - q3

theorem extendedCap_gt_half : Q'.mkPos 1 2 (by decide) < extendedCap := by decide

/-- Exact endpoint reserve for the cubic comparison. -/
theorem extendedCap_cubic_slack :
    (((1 : Q') + extendedCap) * ((1 : Q') + extendedCap) *
        ((1 : Q') + extendedCap) -
      q16 * (extendedCap * extendedCap * extendedCap)).eqv
        (Q'.mkPos 47 54872 (by decide)) := by
  decide

/-- Pointwise cubic certificate on the extended window:
`15w^3 <= 1+3w+3w^2`. -/
theorem fifteen_cube_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ extendedCap) :
    q15 * (w * w * w) ≤
      (1 : Q') + q3 * w + q3 * (w * w) := by
  have hww : (0 : Q') ≤ w * w := Q'.mul_nonneg _ _ hw0 hw0
  have hcube : w * (w * w) ≤ extendedCap * (w * w) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hwc hww
  have h15cube : q15 * (w * (w * w)) ≤
      q15 * (extendedCap * (w * w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcube (by decide)
  have hsq : w * w ≤ extendedCap * w :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hwc hw0
  have hcoef0 : (0 : Q') ≤ q15 * extendedCap - q3 := by decide
  have hcoef : (q15 * extendedCap - q3) * (w * w) ≤
      (q15 * extendedCap - q3) * (extendedCap * w) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsq hcoef0
  have hB0 : (0 : Q') ≤ cubicB := by decide
  have hBw : cubicB * w ≤ cubicB * extendedCap :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hwc hB0
  have hBc : cubicB * extendedCap ≤ (1 : Q') := by decide
  have hBw1 : cubicB * w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hBw hBc
  have hcoef_target : (q15 * extendedCap - q3) * (w * w) ≤
      (1 : Q') + q3 * w := by
    have hmid : (q15 * extendedCap - q3) * (extendedCap * w) ≈
        cubicB * w + q3 * w := by
      have hc : ((q15 * extendedCap - q3) * extendedCap).eqv
          (cubicB + q3) := by decide
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (q15 * extendedCap - q3) extendedCap w)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w hc) ?_
      exact Q'.add_mul_eqv cubicB q3 w
    refine Q'.le_trans' _ _ _ hcoef ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hmid) ?_
    exact Q'.add_le_add_right _ _ (q3 * w) hBw1
  have hrearrL : q15 * (extendedCap * (w * w)) ≈
      q3 * (w * w) + (q15 * extendedCap - q3) * (w * w) := by
    have hc : (q15 * extendedCap).eqv
        (q3 + (q15 * extendedCap - q3)) := by decide
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv q15 extendedCap (w * w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (w * w) hc) ?_
    exact Q'.add_mul_eqv q3 (q15 * extendedCap - q3) (w * w)
  have hadd : q3 * (w * w) +
        (q15 * extendedCap - q3) * (w * w) ≤
      q3 * (w * w) + ((1 : Q') + q3 * w) :=
    Q'.add_le_add_left _ _ _ hcoef_target
  have hrearrR : q3 * (w * w) + ((1 : Q') + q3 * w) ≈
      (1 : Q') + q3 * w + q3 * (w * w) := by
    exact Q'.add_comm_eqv _ _
  have hmain : q15 * (extendedCap * (w * w)) ≤
      (1 : Q') + q3 * w + q3 * (w * w) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearrL)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hrearrR))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left q15 _ _ (Q'.mul_assoc_eqv w w w))) h15cube)
    hmain

/-- Cleared cubic form `16w^3 <= (1+w)^3`. -/
theorem sixteen_cube_le_one_add_cube {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ extendedCap) :
    q16 * (w * w * w) ≤
      ((1 : Q') + w) * ((1 : Q') + w) * ((1 : Q') + w) := by
  have h := fifteen_cube_le hw0 hwc
  have hadd := Q'.add_le_add_left (w * w * w) _ _ h
  have h16split : q16 * (w * w * w) ≈
      (w * w * w) + q15 * (w * w * w) := by
    have hc : q16.eqv ((1 : Q') + q15) := by decide
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (w * w * w) hc) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 q15 (w * w * w)) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)
  have hcube := one_add_cube_expand w
  have hcomm : (w * w * w) + ((1 : Q') + q3 * w + q3 * (w * w)) ≈
      (1 : Q') + q3 * w + q3 * (w * w) + (w * w * w) :=
    Q'.add_comm_eqv _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h16split)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
        (Q'.le_of_eqv (Q'.eqv_symm hcube))))

/-- The fundamental anchor obeys the retune cube through `w=25/38`. -/
theorem anchor_le_retuneCube_extended {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ extendedCap) :
    coeffW w 1 ≤ retuneCube w := by
  have h16 := sixteen_cube_le_one_add_cube hw0 hwc
  have hL : q8 * coeffW w 1 ≈ q16 * (w * w * w) := by
    have hc : (q8 * Q'.ofNat 2).eqv q16 := by decide
    change q8 * (Q'.ofNat 2 * RGTransport.qpow w 3) ≈
      q16 * (w * w * w)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q8 _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (qpow_three_eqv w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv q8 (Q'.ofNat 2) (w * w * w))) ?_
    exact Q'.mul_eqv_congr_right _ _ (w * w * w) hc
  have hR : q8 * retuneCube w ≈
      ((1 : Q') + w) * ((1 : Q') + w) * ((1 : Q') + w) := by
    let half : Q' := Q'.mkPos 1 2 (by decide)
    let S : Q' := (1 : Q') + w
    have hb : (retuneBase w).eqv (half * S) := Q'.eqv_refl _
    have hp : (retuneCube w).eqv ((half * S) * (half * S) * (half * S)) := by
      unfold retuneCube
      refine Q'.eqv_trans _ _ _ (qpow_three_eqv (retuneBase w)) ?_
      exact mul_eqv_both (mul_eqv_both hb hb) hb
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q8 _ _ hp) ?_
    refine Q'.eqv_trans _ _ _ (scale_mul_cube_regroup half S) ?_
    have hh : (q8 * (half * half * half)).eqv (1 : Q') := by decide
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (S * S * S) hh) ?_
    exact Q'.one_mul_eqv (S * S * S)
  have hscaled : q8 * coeffW w 1 ≤ q8 * retuneCube w :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ h16 (Q'.le_of_eqv (Q'.eqv_symm hR)))
  exact Q'.le_of_mul_le_mul_left hscaled (by decide : (0 : Q') < q8)

/-- **Arbitrary-cutoff correlation theorem on the extended window.** -/
theorem arbitrary_truncation_retune_extended {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ extendedCap) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hwc (by decide : extendedCap ≤ (1 : Q'))
  have hA := adjCorr_le_anchor_norm hw0 hw1 N
  have hD := coordNormSq_nonneg hw0 N
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    (anchor_le_retuneCube_extended hw0 hwc) hD
  exact Q'.le_trans' _ _ _ hA hscale

/-- The equivalent sharp weighted discrete Poincare inequality on the same
extended window. -/
theorem weighted_poincare_extended {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwc : w ≤ extendedCap) (N : Nat) :
    Q'.ofNat 2 * ((1 : Q') - retuneCube w) * coordNormSq w N ≤
      coeffW w 0 * coeffW w 0 +
        coeffW w N * coeffW w N + dirichletEnergy w N := by
  let D := coordNormSq w N
  let A := adjCorr w N
  let R := retuneCube w * D
  have hAR : A ≤ R := arbitrary_truncation_retune_extended hw0 hwc N
  have hneg : -R ≤ -A := Q'.neg_le_neg hAR
  have hsub : D + (-R) ≤ D + (-A) := Q'.add_le_add_left D _ _ hneg
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hsub (by decide)
  have hL : Q'.ofNat 2 * ((1 : Q') - retuneCube w) * D ≈
      Q'.ofNat 2 * (D + (-R)) := by
    unfold R
    have hdist : (((1 : Q') - retuneCube w) * D).eqv
        (D + (-(retuneCube w * D))) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-retuneCube w) D) ?_
      exact Q'.add_eqv_congr' (Q'.one_mul_eqv D)
        (Q'.neg_mul_eqv (retuneCube w) D)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 2) ((1 : Q') - retuneCube w) D) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hdist
  have hdir := twice_norm_sub_corr_eq_boundary_dirichlet w N
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hdir))

end YMGap.Continuum.ExtendedWindowCorrPoincare

#print axioms YMGap.Continuum.ExtendedWindowCorrPoincare.extendedCap_cubic_slack
#print axioms YMGap.Continuum.ExtendedWindowCorrPoincare.fifteen_cube_le
#print axioms YMGap.Continuum.ExtendedWindowCorrPoincare.sixteen_cube_le_one_add_cube
#print axioms YMGap.Continuum.ExtendedWindowCorrPoincare.anchor_le_retuneCube_extended
#print axioms YMGap.Continuum.ExtendedWindowCorrPoincare.arbitrary_truncation_retune_extended
#print axioms YMGap.Continuum.ExtendedWindowCorrPoincare.weighted_poincare_extended
