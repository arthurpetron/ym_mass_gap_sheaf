/-
The represented limit of the actual dyadic resolvents lies in the witnessed
original T(1)-range closure.  At each depth, the resolvent differs from a
scaled root image by a small scalar multiple of the original input.  The
root-image witnesses and the explicit dyadic convergence modulus are
diagonalized on the unchanged carrier; no kernel is quotiented away and no
uniform bound on range preimages is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeResolventLimit
import YMGap.Continuum.BF4WilsonAllNomeRootTimeRange
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed

namespace YMGap.Continuum.BF4WilsonAllNomeResolventRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
  (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent
  (ratio ratio_nonnegative ratio_lt_one denominator denominator_normalized)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeRootTimeRange (rootRange)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters fromTime)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (ofLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear (rationalSmul)
open YMGap.Continuum.BF4WilsonAllNomeResolventLimit
  (resolvent resolvent_pin representedLimit convergenceModulus approximation)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "R" => root hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "half" => HalfPow.half
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def stepRatio (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) : Q' :=
  ratio (lambda * half^depth) 1
    (Q'.mul_pos hl (dyadicStep_positive depth)) (by decide)

private theorem stepRatio_nonnegative (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) : (0 : Q') ≤ stepRatio depth lambda hl :=
  ratio_nonnegative _ _ _ (by decide)

private theorem stepRatio_lt_one (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) : stepRatio depth lambda hl < 1 :=
  ratio_lt_one _ _ _ (by decide)

/-- One resolvent row is a scaled fixed-depth root image plus a small
residual of the original input.  The identity is before taking any limit. -/
theorem dyadic_root_residual (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x : V) :
    Sub (dyadic hw0 hw1 depth lambda hl x)
      (S (stepRatio depth lambda hl)
        (R depth (dyadic hw0 hw1 depth lambda hl x))) =
      S (half^depth * stepRatio depth lambda hl) x := by
  let h := half^depth
  let alpha := lambda*h
  let r := stepRatio depth lambda hl
  let y := dyadic hw0 hw1 depth lambda hl x
  have hden : denominator hw0 hw1 depth alpha 1 y = S h x := by
    exact atStep_equation hw0 hw1 depth lambda h hl
      (dyadicStep_positive depth) x
  have hnormalized := denominator_normalized hw0 hw1 depth alpha 1
    (Q'.mul_pos hl (dyadicStep_positive depth)) (by decide) y
  rw [hnormalized] at hden
  have hcancel : Q'.eqv (r*(alpha+1)) 1 :=
    Q'.divPos_mul_eqv _ _ _
  have hscaled := congrArg (S r) hden
  rw [completedSmul_mul,
    completedSmul_congr hw0 hw1 hcancel, completedSmul_one,
    completedSmul_mul] at hscaled
  change Sub y (S r (R depth y)) = S (h*r) x
  exact hscaled.trans (completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv r h) x)

/-- The residual is controlled by the original representative's explicit
dyadic range modulus, uniformly for every sufficiently fine row. -/
private theorem residual_small (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth : Nat) (hn : rangeModulus hw0 hw1 X epsilon ≤ depth) :
    RCle
      (dist (S (stepRatio depth lambda hl)
        (R depth (dyadic hw0 hw1 depth lambda hl (Class X))))
        (dyadic hw0 hw1 depth lambda hl (Class X)))
      (rat epsilon) := by
  let h := half^depth
  let r := stepRatio depth lambda hl
  let c := h*r
  have hr0 : (0 : Q') ≤ r := stepRatio_nonnegative depth lambda hl
  have hr1 : r ≤ 1 := Q'.le_of_lt (stepRatio_lt_one depth lambda hl)
  have hh0 : (0 : Q') ≤ h := Q'.pow_nonneg half half_nonneg depth
  have hh1 : h ≤ 1 := HKPos.pow_le_one half_nonneg (by decide) depth
  have hc0 : (0 : Q') ≤ c := Q'.mul_nonneg _ _ hh0 hr0
  have hch : c ≤ h := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hr1 hh0)
      (Q'.le_of_eqv (Q'.mul_one_eqv h))
  have hc1 : c ≤ 1 := Q'.le_trans' _ _ _ hch hh1
  have hcc : c*c ≤ h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hc1 hc0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv c)) hch)
  rw [completedDist_symm]
  unfold completedDist
  rw [dyadic_root_residual]
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  have hmono := RCscale_scalar_mono hcc
    (completedInner_nonnegative hw0 hw1 (Class X))
  exact RCle_trans hmono
    (scaled_norm_small hw0 hw1 X epsilon he depth hn)

/-- The root part of a finite resolvent row already has an explicit range
witness, obtained by applying the root-range construction to its supplied
resolvent representative. -/
private def rootPartRange (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (depth : Nat) :
    RangeLimit hw0 hw1
      (S (stepRatio depth lambda hl)
        (R depth (dyadic hw0 hw1 depth lambda hl (Class X)))) := by
  let Y := dyadicRepresentative hw0 hw1 depth lambda hl X
  let H := rootRange hw0 hw1 depth Y
  have hp := dyadicRepresentative_pin hw0 hw1 depth lambda hl X
  exact (congrArg (fun z => S (stepRatio depth lambda hl) (R depth z)) hp) ▸
    rationalSmul hw0 hw1 (stepRatio depth lambda hl) H

/-- A concrete outer modulus for the root-part rows approaching the
represented resolvent: one quarter pays for the vanishing residual and one
quarter for the represented resolvent convergence. -/
def rangeModulus (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') : Nat :=
  max (convergenceModulus hw0 hw1 lambda hl X (quarter epsilon))
    (YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity.rangeModulus
      hw0 hw1 X (quarter epsilon))

theorem rootPart_close (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth : Nat) (hn : rangeModulus hw0 hw1 lambda hl X epsilon ≤ depth) :
    RCle
      (dist (S (stepRatio depth lambda hl)
        (R depth (dyadic hw0 hw1 depth lambda hl (Class X))))
        (resolvent hw0 hw1 lambda hl (Class X)))
      (rat epsilon) := by
  let delta := quarter epsilon
  have hd : (0 : Q') < delta := quarter_positive he
  have hres := residual_small hw0 hw1 lambda hl X delta hd depth
    (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hlim := approximation hw0 hw1 lambda hl X delta hd depth
    (Nat.le_trans (Nat.le_max_left _ _) hn)
  have h := RCle_trans
    (completedDist_triangle hw0 hw1 _
      (dyadic hw0 hw1 depth lambda hl (Class X))
      (representedLimit hw0 hw1 lambda hl X))
    (RCadd_le_add (RCadd_le_add hres hres) (RCadd_le_add hlim hlim))
  rwa [four_quarters] at h

/-- The represented resolvent has a computed original-carrier time-range
witness.  The construction is valid for every original input representative,
including those with a nonzero component in the kernel of T(1). -/
def resolventRange (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) :
    RangeLimit hw0 hw1 (resolvent hw0 hw1 lambda hl (Class X)) :=
  ofLimit hw0 hw1
    (rootPartRange hw0 hw1 lambda hl X)
    (resolvent hw0 hw1 lambda hl (Class X))
    (rangeModulus hw0 hw1 lambda hl X)
    (rootPart_close hw0 hw1 lambda hl X)

#print axioms dyadic_root_residual
#print axioms residual_small
#print axioms rootPartRange
#print axioms rangeModulus
#print axioms rootPart_close
#print axioms resolventRange

end YMGap.Continuum.BF4WilsonAllNomeResolventRange
