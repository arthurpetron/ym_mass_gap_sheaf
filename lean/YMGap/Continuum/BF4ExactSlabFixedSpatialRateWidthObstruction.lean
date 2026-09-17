/-
# The existing all-nome comparison rate degenerates with spatial width

The original kinetic floor/cap comparison has margin at most
(1/32)^numberOfTemporalFaces, hence at most (1/32)^width. An explicit
width modulus makes this computed margin arbitrarily small. For every
proposed common rate q<1, a returned width violates mixRate <= q.

The consumer being excluded is a volume-uniform promotion of the existing
fixed-width separated-covariance bound. This is ONLY a theorem about that
computed bound: it is neither a lower bound on actual correlations nor a
refutation of a stronger Yang--Mills spectral gap. No action, transfer,
frontier field, small-nome estimate or continuum statement is changed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.CasimirMoment
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

local infix:50 " ≈ " => Q'.eqv

/-- A literal row of distinct temporal plaquettes already has width faces. -/
theorem width_le_temporalFaces_length (width : Nat) :
    width ≤ (temporalFaces width).length := by
  let f : Nat → Z4Plaq := fun i => ((i, 0, 0, 0), Z4Plane.p03)
  have hn : ((List.range width).map f).Nodup :=
    CayleyPruferInjection.nodup_map_of_injOn f _
      (CayleyParentInj.range_nodup width)
      (fun a _ b _ h => congrArg (fun p : Z4Plaq => p.1.1) h)
  have hs : ∀ p, p ∈ (List.range width).map f → p ∈ temporalFaces width := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hiw : i < width := List.mem_range.mp hi
    apply (temporalFaces_mem_iff width (f i)).mpr
    change i < width ∧ 0 < width ∧ 0 < width ∧ 0 = 0 ∧ Dir4.x3 = Dir4.x3
    exact ⟨hiw, by omega, by omega, rfl, rfl⟩
  have h := CayleyPruferInjection.nodup_subset_length_le
    ((List.range width).map f) (temporalFaces width) hn hs
  simpa only [List.length_map, List.length_range] using h

/-- This base bounds the already defined margin; it is not a new mixing rate. -/
def marginBase : Q' := Q'.mkPos 1 32 (by decide)

/-- The complete kinetic product pays the absolute-window loss on every face. -/
theorem mixFraction_le_face_power {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    mixFraction hw0 hw1 width ≤ marginBase ^ (temporalFaces width).length := by
  have hcap : (1 : Q') ≤ kineticCap w width :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (CasimirMoment.one_pow_eqv _))
      (HKConv.pow_le_pow_base (by decide : (0 : Q') ≤ 1)
        (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1) _)
  have hfrac := Q'.le_of_lt (mixFraction_positive hw0 hw1 width)
  have hfloor : kineticFloor w width ≤ marginBase ^ (temporalFaces width).length :=
    HKConv.pow_le_pow_base (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (headFloor_le_oneThirtySecond hw0 hw1) _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hcap hfrac)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (mixFraction_mul_cap hw0 hw1 width)) hfloor))

theorem mixFraction_le_width_power {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    mixFraction hw0 hw1 width ≤ marginBase ^ width :=
  Q'.le_trans' _ _ _ (mixFraction_le_face_power hw0 hw1 width)
    (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ marginBase)
      (by decide : marginBase ≤ (1 : Q')) (width_le_temporalFaces_length width))

/-- Computed from tolerance alone, valid for every rational nome 0<w<1. -/
def widthModulus (epsilon : Q') : Nat := HKConvGen.powBaseCutoff marginBase epsilon

theorem mixFraction_le_epsilon {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (width : Nat)
    (hwidth : widthModulus epsilon ≤ width) :
    mixFraction hw0 hw1 width ≤ epsilon :=
  Q'.le_trans' _ _ _ (mixFraction_le_width_power hw0 hw1 width)
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ marginBase)
        (by decide : marginBase ≤ (1 : Q')) hwidth)
      (HKConvGen.pow_base_le_cutoff (by decide : (0 : Q') < marginBase)
        (by decide : marginBase < (1 : Q')) he))

/-- The existing computed rate approaches one; its actual operator need not. -/
theorem one_sub_epsilon_le_mixRate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (width : Nat)
    (hwidth : widthModulus epsilon ≤ width) :
    1 + -epsilon ≤ mixRate hw0 hw1 width :=
  Q'.add_le_add (Q'.le_refl' 1)
    (Q'.neg_le_neg (mixFraction_le_epsilon hw0 hw1 epsilon he width hwidth))

/-- A positive explicit width refuting any proposed common rate q<1. -/
def violatingWidth (q : Q') : Nat := widthModulus (HalfPow.half * (1 + -q)) + 1

theorem rate_not_le_at_violatingWidth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q : Q') (hq : q < (1 : Q')) :
    ¬ (mixRate hw0 hw1 (violatingWidth q) ≤ q) := by
  intro h
  let e := HalfPow.half * (1 + -q)
  have hm := HKPos.one_sub_pos hq
  have he : (0 : Q') < e := ExpNeg.half_mul_pos _ hm
  have hf := mixFraction_le_epsilon hw0 hw1 e he (violatingWidth q) (Nat.le_succ _)
  have hc : mixRate hw0 hw1 (violatingWidth q) +
      mixFraction hw0 hw1 (violatingWidth q) ≈ 1 :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0))) (.var 0)) (.const 1)
      (by decide) (fun _ => mixFraction hw0 hw1 (violatingWidth q))
  have hsum : (1 : Q') ≤ q + mixFraction hw0 hw1 (violatingWidth q) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc) (Q'.add_le_add_right _ _ _ h)
  have hbad : 1 + -q ≤ e := Q'.le_trans' _ _ _ (Q'.sub_le_of_le_add hsum) hf
  have hlt : e < 1 + -q := ClusteringImpliesGap.lt_of_lt_of_le
    (ClusteringImpliesGap.mul_lt_mul_of_pos_right hm
      (by decide : HalfPow.half < (1 : Q')))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Int.not_lt.mpr hbad hlt

/-- Fixed-nome, late-cutoff uniformity of this bound does NOT extend over width. -/
theorem no_width_uniform_computed_rate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q : Q') (hq : q < (1 : Q')) :
    ¬ (∀ width, 0 < width → mixRate hw0 hw1 width ≤ q) := by
  intro h
  exact rate_not_le_at_violatingWidth hw0 hw1 q hq
    (h (violatingWidth q) (Nat.succ_pos _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.width_le_temporalFaces_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.marginBase
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.mixFraction_le_face_power
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.mixFraction_le_width_power
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.widthModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.mixFraction_le_epsilon
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.one_sub_epsilon_le_mixRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.violatingWidth
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.rate_not_le_at_violatingWidth
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction.no_width_uniform_computed_rate
