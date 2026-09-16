/-
# The existing absolute window alone cannot force a small conditional norm

Use the actual four positive weights [[M,m],[m,M]], with m=headFloor(w)
and M=prefixCap(w). Its centered sign input has unit squared norm; the
computed conditional average has squared norm at least 961/1089 > 7/8.
The weights obey the existing one-face absolute window at every 0<w<1.

Thus a universal half-squared-norm inference from only that window already
fails on this explicit finite family. This family is NOT the original
Yang--Mills law. Nothing here bounds actual Yang--Mills influence, refutes
a sharper small-nome window, or decides spatial mixing or the mass gap.
-/

import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.RationalTwoStateWindowWitness

namespace YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.RationalTwoStateWindowWitness

local infix:50 " ≈ " => Q'.eqv

private theorem window_order {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : headFloor w ≤ prefixCap w :=
  Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1)
    (Q'.le_trans' _ _ _ (by decide : Q'.mkPos 1 32 (by decide) ≤ (1 : Q'))
      (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1))

private theorem witness_sum_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < prefixCap w + headFloor w :=
  sum_positive _ _ (headFloor_positive hw0 hw1) (window_order hw0 hw1)

private theorem rho_lower (m M : Q') (hs : (0 : Q') < M+m)
    (h32 : (32 : Q') * m ≤ M) :
    Q'.mkPos 31 33 (by decide) ≤ rho m M hs := by
  have hcross : (31 : Q') * (M+m) ≤ (33 : Q') * (M + -m) := by
    apply Q'.le_of_sub_nonneg
    have he : (33 : Q') * (M + -m) + -((31 : Q') * (M+m)) ≈
        (2 : Q') * (M + -((32 : Q') * m)) :=
      poly_identity_of_normal_eq
        (.add (.mul (.const 33) (.add (.var 1) (.neg (.var 0))))
          (.neg (.mul (.const 31) (.add (.var 1) (.var 0)))))
        (.mul (.const 2) (.add (.var 1) (.neg (.mul (.const 32) (.var 0)))))
        (by decide) (fun | 0 => m | _ => M)
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le h32)) (Q'.ge_of_eqv he)
  change Q'.mkPos 31 33 (by decide) ≤ Q'.divPos (M + -m) (M+m) hs
  apply Q'.le_divPos_of_mul_le
  apply HKConvGen.mul_le_mul_left_cancel (by decide : (0 : Q') < 33)
  have he : (33 : Q') * (Q'.mkPos 31 33 (by decide) * (M+m)) ≈
      (31 : Q') * (M+m) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (by decide))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hcross

/-- The computed conditional squared norm in the actual four-weight law. -/
def conditionalSquaredNorm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Q' :=
  let hs := witness_sum_positive hw0 hw1
  expectation (headFloor w) (prefixCap w) hs
    (fun i _ => conditionalSign (headFloor w) (prefixCap w) hs i *
      conditionalSign (headFloor w) (prefixCap w) hs i)

/-- Every weight of the constructed finite witness lies in the named
window and is strictly positive. No claim about physical weights is made. -/
theorem witness_weight_window {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (i j : Bool) :
    (0 : Q') < weight (headFloor w) (prefixCap w) i j ∧
      headFloor w ≤ weight (headFloor w) (prefixCap w) i j ∧
      weight (headFloor w) (prefixCap w) i j ≤ prefixCap w :=
  ⟨weight_positive _ _ (headFloor_positive hw0 hw1) (window_order hw0 hw1) i j,
    weight_window _ _ (window_order hw0 hw1) i j⟩

/-- The lower bound is on the evaluated conditional norm, not an assumed
influence parameter. Its input is the centered unit sign from the witness. -/
theorem conditionalSquaredNorm_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.mkPos 961 1089 (by decide) ≤ conditionalSquaredNorm hw0 hw1 := by
  let hs := witness_sum_positive hw0 hw1
  have hr := rho_lower (headFloor w) (prefixCap w) hs
    (thirtyTwo_mul_headFloor_le_prefixCap hw0 hw1)
  have hn : (0 : Q') ≤ rho (headFloor w) (prefixCap w) hs :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ Q'.mkPos 31 33 (by decide)) hr
  have hsq := HKConv.mul_le_mul' (by decide : (0 : Q') ≤ Q'.mkPos 31 33 (by decide)) hn hr hr
  exact Q'.le_trans' _ _ _
    (by decide : Q'.mkPos 961 1089 (by decide) ≤
      Q'.mkPos 31 33 (by decide) * Q'.mkPos 31 33 (by decide))
    (Q'.le_trans' _ _ _ hsq
      (Q'.ge_of_eqv (conditional_squared_norm (headFloor w) (prefixCap w) hs)))

theorem conditionalSquaredNorm_gt_sevenEighths {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.mkPos 7 8 (by decide) < conditionalSquaredNorm hw0 hw1 := by
  apply Int.not_le.mp
  intro h
  have hbad := Q'.le_trans' _ _ _ (conditionalSquaredNorm_lower hw0 hw1) h
  exact (by decide : ¬ (Q'.mkPos 961 1089 (by decide) ≤ Q'.mkPos 7 8 (by decide))) hbad

/-- A universal inference from this absolute window to half the input's
squared norm already fails on literal positive two-state laws. The input
sign is centered and has unit squared norm by the witness's exact theorems.
No universal family of Yang--Mills laws is asserted here. -/
theorem not_absolute_window_half_norm_inference {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ¬ (∀ (a b : Q') (hs : (0 : Q') < b+a),
      (∀ i j, headFloor w ≤ weight a b i j ∧ weight a b i j ≤ prefixCap w) →
      expectation a b hs (fun i _ => conditionalSign a b hs i * conditionalSign a b hs i) ≤
        HalfPow.half * expectation a b hs (fun _ j => sign j * sign j)) := by
  intro h
  let hs := witness_sum_positive hw0 hw1
  have hh := h (headFloor w) (prefixCap w) hs
    (fun i j => (witness_weight_window hw0 hw1 i j).2)
  have he : HalfPow.half * expectation (headFloor w) (prefixCap w) hs
      (fun _ j => sign j * sign j) ≈ HalfPow.half :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (sign_squared_norms (headFloor w) (prefixCap w) hs).2)
      (Q'.mul_one_eqv _)
  have hbad := Q'.le_trans' _ _ _ (conditionalSquaredNorm_lower hw0 hw1)
    (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv he))
  exact (by decide : ¬ (Q'.mkPos 961 1089 (by decide) ≤ HalfPow.half)) hbad

end YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction

#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction.conditionalSquaredNorm
#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction.witness_weight_window
#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction.conditionalSquaredNorm_lower
#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction.conditionalSquaredNorm_gt_sevenEighths
#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowInfluenceObstruction.not_absolute_window_half_norm_inference
