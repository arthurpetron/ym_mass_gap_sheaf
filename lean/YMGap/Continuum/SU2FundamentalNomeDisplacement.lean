/-
# Fundamental SU(2) nome displacement

The first nonvacuum heat coefficient is exactly `2*w^3`.  On the rational
unit interval its displacement from the flat value is therefore nonnegative
and at most `6*(1-w)`, by the exact factorization
`1-w^3 = (1-w)*(1+w+w^2)`.

This is only a scalar nome estimate.  It is not a Wilson-loop variance bound,
a spectral gap, or a continuum statement.
-/

import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2FundamentalNomeDisplacement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW coeffW_one)
open YMGap.Continuum.HeatKernelGap (heatKernelSep qpow_le_one)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem heatKernelSep_cube (w : Q') :
    heatKernelSep w ≈ (w * w) * w := by
  unfold heatKernelSep RGTransport.qpow
  exact Q'.mul_eqv_congr_right _ _ w
    (Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w))

private theorem one_sub_cube_factor (w : Q') :
    (1 : Q') + -(heatKernelSep w) ≈
      (1 + -w) * (1 + w + w * w) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _
      (Q'.neg_eqv_congr _ _ (heatKernelSep_cube w))) ?_
  exact poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 0)) (.var 0))))
    (.mul (.add (.const 1) (.neg (.var 0)))
      (.add (.add (.const 1) (.var 0)) (.mul (.var 0) (.var 0))))
    (by decide) (fun _ => w)

private theorem displacement_twice_margin (w : Q') :
    (2 : Q') + -(coeffW w 1) ≈ 2 * (1 + -(heatKernelSep w)) := by
  rw [coeffW_one]
  change (2 : Q') + -(2 * heatKernelSep w) ≈ 2 * (1 + -(heatKernelSep w))
  exact poly_identity_of_normal_eq
    (.add (.const 2) (.neg (.mul (.const 2) (.var 0))))
    (.mul (.const 2) (.add (.const 1) (.neg (.var 0))))
    (by decide) (fun _ => heatKernelSep w)

/-- On `0 ≤ w ≤ 1`, the fundamental coefficient does not exceed its
flat-value coefficient two. -/
theorem displacement_nonnegative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤ 2 + -(coeffW w 1) := by
  have hsep : heatKernelSep w ≤ (1 : Q') := qpow_le_one hw0 hw1 3
  have hmargin : (0 : Q') ≤ 1 + -(heatKernelSep w) :=
    Q'.sub_nonneg_of_le hsep
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg 2 (1 + -(heatKernelSep w)) (by decide) hmargin)
    (Q'.ge_of_eqv (displacement_twice_margin w))

/-- The exact first-mode displacement is at most its endpoint-linear nome
modulus `6*(1-w)`. -/
theorem displacement_le_six_one_sub {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (2 : Q') + -(coeffW w 1) ≤ 6 * (1 + -w) := by
  have hw2 : w * w ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg hw1 hw1 (by decide) hw0)
      (Q'.le_of_eqv (Q'.mul_one_eqv 1))
  have hsum : 1 + w + w * w ≤ (3 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.add_le_add (Q'.le_refl' 1) hw1) hw2)
      (by decide)
  have hmargin : (0 : Q') ≤ 1 + -w := Q'.sub_nonneg_of_le hw1
  have hfactor : (1 + -w) * (1 + w + w * w) ≤ (1 + -w) * 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsum hmargin
  have hone : 1 + -(heatKernelSep w) ≤ 3 * (1 + -w) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_cube_factor w))
      (Q'.le_trans' _ _ _ hfactor
        (Q'.le_of_eqv (Q'.mul_comm_eqv (1 + -w) 3)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hone (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (displacement_twice_margin w))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.mul (.const 3) (.var 0)))
        (.mul (.const 6) (.var 0))
        (by decide) (fun _ => 1 + -w))))

/-- The path-length-scaled form used by the Wilson kinetic increment. -/
theorem scaled_displacement_le {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (L : Nat) :
    (4 : Q') * (Q'.ofNat L * Q'.ofNat L) * (2 + -(coeffW w 1)) ≤
      24 * (Q'.ofNat L * Q'.ofNat L) * (1 + -w) := by
  let s : Q' := 4 * (Q'.ofNat L * Q'.ofNat L)
  have hn : (0 : Q') ≤ Q'.ofNat L := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg L
  have hs : (0 : Q') ≤ s :=
    Q'.mul_nonneg 4 _ (by decide) (Q'.mul_nonneg _ _ hn hn)
  have h := Q'.mul_le_mul_of_nonneg_left _ _ s
    (displacement_le_six_one_sub hw0 hw1) hs
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_refl _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 4) (.mul (.var 0) (.var 0)))
          (.mul (.const 6) (.var 1)))
        (.mul (.mul (.const 24) (.mul (.var 0) (.var 0))) (.var 1))
        (by decide) (fun | 0 => Q'.ofNat L | _ => 1 + -w))))

end YMGap.Continuum.SU2FundamentalNomeDisplacement

#print axioms YMGap.Continuum.SU2FundamentalNomeDisplacement.displacement_nonnegative
#print axioms YMGap.Continuum.SU2FundamentalNomeDisplacement.displacement_le_six_one_sub
#print axioms YMGap.Continuum.SU2FundamentalNomeDisplacement.scaled_displacement_le
