/-
# The existing collar coefficient cannot pay the proposed box-overlap cost

This module compares computed certificate NUMBERS. For L >= 1 and
L <= 6*size, the existing supportRatio obeys L*supportRatio <= 1.
Consequently its proposed scaled patch margin
  L^2*supportRatio - (18*L-3)
is at most -14. In particular this applies to the full box budget 4*L^4.

The factor 18*L-3 comes from the UNFORMALIZED overlapping-box calculation in
audits/RESEARCH-COLLECTIVE-PATCH-THRESHOLD-2026-09-30.md. No patch operator,
patch spectral gap, or overlap theorem is asserted here. Even a valid join
that delivered exactly this conservative coefficient would fail that test.
This is NOT an upper bound on an actual gap, or a Yang--Mills no-go theorem.
Useful original-action collective control and physical scaling remain open.
-/

import YMGap.Continuum.BF4ExactSlabLocalChebyshevObstruction
import YMGap.Constructive.GeomBeatsLinear

namespace YMGap.Continuum.BF4ExactSlabPatchCollarBudgetObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabLocalChebyshevObstruction

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Linear rescaling cannot compensate the actual conservative collar cost.
The support budget and rescaling length remain explicit. -/
theorem linear_scaled_ratio_le_one (size L : Nat) (hL : L <= 6*size) :
    Q'.ofNat L * supportRatio hw0 hw1 size <= (1 : Q') := by
  have hc := supportRatio_le_eighth_pow hw0 hw1 size L hL
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat L) hc
    (ClusterCount.ofNat_nonneg L)
  exact Q'.le_trans' _ _ _ h
    (geom_beats_linear (s := Q'.mkPos 1 8 (by decide)) (by decide) (by decide) L)

/-- This is the numerator of a CANDIDATE margin, not an actual gap.
It stays negative at every nome and every permitted support/length budget. -/
theorem scaled_margin_le_neg_fourteen (size L : Nat)
    (hpos : 1 <= L) (hL : L <= 6*size) :
    Q'.ofNat L * (Q'.ofNat L * supportRatio hw0 hw1 size) +
      -(18 * Q'.ofNat L + -(3 : Q')) <= -(14 : Q') := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat L)
    (linear_scaled_ratio_le_one hw0 hw1 size L hL)
    (ClusterCount.ofNat_nonneg L)
  have hside : Q'.ofNat L * (Q'.ofNat L * supportRatio hw0 hw1 size) <= Q'.ofNat L :=
    Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hn : Q'.ofNat L + -(18 * Q'.ofNat L + -(3 : Q')) <= -(14 : Q') := by
    have hl : (1 : Q') <= Q'.ofNat L := by
      change (1 : Int) * 1 <= (L : Int) * 1
      omega
    apply Q'.le_of_sub_nonneg
    have he : Q'.eqv
        (-(14 : Q') + -(Q'.ofNat L + -(18 * Q'.ofNat L + -(3 : Q'))))
        (17 * (Q'.ofNat L + -(1 : Q'))) :=
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.neg (.const 14))
          (.neg (.add (.var 0) (.neg (.add (.mul (.const 18) (.var 0)) (.neg (.const 3)))))))
        (.mul (.const 17) (.add (.var 0) (.neg (.const 1))))
        (by decide) (fun _ => Q'.ofNat L)
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') <= 17) (Q'.sub_nonneg_of_le hl))
      (Q'.ge_of_eqv he)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hside) hn

private theorem side_le_box_budget (L : Nat) (hL : 1 <= L) : L <= 6*(4*L^4) := by
  have hcube : 1 <= L^3 := Nat.succ_le_of_lt (Nat.pow_pos (by omega : 0 < L))
  have hp : L <= L^4 := by
    have hm := Nat.mul_le_mul_left L hcube
    simpa only [Nat.mul_one, Nat.pow_succ, Nat.mul_comm] using hm
  omega

/-- The full four-direction box budget cannot pass the proposed overlap
test at ANY box side or strict nome. Boundary improvements or a sharper
coefficient are not excluded by this scalar statement. -/
theorem full_box_budget_margin_le_neg_fourteen (L : Nat) (hL : 1 <= L) :
    Q'.ofNat L * (Q'.ofNat L * supportRatio hw0 hw1 (4*L^4)) +
      -(18 * Q'.ofNat L + -(3 : Q')) <= -(14 : Q') :=
  scaled_margin_le_neg_fourteen hw0 hw1 (4*L^4) L hL (side_le_box_budget L hL)

#print axioms linear_scaled_ratio_le_one
#print axioms scaled_margin_le_neg_fourteen
#print axioms full_box_budget_margin_le_neg_fourteen

end YMGap.Continuum.BF4ExactSlabPatchCollarBudgetObstruction
