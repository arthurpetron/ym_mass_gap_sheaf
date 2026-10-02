/-
# A quantitative Jacobi-factor estimate for original heat widening

For F(a,x)=1+2*a*x+a^2, the normalized factor at a is no larger
than the normalized factor at a^2. On the explicit amplitude block
1/4 <= a <= 3/4 it pays a further factor 1+(1-x)/512.

The estimates are proved from exact rational differences, not supplied
kernel-shape inequalities. They are intended for the original Jacobi
product already identified with the SU(2) heat series. Retaining and
counting enough such factors, bounding the theta height, passing the
limits, and compiling an original Haar square certificate are still
separate obligations. No full heat profile, survival or gap is claimed.
-/

import YMGap.Continuum.ThetaConv
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.SU2HeatJacobiProductWidening

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HKPos (factor two)
open YMGap.Continuum.HKConv (mul_le_mul')
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Exact numerator of the normalized-factor improvement. -/
def gain (a : Q') : Q' := (2*a)*((1-a)*(1-a))*(1+a+a*a)

private theorem factor_gap (a x : Q') :
    factor a 1*factor (a*a) x + -(factor a x*factor (a*a) 1)
      ≈ gain a*(1-x) := by
  unfold factor two gain
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.const 1)) (.mul (.var 0) (.var 0))))
        (.add (.const 1) (.add
          (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.var 1))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))))
      (.neg (.mul
        (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 1)) (.mul (.var 0) (.var 0))))
        (.add (.const 1) (.add
          (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.const 1))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))))))
    (.mul
      (.mul (.mul (.mul (.const 2) (.var 0))
        (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0)))))
        (.add (.add (.const 1) (.var 0)) (.mul (.var 0) (.var 0))))
      (.add (.const 1) (.neg (.var 1))))
    (by decide) (fun | 0 => a | _ => x)

theorem gain_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) : (0 : Q') ≤ gain a :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) ha)
      (SumOfSquares.q_mul_self_nonneg (1-a)))
    (Q'.zero_le_add _ _ (Q'.zero_le_add _ _ Q'.zero_le_one ha)
      (SumOfSquares.q_mul_self_nonneg a))

/-- The original normalized Jacobi factor increases under nome squaring.
The cross multiplication avoids a reciprocal theta or heat floor. -/
theorem factor_squared_nome_order {a x : Q'}
    (ha : (0 : Q') ≤ a) (hx : x ≤ (1 : Q')) :
    factor a x*factor (a*a) 1 ≤ factor a 1*factor (a*a) x := by
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (gain_nonnegative ha) (Q'.sub_nonneg_of_le hx))
    (Q'.ge_of_eqv (factor_gap a x))

private def quarter : Q' := Q'.mkPos 1 4 (by decide)
private def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

private theorem block_gain {a : Q'} (hl : quarter ≤ a) (hu : a ≤ threeQuarters) :
    (Q'.mkPos 1 32 (by decide)) ≤ gain a := by
  have ha : (0 : Q') ≤ a := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ quarter) hl
  have hh : quarter ≤ 1-a := by
    have h := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hu)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : 1-threeQuarters ≈ quarter)) h
  have hh0 : (0 : Q') ≤ 1-a := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ quarter) hh
  have hs : quarter*quarter ≤ (1-a)*(1-a) := mul_le_mul'
    (by decide : (0 : Q') ≤ quarter) hh0 hh hh
  have ht : (1 : Q') ≤ 1+a+a*a := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg 1 a ha)
    (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg a))
  have htwo : 2*quarter ≤ 2*a := Q'.mul_le_mul_of_nonneg_left _ _ _ hl (by decide)
  have hprod := mul_le_mul' (by decide : (0 : Q') ≤ 2*quarter)
    (Q'.mul_nonneg _ _ hh0 hh0) htwo hs
  have h := mul_le_mul' (by decide : (0 : Q') ≤ (2*quarter)*(quarter*quarter))
    (Q'.le_trans' _ _ _ Q'.zero_le_one ht) hprod ht
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by decide : ((2*quarter)*(quarter*quarter))*1 ≈ Q'.mkPos 1 32 (by decide))) h

private theorem block_height {a : Q'} (hl : quarter ≤ a) (hu : a ≤ threeQuarters) :
    factor a 1*factor (a*a) 1 ≤ (16 : Q') := by
  have ha0 : (0 : Q') ≤ a := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ quarter) hl
  have ha1 : a < (1 : Q') := HKPos.q_lt_of_le_of_lt hu (by decide : threeQuarters < (1 : Q'))
  have haa : a*a ≤ a := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_lt ha1) ha0)
    (Q'.le_of_eqv (Q'.mul_one_eqv a))
  have haa0 := Q'.mul_nonneg _ _ ha0 ha0
  have haa1 : a*a < (1 : Q') := HKPos.q_lt_of_le_of_lt haa ha1
  have hf := ThetaConv.factor_le_four ha0 ha1 (Q'.le_refl' (1 : Q'))
  have hg := ThetaConv.factor_le_four haa0 haa1 (Q'.le_refl' (1 : Q'))
  exact Q'.le_trans' _ _ _
    (mul_le_mul' (Q'.le_of_lt (HKPos.factor_pos ha0 ha1 (by decide)))
      (by decide : (0 : Q') ≤ ThetaConv.four) hf hg)
    (Q'.le_of_eqv (by decide : ThetaConv.four*ThetaConv.four ≈ (16 : Q')))

/-- A genuine quantitative factor bound on an explicit amplitude block.
Both x endpoints are allowed; no near-one nome constant is opaque. -/
theorem factor_squared_nome_block {a x : Q'}
    (hl : Q'.mkPos 1 4 (by decide) ≤ a) (hu : a ≤ Q'.mkPos 3 4 (by decide))
    (hx : x ≤ (1 : Q')) :
    (factor a x*factor (a*a) 1)*(512+(1-x)) ≤
      512*(factor a 1*factor (a*a) x) := by
  have ha0 : (0 : Q') ≤ a := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ quarter) hl
  have ha1 : a < (1 : Q') := HKPos.q_lt_of_le_of_lt hu (by decide : threeQuarters < (1 : Q'))
  have haa : a*a ≤ a := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_lt ha1) ha0)
    (Q'.le_of_eqv (Q'.mul_one_eqv a))
  have hB : (0 : Q') ≤ factor (a*a) 1 := Q'.le_of_lt
    (HKPos.factor_pos (Q'.mul_nonneg _ _ ha0 ha0) (HKPos.q_lt_of_le_of_lt haa ha1) (by decide))
  have hgain : (16 : Q') ≤ 512*gain a := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by decide : 512*(Q'.mkPos 1 32 (by decide)) ≈ (16 : Q')))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (block_gain hl hu) (by decide))
  have hbudget : (0 : Q') ≤ 512*gain a + -(factor a 1*factor (a*a) 1) :=
    Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ (block_height hl hu) hgain)
  let z := 1-x
  have hz : (0 : Q') ≤ z := Q'.sub_nonneg_of_le hx
  have hgap : (0 : Q') ≤
      (512*gain a + -(factor a 1*factor (a*a) 1))*z +
      ((2*a)*factor (a*a) 1)*(z*z) := Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hbudget hz)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) ha0) hB)
      (Q'.mul_nonneg _ _ hz hz))
  have he : 512*(factor a 1*factor (a*a) x) +
      -((factor a x*factor (a*a) 1)*(512+z)) ≈
      (512*gain a + -(factor a 1*factor (a*a) 1))*z +
      ((2*a)*factor (a*a) 1)*(z*z) := by
    have hg := factor_gap a x
    have hfac : factor a 1 + -(factor a x) ≈ (2*a)*z := by
      unfold factor two z
      exact poly_identity_of_normal_eq
        (.add (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.const 1)) (.mul (.var 0) (.var 0))))
          (.neg (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 1)) (.mul (.var 0) (.var 0))))))
        (.mul (.mul (.const 2) (.var 0)) (.add (.const 1) (.neg (.var 1))))
        (by decide) (fun | 0 => a | _ => x)
    have hsplit := poly_identity_of_normal_eq
      (.add (.mul (.const 512) (.var 0))
        (.neg (.mul (.var 1) (.add (.const 512) (.var 2)))))
      (.add (.mul (.const 512) (.add (.var 0) (.neg (.var 1))))
        (.neg (.mul (.var 1) (.var 2)))) (by decide)
      (fun | 0 => factor a 1*factor (a*a) x | 1 => factor a x*factor (a*a) 1 | _ => z)
    have hrewrite :
        512*(factor a 1*factor (a*a) x + -(factor a x*factor (a*a) 1)) +
          -(factor a x*factor (a*a) 1*z) ≈
        512*(gain a*z) + -(factor a x*factor (a*a) 1*z) :=
      Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left 512 _ _ hg)
    have hlast := poly_identity_of_normal_eq
      (.add (.mul (.const 512) (.mul (.var 0) (.var 1)))
        (.neg (.mul (.mul (.var 2) (.var 3)) (.var 1))))
      (.add (.mul (.add (.mul (.const 512) (.var 0)) (.neg (.mul (.var 4) (.var 3)))) (.var 1))
        (.mul (.mul (.add (.var 4) (.neg (.var 2))) (.var 3)) (.var 1))) (by decide)
      (fun | 0 => gain a | 1 => z | 2 => factor a x | 3 => factor (a*a) 1 | _ => factor a 1)
    exact Q'.eqv_trans _ _ _ hsplit (Q'.eqv_trans _ _ _ hrewrite
      (Q'.eqv_trans _ _ _ hlast
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ _ hfac))
            (poly_identity_of_normal_eq
              (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 1))
              (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
              (by decide) (fun | 0 => 2*a | 1 => z | _ => factor (a*a) 1))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hgap (Q'.ge_of_eqv he))

end YMGap.Continuum.SU2HeatJacobiProductWidening

#print axioms YMGap.Continuum.SU2HeatJacobiProductWidening.gain_nonnegative
#print axioms YMGap.Continuum.SU2HeatJacobiProductWidening.factor_squared_nome_order
#print axioms YMGap.Continuum.SU2HeatJacobiProductWidening.factor_squared_nome_block
