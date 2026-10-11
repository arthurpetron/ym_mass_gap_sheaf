/-
# Four-link kernel product on rational unit quaternions

Each factor is the actual scalar polynomial `(1+r)/2`. Its four-factor
product belongs to `[0,1]`, and the scalar deficit of the ordered Hamilton
word is at most `32*(1-product)`. Repetitions and inverse factors are allowed;
no commutation, statistical independence, Haar premise or action replacement
is used. This is a pointwise input to finite polynomial localization only.
-/

import YMGap.RepTheory.RationalQuaternionFourFactorDeficit
import YMGap.RepTheory.RationalQuaternionNormRepair
import YMGap.Constructive.HalfPow

namespace YMGap.RepTheory.RationalQuaternionFourKernelProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair (coordinate_square_le)
open YMGap.RepTheory.RationalQuaternionFourFactorDeficit (four_factor_deficit)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩

/-- The original one-link scalar kernel base. -/
def base (a : UnitNorm) : Q' := half*((1 : Q')+a.val.r)

/-- Balanced product of the four actual scalar bases. -/
def product (a b c d : UnitNorm) : Q' := (base a*base b)*(base c*base d)

private theorem scalar_abs_bound (a : UnitNorm) : Q'.abs a.val.r ≤ (1 : Q') := by
  have hs : a.val.r*a.val.r ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (coordinate_square_le a.val 0) (Q'.le_of_eqv a.unitNorm)
  have ha : Q'.abs a.val.r*Q'.abs a.val.r ≈ a.val.r*a.val.r := by
    unfold Q'.abs
    split
    · exact Q'.eqv_refl _
    · exact poly_identity_of_normal_eq
        (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
        (by decide) (fun _ => a.val.r)
  exact CReal.le_of_sq_le_sq (by decide) (Q'.abs_nonneg _)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
      (Q'.le_trans' _ _ _ hs (by decide : (1 : Q') ≤ 1*1)))

/-- Both endpoints of the base interval are included. -/
theorem base_bounds (a : UnitNorm) : (0 : Q') ≤ base a ∧ base a ≤ (1 : Q') := by
  have hu : a.val.r ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) (scalar_abs_bound a)
  have hn : -(1 : Q') ≤ a.val.r :=
    Q'.le_trans' _ _ _
      (Q'.neg_le_neg (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) (scalar_abs_bound a)))
      (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  have hp : (0 : Q') ≤ (1 : Q')+a.val.r :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ 1 + -1))
      (Q'.add_le_add_left 1 _ _ hn)
  refine ⟨Q'.mul_nonneg _ _ (by decide) hp, ?_⟩
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ half
      (Q'.add_le_add_left 1 _ _ hu) (by decide))
    (Q'.le_of_eqv (by decide : half*((1 : Q')+1) ≈ 1))

private theorem mul_le_left (x y : Q') (hx : (0 : Q') ≤ x) (hy : y ≤ (1 : Q')) :
    x*y ≤ x :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ x hy hx)
    (Q'.le_of_eqv (Q'.mul_one_eqv x))

private theorem mul_le_right (x y : Q') (hx : x ≤ (1 : Q')) (hy : (0 : Q') ≤ y) :
    x*y ≤ y :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ y hx hy)
    (Q'.le_of_eqv (Q'.one_mul_eqv y))

private theorem mul_bounds (x y : Q')
    (hx : (0 : Q') ≤ x ∧ x ≤ (1 : Q')) (hy : (0 : Q') ≤ y ∧ y ≤ (1 : Q')) :
    (0 : Q') ≤ x*y ∧ x*y ≤ (1 : Q') :=
  ⟨Q'.mul_nonneg _ _ hx.1 hy.1, Q'.le_trans' _ _ _ (mul_le_left x y hx.1 hy.2) hx.2⟩

/-- The product remains in the unit interval without distinctness assumptions. -/
theorem product_bounds (a b c d : UnitNorm) :
    (0 : Q') ≤ product a b c d ∧ product a b c d ≤ (1 : Q') :=
  mul_bounds _ _ (mul_bounds _ _ (base_bounds a) (base_bounds b))
    (mul_bounds _ _ (base_bounds c) (base_bounds d))

private theorem product_le_bases (a b c d : UnitNorm) :
    (product a b c d ≤ base a ∧ product a b c d ≤ base b) ∧
    (product a b c d ≤ base c ∧ product a b c d ≤ base d) := by
  have hab := mul_bounds _ _ (base_bounds a) (base_bounds b)
  have hcd := mul_bounds _ _ (base_bounds c) (base_bounds d)
  have hl : product a b c d ≤ base a*base b := mul_le_left _ _ hab.1 hcd.2
  have hr : product a b c d ≤ base c*base d := mul_le_right _ _ hab.2 hcd.1
  exact ⟨⟨Q'.le_trans' _ _ _ hl (mul_le_left _ _ (base_bounds a).1 (base_bounds b).2),
    Q'.le_trans' _ _ _ hl (mul_le_right _ _ (base_bounds a).2 (base_bounds b).1)⟩,
    ⟨Q'.le_trans' _ _ _ hr (mul_le_left _ _ (base_bounds c).1 (base_bounds d).2),
    Q'.le_trans' _ _ _ hr (mul_le_right _ _ (base_bounds c).2 (base_bounds d).1)⟩⟩

private theorem base_deficit (a : UnitNorm) :
    (1 : Q') + -a.val.r ≈ 2*((1 : Q') + -base a) := by
  have h := poly_identity_of_normal_eq
    (.mul (.var 2) (.add (.var 3) (.neg (.mul (.var 1) (.add (.var 3) (.var 0))))))
    (.add (.mul (.var 2) (.add (.var 3) (.neg (.mul (.var 1) (.var 3)))))
      (.neg (.mul (.mul (.var 2) (.var 1)) (.var 0))))
    (by decide) (fun | 0 => a.val.r | 1 => half | 2 => 2 | _ => 1)
  have hleft : 2*((1 : Q') + -base a) ≈ (1 : Q') + -a.val.r :=
    Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (by decide : (2 : Q')*((1 : Q') + -(half*1)) ≈ 1)
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ a.val.r
            (by decide : (2 : Q')*half ≈ 1))))
        (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a.val.r))))
  exact Q'.eqv_symm hleft

private theorem deficit_le (a : UnitNorm) (u : Q') (hu : u ≤ base a) :
    (1 : Q') + -a.val.r ≤ 2*((1 : Q') + -u) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (base_deficit a))
    (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hu)) (by decide))

/-- Ordered word deficit paid by the joint scalar kernel-product deficit.
Inverses preserve the base scalar and may be supplied as any factors. -/
theorem four_word_deficit (a b c d : UnitNorm) :
    (1 : Q') + -(UnitNorm.mul (UnitNorm.mul (UnitNorm.mul a b) c) d).val.r ≤
      32*((1 : Q') + -product a b c d) := by
  have hb := product_le_bases a b c d
  have hs := Q'.add_le_add
    (Q'.add_le_add (deficit_le a _ hb.1.1) (deficit_le b _ hb.1.2))
    (Q'.add_le_add (deficit_le c _ hb.2.1) (deficit_le d _ hb.2.2))
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ 4 hs (by decide)
  have hfinish :
      (4 : Q')*((2*((1 : Q') + -product a b c d)+2*((1 : Q') + -product a b c d))+
        (2*((1 : Q') + -product a b c d)+2*((1 : Q') + -product a b c d))) ≈
      32*((1 : Q') + -product a b c d) :=
    poly_identity_of_normal_eq
      (.mul (.const 4) (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
        (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))))
      (.mul (.const 32) (.var 0)) (by decide)
      (fun _ => (1 : Q') + -product a b c d)
  exact Q'.le_trans' _ _ _ (four_factor_deficit a b c d)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hfinish))

#print axioms base
#print axioms product
#print axioms base_bounds
#print axioms product_bounds
#print axioms four_word_deficit

end YMGap.RepTheory.RationalQuaternionFourKernelProduct
