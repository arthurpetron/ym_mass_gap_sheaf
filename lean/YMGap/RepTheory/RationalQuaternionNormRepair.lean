/-
# Rational norm repair in the actual quaternion coordinates

Every raw rational quaternion is sent to an actual rational unit quaternion.
The sign is chosen from its rational scalar coordinate, never from a real
number.  The exact squared repair error is the squared norm defect divided
by a denominator at least one.  Zero and the equator are included.

This finite algebra is used by the coordinate realization of the existing
point-Cauchy quotient.  It is not a compactness or Haar assertion.
-/

import YMGap.RepTheory.RationalQuaternionCauchyGroup

namespace YMGap.RepTheory.RationalQuaternionNormRepair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)
private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)
private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b := Q'.neg_eqv_congr _ _ h
private theorem sq_nonnegative (a : Q') : (0:Q') ≤ a*a :=
  SumOfSquares.q_mul_self_nonneg a

/-- The four actual coordinates, in scalar-first order. -/
def coordinate (a : RationalQuaternion) (j : Fin 4) : Q' :=
  match j.val with | 0 => a.r | 1 => a.i | 2 => a.j | _ => a.k

theorem coordinate_congr {a b : RationalQuaternion} (h : a.Equivalent b)
    (j : Fin 4) : coordinate a j ≈ coordinate b j := by
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact h.1
  | succ j => cases j with
    | zero => exact h.2.1
    | succ j => cases j with
      | zero => exact h.2.2.1
      | succ j => exact h.2.2.2

private theorem summand_le (a b : Q') (hb : (0:Q') ≤ b) : a ≤ a+b :=
  Q'.add_le_self_of_nonneg a b hb
private theorem right_le (a b : Q') (ha : (0:Q') ≤ a) : b ≤ a+b :=
  Q'.le_trans' _ _ _ (summand_le b a ha) (Q'.le_of_eqv (Q'.add_comm_eqv b a))

theorem coordinate_square_le (a : RationalQuaternion) (j : Fin 4) :
    coordinate a j * coordinate a j ≤ normSq a := by
  have hl : a.r*a.r+a.i*a.i ≤ normSq a :=
    summand_le _ _ (Q'.zero_le_add _ _ (sq_nonnegative _) (sq_nonnegative _))
  have hr : a.j*a.j+a.k*a.k ≤ normSq a :=
    right_le _ _ (Q'.zero_le_add _ _ (sq_nonnegative _) (sq_nonnegative _))
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact Q'.le_trans' _ _ _ (summand_le _ _ (sq_nonnegative _)) hl
  | succ j => cases j with
    | zero => exact Q'.le_trans' _ _ _ (right_le _ _ (sq_nonnegative _)) hl
    | succ j => cases j with
      | zero => exact Q'.le_trans' _ _ _ (summand_le _ _ (sq_nonnegative _)) hr
      | succ j => exact Q'.le_trans' _ _ _ (right_le _ _ (sq_nonnegative _)) hr

private def sub (a b : RationalQuaternion) : RationalQuaternion :=
  ⟨a.r + -b.r,a.i + -b.i,a.j + -b.j,a.k + -b.k⟩

theorem coordinate_difference_square_le (a b : RationalQuaternion) (j : Fin 4) :
    (coordinate a j + -coordinate b j)*(coordinate a j + -coordinate b j) ≤
      distSq a b := by
  have h := coordinate_square_le (sub a b) j
  rcases j with ⟨j,hj⟩
  cases j with
  | zero => exact h
  | succ j => cases j with
    | zero => exact h
    | succ j => cases j with
      | zero => exact h
      | succ j => exact h

theorem distance_nonnegative (a b : RationalQuaternion) : (0:Q') ≤ distSq a b :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (sq_nonnegative _) (sq_nonnegative _))
    (Q'.zero_le_add _ _ (sq_nonnegative _) (sq_nonnegative _))

private theorem diff_square_symm (a b : Q') :
    (a + -b)*(a + -b) ≈ (b + -a)*(b + -a) :=
  poly_identity_of_normal_eq
    ((.var 0 + -(.var 1))*(.var 0 + -(.var 1)))
    ((.var 1 + -(.var 0))*(.var 1 + -(.var 0)))
    (by decide) (fun | 0 => a | _ => b)

theorem distance_symm (a b : RationalQuaternion) : distSq a b ≈ distSq b a :=
  ac (ac (diff_square_symm _ _) (diff_square_symm _ _))
    (ac (diff_square_symm _ _) (diff_square_symm _ _))

private theorem scalar_triangle (a b c : Q') :
    (a + -c)*(a + -c) ≤ 2*((a + -b)*(a + -b))+2*((b + -c)*(b + -c)) := by
  refine Q'.le_trans' _ _ _
    (summand_le ((a + -c)*(a + -c)) _ (sq_nonnegative (a+c + -(2*b)))) ?_
  exact Q'.le_of_eqv (poly_identity_of_normal_eq
    ((.var 0 + -(.var 2))*(.var 0 + -(.var 2))+
      (.var 0+.var 2 + -(2*.var 1))*(.var 0+.var 2 + -(2*.var 1)))
    (2*((.var 0 + -(.var 1))*(.var 0 + -(.var 1)))+
      2*((.var 1 + -(.var 2))*(.var 1 + -(.var 2))))
    (by decide) (fun | 0 => a | 1 => b | _ => c))

theorem distance_triangle (a b c : RationalQuaternion) :
    distSq a c ≤ 2*distSq a b+2*distSq b c := by
  have h := Q'.add_le_add
    (Q'.add_le_add (scalar_triangle a.r b.r c.r) (scalar_triangle a.i b.i c.i))
    (Q'.add_le_add (scalar_triangle a.j b.j c.j) (scalar_triangle a.k b.k c.k))
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  exact poly_identity_of_normal_eq
    (((2*.var 0+2*.var 4)+(2*.var 1+2*.var 5))+
      ((2*.var 2+2*.var 6)+(2*.var 3+2*.var 7)))
    (2*((.var 0+.var 1)+(.var 2+.var 3))+
      2*((.var 4+.var 5)+(.var 6+.var 7))) (by decide)
    (fun
      | 0 => (a.r + -b.r)*(a.r + -b.r)
      | 1 => (a.i + -b.i)*(a.i + -b.i)
      | 2 => (a.j + -b.j)*(a.j + -b.j)
      | 3 => (a.k + -b.k)*(a.k + -b.k)
      | 4 => (b.r + -c.r)*(b.r + -c.r)
      | 5 => (b.i + -c.i)*(b.i + -c.i)
      | 6 => (b.j + -c.j)*(b.j + -c.j)
      | _ => (b.k + -c.k)*(b.k + -c.k))

private def scale (t : Q') (a : RationalQuaternion) : RationalQuaternion :=
  ⟨t*a.r,t*a.i,t*a.j,t*a.k⟩
private def dot (a b : RationalQuaternion) : Q' :=
  (a.r*b.r+a.i*b.i)+(a.j*b.j+a.k*b.k)
private def imagNorm (a : RationalQuaternion) : Q' := (a.i*a.i+a.j*a.j)+a.k*a.k
private def denom (a : RationalQuaternion) : Q' := (1+a.r)*(1+a.r)+imagNorm a
private def numerator (a : RationalQuaternion) : RationalQuaternion :=
  ⟨(1+a.r)*(1+a.r) + -imagNorm a, 2*(1+a.r)*a.i,
    2*(1+a.r)*a.j, 2*(1+a.r)*a.k⟩

private theorem imag_nonnegative (a : RationalQuaternion) : (0:Q') ≤ imagNorm a :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (sq_nonnegative _) (sq_nonnegative _))
    (sq_nonnegative _)
private theorem denom_ge_one (a : RationalQuaternion) (ha : (0:Q') ≤ a.r) :
    (1:Q') ≤ denom a := by
  have hd : (1:Q') ≤ 1+a.r := summand_le _ _ ha
  have hd0 : (0:Q') ≤ 1+a.r := Q'.le_trans' _ _ _ (by decide) hd
  have hsq := Q'.mul_le_mul_of_nonneg hd hd hd0 (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (by decide : (1:Q') ≤ 1*1) hsq)
    (summand_le _ _ (imag_nonnegative a))
private theorem denom_pos (a : RationalQuaternion) (ha : (0:Q') ≤ a.r) :
    (0:Q') < denom a := by
  have hd : (0:Q') < 1+a.r := Q'.pos_add_nonneg (by decide) ha
  exact Q'.pos_add_nonneg (Q'.mul_pos hd hd) (imag_nonnegative a)

private theorem norm_scale (t : Q') (a : RationalQuaternion) :
    normSq (scale t a) ≈ (t*t)*normSq a :=
  poly_identity_of_normal_eq
    (((.var 0*.var 1)*(.var 0*.var 1)+(.var 0*.var 2)*(.var 0*.var 2))+
      ((.var 0*.var 3)*(.var 0*.var 3)+(.var 0*.var 4)*(.var 0*.var 4)))
    ((.var 0*.var 0)*((.var 1*.var 1+.var 2*.var 2)+(.var 3*.var 3+.var 4*.var 4)))
    (by decide) (fun | 0 => t | 1 => a.r | 2 => a.i | 3 => a.j | _ => a.k)

private theorem numerator_norm (a : RationalQuaternion) :
    normSq (numerator a) ≈ denom a*denom a := by
  let d : PE := 1+.var 0
  let s : PE := (.var 1*.var 1+.var 2*.var 2)+.var 3*.var 3
  exact poly_identity_of_normal_eq
    (((d*d + -s)*(d*d + -s)+(2*d*.var 1)*(2*d*.var 1))+
      ((2*d*.var 2)*(2*d*.var 2)+(2*d*.var 3)*(2*d*.var 3)))
    ((d*d+s)*(d*d+s)) (by decide)
    (fun | 0 => a.r | 1 => a.i | 2 => a.j | _ => a.k)

private theorem inverse_square (p t : Q') (h : p*t ≈ 1) : (t*t)*(p*p) ≈ 1 :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    ((.var 1*.var 1)*(.var 0*.var 0)) ((.var 0*.var 1)*(.var 0*.var 1))
    (by decide) (fun | 0 => p | _ => t))
    (Q'.eqv_trans _ _ _ (mc h h) (by decide))

private def northRepair (a : RationalQuaternion) (ha : (0:Q') ≤ a.r) : UnitNorm :=
  ⟨scale (Q'.recipPos (denom a) (denom_pos a ha)) (numerator a), by
    exact Q'.eqv_trans _ _ _ (norm_scale _ _) (Q'.eqv_trans _ _ _
      (mc (Q'.eqv_refl _) (numerator_norm a))
      (inverse_square _ _ (Q'.mul_recipPos_eqv (denom a) (denom_pos a ha))))⟩

private theorem distance_expansion (a b : RationalQuaternion) :
    distSq a b ≈ normSq a+normSq b + -(2*dot a b) :=
  poly_identity_of_normal_eq
    (((.var 0 + -(.var 4))*(.var 0 + -(.var 4))+(.var 1 + -(.var 5))*(.var 1 + -(.var 5)))+
      ((.var 2 + -(.var 6))*(.var 2 + -(.var 6))+(.var 3 + -(.var 7))*(.var 3 + -(.var 7))))
    (((.var 0*.var 0+.var 1*.var 1)+(.var 2*.var 2+.var 3*.var 3))+
      ((.var 4*.var 4+.var 5*.var 5)+(.var 6*.var 6+.var 7*.var 7))+
      -(2*((.var 0*.var 4+.var 1*.var 5)+(.var 2*.var 6+.var 3*.var 7))))
    (by decide) (fun
      | 0 => a.r | 1 => a.i | 2 => a.j | 3 => a.k
      | 4 => b.r | 5 => b.i | 6 => b.j | _ => b.k)

private theorem dot_scale (t : Q') (a b : RationalQuaternion) :
    dot (scale t a) b ≈ t*dot a b :=
  poly_identity_of_normal_eq
    (((.var 0*.var 1)*.var 5+(.var 0*.var 2)*.var 6)+
      ((.var 0*.var 3)*.var 7+(.var 0*.var 4)*.var 8))
    (.var 0*((.var 1*.var 5+.var 2*.var 6)+(.var 3*.var 7+.var 4*.var 8)))
    (by decide) (fun
      | 0 => t | 1 => a.r | 2 => a.i | 3 => a.j | 4 => a.k
      | 5 => b.r | 6 => b.i | 7 => b.j | _ => b.k)

private theorem defect_numerator (a : RationalQuaternion) :
    denom a*(1+normSq a) + -(2*dot (numerator a) a) ≈
      (normSq a + -(1:Q'))*(normSq a + -(1:Q')) := by
  let d : PE := 1+.var 0
  let s : PE := (.var 1*.var 1+.var 2*.var 2)+.var 3*.var 3
  let n : PE := (.var 0*.var 0+.var 1*.var 1)+(.var 2*.var 2+.var 3*.var 3)
  exact poly_identity_of_normal_eq
    ((d*d+s)*(1+n)+ -(2*(((d*d + -s)*.var 0+(2*d*.var 1)*.var 1)+
      ((2*d*.var 2)*.var 2+(2*d*.var 3)*.var 3))))
    ((n + -1)*(n + -1)) (by decide)
    (fun | 0 => a.r | 1 => a.i | 2 => a.j | _ => a.k)

private theorem insert_inverse (p t n v : Q') (h : p*t ≈ 1) :
    1+n + -(2*(t*v)) ≈ t*(p*(1+n) + -(2*v)) := by
  have hi : p*t*(1+n) ≈ 1+n := Q'.eqv_trans _ _ _
    (mc h (Q'.eqv_refl _)) (Q'.one_mul_eqv _)
  exact Q'.eqv_trans _ _ _ (ac (Q'.eqv_symm hi) (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.var 0*.var 1*(1+.var 2)+ -(2*(.var 1*.var 3)))
      (.var 1*(.var 0*(1+.var 2)+ -(2*.var 3))) (by decide)
      (fun | 0 => p | 1 => t | 2 => n | _ => v))

private theorem north_error (a : RationalQuaternion) (ha : (0:Q') ≤ a.r) :
    distSq (northRepair a ha).val a ≈
      ((normSq a + -(1:Q'))*(normSq a + -(1:Q')))*
        Q'.recipPos (denom a) (denom_pos a ha) := by
  let t := Q'.recipPos (denom a) (denom_pos a ha)
  have h1 := distance_expansion (northRepair a ha).val a
  have h2 : normSq (northRepair a ha).val+normSq a +
      -(2*dot (northRepair a ha).val a) ≈ 1+normSq a + -(2*(t*dot (numerator a) a)) :=
    ac (ac (northRepair a ha).unitNorm (Q'.eqv_refl _))
      (nc (mc (Q'.eqv_refl _) (dot_scale t (numerator a) a)))
  have h3 := insert_inverse (denom a) t (normSq a) (dot (numerator a) a)
    (Q'.mul_recipPos_eqv (denom a) (denom_pos a ha))
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3
    (Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl t) (defect_numerator a)) (Q'.mul_comm_eqv _ _))))

private theorem neg_square (a : Q') : (-a)*(-a) ≈ a*a :=
  poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
    (.mul (.var 0) (.var 0))
    (by decide) (fun _ => a)
private theorem norm_neg (a : RationalQuaternion) : normSq (neg a) ≈ normSq a :=
  ac (ac (neg_square _) (neg_square _)) (ac (neg_square _) (neg_square _))
private theorem neg_distance (a b : RationalQuaternion) : distSq (neg a) b ≈ distSq a (neg b) := by
  have h (u v : Q') : (-u + -v)*(-u + -v) ≈ (u + -(-v))*(u + -(-v)) :=
    poly_identity_of_normal_eq ((-(.var 0)+ -(.var 1))*(-(.var 0)+ -(.var 1)))
      ((.var 0+ -(-(.var 1)))*(.var 0+ -(-(.var 1)))) (by decide) (fun | 0 => u | _ => v)
  exact ac (ac (h _ _) (h _ _)) (ac (h _ _) (h _ _))

/-- Computed rational sign; zero uses the northern chart. -/
def repairSign (a : RationalQuaternion) : Bool := decide (¬ (0:Q') ≤ a.r)
private def northern (a : RationalQuaternion) : RationalQuaternion :=
  if repairSign a then neg a else a
private theorem northern_nonnegative (a : RationalQuaternion) : (0:Q') ≤ (northern a).r := by
  unfold northern repairSign
  by_cases h : (0:Q') ≤ a.r
  · simpa only [h,not_true_eq_false,decide_false,Bool.false_eq_true,if_false] using h
  · simpa only [h,not_false_eq_true,decide_true,if_true,neg] using
      (Q'.neg_nonneg_of_not_nonneg h)

/-- Actual unit rational repair of every raw input, including zero. -/
def repair (a : RationalQuaternion) : UnitNorm :=
  signed (repairSign a) (northRepair (northern a) (northern_nonnegative a))
def repairDenominator (a : RationalQuaternion) : Q' := denom (northern a)
theorem repairDenominator_ge_one (a : RationalQuaternion) : (1:Q') ≤ repairDenominator a :=
  denom_ge_one _ (northern_nonnegative a)
theorem repairDenominator_pos (a : RationalQuaternion) : (0:Q') < repairDenominator a :=
  denom_pos _ (northern_nonnegative a)

/-- Exact finite defect identity, before taking an estimate. -/
theorem repair_error_identity (a : RationalQuaternion) :
    distSq (repair a).val a ≈
      ((normSq a + -(1:Q'))*(normSq a + -(1:Q')))*
        Q'.recipPos (repairDenominator a) (repairDenominator_pos a) := by
  have hn : normSq (northern a) ≈ normSq a := by
    unfold northern
    split
    · exact norm_neg a
    · exact Q'.eqv_refl _
  have hd : distSq (repair a).val a ≈
      distSq (northRepair (northern a) (northern_nonnegative a)).val (northern a) := by
    let q := (northRepair (northern a) (northern_nonnegative a)).val
    unfold repair signed
    split
    · rename_i h
      have hN : northern a = neg a := by simp only [northern, h, if_true]
      change distSq (neg q) a ≈ distSq q (northern a)
      rw [hN]
      exact neg_distance q a
    · rename_i h
      have hN : northern a = a := by simp [northern, h]
      change distSq q a ≈ distSq q (northern a)
      rw [hN]
      exact Q'.eqv_refl _
  have he := ac hn (Q'.eqv_refl (-(1:Q')))
  exact Q'.eqv_trans _ _ _ hd (Q'.eqv_trans _ _ _ (north_error _ _)
    (mc (mc he he) (Q'.eqv_refl _)))

theorem repair_error_le (a : RationalQuaternion) :
    distSq (repair a).val a ≤ (normSq a + -(1:Q'))*(normSq a + -(1:Q')) := by
  have ht : Q'.recipPos (repairDenominator a) (repairDenominator_pos a) ≤ (1:Q') := by
    apply Q'.le_of_mul_le_mul_left (c := repairDenominator a) _ (repairDenominator_pos a)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ _))
      (Q'.le_trans' _ _ _ (repairDenominator_ge_one a) (Q'.ge_of_eqv (Q'.mul_one_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (repair_error_identity a))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ht (sq_nonnegative _))
      (Q'.le_of_eqv (Q'.mul_one_eqv _)))

/-- Exact unit inputs are recovered semantically, for both chart signs. -/
theorem repair_unit (a : UnitNorm) : (repair a.val).Equivalent a := by
  apply (chord_zero_iff _ _).mp
  have he : normSq a.val + -(1:Q') ≈ 0 :=
    Q'.eqv_trans _ _ _ (ac a.unitNorm (Q'.eqv_refl _)) (by decide)
  have hu : chord (repair a.val) a ≤ (0:Q') := Q'.le_trans' _ _ _ (repair_error_le a.val)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (mc he he) (by decide)))
  exact Q'.eqv_of_le_le hu (chord_nonnegative _ _)

theorem repair_zero : (repair RationalQuaternion.zero).Equivalent unitOne := by
  unfold UnitNorm.Equivalent RationalQuaternion.Equivalent
  decide

end YMGap.RepTheory.RationalQuaternionNormRepair

#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.coordinate_congr
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.coordinate_square_le
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.coordinate_difference_square_le
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.distance_nonnegative
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.distance_symm
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.distance_triangle
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repair
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repairDenominator_ge_one
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repairDenominator_pos
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repair_error_identity
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repair_error_le
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repair_unit
#print axioms YMGap.RepTheory.RationalQuaternionNormRepair.repair_zero
