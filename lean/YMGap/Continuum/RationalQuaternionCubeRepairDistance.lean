/-
Pointwise rational cube-to-sphere repair preserves distance to a unit input
up to a computed factor in squared distance.
The comparison uses only four coordinate squares, the actual unit-norm pin,
and the existing rational norm repair. It holds at zero and at both chart
sign boundaries; no Haar functional, cubature, or continuous integral occurs.
-/

import YMGap.RepTheory.RationalQuaternionNormRepair

namespace YMGap.Continuum.RationalQuaternionCubeRepairDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionNormRepair

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem square_nonnegative (a : Q') : (0 : Q') ≤ a*a :=
  SumOfSquares.q_mul_self_nonneg a

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem two_sum_square (a b : Q') :
    (a+b)*(a+b) ≤ 2*(a*a+b*b) := by
  have hstep := Q'.add_le_self_of_nonneg ((a+b)*(a+b))
    ((a+-b)*(a+-b)) (square_nonnegative (a+-b))
  have hring : (a+b)*(a+b)+(a+-b)*(a+-b) ≈ 2*(a*a+b*b) :=
    poly_identity_of_normal_eq
      ((.var 0+.var 1)*(.var 0+.var 1)+
        (.var 0+ -(.var 1))*(.var 0+ -(.var 1)))
      (2*(.var 0*.var 0+.var 1*.var 1))
      (by decide) (fun | 0 => a | _ => b)
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hring)

private theorem four_sum_square (a b c d : Q') :
    ((a+b)+(c+d))*((a+b)+(c+d)) ≤
      4*((a*a+b*b)+(c*c+d*d)) := by
  have htop := two_sum_square (a+b) (c+d)
  have hpair := Q'.add_le_add (two_sum_square a b) (two_sum_square c d)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 2 hpair
    (by decide : (0 : Q') ≤ 2)
  have hring :
      2*(2*(a*a+b*b)+2*(c*c+d*d)) ≈
        4*((a*a+b*b)+(c*c+d*d)) :=
    poly_identity_of_normal_eq
      (2*(2*(.var 0+.var 1)+2*(.var 2+.var 3)))
      (4*((.var 0+.var 1)+(.var 2+.var 3)))
      (by decide) (fun | 0 => a*a | 1 => b*b | 2 => c*c | _ => d*d)
  exact Q'.le_trans' _ _ _ htop
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hring))

private theorem coordinate_sum_square_le_four (a b : Q')
    (ha : a*a ≤ (1 : Q')) (hb : b*b ≤ (1 : Q')) :
    (a+b)*(a+b) ≤ 4 := by
  have hsum : a*a+b*b ≤ (2 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add ha hb)
      (Q'.le_of_eqv (by decide : (1 : Q')+1 ≈ 2))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 2 hsum
    (by decide : (0 : Q') ≤ 2)
  exact Q'.le_trans' _ _ _ (two_sum_square a b)
    (Q'.le_trans' _ _ _ hscaled (by decide : (2 : Q')*2 ≤ 4))

private theorem scalar_norm_difference_square (a b : Q')
    (ha : a*a ≤ (1 : Q')) (hb : b*b ≤ (1 : Q')) :
    (a*a+-(b*b))*(a*a+-(b*b)) ≤
      4*((a+-b)*(a+-b)) := by
  have hfactor : (a*a+-(b*b))*(a*a+-(b*b)) ≈
      ((a+b)*(a+b))*((a+-b)*(a+-b)) :=
    poly_identity_of_normal_eq
      ((.var 0*.var 0+ -(.var 1*.var 1))*
        (.var 0*.var 0+ -(.var 1*.var 1)))
      (((.var 0+.var 1)*(.var 0+.var 1))*
        ((.var 0+ -(.var 1))*(.var 0+ -(.var 1))))
      (by decide) (fun | 0 => a | _ => b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (coordinate_sum_square_le_four a b ha hb)
      (square_nonnegative (a+-b)))

private theorem x_coordinate_square_le_one (x : UnitNorm) (i : Fin 4) :
    coordinate x.val i * coordinate x.val i ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (coordinate_square_le x.val i)
    (Q'.le_of_eqv x.unitNorm)

/-- Under literal four-coordinate cube guards, the radial norm defect is
controlled by squared chordal distance to ANY rational unit quaternion. -/
theorem norm_defect_square_le_distance (r : RationalQuaternion)
    (hr : ∀ i : Fin 4,
      coordinate r i * coordinate r i ≤ (1 : Q')) (x : UnitNorm) :
    (normSq r + -(1 : Q'))*(normSq r + -(1 : Q')) ≤
      16*distSq r x.val := by
  let u0 := r.r*r.r + -(x.val.r*x.val.r)
  let u1 := r.i*r.i + -(x.val.i*x.val.i)
  let u2 := r.j*r.j + -(x.val.j*x.val.j)
  let u3 := r.k*r.k + -(x.val.k*x.val.k)
  let d0 := r.r + -x.val.r
  let d1 := r.i + -x.val.i
  let d2 := r.j + -x.val.j
  let d3 := r.k + -x.val.k
  have hr0 : r.r*r.r ≤ (1 : Q') := by
    have h := hr (⟨0,by decide⟩ : Fin 4)
    change r.r*r.r ≤ (1 : Q') at h
    exact h
  have hr1 : r.i*r.i ≤ (1 : Q') := by
    have h := hr (⟨1,by decide⟩ : Fin 4)
    change r.i*r.i ≤ (1 : Q') at h
    exact h
  have hr2 : r.j*r.j ≤ (1 : Q') := by
    have h := hr (⟨2,by decide⟩ : Fin 4)
    change r.j*r.j ≤ (1 : Q') at h
    exact h
  have hr3 : r.k*r.k ≤ (1 : Q') := by
    have h := hr (⟨3,by decide⟩ : Fin 4)
    change r.k*r.k ≤ (1 : Q') at h
    exact h
  have hx0 : x.val.r*x.val.r ≤ (1 : Q') := by
    have h := x_coordinate_square_le_one x (⟨0,by decide⟩ : Fin 4)
    change x.val.r*x.val.r ≤ (1 : Q') at h
    exact h
  have hx1 : x.val.i*x.val.i ≤ (1 : Q') := by
    have h := x_coordinate_square_le_one x (⟨1,by decide⟩ : Fin 4)
    change x.val.i*x.val.i ≤ (1 : Q') at h
    exact h
  have hx2 : x.val.j*x.val.j ≤ (1 : Q') := by
    have h := x_coordinate_square_le_one x (⟨2,by decide⟩ : Fin 4)
    change x.val.j*x.val.j ≤ (1 : Q') at h
    exact h
  have hx3 : x.val.k*x.val.k ≤ (1 : Q') := by
    have h := x_coordinate_square_le_one x (⟨3,by decide⟩ : Fin 4)
    change x.val.k*x.val.k ≤ (1 : Q') at h
    exact h
  have h0 : u0*u0 ≤ 4*(d0*d0) :=
    scalar_norm_difference_square r.r x.val.r hr0 hx0
  have h1 : u1*u1 ≤ 4*(d1*d1) :=
    scalar_norm_difference_square r.i x.val.i hr1 hx1
  have h2 : u2*u2 ≤ 4*(d2*d2) :=
    scalar_norm_difference_square r.j x.val.j hr2 hx2
  have h3 : u3*u3 ≤ 4*(d3*d3) :=
    scalar_norm_difference_square r.k x.val.k hr3 hx3
  have hsum : ((u0*u0+u1*u1)+(u2*u2+u3*u3)) ≤
      ((4*(d0*d0)+4*(d1*d1))+(4*(d2*d2)+4*(d3*d3))) :=
    Q'.add_le_add (Q'.add_le_add h0 h1) (Q'.add_le_add h2 h3)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ 4 hsum
    (by decide : (0 : Q') ≤ 4)
  have hfour := four_sum_square u0 u1 u2 u3
  have hdef : normSq r + -(1 : Q') ≈ (u0+u1)+(u2+u3) := by
    have hx : normSq r + -(1 : Q') ≈ normSq r + -(normSq x.val) :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm x.unitNorm))
    have hring : normSq r + -(normSq x.val) ≈ (u0+u1)+(u2+u3) :=
      poly_identity_of_normal_eq
        (((.var 0*.var 0+.var 1*.var 1)+
            (.var 2*.var 2+.var 3*.var 3))+
          -((.var 4*.var 4+.var 5*.var 5)+
            (.var 6*.var 6+.var 7*.var 7)))
        (((.var 0*.var 0+ -(.var 4*.var 4))+
            (.var 1*.var 1+ -(.var 5*.var 5)))+
          ((.var 2*.var 2+ -(.var 6*.var 6))+
            (.var 3*.var 3+ -(.var 7*.var 7))))
        (by decide)
        (fun
          | 0 => r.r | 1 => r.i | 2 => r.j | 3 => r.k
          | 4 => x.val.r | 5 => x.val.i | 6 => x.val.j | _ => x.val.k)
    exact Q'.eqv_trans _ _ _ hx hring
  have hright : 4*((4*(d0*d0)+4*(d1*d1))+
      (4*(d2*d2)+4*(d3*d3))) ≈ 16*distSq r x.val :=
    poly_identity_of_normal_eq
      (4*((4*(.var 0*.var 0)+4*(.var 1*.var 1))+
        (4*(.var 2*.var 2)+4*(.var 3*.var 3))))
      (16*((.var 0*.var 0+.var 1*.var 1)+
        (.var 2*.var 2+.var 3*.var 3)))
      (by decide) (fun | 0 => d0 | 1 => d1 | 2 => d2 | _ => d3)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (mul_congr hdef hdef))
    (Q'.le_trans' _ _ _ hfour
      (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hright)))

private theorem triangle_34 (u v d : Q')
    (ht : u ≤ 2*v+2*d) (hv : v ≤ 16*d) : u ≤ 34*d := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 2 hv
    (by decide : (0 : Q') ≤ 2)
  have hsum := Q'.add_le_add_right _ _ (2*d) hscaled
  have hring : 2*(16*d)+2*d ≈ 34*d :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.const 2) (.mul (.const 16) (.var 0)))
        (.mul (.const 2) (.var 0)))
      (.mul (.const 34) (.var 0))
      (by decide) (fun _ => d)
  exact Q'.le_trans' _ _ _ ht
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hring))

/-- The ACTUAL rational norm repair has a 34-times squared-distance bound
relative to any unit input. No chart exception is removed. This is not a
general Lipschitz claim for the repair map on pairs of cube inputs. -/
theorem repair_distance_le (r : RationalQuaternion)
    (hr : ∀ i : Fin 4,
      coordinate r i * coordinate r i ≤ (1 : Q')) (x : UnitNorm) :
    distSq (repair r).val x.val ≤ 34*distSq r x.val := by
  have hv : distSq (repair r).val r ≤ 16*distSq r x.val :=
    Q'.le_trans' _ _ _ (repair_error_le r)
      (norm_defect_square_le_distance r hr x)
  exact triangle_34 _ _ _ (distance_triangle (repair r).val r x.val) hv

end YMGap.Continuum.RationalQuaternionCubeRepairDistance

#print axioms YMGap.Continuum.RationalQuaternionCubeRepairDistance.norm_defect_square_le_distance
#print axioms YMGap.Continuum.RationalQuaternionCubeRepairDistance.repair_distance_le
