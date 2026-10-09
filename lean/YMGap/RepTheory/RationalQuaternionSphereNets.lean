/-
# Explicit finite nets of the rational unit quaternion sphere

Both stereographic signs and a finite rational cube mesh are retained as
computable data. Every actual `RationalQuaternion.UnitNorm` has a computed
net index, with squared Euclidean error at most `12/N^2` for positive N.
The mesh points need not lie in the stereographic unit ball.

This is effective total boundedness of the rational source. Rational points
are NOT asserted compact or complete. No compact SU(2), Haar extension,
continuum action, or Yang--Mills gap is constructed here.
-/

import Init.Data.List.FinRange
import YMGap.RepTheory.RationalQuaternionUnitNormGroup
import YMGap.Constructive.Sqrt

namespace YMGap.RepTheory.RationalQuaternionSphereNets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv
local instance : Trans Q'.eqv Q'.eqv Q'.eqv :=
  ⟨fun h k => Q'.eqv_trans _ _ _ h k⟩

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a+c ≈ b+d := Q'.eqv_trans _ _ _
  (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _
  (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h

private theorem sq_nonneg (a : Q') : (0 : Q') ≤ a*a :=
  SumOfSquares.q_mul_self_nonneg a

private theorem eqv_of_le_ge {a b : Q'} (h : a ≤ b) (k : b ≤ a) : a ≈ b :=
  Int.le_antisymm h k

private theorem cancel_pos {d a b : Q'} (hd : (0 : Q') < d)
    (h : d*a ≈ d*b) : a ≈ b := eqv_of_le_ge
  (Q'.le_of_mul_le_mul_left (Q'.le_of_eqv h) hd)
  (Q'.le_of_mul_le_mul_left (Q'.ge_of_eqv h) hd)

private theorem recip_le_one (d : Q') (hd : (0 : Q') < d) (h1 : (1 : Q') ≤ d) :
    Q'.recipPos d hd ≤ (1 : Q') := by
  apply Q'.le_of_mul_le_mul_left (c := d) _ hd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv d hd))
    (Q'.le_trans' _ _ _ h1 (Q'.ge_of_eqv (Q'.mul_one_eqv d)))

private theorem neg_square (a : Q') : (-a)*(-a) ≈ a*a :=
  poly_identity_of_normal_eq ((-(PolyExpr.var 0 : PE))*(-(PolyExpr.var 0)))
    ((PolyExpr.var 0)*(PolyExpr.var 0)) (by decide) (fun _ => a)

private theorem abs_square (a : Q') : Q'.abs a * Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact neg_square a

private theorem coordinate_bound (a : Q') (h : a*a ≤ (1 : Q')) :
    -(1 : Q') ≤ a ∧ a ≤ (1 : Q') := by
  have ha : Q'.abs a ≤ (1 : Q') := CReal.le_of_sq_le_sq (by decide)
    (Q'.abs_nonneg a) (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square a)) h)
  refine ⟨?_, Q'.le_trans' _ _ _ (Q'.le_abs_self a) ha⟩
  have hn := Q'.neg_le_neg (Q'.le_trans' _ _ _ (Q'.neg_le_abs a) ha)
  exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.neg_neg_eqv a))

/-- A rational stereographic parameter, with all three coordinates explicit. -/
structure Triple where
  x : Q'
  y : Q'
  z : Q'

def norm3 (t : Triple) : Q' := (t.x*t.x+t.y*t.y)+t.z*t.z

def dist3 (t u : Triple) : Q' :=
  ((t.x + -u.x)*(t.x + -u.x) + (t.y + -u.y)*(t.y + -u.y)) +
    (t.z + -u.z)*(t.z + -u.z)

private def dot3 (t u : Triple) : Q' := (t.x*u.x+t.y*u.y)+t.z*u.z

private theorem norm3_nonneg (t : Triple) : (0 : Q') ≤ norm3 t :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (sq_nonneg t.x) (sq_nonneg t.y))
    (sq_nonneg t.z)

private theorem dist3_nonneg (t u : Triple) : (0 : Q') ≤ dist3 t u :=
  Q'.zero_le_add _ _ (Q'.zero_le_add _ _ (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

def denominator (t : Triple) : Q' := 1+norm3 t

theorem denominator_positive (t : Triple) : (0 : Q') < denominator t :=
  Q'.pos_add_nonneg (by decide) (norm3_nonneg t)

private theorem denominator_ge_one (t : Triple) : (1 : Q') ≤ denominator t :=
  Q'.add_le_self_of_nonneg _ _ (norm3_nonneg t)

private def raw (t : Triple) : RationalQuaternion :=
  ⟨1 + -norm3 t, 2*t.x, 2*t.y, 2*t.z⟩

private def scale (c : Q') (x : RationalQuaternion) : RationalQuaternion :=
  ⟨c*x.r,c*x.i,c*x.j,c*x.k⟩

/-- Literal squared chord distance in four rational coordinates. -/
def distSq (x y : RationalQuaternion) : Q' :=
  ((x.r + -y.r)*(x.r + -y.r) + (x.i + -y.i)*(x.i + -y.i)) +
    ((x.j + -y.j)*(x.j + -y.j) + (x.k + -y.k)*(x.k + -y.k))

private def dot4 (x y : RationalQuaternion) : Q' :=
  (x.r*y.r+x.i*y.i)+(x.j*y.j+x.k*y.k)

private theorem norm_scale (c : Q') (x : RationalQuaternion) :
    normSq (scale c x) ≈ (c*c)*normSq x :=
  poly_identity_of_normal_eq
    (((PolyExpr.var 0*PolyExpr.var 1)*(PolyExpr.var 0*PolyExpr.var 1)+(PolyExpr.var 0*PolyExpr.var 2)*(PolyExpr.var 0*PolyExpr.var 2))+
      ((PolyExpr.var 0*PolyExpr.var 3)*(PolyExpr.var 0*PolyExpr.var 3)+(PolyExpr.var 0*PolyExpr.var 4)*(PolyExpr.var 0*PolyExpr.var 4)))
    ((PolyExpr.var 0*PolyExpr.var 0)*((PolyExpr.var 1*PolyExpr.var 1+PolyExpr.var 2*PolyExpr.var 2)+
      (PolyExpr.var 3*PolyExpr.var 3+PolyExpr.var 4*PolyExpr.var 4))) (by decide)
    (fun | 0 => c | 1 => x.r | 2 => x.i | 3 => x.j | _ => x.k)

private theorem raw_norm (t : Triple) : normSq (raw t) ≈ denominator t*denominator t := by
  have h : normSq (raw t) ≈ (1 + -norm3 t)*(1 + -norm3 t)+4*norm3 t :=
    poly_identity_of_normal_eq
      (((1 + -(PolyExpr.var 0))*(1 + -(PolyExpr.var 0))+(2*PolyExpr.var 1)*(2*PolyExpr.var 1))+
        ((2*PolyExpr.var 2)*(2*PolyExpr.var 2)+(2*PolyExpr.var 3)*(2*PolyExpr.var 3)))
      ((1 + -(PolyExpr.var 0))*(1 + -(PolyExpr.var 0))+4*((PolyExpr.var 1*PolyExpr.var 1+PolyExpr.var 2*PolyExpr.var 2)+PolyExpr.var 3*PolyExpr.var 3))
      (by decide) (fun | 0 => norm3 t | 1 => t.x | 2 => t.y | _ => t.z)
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    ((1 + -(PolyExpr.var 0))*(1 + -(PolyExpr.var 0))+4*PolyExpr.var 0)
    ((1+PolyExpr.var 0)*(1+PolyExpr.var 0)) (by decide) (fun _ => norm3 t))

private theorem reciprocal_square (d e : Q') (h : d*e ≈ 1) :
    (e*e)*(d*d) ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq ((PolyExpr.var 1*PolyExpr.var 1)*(PolyExpr.var 0*PolyExpr.var 0))
      ((PolyExpr.var 0*PolyExpr.var 1)*(PolyExpr.var 0*PolyExpr.var 1)) (by decide) (fun | 0 => d | _ => e))
    (Q'.eqv_trans _ _ _ (mc h h) (by decide))

/-- The exact rational stereographic point, not a normalized approximation. -/
def stereographic (t : Triple) : UnitNorm :=
  ⟨scale (Q'.recipPos (denominator t) (denominator_positive t)) (raw t), by
    exact Q'.eqv_trans _ _ _ (norm_scale _ _) (Q'.eqv_trans _ _ _
      (mc (Q'.eqv_refl _) (raw_norm t))
      (reciprocal_square _ _ (Q'.mul_recipPos_eqv _ _)))⟩

private theorem dot_scale (a b : Q') (x y : RationalQuaternion) :
    dot4 (scale a x) (scale b y) ≈ (a*b)*dot4 x y :=
  poly_identity_of_normal_eq
    (((PolyExpr.var 0*PolyExpr.var 2)*(PolyExpr.var 1*PolyExpr.var 6)+(PolyExpr.var 0*PolyExpr.var 3)*(PolyExpr.var 1*PolyExpr.var 7))+
      ((PolyExpr.var 0*PolyExpr.var 4)*(PolyExpr.var 1*PolyExpr.var 8)+(PolyExpr.var 0*PolyExpr.var 5)*(PolyExpr.var 1*PolyExpr.var 9)))
    ((PolyExpr.var 0*PolyExpr.var 1)*((PolyExpr.var 2*PolyExpr.var 6+PolyExpr.var 3*PolyExpr.var 7)+
      (PolyExpr.var 4*PolyExpr.var 8+PolyExpr.var 5*PolyExpr.var 9))) (by decide)
    (fun | 0 => a | 1 => b | 2 => x.r | 3 => x.i | 4 => x.j | 5 => x.k | 6 => y.r | 7 => y.i | 8 => y.j | _ => y.k)

private theorem distance_expansion (x y : RationalQuaternion) :
    distSq x y ≈ normSq x+normSq y + -(2*dot4 x y) :=
  poly_identity_of_normal_eq
    (((PolyExpr.var 0 + -(PolyExpr.var 4))*(PolyExpr.var 0 + -(PolyExpr.var 4))+
      (PolyExpr.var 1 + -(PolyExpr.var 5))*(PolyExpr.var 1 + -(PolyExpr.var 5)))+
     ((PolyExpr.var 2 + -(PolyExpr.var 6))*(PolyExpr.var 2 + -(PolyExpr.var 6))+
      (PolyExpr.var 3 + -(PolyExpr.var 7))*(PolyExpr.var 3 + -(PolyExpr.var 7))))
    (((PolyExpr.var 0*PolyExpr.var 0+PolyExpr.var 1*PolyExpr.var 1)+(PolyExpr.var 2*PolyExpr.var 2+PolyExpr.var 3*PolyExpr.var 3))+
      ((PolyExpr.var 4*PolyExpr.var 4+PolyExpr.var 5*PolyExpr.var 5)+(PolyExpr.var 6*PolyExpr.var 6+PolyExpr.var 7*PolyExpr.var 7))+
      -(2*((PolyExpr.var 0*PolyExpr.var 4+PolyExpr.var 1*PolyExpr.var 5)+(PolyExpr.var 2*PolyExpr.var 6+PolyExpr.var 3*PolyExpr.var 7))))
    (by decide) (fun | 0 => x.r | 1 => x.i | 2 => x.j | 3 => x.k | 4 => y.r | 5 => y.i | 6 => y.j | _ => y.k)

private theorem chord_numerator (t u : Triple) :
    denominator t*denominator u + -dot4 (raw t) (raw u) ≈ 2*dist3 t u := by
  have hdot : dot4 (raw t) (raw u) ≈
      (1 + -norm3 t)*(1 + -norm3 u)+4*dot3 t u :=
    poly_identity_of_normal_eq
      (((1 + -(PolyExpr.var 0))*(1 + -(PolyExpr.var 1))+(2*PolyExpr.var 2)*(2*PolyExpr.var 5))+
        ((2*PolyExpr.var 3)*(2*PolyExpr.var 6)+(2*PolyExpr.var 4)*(2*PolyExpr.var 7)))
      ((1 + -(PolyExpr.var 0))*(1 + -(PolyExpr.var 1))+4*((PolyExpr.var 2*PolyExpr.var 5+PolyExpr.var 3*PolyExpr.var 6)+PolyExpr.var 4*PolyExpr.var 7))
      (by decide) (fun | 0 => norm3 t | 1 => norm3 u | 2 => t.x | 3 => t.y | 4 => t.z | 5 => u.x | 6 => u.y | _ => u.z)
  refine Q'.eqv_trans _ _ _ (ac (Q'.eqv_refl _) (nc hdot)) ?_
  have h := poly_identity_of_normal_eq
    ((1+PolyExpr.var 0)*(1+PolyExpr.var 1) + -((1 + -(PolyExpr.var 0))*(1 + -(PolyExpr.var 1))+4*PolyExpr.var 2))
    (2*(PolyExpr.var 0+PolyExpr.var 1 + -(2*PolyExpr.var 2))) (by decide)
    (fun | 0 => norm3 t | 1 => norm3 u | _ => dot3 t u)
  refine Q'.eqv_trans _ _ _ h (mc (Q'.eqv_refl _) ?_)
  exact poly_identity_of_normal_eq
    (((PolyExpr.var 0*PolyExpr.var 0+PolyExpr.var 1*PolyExpr.var 1)+PolyExpr.var 2*PolyExpr.var 2)+
      ((PolyExpr.var 3*PolyExpr.var 3+PolyExpr.var 4*PolyExpr.var 4)+PolyExpr.var 5*PolyExpr.var 5)+
      -(2*((PolyExpr.var 0*PolyExpr.var 3+PolyExpr.var 1*PolyExpr.var 4)+PolyExpr.var 2*PolyExpr.var 5)))
    (((PolyExpr.var 0 + -(PolyExpr.var 3))*(PolyExpr.var 0 + -(PolyExpr.var 3))+
      (PolyExpr.var 1 + -(PolyExpr.var 4))*(PolyExpr.var 1 + -(PolyExpr.var 4)))+
      (PolyExpr.var 2 + -(PolyExpr.var 5))*(PolyExpr.var 2 + -(PolyExpr.var 5))) (by decide)
    (fun | 0 => t.x | 1 => t.y | 2 => t.z | 3 => u.x | 4 => u.y | _ => u.z)

/-- The exact chord identity, with positive reciprocal factors retained. -/
theorem stereographic_chord (t u : Triple) :
    distSq (stereographic t).val (stereographic u).val ≈
      (4*dist3 t u)*(Q'.recipPos (denominator t) (denominator_positive t)*
        Q'.recipPos (denominator u) (denominator_positive u)) := by
  let a := Q'.recipPos (denominator t) (denominator_positive t)
  let b := Q'.recipPos (denominator u) (denominator_positive u)
  have hi : (a*b)*(denominator t*denominator u) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq ((PolyExpr.var 0*PolyExpr.var 1)*(PolyExpr.var 2*PolyExpr.var 3))
        ((PolyExpr.var 2*PolyExpr.var 0)*(PolyExpr.var 3*PolyExpr.var 1)) (by decide)
        (fun | 0 => a | 1 => b | 2 => denominator t | _ => denominator u))
      (Q'.eqv_trans _ _ _ (mc
        (Q'.mul_recipPos_eqv (denominator t) (denominator_positive t))
        (Q'.mul_recipPos_eqv (denominator u) (denominator_positive u))) (by decide))
  have hn := distance_expansion (stereographic t).val (stereographic u).val
  refine Q'.eqv_trans _ _ _ hn ?_
  refine Q'.eqv_trans _ _ _
    (ac (ac (stereographic t).unitNorm (stereographic u).unitNorm)
      (nc (mc (Q'.eqv_refl _) (dot_scale a b (raw t) (raw u))))) ?_
  have hreplace : (1:Q')+1 + -(2*((a*b)*dot4 (raw t) (raw u))) ≈
      2*((a*b)*(denominator t*denominator u + -dot4 (raw t) (raw u))) := by
    refine Q'.eqv_trans _ _ _ (ac (ac (Q'.eqv_symm hi) (Q'.eqv_symm hi)) (Q'.eqv_refl _)) ?_
    exact poly_identity_of_normal_eq
      (PolyExpr.var 0*PolyExpr.var 1+PolyExpr.var 0*PolyExpr.var 1 + -(2*(PolyExpr.var 0*PolyExpr.var 2)))
      (2*(PolyExpr.var 0*(PolyExpr.var 1 + -(PolyExpr.var 2)))) (by decide)
      (fun | 0 => a*b | 1 => denominator t*denominator u | _ => dot4 (raw t) (raw u))
  refine Q'.eqv_trans _ _ _ hreplace ?_
  refine Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (chord_numerator t u))) ?_
  exact poly_identity_of_normal_eq (2*(PolyExpr.var 0*(2*PolyExpr.var 1)))
    ((4*PolyExpr.var 1)*PolyExpr.var 0) (by decide) (fun | 0 => a*b | _ => dist3 t u)

/-- Global squared-Lipschitz bound; no unit-ball hypothesis on either parameter. -/
theorem stereographic_lipschitz (t u : Triple) :
    distSq (stereographic t).val (stereographic u).val ≤ 4*dist3 t u := by
  have ha := recip_le_one _ (denominator_positive t) (denominator_ge_one t)
  have hb := recip_le_one _ (denominator_positive u) (denominator_ge_one u)
  have hab := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hb)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (stereographic_chord t u))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hab
        (Q'.mul_nonneg _ _ (by decide) (dist3_nonneg t u)))
      (Q'.le_of_eqv (Q'.mul_one_eqv _)))

private theorem four_bounds (a b c d : Q')
    (h : (a*a+b*b)+(c*c+d*d) ≈ 1) :
    (-(1:Q') ≤ a ∧ a ≤ 1) ∧ (-(1:Q') ≤ b ∧ b ≤ 1) ∧
      (-(1:Q') ≤ c ∧ c ≤ 1) ∧ (-(1:Q') ≤ d ∧ d ≤ 1) := by
  have hab := Q'.zero_le_add _ _ (sq_nonneg a) (sq_nonneg b)
  have hcd := Q'.zero_le_add _ _ (sq_nonneg c) (sq_nonneg d)
  have hleft : a*a+b*b ≤ (1:Q') := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hcd) (Q'.le_of_eqv h)
  have hright : c*c+d*d ≤ (1:Q') := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hab)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) (Q'.le_of_eqv h))
  refine ⟨coordinate_bound a (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (sq_nonneg b)) hleft),
    coordinate_bound b ?_, coordinate_bound c (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ (sq_nonneg d)) hright), coordinate_bound d ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (sq_nonneg a))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) hleft)
  · exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (sq_nonneg c))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) hright)

private theorem scaled_bounds (e x : Q') (he : (0:Q') ≤ e) (he1 : e ≤ 1)
    (hx : -(1:Q') ≤ x ∧ x ≤ 1) : -(1:Q') ≤ e*x ∧ e*x ≤ 1 := by
  constructor
  · have hn := Q'.neg_le_neg he1
    have hp : -e ≈ e*(-1) := poly_identity_of_normal_eq (- (PolyExpr.var 0))
      (PolyExpr.var 0*(-1)) (by decide) (fun _ => e)
    exact Q'.le_trans' _ _ _ hn (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hx.1 he))
  · exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hx.2 he)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) he1)

private theorem inverse_scalar (r s e : Q') (hn : r*r+s ≈ 1)
    (hi : (1+r)*e ≈ 1) :
    (1+s*(e*e) ≈ 2*e) ∧ (1 + -(s*(e*e)) ≈ (2*e)*r) := by
  have hd : 1+s*(e*e) ≈ 2*e := by
    have h := poly_identity_of_normal_eq
      (1+PolyExpr.var 1*(PolyExpr.var 2*PolyExpr.var 2))
      (2*PolyExpr.var 2+(PolyExpr.var 0*PolyExpr.var 0+PolyExpr.var 1 + -1)*(PolyExpr.var 2*PolyExpr.var 2)+
        (1 + -((1+PolyExpr.var 0)*PolyExpr.var 2))*(1+(1+PolyExpr.var 0)*PolyExpr.var 2 + -(2*PolyExpr.var 2)))
      (by decide) (fun | 0 => r | 1 => s | _ => e)
    refine Q'.eqv_trans _ _ _ h ?_
    refine Q'.eqv_trans _ _ _
      (ac (ac (Q'.eqv_refl _) (mc (ac hn (Q'.eqv_refl _)) (Q'.eqv_refl _)))
        (mc (ac (Q'.eqv_refl _) (nc hi))
          (ac (ac (Q'.eqv_refl _) hi) (Q'.eqv_refl _)))) ?_
    exact poly_identity_of_normal_eq
      (2*PolyExpr.var 0+(1 + -1)*(PolyExpr.var 0*PolyExpr.var 0)+(1 + -1)*(1+1 + -(2*PolyExpr.var 0)))
      (2*PolyExpr.var 0) (by decide) (fun _ => e)
  refine ⟨hd, ?_⟩
  calc
    1 + -(s*(e*e)) ≈ 2 + -(1+s*(e*e)) :=
      poly_identity_of_normal_eq (1 + -(PolyExpr.var 0)) (2 + -(1+PolyExpr.var 0))
        (by decide) (fun _ => s*(e*e))
    _ ≈ 2 + -(2*e) := ac (Q'.eqv_refl _) (nc hd)
    _ ≈ 2*((1+r)*e) + -(2*e) := ac
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) hi) (by decide)))
      (Q'.eqv_refl _)
    _ ≈ (2*e)*r := poly_identity_of_normal_eq
      (2*((1+PolyExpr.var 0)*PolyExpr.var 1) + -(2*PolyExpr.var 1)) ((2*PolyExpr.var 1)*PolyExpr.var 0)
      (by decide) (fun | 0 => r | _ => e)

/-- Inverse coordinates on the closed northern hemisphere, including the equator. -/
def inverseChart (x : UnitNorm) (hx : (0:Q') ≤ x.val.r) : Triple :=
  let e := Q'.recipPos (1+x.val.r) (Q'.pos_add_nonneg (by decide) hx)
  ⟨e*x.val.i,e*x.val.j,e*x.val.k⟩

theorem inverseChart_bounds (x : UnitNorm) (hx : (0:Q') ≤ x.val.r) :
    (-(1:Q') ≤ (inverseChart x hx).x ∧ (inverseChart x hx).x ≤ 1) ∧
    (-(1:Q') ≤ (inverseChart x hx).y ∧ (inverseChart x hx).y ≤ 1) ∧
    (-(1:Q') ≤ (inverseChart x hx).z ∧ (inverseChart x hx).z ≤ 1) := by
  have hb := four_bounds x.val.r x.val.i x.val.j x.val.k x.unitNorm
  have hd := Q'.pos_add_nonneg (by decide : (0:Q') < 1) hx
  have he := Q'.le_of_lt (Q'.recipPos_pos (1+x.val.r) hd)
  have he1 := recip_le_one _ hd (Q'.add_le_self_of_nonneg _ _ hx)
  exact ⟨scaled_bounds _ _ he he1 hb.2.1,
    scaled_bounds _ _ he he1 hb.2.2.1, scaled_bounds _ _ he he1 hb.2.2.2⟩

private theorem multiply_inverse (d c v : Q') (h : d*c ≈ 1) : c*(d*v) ≈ v :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (PolyExpr.var 1*(PolyExpr.var 0*PolyExpr.var 2))
      ((PolyExpr.var 0*PolyExpr.var 1)*PolyExpr.var 2) (by decide) (fun | 0 => d | 1 => c | _ => v))
    (Q'.eqv_trans _ _ _ (mc h (Q'.eqv_refl _)) (Q'.one_mul_eqv v))

/-- Exact semantic inversion; no approximation of the unit-norm constraint. -/
theorem stereographic_inverse (x : UnitNorm) (hx : (0:Q') ≤ x.val.r) :
    (stereographic (inverseChart x hx)).val.Equivalent x.val := by
  let e := Q'.recipPos (1+x.val.r) (Q'.pos_add_nonneg (by decide) hx)
  let s := (x.val.i*x.val.i+x.val.j*x.val.j)+x.val.k*x.val.k
  let t := inverseChart x hx
  have hn : x.val.r*x.val.r+s ≈ 1 := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (PolyExpr.var 0+((PolyExpr.var 1+PolyExpr.var 2)+PolyExpr.var 3))
      ((PolyExpr.var 0+PolyExpr.var 1)+(PolyExpr.var 2+PolyExpr.var 3)) (by decide)
      (fun | 0 => x.val.r*x.val.r | 1 => x.val.i*x.val.i | 2 => x.val.j*x.val.j | _ => x.val.k*x.val.k)) x.unitNorm
  have hs : norm3 t ≈ s*(e*e) := poly_identity_of_normal_eq
    (((PolyExpr.var 0*PolyExpr.var 1)*(PolyExpr.var 0*PolyExpr.var 1)+(PolyExpr.var 0*PolyExpr.var 2)*(PolyExpr.var 0*PolyExpr.var 2))+
      (PolyExpr.var 0*PolyExpr.var 3)*(PolyExpr.var 0*PolyExpr.var 3))
    (((PolyExpr.var 1*PolyExpr.var 1+PolyExpr.var 2*PolyExpr.var 2)+PolyExpr.var 3*PolyExpr.var 3)*(PolyExpr.var 0*PolyExpr.var 0))
    (by decide) (fun | 0 => e | 1 => x.val.i | 2 => x.val.j | _ => x.val.k)
  have hh := inverse_scalar x.val.r s e hn
    (Q'.mul_recipPos_eqv (1+x.val.r) (Q'.pos_add_nonneg (by decide) hx))
  have hd : denominator t ≈ 2*e := Q'.eqv_trans _ _ _ (ac (Q'.eqv_refl _) hs) hh.1
  have hr : (raw t).r ≈ denominator t*x.val.r :=
    Q'.eqv_trans _ _ _ (ac (Q'.eqv_refl _) (nc hs))
      (Q'.eqv_trans _ _ _ hh.2 (mc (Q'.eqv_symm hd) (Q'.eqv_refl _)))
  have him (v : Q') : 2*(e*v) ≈ denominator t*v := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv 2 e v)) (mc (Q'.eqv_symm hd) (Q'.eqv_refl _))
  have hc := Q'.mul_recipPos_eqv (denominator t) (denominator_positive t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) hr) (multiply_inverse _ _ _ hc)
  · exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (him x.val.i)) (multiply_inverse _ _ _ hc)
  · exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (him x.val.j)) (multiply_inverse _ _ _ hc)
  · exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (him x.val.k)) (multiply_inverse _ _ _ hc)

private theorem norm_neg (x : RationalQuaternion) : normSq (neg x) ≈ normSq x :=
  ac (ac (neg_square x.r) (neg_square x.i)) (ac (neg_square x.j) (neg_square x.k))

/-- Both chart signs occur as actual unit quaternions. -/
def signed (south : Bool) (x : UnitNorm) : UnitNorm :=
  if south then ⟨neg x.val, Q'.eqv_trans _ _ _ (norm_neg x.val) x.unitNorm⟩ else x

private theorem signed_involutive (s : Bool) (x : UnitNorm) :
    (signed s (signed s x)).val.Equivalent x.val := by
  cases s
  · exact ⟨Q'.eqv_refl _,Q'.eqv_refl _,Q'.eqv_refl _,Q'.eqv_refl _⟩
  · exact ⟨Q'.neg_neg_eqv _,Q'.neg_neg_eqv _,Q'.neg_neg_eqv _,Q'.neg_neg_eqv _⟩

private theorem neg_diff_square (a b : Q') :
    (-a + -(-b))*(-a + -(-b)) ≈ (a + -b)*(a + -b) :=
  poly_identity_of_normal_eq
    ((-(PolyExpr.var 0) + -(-(PolyExpr.var 1)))*(-(PolyExpr.var 0) + -(-(PolyExpr.var 1))))
    ((PolyExpr.var 0 + -(PolyExpr.var 1))*(PolyExpr.var 0 + -(PolyExpr.var 1))) (by decide)
    (fun | 0 => a | _ => b)

private theorem signed_distance (s : Bool) (x y : UnitNorm) :
    distSq (signed s x).val (signed s y).val ≈ distSq x.val y.val := by
  cases s
  · exact Q'.eqv_refl _
  · exact ac (ac (neg_diff_square _ _) (neg_diff_square _ _))
      (ac (neg_diff_square _ _) (neg_diff_square _ _))

private theorem distSq_congr {x x' y y' : RationalQuaternion}
    (h : x.Equivalent x') (k : y.Equivalent y') : distSq x y ≈ distSq x' y' :=
  ac (ac (mc (ac h.1 (nc k.1)) (ac h.1 (nc k.1)))
      (mc (ac h.2.1 (nc k.2.1)) (ac h.2.1 (nc k.2.1))))
    (ac (mc (ac h.2.2.1 (nc k.2.2.1)) (ac h.2.2.1 (nc k.2.2.1)))
      (mc (ac h.2.2.2 (nc k.2.2.2)) (ac h.2.2.2 (nc k.2.2.2))))

def chartSign (x : UnitNorm) : Bool := decide (¬ (0:Q') ≤ x.val.r)

theorem chartSign_nonnegative (x : UnitNorm) : (0:Q') ≤ (signed (chartSign x) x).val.r := by
  unfold chartSign
  by_cases h : (0:Q') ≤ x.val.r
  · simp only [h, not_true_eq_false, decide_false, signed, Bool.false_eq_true, if_false]
  · simpa only [h, not_false_eq_true, decide_true, signed, if_true, neg] using
      (Q'.neg_nonneg_of_not_nonneg h)

/-! ## The finite lower mesh, with a computed index -/

private def fraction (N : Nat) (hN : 0 < N) (k : Nat) : Q' :=
  Q'.mkPos (k : Int) N hN

private def floorIndex (N : Nat) (q : Q') : Nat := q.num.toNat*N/q.den

private theorem fraction_add (N : Nat) (hN : 0 < N) (a b : Nat) :
    fraction N hN (a+b) ≈ fraction N hN a+fraction N hN b := by
  change ((a+b:Nat):Int) * ((fraction N hN a+fraction N hN b).den:Int) =
    ((a:Int)*((fraction N hN b).den:Int)+(b:Int)*((fraction N hN a).den:Int)) *
      ((fraction N hN (a+b)).den:Int)
  simp only [Q'.add_den_cast, fraction, Q'.mkPos_den,
    Int.natCast_add, Int.add_mul, Int.mul_assoc]

private theorem floor_lower (N : Nat) (hN : 0 < N) (q : Q') (hq : (0:Q') ≤ q) :
    fraction N hN (floorIndex N q) ≤ q := by
  have hn : (q.num.toNat:Int) = q.num :=
    Int.toNat_of_nonneg ((Q'.zero_le_iff_num_nonneg q).mp hq)
  have h := Nat.div_mul_le_self (q.num.toNat*N) q.den
  change ((floorIndex N q:Int)*(q.den:Int)) ≤ q.num*((fraction N hN (floorIndex N q)).den:Int)
  rw [show (fraction N hN (floorIndex N q)).den = N from Q'.mkPos_den _ _ _, ← hn]
  exact_mod_cast h

private theorem floor_upper (N : Nat) (hN : 0 < N) (q : Q') (hq : (0:Q') ≤ q) :
    q ≤ fraction N hN (floorIndex N q)+fraction N hN 1 := by
  have hn : (q.num.toNat:Int) = q.num :=
    Int.toNat_of_nonneg ((Q'.zero_le_iff_num_nonneg q).mp hq)
  have h := Nat.le_of_lt (Nat.lt_mul_div_succ (q.num.toNat*N) q.den_pos)
  rw [Nat.mul_comm q.den] at h
  have hb : q ≤ fraction N hN (floorIndex N q+1) := by
    change q.num*((fraction N hN (floorIndex N q+1)).den:Int) ≤
      ((floorIndex N q+1:Nat):Int)*(q.den:Int)
    rw [show (fraction N hN (floorIndex N q+1)).den = N from Q'.mkPos_den _ _ _, ← hn]
    exact_mod_cast h
  exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (fraction_add N hN _ _))

private theorem floor_bounded (N : Nat) (q : Q') (hq : (0:Q') ≤ q) (h2 : q ≤ 2) :
    floorIndex N q ≤ 2*N := by
  have hn : (q.num.toNat:Int) = q.num :=
    Int.toNat_of_nonneg ((Q'.zero_le_iff_num_nonneg q).mp hq)
  have h : q.num.toNat ≤ 2*q.den := by
    have hi : q.num ≤ 2*(q.den:Int) := by
      change q.num*1 ≤ 2*(q.den:Int) at h2
      simpa only [Int.mul_one] using h2
    rw [← hn] at hi
    exact_mod_cast hi
  apply Nat.div_le_of_le_mul
  have he : (2*q.den)*N = q.den*(2*N) := by ac_rfl
  exact Nat.le_trans (Nat.mul_le_mul_right N h) (Nat.le_of_eq he)

private theorem shifted_bounds (x : Q') (hx : -(1:Q') ≤ x ∧ x ≤ 1) :
    (0:Q') ≤ x+1 ∧ x+1 ≤ 2 :=
  ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : (-(1:Q'))+1 ≈ 0))
      (Q'.add_le_add_right _ _ 1 hx.1),
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ 1 hx.2)
      (Q'.le_of_eqv (by decide : (1:Q')+1 ≈ 2))⟩

private def meshIndex (N : Nat) (x : Q') (hx : -(1:Q') ≤ x ∧ x ≤ 1) : Fin (2*N+1) :=
  ⟨floorIndex N (x+1), Nat.lt_succ_of_le
    (floor_bounded N (x+1) (shifted_bounds x hx).1 (shifted_bounds x hx).2)⟩

private def meshPoint (N : Nat) (hN : 0 < N) (k : Fin (2*N+1)) : Q' :=
  fraction N hN k.val + -1

private theorem mesh_error (N : Nat) (hN : 0 < N) (x : Q')
    (hx : -(1:Q') ≤ x ∧ x ≤ 1) :
    (0:Q') ≤ x + -meshPoint N hN (meshIndex N x hx) ∧
    x + -meshPoint N hN (meshIndex N x hx) ≤ fraction N hN 1 := by
  let l := fraction N hN (floorIndex N (x+1))
  have hq := (shifted_bounds x hx).1
  have hl := floor_lower N hN (x+1) hq
  have hu := floor_upper N hN (x+1) hq
  have he : x + -meshPoint N hN (meshIndex N x hx) ≈ (x+1) + -l :=
    poly_identity_of_normal_eq (PolyExpr.var 0 + -(PolyExpr.var 1 + -1))
      ((PolyExpr.var 0+1) + -(PolyExpr.var 1)) (by decide) (fun | 0 => x | _ => l)
  refine ⟨?_, Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.sub_le_of_le_add hu)⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv l))
      (Q'.add_le_add_right _ _ (-l) hl)) (Q'.ge_of_eqv he)

private theorem mesh_square (N : Nat) (hN : 0 < N) (x : Q')
    (hx : -(1:Q') ≤ x ∧ x ≤ 1) :
    (x + -meshPoint N hN (meshIndex N x hx))*(x + -meshPoint N hN (meshIndex N x hx)) ≤
      fraction N hN 1*fraction N hN 1 := by
  have he := mesh_error N hN x hx
  have hu : (0:Q') ≤ fraction N hN 1 :=
    (Q'.zero_le_iff_num_nonneg _).mpr (by change (0:Int) ≤ 1; decide)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ he.2 he.1)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ he.2 hu)

/-- Two signs and three bounded integer coordinates; no witness is erased. -/
abbrev NetIndex (N : Nat) := Bool × Fin (2*N+1) × Fin (2*N+1) × Fin (2*N+1)

private def meshTriple (N : Nat) (hN : 0 < N)
    (i j k : Fin (2*N+1)) : Triple :=
  ⟨meshPoint N hN i,meshPoint N hN j,meshPoint N hN k⟩

/-- Every index returns an exact point of the original rational unit sphere. -/
def netPoint (N : Nat) (hN : 0 < N) (i : NetIndex N) : UnitNorm :=
  signed i.1 (stereographic (meshTriple N hN i.2.1 i.2.2.1 i.2.2.2))

/-- Computed chart sign followed by three natural-division mesh indices. -/
def netIndex (N : Nat) (x : UnitNorm) : NetIndex N :=
  let y := signed (chartSign x) x
  let t := inverseChart y (chartSign_nonnegative x)
  let ht := inverseChart_bounds y (chartSign_nonnegative x)
  (chartSign x,meshIndex N t.x ht.1,meshIndex N t.y ht.2.1,meshIndex N t.z ht.2.2)

private theorem meshTriple_error (N : Nat) (hN : 0 < N) (t : Triple)
    (hx : -(1:Q') ≤ t.x ∧ t.x ≤ 1) (hy : -(1:Q') ≤ t.y ∧ t.y ≤ 1)
    (hz : -(1:Q') ≤ t.z ∧ t.z ≤ 1) :
    4*dist3 t (meshTriple N hN (meshIndex N t.x hx) (meshIndex N t.y hy) (meshIndex N t.z hz)) ≤
      Q'.mkPos 12 (N*N) (Nat.mul_pos hN hN) := by
  have h := Q'.add_le_add (Q'.add_le_add
    (mesh_square N hN t.x hx) (mesh_square N hN t.y hy)) (mesh_square N hN t.z hz)
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (4:Q') h (by decide)
  refine Q'.le_trans' _ _ _ hs (Q'.le_of_eqv ?_)
  have he : (4:Q')*((fraction N hN 1*fraction N hN 1+
      fraction N hN 1*fraction N hN 1)+fraction N hN 1*fraction N hN 1) ≈
      12*(fraction N hN 1*fraction N hN 1) :=
    poly_identity_of_normal_eq (4*((PolyExpr.var 0*PolyExpr.var 0+PolyExpr.var 0*PolyExpr.var 0)+PolyExpr.var 0*PolyExpr.var 0))
      (12*(PolyExpr.var 0*PolyExpr.var 0)) (by decide) (fun _ => fraction N hN 1)
  refine Q'.eqv_trans _ _ _ he ?_
  change (12*(fraction N hN 1*fraction N hN 1)).num *
    ((Q'.mkPos 12 (N*N) (Nat.mul_pos hN hN)).den:Int) =
    (12:Int)*((12*(fraction N hN 1*fraction N hN 1)).den:Int)
  simp only [Q'.mul_den_cast, fraction, Q'.mkPos_den, Int.natCast_mul]
  change (12:Int)*((N:Int)*N) = 12*(1*((N:Int)*N))
  rw [Int.one_mul]

/-- Every rational unit quaternion has the explicitly selected net point
within squared chord error `12/N^2`. This includes the south pole and equator. -/
theorem net_covers (N : Nat) (hN : 0 < N) (x : UnitNorm) :
    distSq x.val (netPoint N hN (netIndex N x)).val ≤
      Q'.mkPos 12 (N*N) (Nat.mul_pos hN hN) := by
  let s := chartSign x
  let y := signed s x
  let t := inverseChart y (chartSign_nonnegative x)
  let ht := inverseChart_bounds y (chartSign_nonnegative x)
  let u := meshTriple N hN (meshIndex N t.x ht.1)
    (meshIndex N t.y ht.2.1) (meshIndex N t.z ht.2.2)
  have hy : (stereographic t).val.Equivalent y.val := stereographic_inverse y _
  have hback : distSq x.val (signed s (stereographic u)).val ≈
      distSq y.val (stereographic u).val := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (distSq_congr (signed_involutive s x)
      (show (signed s (stereographic u)).val.Equivalent (signed s (stereographic u)).val from
        ⟨Q'.eqv_refl _,Q'.eqv_refl _,Q'.eqv_refl _,Q'.eqv_refl _⟩))) ?_
    exact signed_distance s y (stereographic u)
  have hchart : distSq y.val (stereographic u).val ≈
      distSq (stereographic t).val (stereographic u).val :=
    Q'.eqv_symm (distSq_congr hy
      ⟨Q'.eqv_refl _,Q'.eqv_refl _,Q'.eqv_refl _,Q'.eqv_refl _⟩)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hback hchart))
    (Q'.le_trans' _ _ _ (stereographic_lipschitz t u)
      (meshTriple_error N hN t ht.1 ht.2.1 ht.2.2))

/-! ## Explicit finite enumeration, retaining BOTH signs -/

private def pairs {A B : Type} (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun a => ys.map (fun b => (a,b)))

private theorem mem_pairs {A B : Type} {xs : List A} {ys : List B} {a : A} {b : B}
    (ha : a ∈ xs) (hb : b ∈ ys) : (a,b) ∈ pairs xs ys :=
  List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

private theorem pairs_length {A B : Type} (xs : List A) (ys : List B) :
    (pairs xs ys).length = xs.length*ys.length := by
  induction xs with
  | nil => simp only [pairs, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons a xs ih =>
    simpa only [pairs, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.succ_mul, Nat.add_comm] using congrArg (fun n => ys.length+n) ih

/-- A literal finite list, of cardinality `2*(2*N+1)^3` with duplicates allowed. -/
def netIndices (N : Nat) : List (NetIndex N) :=
  pairs [false,true] (pairs (List.finRange (2*N+1))
    (pairs (List.finRange (2*N+1)) (List.finRange (2*N+1))))

theorem mem_netIndices (N : Nat) (i : NetIndex N) : i ∈ netIndices N := by
  obtain ⟨s,i,j,k⟩ := i
  have hs : s ∈ [false,true] := by cases s <;> simp
  exact mem_pairs hs (mem_pairs (List.mem_finRange i)
    (mem_pairs (List.mem_finRange j) (List.mem_finRange k)))

theorem netIndices_length (N : Nat) :
    (netIndices N).length = 2*((2*N+1)*((2*N+1)*(2*N+1))) := by
  simp only [netIndices, pairs_length, List.length_cons, List.length_nil, List.length_finRange]

/-- Enumerated exact unit points; the sign distinction is retained in the indices. -/
def net (N : Nat) (hN : 0 < N) : List UnitNorm := (netIndices N).map (netPoint N hN)

theorem selected_mem_net (N : Nat) (hN : 0 < N) (x : UnitNorm) :
    netPoint N hN (netIndex N x) ∈ net N hN :=
  List.mem_map.mpr ⟨netIndex N x,mem_netIndices N _,rfl⟩

theorem net_length (N : Nat) (hN : 0 < N) :
    (net N hN).length = 2*((2*N+1)*((2*N+1)*(2*N+1))) := by
  rw [net, List.length_map, netIndices_length]

end YMGap.RepTheory.RationalQuaternionSphereNets

#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.denominator_positive
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.stereographic
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.stereographic_chord
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.stereographic_lipschitz
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.inverseChart
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.inverseChart_bounds
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.stereographic_inverse
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.signed
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.chartSign_nonnegative
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.netPoint
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.netIndex
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.net_covers
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.netIndices
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.mem_netIndices
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.netIndices_length
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.net
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.selected_mem_net
#print axioms YMGap.RepTheory.RationalQuaternionSphereNets.net_length


