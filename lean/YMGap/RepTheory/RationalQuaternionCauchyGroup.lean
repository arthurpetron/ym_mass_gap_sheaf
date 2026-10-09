/-
# A group on the explicit-modulus rational quaternion Cauchy quotient

The distance is the literal four-coordinate squared chord.  Its null relation
is proved to be coordinatewise rational semantic equality.  Hamilton product
and conjugation descend using their proved metric estimates, and all group
laws hold on the resulting quotient.  Constant rows give a faithful group
homomorphism; in particular the two central signs remain distinct.

Approximation below consumes a SUPPLIED Cauchy row with its Type-valued
modulus.  No representative of an arbitrary quotient point is selected.
This file does not construct a completed distance, arbitrary quotient-sequence
completeness, a compact SU(2) identification, or a Haar functional extension.
-/

import YMGap.RepTheory.RationalQuaternionSphereNets
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.RepTheory.RationalQuaternionCauchyGroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.CRealSeminormCompletion
open SquaredSeminorm

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

private def sub (x y : RationalQuaternion) : RationalQuaternion :=
  ⟨x.r + -y.r, x.i + -y.i, x.j + -y.j, x.k + -y.k⟩

/-- Squared chord on the actual rational unit-quaternion carrier. -/
def chord (x y : UnitNorm) : Q' :=
  RationalQuaternionSphereNets.distSq x.val y.val

private theorem raw_nonnegative (x y : RationalQuaternion) :
    (0 : Q') ≤ RationalQuaternionSphereNets.distSq x y :=
  Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ (sq_nonneg _) (sq_nonneg _))
    (Q'.zero_le_add _ _ (sq_nonneg _) (sq_nonneg _))

theorem chord_nonnegative (x y : UnitNorm) : (0 : Q') ≤ chord x y :=
  raw_nonnegative x.val y.val

private theorem raw_congr {x x' y y' : RationalQuaternion}
    (hx : x.Equivalent x') (hy : y.Equivalent y') :
    RationalQuaternionSphereNets.distSq x y ≈
      RationalQuaternionSphereNets.distSq x' y' :=
  normSq_congr (x := sub x y) (y := sub x' y')
    ⟨ac hx.1 (nc hy.1), ac hx.2.1 (nc hy.2.1),
    ac hx.2.2.1 (nc hy.2.2.1), ac hx.2.2.2 (nc hy.2.2.2)⟩

theorem chord_congr {x x' y y' : UnitNorm}
    (hx : x.Equivalent x') (hy : y.Equivalent y') :
    chord x y ≈ chord x' y' := raw_congr hx hy

private theorem normSq_zero : normSq RationalQuaternion.zero ≈ 0 := by decide

private theorem raw_refl (x : RationalQuaternion) :
    RationalQuaternionSphereNets.distSq x x ≈ 0 := by
  have h : (sub x x).Equivalent RationalQuaternion.zero :=
    ⟨Q'.add_neg_self_eqv _, Q'.add_neg_self_eqv _,
      Q'.add_neg_self_eqv _, Q'.add_neg_self_eqv _⟩
  have hn : normSq (sub x x) ≈ normSq RationalQuaternion.zero :=
    normSq_congr (x := sub x x) (y := RationalQuaternion.zero) h
  change normSq (sub x x) ≈ 0
  exact Q'.eqv_trans (normSq (sub x x)) (normSq RationalQuaternion.zero) 0
    hn normSq_zero

theorem chord_refl (x : UnitNorm) : chord x x ≈ 0 := raw_refl x.val

private theorem diff_square_symm (a b : Q') :
    (a + -b)*(a + -b) ≈ (b + -a)*(b + -a) :=
  poly_identity_of_normal_eq
    ((PolyExpr.var 0 + -(PolyExpr.var 1))*(PolyExpr.var 0 + -(PolyExpr.var 1)))
    ((PolyExpr.var 1 + -(PolyExpr.var 0))*(PolyExpr.var 1 + -(PolyExpr.var 0)))
    (by decide) (fun | 0 => a | _ => b)

theorem chord_symm (x y : UnitNorm) : chord x y ≈ chord y x :=
  ac (ac (diff_square_symm _ _) (diff_square_symm _ _))
    (ac (diff_square_symm _ _) (diff_square_symm _ _))

private theorem sum_zero {a b : Q'} (ha : (0 : Q') ≤ a)
    (hb : (0 : Q') ≤ b) (h : a+b ≈ 0) : a ≈ 0 ∧ b ≈ 0 := by
  have ha0 : a ≤ 0 := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg a b hb) (Q'.le_of_eqv h)
  have hb0 : b ≤ 0 := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg b a ha)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv b a))
      (Q'.le_of_eqv h))
  exact ⟨Q'.eqv_of_le_le ha0 ha, Q'.eqv_of_le_le hb0 hb⟩

private theorem square_zero {a : Q'} (h : a*a ≈ 0) : a ≈ 0 := by
  have hn : a.num*a.num = 0 := by
    change (a.num*a.num)*(1 : Int) = (0 : Int)*((a*a).den : Int) at h
    simpa only [Int.mul_one, Int.zero_mul] using h
  have hz : a.num = 0 := by
    rcases Int.mul_eq_zero.mp hn with h0 | h0 <;> exact h0
  show a.num*(1 : Int) = (0 : Int)*(a.den : Int)
  simp only [hz, Int.zero_mul]

private theorem diff_zero {a b : Q'} (h : a + -b ≈ 0) : a ≈ b := by
  have hn : a.num*(b.den : Int) + (-b.num)*(a.den : Int) = 0 := by
    change (a.num*(b.den : Int) + (-b.num)*(a.den : Int))*(1 : Int) =
      (0 : Int)*((a + -b).den : Int) at h
    simpa only [Int.mul_one, Int.zero_mul] using h
  show a.num*(b.den : Int) = b.num*(a.den : Int)
  rw [Int.neg_mul] at hn
  omega

/-- No rational point is collapsed by the chord null relation. -/
theorem chord_zero_iff (x y : UnitNorm) : chord x y ≈ 0 ↔ x.Equivalent y := by
  constructor
  · intro h
    have hab := sum_zero
      (Q'.zero_le_add _ _ (sq_nonneg _) (sq_nonneg _))
      (Q'.zero_le_add _ _ (sq_nonneg _) (sq_nonneg _)) h
    have hri := sum_zero (sq_nonneg _) (sq_nonneg _) hab.1
    have hjk := sum_zero (sq_nonneg _) (sq_nonneg _) hab.2
    exact ⟨diff_zero (square_zero hri.1), diff_zero (square_zero hri.2),
      diff_zero (square_zero hjk.1), diff_zero (square_zero hjk.2)⟩
  · intro h
    exact Q'.eqv_trans _ _ _ (chord_congr (UnitNorm.semanticSetoid.iseqv.refl x)
      (UnitNorm.semanticSetoid.iseqv.symm h)) (chord_refl x)

private theorem scalar_triangle (a b c : Q') :
    (a + -c)*(a + -c) ≤
      ((a + -b)*(a + -b)+(a + -b)*(a + -b)) +
        ((b + -c)*(b + -c)+(b + -c)*(b + -c)) := by
  have h := Q'.add_le_self_of_nonneg ((a + -c)*(a + -c))
    ((a+c + -(2*b))*(a+c + -(2*b))) (sq_nonneg _)
  apply Q'.le_trans' _ _ _ h
  apply Q'.le_of_eqv
  exact poly_identity_of_normal_eq
    ((PolyExpr.var 0 + -(PolyExpr.var 2))*(PolyExpr.var 0 + -(PolyExpr.var 2)) +
      (PolyExpr.var 0+PolyExpr.var 2 + -(2*PolyExpr.var 1))*
        (PolyExpr.var 0+PolyExpr.var 2 + -(2*PolyExpr.var 1)))
    (((PolyExpr.var 0 + -(PolyExpr.var 1))*(PolyExpr.var 0 + -(PolyExpr.var 1))+
      (PolyExpr.var 0 + -(PolyExpr.var 1))*(PolyExpr.var 0 + -(PolyExpr.var 1)))+
      ((PolyExpr.var 1 + -(PolyExpr.var 2))*(PolyExpr.var 1 + -(PolyExpr.var 2))+
      (PolyExpr.var 1 + -(PolyExpr.var 2))*(PolyExpr.var 1 + -(PolyExpr.var 2))))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

private theorem regroup_triangle (a b c d e f g h : Q') :
    (((a+a)+(e+e))+((b+b)+(f+f)))+
      (((c+c)+(g+g))+((d+d)+(h+h))) ≈
    (((a+b)+(c+d))+((a+b)+(c+d)))+
      (((e+f)+(g+h))+((e+f)+(g+h))) :=
  poly_identity_of_normal_eq
    ((((PolyExpr.var 0+PolyExpr.var 0)+(PolyExpr.var 4+PolyExpr.var 4))+
      ((PolyExpr.var 1+PolyExpr.var 1)+(PolyExpr.var 5+PolyExpr.var 5)))+
      (((PolyExpr.var 2+PolyExpr.var 2)+(PolyExpr.var 6+PolyExpr.var 6))+
      ((PolyExpr.var 3+PolyExpr.var 3)+(PolyExpr.var 7+PolyExpr.var 7))))
    ((((PolyExpr.var 0+PolyExpr.var 1)+(PolyExpr.var 2+PolyExpr.var 3))+
      ((PolyExpr.var 0+PolyExpr.var 1)+(PolyExpr.var 2+PolyExpr.var 3)))+
      (((PolyExpr.var 4+PolyExpr.var 5)+(PolyExpr.var 6+PolyExpr.var 7))+
      ((PolyExpr.var 4+PolyExpr.var 5)+(PolyExpr.var 6+PolyExpr.var 7))))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | _ => h)

theorem chord_triangle (x y z : UnitNorm) :
    chord x z ≤ (chord x y+chord x y)+(chord y z+chord y z) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add
      (Q'.add_le_add (scalar_triangle x.val.r y.val.r z.val.r)
        (scalar_triangle x.val.i y.val.i z.val.i))
      (Q'.add_le_add (scalar_triangle x.val.j y.val.j z.val.j)
        (scalar_triangle x.val.k y.val.k z.val.k)))
    (Q'.le_of_eqv (regroup_triangle _ _ _ _ _ _ _ _))

/-! ## Exact metric behavior of the genuine Hamilton operations -/

private structure QuaternionExpr where
  r : PE
  i : PE
  j : PE
  k : PE

private def ev (rho : Nat → Q') (x : QuaternionExpr) : RationalQuaternion :=
  ⟨eval rho x.r, eval rho x.i, eval rho x.j, eval rho x.k⟩

private def qvar (n : Nat) : QuaternionExpr :=
  ⟨.var n, .var (n+1), .var (n+2), .var (n+3)⟩

private def qsub (x y : QuaternionExpr) : QuaternionExpr :=
  ⟨x.r + -y.r, x.i + -y.i, x.j + -y.j, x.k + -y.k⟩

private def qconj (x : QuaternionExpr) : QuaternionExpr :=
  ⟨x.r, -x.i, -x.j, -x.k⟩

private def qmul (x y : QuaternionExpr) : QuaternionExpr :=
  ⟨(x.r*y.r + -(x.i*y.i))+(-(x.j*y.j) + -(x.k*y.k)),
    (x.r*y.i+x.i*y.r)+(x.j*y.k + -(x.k*y.j)),
    (x.r*y.j + -(x.i*y.k))+(x.j*y.r+x.k*y.i),
    (x.r*y.k+x.i*y.j)+(-(x.j*y.i)+x.k*y.r)⟩

private theorem ev_equivalent (rho : Nat → Q') (x y : QuaternionExpr)
    (h : normalize x.r = normalize y.r ∧ normalize x.i = normalize y.i ∧
      normalize x.j = normalize y.j ∧ normalize x.k = normalize y.k) :
    (ev rho x).Equivalent (ev rho y) :=
  ⟨poly_identity_of_normal_eq _ _ h.1 rho,
    poly_identity_of_normal_eq _ _ h.2.1 rho,
    poly_identity_of_normal_eq _ _ h.2.2.1 rho,
    poly_identity_of_normal_eq _ _ h.2.2.2 rho⟩

private def environment (x y z : RationalQuaternion) : Nat → Q'
  | 0 => x.r | 1 => x.i | 2 => x.j | 3 => x.k
  | 4 => y.r | 5 => y.i | 6 => y.j | 7 => y.k
  | 8 => z.r | 9 => z.i | 10 => z.j | _ => z.k

private theorem mul_sub (z x y : RationalQuaternion) :
    (sub (RationalQuaternion.mul z x) (RationalQuaternion.mul z y)).Equivalent
      (RationalQuaternion.mul z (sub x y)) :=
  ev_equivalent (environment z x y)
    (qsub (qmul (qvar 0) (qvar 4)) (qmul (qvar 0) (qvar 8)))
    (qmul (qvar 0) (qsub (qvar 4) (qvar 8))) (by decide)

private theorem sub_mul (x y z : RationalQuaternion) :
    (sub (RationalQuaternion.mul x z) (RationalQuaternion.mul y z)).Equivalent
      (RationalQuaternion.mul (sub x y) z) :=
  ev_equivalent (environment x y z)
    (qsub (qmul (qvar 0) (qvar 8)) (qmul (qvar 4) (qvar 8)))
    (qmul (qsub (qvar 0) (qvar 4)) (qvar 8)) (by decide)

private theorem conj_sub (x y : RationalQuaternion) :
    (sub (RationalQuaternion.conj x) (RationalQuaternion.conj y)).Equivalent
      (RationalQuaternion.conj (sub x y)) :=
  ev_equivalent (environment x y x)
    (qsub (qconj (qvar 0)) (qconj (qvar 4)))
    (qconj (qsub (qvar 0) (qvar 4))) (by decide)

theorem chord_mul_left (z x y : UnitNorm) :
    chord (UnitNorm.mul z x) (UnitNorm.mul z y) ≈ chord x y := by
  calc
    _ ≈ normSq (RationalQuaternion.mul z.val (sub x.val y.val)) :=
      normSq_congr (mul_sub z.val x.val y.val)
    _ ≈ normSq z.val * normSq (sub x.val y.val) := normSq_mul _ _
    _ ≈ 1 * normSq (sub x.val y.val) := mc z.unitNorm (Q'.eqv_refl _)
    _ ≈ chord x y := Q'.one_mul_eqv _

theorem chord_mul_right (x y z : UnitNorm) :
    chord (UnitNorm.mul x z) (UnitNorm.mul y z) ≈ chord x y := by
  calc
    _ ≈ normSq (RationalQuaternion.mul (sub x.val y.val) z.val) :=
      normSq_congr (sub_mul x.val y.val z.val)
    _ ≈ normSq (sub x.val y.val) * normSq z.val := normSq_mul _ _
    _ ≈ normSq (sub x.val y.val) * 1 := mc (Q'.eqv_refl _) z.unitNorm
    _ ≈ chord x y := Q'.mul_one_eqv _

theorem chord_inverse (x y : UnitNorm) :
    chord (UnitNorm.inv x) (UnitNorm.inv y) ≈ chord x y := by
  have hsub :
      normSq (sub (RationalQuaternion.conj x.val) (RationalQuaternion.conj y.val)) ≈
        normSq (RationalQuaternion.conj (sub x.val y.val)) :=
    normSq_congr
      (x := sub (RationalQuaternion.conj x.val) (RationalQuaternion.conj y.val))
      (y := RationalQuaternion.conj (sub x.val y.val)) (conj_sub x.val y.val)
  have hnorm : normSq (RationalQuaternion.conj (sub x.val y.val)) ≈
      normSq (sub x.val y.val) := normSq_conj (sub x.val y.val)
  change normSq (sub (RationalQuaternion.conj x.val) (RationalQuaternion.conj y.val)) ≈
    normSq (sub x.val y.val)
  exact Q'.eqv_trans
    (normSq (sub (RationalQuaternion.conj x.val) (RationalQuaternion.conj y.val)))
    (normSq (RationalQuaternion.conj (sub x.val y.val)))
    (normSq (sub x.val y.val)) hsub hnorm

theorem chord_product (x x' y y' : UnitNorm) :
    chord (UnitNorm.mul x y) (UnitNorm.mul x' y') ≤
      (chord x x'+chord x x')+(chord y y'+chord y y') :=
  Q'.le_trans' _ _ _
    (chord_triangle (UnitNorm.mul x y) (UnitNorm.mul x' y) (UnitNorm.mul x' y'))
    (Q'.le_of_eqv (ac
      (ac (chord_mul_right x x' y) (chord_mul_right x x' y))
      (ac (chord_mul_left x' y y') (chord_mul_left x' y y'))))

/-! ## The actual point-Cauchy quotient and its group -/

private theorem constant_quadratic_bound (a b c : Q')
    (h : a ≤ (b+b)+(c+c)) :
    CReal.leEv (CReal.ofQ' a)
      (CReal.add (CReal.add (CReal.ofQ' b) (CReal.ofQ' b))
        (CReal.add (CReal.ofQ' c) (CReal.ofQ' c))) := by
  rw [CReal.ofQ'_add b b, CReal.ofQ'_add c c, CReal.ofQ'_add (b+b) (c+c)]
  exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' h)

/-- The literal rational chord, embedded as constant constructive reals. -/
def chordSeminorm : SquaredSeminorm where
  Carrier := UnitNorm
  distSq := fun x y => CReal.ofQ' (chord x y)
  distSq_refl := fun x => CReal.ofQ'_equiv_of_eqv (chord_refl x)
  distSq_symm := fun x y => CReal.ofQ'_equiv_of_eqv (chord_symm x y)
  distSq_nonneg := fun x y =>
    CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (chord_nonnegative x y))
  distSq_triangle := fun x y z =>
    constant_quadratic_bound (chord x z) (chord x y) (chord y z)
      (chord_triangle x y z)
  null_congr := by
    intro x x' y y' hx hy
    have hx0 : chord x x' ≈ 0 :=
      CReal.ofQ'_eqv_zero_of_equiv (x := chord x x') hx
    have hy0 : chord y y' ≈ 0 :=
      CReal.ofQ'_eqv_zero_of_equiv (x := chord y y') hy
    have hxsem : x.Equivalent x' := (chord_zero_iff x x').mp hx0
    have hysem : y.Equivalent y' := (chord_zero_iff y y').mp hy0
    have hchord : chord x y ≈ chord x' y' := chord_congr hxsem hysem
    exact CReal.ofQ'_equiv_of_eqv hchord

theorem null_iff_semantic (x y : UnitNorm) :
    chordSeminorm.Null x y ↔ x.Equivalent y := by
  constructor
  · intro h
    exact (chord_zero_iff x y).mp (CReal.ofQ'_eqv_zero_of_equiv h)
  · intro h
    exact CReal.ofQ'_equiv_of_eqv ((chord_zero_iff x y).mpr h)

def multiplication : chordSeminorm.BinaryQuadraticLipschitz where
  toFun := UnitNorm.mul
  contraction := fun x x' y y' =>
    constant_quadratic_bound (chord (UnitNorm.mul x y) (UnitNorm.mul x' y'))
      (chord x x') (chord y y') (chord_product x x' y y')

def inversion : chordSeminorm.Nonexpansive where
  toFun := UnitNorm.inv
  contraction := fun x y =>
    CReal.leEv_of_equiv (CReal.ofQ'_equiv_of_eqv (chord_inverse x y))

abbrev CauchyPoint := chordSeminorm.Cauchy
abbrev Point := chordSeminorm.Completion

def completedOne : Point := chordSeminorm.embedRep unitOne
def completedMul : Point → Point → Point := multiplication.completionMap
def completedInv : Point → Point := inversion.completionMap

private theorem pointwise_eq {X Y : CauchyPoint}
    (h : ∀ n, (X.seq n).Equivalent (Y.seq n)) :
    Quotient.mk chordSeminorm.completionSetoid X =
      Quotient.mk chordSeminorm.completionSetoid Y :=
  Quotient.sound ⟨NonexpansiveSemigroup.closeOfPointwiseNull
    (D := chordSeminorm) (fun n => (null_iff_semantic _ _).mpr (h n))⟩

theorem completedMul_assoc (x y z : Point) :
    completedMul (completedMul x y) z = completedMul x (completedMul y z) := by
  refine Quotient.inductionOn x (fun X => ?_)
  refine Quotient.inductionOn y (fun Y => ?_)
  refine Quotient.inductionOn z (fun Z => ?_)
  exact pointwise_eq (fun n => UnitNorm.mul_assoc (X.seq n) (Y.seq n) (Z.seq n))

theorem completedOne_mul (x : Point) : completedMul completedOne x = x := by
  refine Quotient.inductionOn x (fun X => ?_)
  exact pointwise_eq (fun n => UnitNorm.one_mul (X.seq n))

theorem completedMul_one (x : Point) : completedMul x completedOne = x := by
  refine Quotient.inductionOn x (fun X => ?_)
  exact pointwise_eq (fun n => UnitNorm.mul_one (X.seq n))

theorem completedInv_mul (x : Point) : completedMul (completedInv x) x = completedOne := by
  refine Quotient.inductionOn x (fun X => ?_)
  exact pointwise_eq (fun n => UnitNorm.inv_mul (X.seq n))

theorem completedMul_inv (x : Point) : completedMul x (completedInv x) = completedOne := by
  refine Quotient.inductionOn x (fun X => ?_)
  exact pointwise_eq (fun n => UnitNorm.mul_inv (X.seq n))

/-- A group on the explicit-modulus point-Cauchy quotient, with equality as
its setoid.  No metric completeness or compactness assertion is included. -/
def completedGroup : ConstructiveGroup where
  Carrier := Point
  setoid := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  one := completedOne
  mul := completedMul
  inv := completedInv
  mul_congr := by intro a a' b b' ha hb; cases ha; cases hb; rfl
  inv_congr := by intro a b h; cases h; rfl
  mul_assoc := completedMul_assoc
  one_mul := completedOne_mul
  mul_one := completedMul_one
  inv_mul := completedInv_mul
  mul_inv := completedMul_inv

/-! ## Faithful rational embedding and explicit represented approximation -/

def embed (x : UnitNorm) : Point := chordSeminorm.embedRep x

theorem embed_mul (x y : UnitNorm) :
    embed (UnitNorm.mul x y) = completedMul (embed x) (embed y) :=
  pointwise_eq (fun _ => UnitNorm.semanticSetoid.iseqv.refl _)

theorem embed_inv (x : UnitNorm) : embed (UnitNorm.inv x) = completedInv (embed x) :=
  pointwise_eq (fun _ => UnitNorm.semanticSetoid.iseqv.refl _)

def rationalEmbedding : ConstructiveGroup.Hom UnitNorm.group completedGroup where
  toFun := embed
  map_equivalent := fun h => chordSeminorm.embedRep_eq_of_null
    ((null_iff_semantic _ _).mpr h)
  map_one := rfl
  map_mul := embed_mul

private theorem constant_le_reflect {a b : Q'}
    (h : CReal.leEv (CReal.ofQ' a) (CReal.ofQ' b)) : a ≤ b := by
  apply Q'.le_of_le_add_mul_invSucc a b 1
  intro N
  obtain ⟨M, hM⟩ := h (Q'.invSucc N) (Q'.invSucc_pos N)
  have ht : a ≤ b + Q'.invSucc N := hM M (Nat.le_refl M)
  have he : b + Q'.ofNat 1 * Q'.invSucc N ≈ b + Q'.invSucc N :=
    ac (Q'.eqv_refl _) (Q'.eqv_trans _ _ _
      (mc (show Q'.ofNat 1 ≈ (1 : Q') by decide) (Q'.eqv_refl _))
      (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv he)

/-- Literal equality of embedded rational points is exactly semantic
coordinate equality; no rational geometry is lost in the quotient. -/
theorem embed_eq_iff (x y : UnitNorm) : embed x = embed y ↔ x.Equivalent y := by
  constructor
  · intro h
    have hr : chordSeminorm.CompletionRel (chordSeminorm.constant x)
        (chordSeminorm.constant y) := Quotient.exact h
    rcases hr with ⟨hc⟩
    have hz : chord x y ≤ 0 := by
      apply Q'.le_zero_of_forall_invSucc
      intro N
      exact constant_le_reflect (hc.close (Q'.invSucc N) (Q'.invSucc_pos N)
        (hc.modulus (Q'.invSucc N)) (Nat.le_refl _))
    exact (chord_zero_iff x y).mp (Q'.eqv_of_le_le hz (chord_nonnegative x y))
  · intro h
    exact chordSeminorm.embedRep_eq_of_null ((null_iff_semantic x y).mpr h)

theorem rationalEmbedding_semantic_injective {x y : UnitNorm}
    (h : completedGroup.Equivalent (rationalEmbedding.toFun x)
      (rationalEmbedding.toFun y)) : x.Equivalent y := (embed_eq_iff x y).mp h

/-- In particular the north and south central signs are NOT identified. -/
theorem embedded_signs_distinct : embed unitOne ≠ embed unitNegativeOne := by
  intro h
  have he := (embed_eq_iff unitOne unitNegativeOne).mp h
  have hbad : (1 : Q').eqv (-1) := he.1
  exact (by decide : ¬ (1 : Q').eqv (-1)) hbad

/-- The sampled rational point and its original tail stage remain data. -/
def rowApproximation (X : CauchyPoint) (epsilon : Q') : UnitNorm :=
  X.seq (X.modulus epsilon)

theorem rowApproximation_bound (X : CauchyPoint) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat) (hn : X.modulus epsilon ≤ n) :
    chord (rowApproximation X epsilon) (X.seq n) ≤ epsilon :=
  constant_le_reflect (X.isCauchy epsilon hepsilon _ n (Nat.le_refl _) hn)

/-! ## The finite nets cover every supplied row tail with a computed index -/

private theorem fraction_add (a b : Int) (d : Nat) (hd : 0 < d) :
    Q'.mkPos a d hd + Q'.mkPos b d hd ≈ Q'.mkPos (a+b) d hd := by
  change (a*((Q'.mkPos b d hd).den : Int)+b*((Q'.mkPos a d hd).den : Int))*
    ((Q'.mkPos (a+b) d hd).den : Int) =
      (a+b)*((Q'.mkPos a d hd+Q'.mkPos b d hd).den : Int)
  simp only [Q'.add_den_cast, Q'.mkPos_den, Int.add_mul, Int.mul_assoc]

/-- The exact squared-error tolerance used to sample a row for the N-net. -/
def netTolerance (N : Nat) (hN : 0 < N) : Q' :=
  Q'.mkPos 12 (N*N) (Nat.mul_pos hN hN)

theorem netTolerance_positive (N : Nat) (hN : 0 < N) :
    (0 : Q') < netTolerance N hN := by
  change (0 : Int)*((netTolerance N hN).den : Int) < 12*(1 : Int)
  simp only [Int.zero_mul, Int.mul_one]
  decide

def rowNetStage (X : CauchyPoint) (N : Nat) (hN : 0 < N) : Nat :=
  X.modulus (netTolerance N hN)

def rowNetIndex (X : CauchyPoint) (N : Nat) (hN : 0 < N) :
    RationalQuaternionSphereNets.NetIndex N :=
  RationalQuaternionSphereNets.netIndex N (X.seq (rowNetStage X N hN))

def rowNetPoint (X : CauchyPoint) (N : Nat) (hN : 0 < N) : UnitNorm :=
  RationalQuaternionSphereNets.netPoint N hN (rowNetIndex X N hN)

theorem rowNetPoint_mem (X : CauchyPoint) (N : Nat) (hN : 0 < N) :
    rowNetPoint X N hN ∈ RationalQuaternionSphereNets.net N hN :=
  RationalQuaternionSphereNets.selected_mem_net N hN (X.seq (rowNetStage X N hN))

/-- Computable finite-net coverage of a supplied Cauchy tail.  Both the stage
and index are defined above; the bound is literal rational squared chord. -/
theorem rowNet_tail_bound (X : CauchyPoint) (N : Nat) (hN : 0 < N)
    (k : Nat) (hk : rowNetStage X N hN ≤ k) :
    chord (rowNetPoint X N hN) (X.seq k) ≤
      Q'.mkPos 48 (N*N) (Nat.mul_pos hN hN) := by
  let delta := netTolerance N hN
  let sample := X.seq (rowNetStage X N hN)
  have hnet : chord (rowNetPoint X N hN) sample ≤ delta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (chord_symm _ _))
      (RationalQuaternionSphereNets.net_covers N hN sample)
  have htail : chord sample (X.seq k) ≤ delta :=
    rowApproximation_bound X delta (netTolerance_positive N hN) k hk
  have hsum : (chord (rowNetPoint X N hN) sample+
      chord (rowNetPoint X N hN) sample)+(chord sample (X.seq k)+
      chord sample (X.seq k)) ≤ (delta+delta)+(delta+delta) :=
    Q'.add_le_add (Q'.add_le_add hnet hnet) (Q'.add_le_add htail htail)
  have he : (delta+delta)+(delta+delta) ≈
      Q'.mkPos 48 (N*N) (Nat.mul_pos hN hN) :=
    Q'.eqv_trans _ _ _
      (ac (fraction_add 12 12 _ _) (fraction_add 12 12 _ _))
      (fraction_add 24 24 _ _)
  exact Q'.le_trans' _ _ _ (chord_triangle _ sample _)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv he))

#print axioms chord_nonnegative
#print axioms chord_congr
#print axioms chord_refl
#print axioms chord_symm
#print axioms chord_zero_iff
#print axioms chord_triangle
#print axioms chord_mul_left
#print axioms chord_mul_right
#print axioms chord_inverse
#print axioms chord_product
#print axioms chordSeminorm
#print axioms null_iff_semantic
#print axioms multiplication
#print axioms inversion
#print axioms completedMul_assoc
#print axioms completedOne_mul
#print axioms completedMul_one
#print axioms completedInv_mul
#print axioms completedMul_inv
#print axioms completedGroup
#print axioms embed_mul
#print axioms embed_inv
#print axioms rationalEmbedding
#print axioms embed_eq_iff
#print axioms rationalEmbedding_semantic_injective
#print axioms embedded_signs_distinct
#print axioms rowApproximation
#print axioms rowApproximation_bound
#print axioms netTolerance_positive
#print axioms rowNetStage
#print axioms rowNetIndex
#print axioms rowNetPoint_mem
#print axioms rowNet_tail_bound

end YMGap.RepTheory.RationalQuaternionCauchyGroup
