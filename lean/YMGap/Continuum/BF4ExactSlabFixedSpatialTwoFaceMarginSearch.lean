/-
# Complete rational direction search on an ORIGINAL two-face margin plane

The algorithm classifies a binary quadratic form without division: it returns
an explicit positive rational direction or proves the entire rational plane
nonpositive. Applied to exactly two distinct original faces, it preserves both
off-diagonal entries of the SAME joint covariance/jump pencil. A successful
direction is sent to the EXISTING finite reference checker, which still checks
the original cutoff modulus and tolerance at that same pivot.

No useful successful Yang--Mills instance, scaling family, or EVERY-state gap
is asserted. The small closed regression tests below are generic arithmetic,
not original gauge-theory instances.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginPencil
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginSearch

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (qListSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginPencil
open YMGap.Continuum.BF4ExactSlabFixedSpatialCollectedFamilyMargin (pairing)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression)

local infix:50 " ≈ " => Q'.eqv

namespace Binary

/-- The cross coefficient is retained with its sign. -/
def value (a b d x y : Q') : Q' :=
  a*(x*x)+2*(b*(x*y))+d*(y*y)

def determinant (a b d : Q') : Q' := a*d-b*b

structure Direction (a b d : Q') : Type where
  x : Q'
  y : Q'
  positive : (0 : Q') < value a b d x y

/-- Rejection contains a proof for EVERY rational direction, not just axes. -/
inductive Result (a b d : Q') : Type
  | positive (direction : Direction a b d)
  | nonpositive (bound : ∀ x y : Q', value a b d x y ≤ (0 : Q'))

private theorem nonpos_of_not_pos {a : Q'} (h : ¬ (0 : Q') < a) : a ≤ (0 : Q') := by
  change ¬ (0 : Int)*a.den < a.num*1 at h
  change a.num*1 ≤ (0 : Int)*a.den
  omega

private theorem nonneg_of_not_neg {a : Q'} (h : ¬ a < (0 : Q')) : (0 : Q') ≤ a := by
  change ¬ a.num*1 < (0 : Int)*a.den at h
  change (0 : Int)*a.den ≤ a.num*1
  omega

private theorem zero_of_not_pos_not_neg {a : Q'}
    (hpos : ¬ (0 : Q') < a) (hneg : ¬ a < (0 : Q')) : a ≈ 0 := by
  change ¬ (0 : Int)*a.den < a.num*1 at hpos
  change ¬ a.num*1 < (0 : Int)*a.den at hneg
  change a.num*1 = (0 : Int)*a.den
  omega

private theorem neg_positive {a : Q'} (h : a < (0 : Q')) : (0 : Q') < -a := by
  change a.num*1 < (0 : Int)*a.den at h
  change (0 : Int)*a.den < -a.num*1
  omega

private theorem positive_of_eqv {a b : Q'} (ha : (0 : Q') < a) (hab : a ≈ b) :
    (0 : Q') < b := Q'.pos_of_lt_of_le ha (Q'.le_of_eqv hab)

private theorem square_positive {b : Q'} (hb : ¬ b ≈ 0) : (0 : Q') < b*b := by
  change ¬ b.num*1 = (0 : Int)*b.den at hb
  show (0 : Int)*((b*b).den : Int) < (b.num*b.num)*1
  have hn : b.num ≠ 0 := by omega
  by_cases hp : (0 : Int) < b.num
  · have hs := Int.mul_pos hp hp
    omega
  · have hm : b.num < 0 := by omega
    have hs := Int.mul_pos_of_neg_of_neg hm hm
    omega

private theorem negative_factor_nonpos {a t : Q'} (ha : a < (0 : Q'))
    (h : (0 : Q') ≤ a*t) : t ≤ (0 : Q') := by
  change a.num*1 < (0 : Int)*a.den at ha
  change (0 : Int)*((a*t).den : Int) ≤ (a.num*t.num)*1 at h
  change t.num*1 ≤ (0 : Int)*t.den
  by_cases ht : (0 : Int) < t.num
  · have han : a.num < 0 := by omega
    have hh := Int.mul_neg_of_neg_of_pos han ht
    omega
  · omega

private theorem axis_x (a b d : Q') : value a b d 1 0 ≈ a :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.mul (.const 1) (.const 1)))
      (.mul (.const 2) (.mul (.var 1) (.mul (.const 1) (.const 0)))))
      (.mul (.var 2) (.mul (.const 0) (.const 0))))
    (.var 0) (by decide) (fun | 0 => a | 1 => b | _ => d)

private theorem axis_y (a b d : Q') : value a b d 0 1 ≈ d :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.mul (.const 0) (.const 0)))
      (.mul (.const 2) (.mul (.var 1) (.mul (.const 0) (.const 1)))))
      (.mul (.var 2) (.mul (.const 1) (.const 1))))
    (.var 2) (by decide) (fun | 0 => a | 1 => b | _ => d)

/-- Cleared square completion also handles a singular determinant. -/
theorem completed_square (a b d x y : Q') :
    a*value a b d x y ≈ (a*x+b*y)*(a*x+b*y)+determinant a b d*(y*y) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.add (.mul (.var 0) (.mul (.var 3) (.var 3)))
      (.mul (.const 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))))
      (.mul (.var 2) (.mul (.var 4) (.var 4)))))
    (.add (.mul (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4)))
      (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))))
      (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
        (.mul (.var 4) (.var 4))))
    (by decide) (fun | 0 => a | 1 => b | 2 => d | 3 => x | _ => y)

/-- An explicit signed direction; no inverse of the pivot is needed. -/
theorem negative_pivot_direction (a b d : Q') (ha : a < (0 : Q'))
    (hdet : determinant a b d < (0 : Q')) :
    (0 : Q') < value a b d b (-a) := by
  have hp := Q'.mul_pos (neg_positive ha) (neg_positive hdet)
  have he : value a b d b (-a) ≈ (-a)*(-(determinant a b d)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.const 2) (.mul (.var 1) (.mul (.var 1) (.neg (.var 0))))))
        (.mul (.var 2) (.mul (.neg (.var 0)) (.neg (.var 0)))))
      (.mul (.neg (.var 0))
        (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))))
      (by decide) (fun | 0 => a | 1 => b | _ => d)
  exact positive_of_eqv hp (Q'.eqv_symm he)

theorem negative_pivot_nonpositive (a b d : Q') (ha : a < (0 : Q'))
    (hdet : (0 : Q') ≤ determinant a b d) :
    ∀ x y : Q', value a b d x y ≤ (0 : Q') := by
  intro x y
  have hsum := Q'.zero_le_add _ _
    (SumOfSquares.q_mul_self_nonneg (a*x+b*y))
    (Q'.mul_nonneg _ _ hdet (SumOfSquares.q_mul_self_nonneg y))
  exact negative_factor_nonpos ha
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (completed_square a b d x y)))

private theorem value_zero_first {a : Q'} (ha : a ≈ 0) (b d x y : Q') :
    value a b d x y ≈ value 0 b d x y :=
  Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ (x*x) ha) (Q'.eqv_refl _))
    (Q'.eqv_refl _)

/-- Even a zero diagonal cannot justify rejecting a nonzero cross term. -/
theorem zero_pivot_direction (a b d : Q') (ha : a ≈ 0) (hb : ¬ b ≈ 0) :
    (0 : Q') < value a b d (1-d) (2*b) := by
  have hp := Q'.mul_pos (by decide : (0 : Q') < 4) (square_positive hb)
  have he : value a b d (1-d) (2*b) ≈ 4*(b*b) :=
    Q'.eqv_trans _ _ _ (value_zero_first ha b d (1-d) (2*b))
      (poly_identity_of_normal_eq
        (.add (.add
          (.mul (.const 0) (.mul (.add (.const 1) (.neg (.var 1)))
            (.add (.const 1) (.neg (.var 1)))))
          (.mul (.const 2) (.mul (.var 0)
            (.mul (.add (.const 1) (.neg (.var 1))) (.mul (.const 2) (.var 0))))))
          (.mul (.var 1) (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))))
        (.mul (.const 4) (.mul (.var 0) (.var 0)))
        (by decide) (fun | 0 => b | _ => d))
  exact positive_of_eqv hp (Q'.eqv_symm he)

theorem zero_pivot_nonpositive (a b d : Q') (ha : a ≈ 0) (hb : b ≈ 0)
    (hd : d ≤ (0 : Q')) : ∀ x y : Q', value a b d x y ≤ (0 : Q') := by
  intro x y
  have hm : 2*(b*(x*y)) ≈ 2*((0 : Q')*(x*y)) :=
    Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_eqv_congr_right _ _ (x*y) hb)
  have he : value a b d x y ≈ d*(y*y) :=
    Q'.eqv_trans _ _ _ (value_zero_first ha b d x y)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _) hm) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.const 0) (.mul (.var 1) (.var 1)))
            (.mul (.const 2) (.mul (.const 0) (.mul (.var 1) (.var 2)))))
            (.mul (.var 0) (.mul (.var 2) (.var 2))))
          (.mul (.var 0) (.mul (.var 2) (.var 2)))
          (by decide) (fun | 0 => d | 1 => x | _ => y)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (y*y) hd (SumOfSquares.q_mul_self_nonneg y))
      (Q'.le_of_eqv (Q'.zero_mul_eqv (y*y))))

/-- Exhaustive, computable classification. All choices are rational decisions;
the result carries either the constructed direction or whole-plane rejection. -/
def classify (a b d : Q') : Result a b d :=
  if ha : (0 : Q') < a then
    .positive ⟨1, 0, positive_of_eqv ha (Q'.eqv_symm (axis_x a b d))⟩
  else if hd : (0 : Q') < d then
    .positive ⟨0, 1, positive_of_eqv hd (Q'.eqv_symm (axis_y a b d))⟩
  else if han : a < (0 : Q') then
    if hdet : determinant a b d < (0 : Q') then
      .positive ⟨b, -a, negative_pivot_direction a b d han hdet⟩
    else
      .nonpositive (negative_pivot_nonpositive a b d han (nonneg_of_not_neg hdet))
  else
    if hb : b ≈ 0 then
      .nonpositive (zero_pivot_nonpositive a b d (zero_of_not_pos_not_neg ha han)
        hb (nonpos_of_not_pos hd))
    else
      .positive ⟨1-d, 2*b, zero_pivot_direction a b d
        (zero_of_not_pos_not_neg ha han) hb⟩

/-- Proof-free data computation, independently usable by a certificate search. -/
def direction (a b d : Q') : Option (Q' × Q') :=
  if (0 : Q') < a then some (1, 0)
  else if (0 : Q') < d then some (0, 1)
  else if a < (0 : Q') then
    if determinant a b d < (0 : Q') then some (b, -a) else none
  else if b ≈ 0 then none else some (1-d, 2*b)

/-- The proof-free computation and the complete proof-bearing classifier agree. -/
theorem direction_classify (a b d : Q') : direction a b d = (match classify a b d with
  | .positive v => some (v.x, v.y)
  | .nonpositive _ => none) := by
  by_cases ha : (0 : Q') < a
  · simp only [direction, classify, if_pos ha, dif_pos ha]
  · by_cases hd : (0 : Q') < d
    · simp only [direction, classify, if_neg ha, dif_neg ha, if_pos hd, dif_pos hd]
    · by_cases han : a < (0 : Q')
      · by_cases hdet : determinant a b d < (0 : Q')
        · simp only [direction, classify, if_neg ha, dif_neg ha, if_neg hd, dif_neg hd,
            if_pos han, dif_pos han, if_pos hdet, dif_pos hdet]
        · simp only [direction, classify, if_neg ha, dif_neg ha, if_neg hd, dif_neg hd,
            if_pos han, dif_pos han, if_neg hdet, dif_neg hdet]
      · by_cases hb : b ≈ 0
        · simp only [direction, classify, if_neg ha, dif_neg ha, if_neg hd, dif_neg hd,
            if_neg han, dif_neg han, if_pos hb, dif_pos hb]
        · simp only [direction, classify, if_neg ha, dif_neg ha, if_neg hd, dif_neg hd,
            if_neg han, dif_neg han, if_neg hb, dif_neg hb]

theorem signed_cross_regression : direction (-1) (-2) (-1) = some (-2, 1) := by decide
theorem zero_pivot_regression : direction 0 (-1) (-4) = some (5, -2) := by decide
theorem singular_rejection_regression : direction (-1) (-1) (-1) = none := by decide
theorem zero_rejection_regression : direction 0 0 0 = none := by decide
theorem axis_regression : direction (-1) 7 1 = some (0, 1) := by decide

end Binary

/-- A computed original coefficient function; faces outside the pair get zero. -/
def profile (p q : Z4Plaq) (x y : Q') (r : Z4Plaq) : Q' :=
  if r = p then x else if r = q then y else 0

theorem profile_at_first (p q : Z4Plaq) (x y : Q') : profile p q x y p = x := by
  simp only [profile, ite_true]

theorem profile_at_second {p q : Z4Plaq} (hpq : p ≠ q) (x y : Q') :
    profile p q x y q = y := by
  simp only [profile, if_neg (Ne.symm hpq), ite_true]

/-- Both ordered original cross entries enter, regardless of representation. -/
def crossEntry (w : Q') (K width depth : Nat) (p q : Z4Plaq) (c : Q') : Q' :=
  HalfPow.half*(pencilEntry w K width depth [p,q] c p q+
    pencilEntry w K width depth [p,q] c q p)

private theorem cross_double (u v x y : Q') :
    2*((HalfPow.half*(u+v))*(x*y)) ≈ (u+v)*(x*y) := by
  have he : 2*((HalfPow.half*(u+v))*(x*y)) ≈
      (2*HalfPow.half)*((u+v)*(x*y)) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.mul (.var 3) (.var 4))))
      (.mul (.mul (.const 2) (.var 0))
        (.mul (.add (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
      (by decide) (fun | 0 => HalfPow.half | 1 => u | 2 => v | 3 => x | _ => y)
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (2 : Q')*HalfPow.half ≈ 1))
      (Q'.one_mul_eqv _))

theorem pencil_two_faces (w : Q') (K width depth : Nat) (p q : Z4Plaq)
    (coeff : Z4Plaq → Q') (c : Q') :
    pencil w K width depth [p,q] coeff c ≈
      Binary.value (pencilEntry w K width depth [p,q] c p p)
        (crossEntry w K width depth p q c)
        (pencilEntry w K width depth [p,q] c q q) (coeff p) (coeff q) := by
  have hcross := cross_double
    (pencilEntry w K width depth [p,q] c p q)
    (pencilEntry w K width depth [p,q] c q p) (coeff p) (coeff q)
  have hbody := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl
      (pencilEntry w K width depth [p,q] c p p*((coeff p)*(coeff p)))) hcross)
    (Q'.eqv_refl (pencilEntry w K width depth [p,q] c q q*((coeff q)*(coeff q))))
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hbody)
  simp only [pencil, quadratic, List.map_cons, List.map_nil, qListSum]
  exact poly_identity_of_normal_eq
    (.add
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.const 0)))
      (.add (.add (.mul (.mul (.var 1) (.var 0)) (.var 4))
        (.add (.mul (.mul (.var 1) (.var 1)) (.var 5)) (.const 0))) (.const 0)))
    (.add (.add (.mul (.var 2) (.mul (.var 0) (.var 0)))
      (.mul (.add (.var 3) (.var 4)) (.mul (.var 0) (.var 1))))
      (.mul (.var 5) (.mul (.var 1) (.var 1))))
    (by decide) (fun
      | 0 => coeff p | 1 => coeff q
      | 2 => pencilEntry w K width depth [p,q] c p p
      | 3 => pencilEntry w K width depth [p,q] c p q
      | 4 => pencilEntry w K width depth [p,q] c q p
      | _ => pencilEntry w K width depth [p,q] c q q)

/-- Exact two-face ORIGINAL result, not a replacement physical certificate. -/
inductive Result (w : Q') (K width depth : Nat) (p q : Z4Plaq) (c : Q') : Type
  | positive (x y : Q')
      (bound : (0 : Q') < pencil w K width depth [p,q] (profile p q x y) c)
  | nonpositive
      (bound : ∀ coeff : Z4Plaq → Q', pencil w K width depth [p,q] coeff c ≤ (0 : Q'))

/-- The binary classifier actually computes the signed original profile. -/
def search (w : Q') (K width depth : Nat) (p q : Z4Plaq) (hpq : p ≠ q)
    (c : Q') : Result w K width depth p q c :=
  match Binary.classify (pencilEntry w K width depth [p,q] c p p)
      (crossEntry w K width depth p q c) (pencilEntry w K width depth [p,q] c q q) with
  | .positive v => .positive v.x v.y (by
      have pin := pencil_two_faces w K width depth p q (profile p q v.x v.y) c
      rw [profile_at_first, profile_at_second hpq] at pin
      exact Q'.pos_of_lt_of_le v.positive (Q'.ge_of_eqv pin))
  | .nonpositive h => .nonpositive (fun coeff =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv
        (pencil_two_faces w K width depth p q coeff c)) (h (coeff p) (coeff q)))

section Checker

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (p q : Z4Plaq) (hpq : p ≠ q)
  (hfaces : ∀ r, r ∈ [p,q] → r ∈ spatialFaces base)

local notation "wideFaces" =>
  (fun r hr => spatialFaces_mono (Nat.le_of_lt hwidth) (hfaces r hr))

/-- Direction selection is automatic; acceptance still uses ALL existing
original cutoff/slack conditions, at the very SAME supplied pivot. -/
def certify (s : Nat) (c epsilon : Q') (pivot : Nat) :
    Option (Σ' coeff : Z4Plaq → Q',
      BF4WilsonAllNomeFiniteReferenceMargin.Certificate hw0 hw1
        (familyExpression width [p,q] coeff wideFaces)
        (BF4WilsonPlaquetteFamilySourcePin.family_within width [p,q] coeff wideFaces) s c) :=
  match search w (headCutoff w+pivot) width (s+1) p q hpq c with
  | .nonpositive _ => none
  | .positive x y _ =>
    let coeff := profile p q x y
    match pencilCertify hw0 hw1 hwidth [p,q] coeff hfaces s c epsilon pivot with
    | none => none
    | some certificate => some ⟨coeff, certificate⟩

end Checker

#print axioms Binary.value
#print axioms Binary.determinant
#print axioms Binary.completed_square
#print axioms Binary.negative_pivot_direction
#print axioms Binary.negative_pivot_nonpositive
#print axioms Binary.zero_pivot_direction
#print axioms Binary.zero_pivot_nonpositive
#print axioms Binary.classify
#print axioms Binary.direction
#print axioms Binary.direction_classify
#print axioms Binary.signed_cross_regression
#print axioms Binary.zero_pivot_regression
#print axioms Binary.singular_rejection_regression
#print axioms Binary.zero_rejection_regression
#print axioms Binary.axis_regression
#print axioms profile
#print axioms profile_at_first
#print axioms profile_at_second
#print axioms crossEntry
#print axioms pencil_two_faces
#print axioms search
#print axioms certify

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginSearch
