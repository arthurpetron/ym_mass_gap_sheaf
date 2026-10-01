/-
# Witnessed right-rational tangents on the original physical carrier

The actual Cayley difference quotient is compared with -2i times the supplied
output. Its radius is Type-level data. Original represented graph points
produce this data from the checked normalized residual; uniqueness uses only
the SAME physical squared distance and definiteness. No quotient class is
selected to compute a radius, and no full-real or physical-clock claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
import YMGap.Continuum.RationalScalarTwoSidedError
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance inner_posdef inner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_smul bondValue_negate)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedSmul_mul completedSmul_congr completedSmul_one
    completedAdd_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (realScale imagScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap (limitMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
  (tangentRadius tangentRadius_positive physicalPoint_normalized_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (add_assoc add_zero zero_add neg_add)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "N" => normSq hw0 hw1
local notation "Dist" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Z" => BF4WilsonAllNomeComplexBondOSCompletion.zero hw0 hw1 (width := width)

/-- The ORIGINAL factor-two generator phase, not a physical spacing. -/
def slope (v : H) : H := imagScale hw0 hw1 (-2) v

/-- The actual positive rational difference quotient of the constructed map. -/
def rightQuotient (t : Q') (ht : (0 : Q') < t) (u : H) : H :=
  realScale hw0 hw1 (Q'.recipPos t ht) (diff hw0 hw1 (limitMap hw0 hw1 t ht u) u)

/-- A definition of witnessed rational differentiability, not an assumed
Yang--Mills estimate. Graph points produce it below; the converse consumes it. -/
structure RightTangent (u v : H) : Type where
  radius : (e : Q') → (0 : Q') < e → Q'
  positive : ∀ e he, (0 : Q') < radius e he
  bound : ∀ e he t (ht : (0 : Q') < t), t ≤ radius e he →
    RCle (Dist (rightQuotient hw0 hw1 t ht u) (slope hw0 hw1 v)) (rat e)

private theorem real_scale_add (c : Q') (x y : RH) :
    S c (RA x y) = RA (S c x) (S c y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 c _ _

private theorem real_scale_mul (a b : Q') (x : RH) : S a (S b x) = S (a*b) x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul]
  exact completedSmul_mul hw0 hw1 a b _

private theorem real_scale_congr {a b : Q'} (h : Q'.eqv a b) (x : RH) : S a x = S b x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul]
  exact completedSmul_congr hw0 hw1 h _

private theorem real_scale_neg (c : Q') (x : RH) : S c (Neg x) = Neg (S c x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change completedSmul hw0 hw1 c (completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 x)) =
    completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 c (bondValue hw0 hw1 x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) _

private theorem real_scale_double (c : Q') (x : RH) : S c (RA x x) = S (2*c) x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  rw [completedSmul_add,completedAdd_smul]
  apply completedSmul_congr hw0 hw1
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
    (by decide) (fun _ => c)

private theorem realScale_add (c : Q') (x y : H) :
    realScale hw0 hw1 c (A x y) = A (realScale hw0 hw1 c x) (realScale hw0 hw1 c y) :=
  Prod.ext (real_scale_add hw0 hw1 c x.1 y.1) (real_scale_add hw0 hw1 c x.2 y.2)

private theorem realScale_imagScale (c t : Q') (x : H) :
    realScale hw0 hw1 c (imagScale hw0 hw1 t x) = imagScale hw0 hw1 (c*t) x := by
  apply Prod.ext
  · change S c (Neg (S t x.2)) = Neg (S (c*t) x.2)
    rw [real_scale_neg,real_scale_mul]
  · exact real_scale_mul hw0 hw1 c t x.1

private theorem imagScale_congr {a b : Q'} (h : Q'.eqv a b) (x : H) :
    imagScale hw0 hw1 a x = imagScale hw0 hw1 b x :=
  Prod.ext (congrArg Neg (real_scale_congr hw0 hw1 h x.2))
    (real_scale_congr hw0 hw1 h x.1)

private theorem imagScale_double_one (x : H) :
    imagScale hw0 hw1 1 (A x x) = imagScale hw0 hw1 2 x := by
  apply Prod.ext
  · change Neg (S 1 (RA x.2 x.2)) = Neg (S 2 x.2)
    rw [real_scale_double]
    exact congrArg Neg (real_scale_congr hw0 hw1 (by decide : Q'.eqv (2*1) 2) x.2)
  · change S 1 (RA x.1 x.1) = S 2 x.1
    rw [real_scale_double]
    exact real_scale_congr hw0 hw1 (by decide : Q'.eqv (2*1) 2) x.1

private theorem cneg_slope (x : H) : cneg hw0 hw1 (slope hw0 hw1 x) = imagScale hw0 hw1 2 x := by
  apply Prod.ext
  · change Neg (Neg (S (-2) x.2)) = Neg (S 2 x.2)
    apply bondValue_injective hw0 hw1
    simp only [bondValue_negate,bondValue_smul]
    change completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 (-2) (bondValue hw0 hw1 x.2))) =
      completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 2 (bondValue hw0 hw1 x.2))
    rw [completedSmul_mul,completedSmul_mul,completedSmul_mul]
    exact completedSmul_congr hw0 hw1 (by decide : Q'.eqv ((-1*(-1))*(-2)) (-1*2)) _
  · change Neg (S (-2) x.1) = S 2 x.1
    apply bondValue_injective hw0 hw1
    simp only [bondValue_negate,bondValue_smul]
    change completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 (-2) (bondValue hw0 hw1 x.1)) =
      completedSmul hw0 hw1 2 (bondValue hw0 hw1 x.1)
    rw [completedSmul_mul]
    exact completedSmul_congr hw0 hw1 (by decide : Q'.eqv (-1*(-2)) 2) _

/-- The original slope has a computed inverse rotation. -/
theorem slope_inverse (x : H) : imagScale hw0 hw1 HalfPow.half (slope hw0 hw1 x) = x := by
  apply Prod.ext
  · change Neg (S HalfPow.half (S (-2) x.1)) = x.1
    apply bondValue_injective hw0 hw1
    simp only [bondValue_negate,bondValue_smul]
    change completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 HalfPow.half
        (completedSmul hw0 hw1 (-2) (bondValue hw0 hw1 x.1))) = bondValue hw0 hw1 x.1
    rw [completedSmul_mul,completedSmul_mul,
      completedSmul_congr hw0 hw1 (by decide : Q'.eqv ((-1*HalfPow.half)*(-2)) 1),
      completedSmul_one]
  · change S HalfPow.half (Neg (S (-2) x.2)) = x.2
    apply bondValue_injective hw0 hw1
    simp only [bondValue_negate,bondValue_smul]
    change completedSmul hw0 hw1 HalfPow.half
      (completedSmul hw0 hw1 (-1)
        (completedSmul hw0 hw1 (-2) (bondValue hw0 hw1 x.2))) = bondValue hw0 hw1 x.2
    rw [completedSmul_mul,completedSmul_mul,
      completedSmul_congr hw0 hw1 (by decide : Q'.eqv ((HalfPow.half*(-1))*(-2)) 1),
      completedSmul_one]

theorem slope_injective {x y : H} (h : slope hw0 hw1 x = slope hw0 hw1 y) : x = y := by
  have hi := congrArg (imagScale hw0 hw1 HalfPow.half) h
  rwa [slope_inverse,slope_inverse] at hi

private def normalizedPairError (t : Q') (ht : (0 : Q') < t) (u v : H) : H :=
  realScale hw0 hw1 (Q'.recipPos t ht)
    (A (diff hw0 hw1 (limitMap hw0 hw1 t ht u) u) (imagScale hw0 hw1 t (A v v)))

private theorem quotient_distance_pin (t : Q') (ht : (0 : Q') < t) (u v : H) :
    Dist (rightQuotient hw0 hw1 t ht u) (slope hw0 hw1 v) =
      N (normalizedPairError hw0 hw1 t ht u v) := by
  have hrt : Q'.eqv (Q'.recipPos t ht*t) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv t ht)
  have hn : normalizedPairError hw0 hw1 t ht u v =
      A (rightQuotient hw0 hw1 t ht u) (imagScale hw0 hw1 2 v) := by
    unfold normalizedPairError
    rw [realScale_add,realScale_imagScale,imagScale_congr hw0 hw1 hrt,
      imagScale_double_one]
    rfl
  rw [distance_eq_norm_difference]
  unfold diff
  rw [cneg_slope,← hn]

/-- The supplied ORIGINAL Point computes the whole right-tangent modulus. -/
def ofPointTangent (p : Point hw0 hw1 (width := width)) :
    RightTangent hw0 hw1 (input hw0 hw1 (ofPoint hw0 hw1 p))
      (output hw0 hw1 (ofPoint hw0 hw1 p)) where
  radius := tangentRadius hw0 hw1 p
  positive := tangentRadius_positive hw0 hw1 p
  bound := by
    intro e he t ht htr
    rw [quotient_distance_pin]
    exact physicalPoint_normalized_bound hw0 hw1 p e he t ht htr

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (X.approx n)))

/-- Equality is detected by the ORIGINAL physical squared distance. -/
theorem eq_of_distance_small (x y : H)
    (h : ∀ e : Q', (0 : Q') < e → RCle (Dist x y) (rat e)) : x = y := by
  have hle : RCle (Dist x y) RCzero := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro e he
    rw [rc_zero_add]
    exact h e he
  have hnorm : N (diff hw0 hw1 x y) = RCzero := by
    apply RCle_antisymm
    · rw [← distance_eq_norm_difference]
      exact hle
    · exact inner_nonnegative hw0 hw1 (diff hw0 hw1 x y)
  have hdiff : diff hw0 hw1 x y = Z :=
    (inner_posdef hw0 hw1 (diff hw0 hw1 x y)).mp hnorm
  calc
    x = A x Z := (add_zero hw0 hw1 x).symm
    _ = A x (A (cneg hw0 hw1 y) y) := congrArg (A x) (neg_add hw0 hw1 y).symm
    _ = A (diff hw0 hw1 x y) y := (add_assoc hw0 hw1 _ _ _).symm
    _ = A Z y := congrArg (fun z => A z y) hdiff
    _ = y := zero_add hw0 hw1 y

/-- Two Type-witnessed tangents on the SAME input have the SAME graph output. -/
theorem RightTangent.unique {u v z : H}
    (P : RightTangent hw0 hw1 u v) (Q : RightTangent hw0 hw1 u z) : v = z := by
  apply slope_injective hw0 hw1
  apply eq_of_distance_small hw0 hw1
  intro e he
  let q := (Q'.mkPos 1 4 (by decide))*e
  have hq : (0 : Q') < q := Q'.mul_pos (by decide) he
  let t := Q'.min' (P.radius q hq) (Q.radius q hq)
  have ht : (0 : Q') < t := CReal.min_pos (P.positive q hq) (Q.positive q hq)
  have hp := P.bound q hq t ht (Q'.min_le_left' _ _)
  have hz := Q.bound q hq t ht (Q'.min_le_right' _ _)
  rw [distance_symm] at hp
  have hsum := RCle_trans (distance_triangle hw0 hw1
      (slope hw0 hw1 v) (rightQuotient hw0 hw1 t ht u) (slope hw0 hw1 z))
    (RCadd_le_add (RCadd_le_add hp hp) (RCadd_le_add hz hz))
  have hbudget : RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)) = rat e :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
          (.mul (.mul (.const 4) (.var 0)) (.var 1))
          (by decide) (fun | 0 => Q'.mkPos 1 4 (by decide) | _ => e))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ e (by decide : Q'.eqv (4*(Q'.mkPos 1 4 (by decide))) 1))
          (Q'.one_mul_eqv e))))
  rwa [hbudget] at hsum

#print axioms slope
#print axioms rightQuotient
#print axioms slope_inverse
#print axioms slope_injective
#print axioms ofPointTangent
#print axioms eq_of_distance_small
#print axioms RightTangent.unique

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData
