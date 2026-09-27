/-
# Supported products of original spatial-union Wilson expressions

Both factors are placed at one computed spatial base and reflection radius.
The product retains their original loops, coefficients and time offsets.
Common-chart coherence and finite polynomial identities give associativity,
commutativity and distributivity as equalities of the existing Wilson states.
An explicit forward-time-tested equivalence on these stages is preserved by
time and products and implies equality in the existing completed carrier.

This does NOT define multiplication on OS-null classes or on the completion:
equality of two completed states is not used as a product congruence premise.
It also does not construct the canonical observable algebra, identify a
completed real-normalized probe with a raw observable, or change spacing.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
import YMGap.Continuum.BF4WilsonSpatialUnionLinear

namespace YMGap.Continuum.BF4WilsonSpatialUnionProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum chart_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (chart_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance chart_advance_add_center)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity (chartInsertion_source_congr)
open YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent
  (intrinsic_distSq_zero_of_padded_diagonal)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix (prefix_mul_one)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Literal multiplication at the common reflection center. -/
def product {base : Nat} (x y : IntrinsicExpression base) : IntrinsicExpression base where
  radius := max x.radius y.radius
  expression := .mul (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
  within := ⟨chart_within _ x (Nat.le_max_left _ _), chart_within _ y (Nat.le_max_right _ _)⟩

theorem chart_product {base : Nat} (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    chart H (product x y) = .mul (chart H x) (chart H y) := by
  let M := max x.radius y.radius
  have hM : M ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hsum : M+(H-M)=H := by omega
  change WindowExpression.mul (shift (H-M) (chart M x)) (shift (H-M) (chart M y)) = _
  rw [← chart_step M (H-M) x (Nat.le_max_left _ _),
    ← chart_step M (H-M) y (Nat.le_max_right _ _), hsum]

private theorem intrinsic_ext {base : Nat} (x y : IntrinsicExpression base)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x = y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem inclusion_product {base larger : Nat} (h : base ≤ larger)
    (x y : IntrinsicExpression base) :
    inclusion h (product x y) = product (inclusion h x) (inclusion h y) := by
  apply intrinsic_ext
  · rfl
  · change includeExpression h
        (.mul (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)) =
      .mul (chart (max x.radius y.radius) (inclusion h x))
        (chart (max x.radius y.radius) (inclusion h y))
    rw [includeExpression_mul, inclusion_chart, inclusion_chart]

/-- Advance the common center together with both original factors. -/
theorem advance_product {base : Nat} (n : Nat) (x y : IntrinsicExpression base) :
    advance n (product x y) = product (advance n x) (advance n y) := by
  apply intrinsic_ext
  · change max x.radius y.radius+n = max (x.radius+n) (y.radius+n)
    omega
  · change WindowExpression.mul (chart (max x.radius y.radius) x)
        (chart (max x.radius y.radius) y) =
      WindowExpression.mul (chart (max (x.radius+n) (y.radius+n)) (advance n x))
        (chart (max (x.radius+n) (y.radius+n)) (advance n y))
    rw [show max (x.radius+n) (y.radius+n) = max x.radius y.radius+n by omega,
      chart_advance_add_center, chart_advance_add_center]

/-- Finite supported syntax, not an operation on completed equivalence classes. -/
def productStage (x y : Stage) : Stage :=
  ⟨max x.base y.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _),
    product (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))⟩

theorem atBase_product (x y : Stage) {larger : Nat}
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    atBase (productStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      product (atBase x hx) (atBase y hy) := by
  simp only [atBase, productStage, inclusion_product, inclusion_trans]

/-- Exact raw-stage identity; no completion or equivalence premise is used. -/
theorem time_product (n : Nat) (x y : Stage) :
    time n (productStage x y) = productStage (time n x) (time n y) := by
  change (⟨max x.base y.base, _, advance n
    (product (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _)))⟩ : Stage) =
    ⟨max x.base y.base, _, product (advance n (atBase x (Nat.le_max_left _ _)))
      (advance n (atBase y (Nat.le_max_right _ _)))⟩
  rw [advance_product]

/-- One supported chart in a supplied common spatial base. -/
def commonChart (N H : Nat) (x : Stage) (hx : x.base ≤ N) : WindowExpression N :=
  chart H (atBase x hx)

theorem commonChart_product (N H : Nat) (x y : Stage)
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (hxH : x.value.radius ≤ H) (hyH : y.value.radius ≤ H) :
    commonChart N H (productStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      .mul (commonChart N H x hx) (commonChart N H y hy) := by
  unfold commonChart
  rw [atBase_product]
  exact chart_product H (atBase x hx) (atBase y hy) hxH hyH

theorem commonChart_sum (N H : Nat) (x y : Stage)
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (hxH : x.value.radius ≤ H) (hyH : y.value.radius ≤ H) :
    commonChart N H (sumStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      .add (commonChart N H x hx) (commonChart N H y hy) := by
  unfold commonChart
  rw [atBase_sum]
  exact chart_sum H (atBase x hx) (atBase y hy) hxH hyH

theorem commonChart_smul (N H : Nat) (c : Q') (x : Stage) (hx : x.base ≤ N) :
    commonChart N H (smulStage c x) hx = .smul c (commonChart N H x hx) := by
  simp only [commonChart, atBase_smul, chart_smul]

theorem commonChart_unit (N H : Nat) (hN : 1 ≤ N) :
    commonChart N H unitStage hN = .one := by
  simp only [commonChart, atBase_unit, chart_unit]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "E" => embedStage hw0 hw1 hsmall hd hs

/-- A finite common-source identity reaches the SAME completed carrier even
when the two raw stages have different spatial bases. -/
theorem embedStage_eq_of_common_source (x y : Stage) (N H : Nat)
    (hx : x.base ≤ N) (hy : y.base ≤ N)
    (hxH : x.value.radius ≤ H) (hyH : y.value.radius ≤ H)
    (hp : PaddedPolynomialCoeffEqv ((H+1)*(baseLinks N).length)
      (sourcePolynomial (commonChart N H x hx))
      (sourcePolynomial (commonChart N H y hy))) : E x = E y := by
  apply (unionSeminorm hw0 hw1 hsmall hd hs).embedRep_eq_of_null
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans
    (intrinsic_distSq_zero_of_padded_diagonal hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le x.positive hx) H (atBase x hx) (atBase y hy) hxH hyH
      (fun n => chartInsertion_source_congr n H n
        (commonChart N H x hx) (commonChart N H y hy)
        (chart_within H (atBase x hx) hxH) (chart_within H (atBase y hy) hyH) hp))

theorem product_comm (x y : Stage) : E (productStage x y) = E (productStage y x) := by
  let N := max x.base y.base
  let H := max x.value.radius y.value.radius
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hxH : x.value.radius ≤ H := Nat.le_max_left _ _
  have hyH : y.value.radius ≤ H := Nat.le_max_right _ _
  apply embedStage_eq_of_common_source hw0 hw1 hsmall hd hs _ _ N H
    (Nat.max_le.mpr ⟨hx,hy⟩) (Nat.max_le.mpr ⟨hy,hx⟩)
    (Nat.max_le.mpr ⟨hxH,hyH⟩) (Nat.max_le.mpr ⟨hyH,hxH⟩)
  rw [commonChart_product N H x y hx hy hxH hyH,
    commonChart_product N H y x hy hx hyH hxH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_comm _ _)

theorem product_assoc (x y z : Stage) :
    E (productStage (productStage x y) z) = E (productStage x (productStage y z)) := by
  let N := max (max x.base y.base) z.base
  let H := max (max x.value.radius y.value.radius) z.value.radius
  have hx : x.base ≤ N := by dsimp [N]; omega
  have hy : y.base ≤ N := by dsimp [N]; omega
  have hz : z.base ≤ N := by dsimp [N]; omega
  have hxH : x.value.radius ≤ H := by dsimp [H]; omega
  have hyH : y.value.radius ≤ H := by dsimp [H]; omega
  have hzH : z.value.radius ≤ H := by dsimp [H]; omega
  have hxy := Nat.max_le.mpr ⟨hx,hy⟩
  have hyz := Nat.max_le.mpr ⟨hy,hz⟩
  have hxyH := Nat.max_le.mpr ⟨hxH,hyH⟩
  have hyzH := Nat.max_le.mpr ⟨hyH,hzH⟩
  apply embedStage_eq_of_common_source hw0 hw1 hsmall hd hs _ _ N H
    (Nat.max_le.mpr ⟨hxy,hz⟩) (Nat.max_le.mpr ⟨hx,hyz⟩)
    (Nat.max_le.mpr ⟨hxyH,hzH⟩) (Nat.max_le.mpr ⟨hxH,hyzH⟩)
  rw [commonChart_product N H (productStage x y) z hxy hz hxyH hzH,
    commonChart_product N H x (productStage y z) hx hyz hxH hyzH,
    commonChart_product N H x y hx hy hxH hyH,
    commonChart_product N H y z hy hz hyH hzH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)

theorem product_sum_right (x y z : Stage) :
    E (productStage x (sumStage y z)) =
      E (sumStage (productStage x y) (productStage x z)) := by
  let N := max (max x.base y.base) z.base
  let H := max (max x.value.radius y.value.radius) z.value.radius
  have hx : x.base ≤ N := by dsimp [N]; omega
  have hy : y.base ≤ N := by dsimp [N]; omega
  have hz : z.base ≤ N := by dsimp [N]; omega
  have hxH : x.value.radius ≤ H := by dsimp [H]; omega
  have hyH : y.value.radius ≤ H := by dsimp [H]; omega
  have hzH : z.value.radius ≤ H := by dsimp [H]; omega
  have hxy := Nat.max_le.mpr ⟨hx,hy⟩
  have hxz := Nat.max_le.mpr ⟨hx,hz⟩
  have hyz := Nat.max_le.mpr ⟨hy,hz⟩
  have hxyH := Nat.max_le.mpr ⟨hxH,hyH⟩
  have hxzH := Nat.max_le.mpr ⟨hxH,hzH⟩
  have hyzH := Nat.max_le.mpr ⟨hyH,hzH⟩
  apply embedStage_eq_of_common_source hw0 hw1 hsmall hd hs _ _ N H
    (Nat.max_le.mpr ⟨hx,hyz⟩) (Nat.max_le.mpr ⟨hxy,hxz⟩)
    (Nat.max_le.mpr ⟨hxH,hyzH⟩) (Nat.max_le.mpr ⟨hxyH,hxzH⟩)
  rw [commonChart_product N H x (sumStage y z) hx hyz hxH hyzH,
    commonChart_sum N H (productStage x y) (productStage x z) hxy hxz hxyH hxzH,
    commonChart_sum N H y z hy hz hyH hzH,
    commonChart_product N H x y hx hy hxH hyH,
    commonChart_product N H x z hx hz hxH hzH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)

theorem product_smul_left (c : Q') (x y : Stage) :
    E (productStage (smulStage c x) y) = E (smulStage c (productStage x y)) := by
  let N := max x.base y.base
  let H := max x.value.radius y.value.radius
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hxH : x.value.radius ≤ H := Nat.le_max_left _ _
  have hyH : y.value.radius ≤ H := Nat.le_max_right _ _
  have hxy := Nat.max_le.mpr ⟨hx,hy⟩
  have hxyH := Nat.max_le.mpr ⟨hxH,hyH⟩
  apply embedStage_eq_of_common_source hw0 hw1 hsmall hd hs _ _ N H hxy hxy hxyH hxyH
  rw [commonChart_product N H (smulStage c x) y hx hy hxH hyH,
    commonChart_smul, commonChart_smul,
    commonChart_product N H x y hx hy hxH hyH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.polyMul_smul_left c _ _)

theorem product_unit_right (x : Stage) : E (productStage x unitStage) = E x := by
  have hu : 1 ≤ x.base := x.positive
  apply embedStage_eq_of_common_source hw0 hw1 hsmall hd hs _ _ x.base x.value.radius
    (Nat.max_le.mpr ⟨Nat.le_refl _,hu⟩) (Nat.le_refl _)
    (Nat.max_le.mpr ⟨Nat.le_refl _,Nat.zero_le _⟩) (Nat.le_refl _)
  rw [commonChart_product x.base x.value.radius x unitStage (Nat.le_refl _) hu
    (Nat.le_refl _) (Nat.zero_le _), commonChart_unit]
  exact PaddedPolynomialCoeffEqv.of_prefix (prefix_mul_one _ _)

theorem product_unit_left (x : Stage) : E (productStage unitStage x) = E x :=
  (product_comm hw0 hw1 hsmall hd hs unitStage x).trans
    (product_unit_right hw0 hw1 hsmall hd hs x)

/-- Equality tested in the SAME physical completion after every forward time
and every supported multiplier. This is a defined relation, not an assumed
ideal property of the OS null relation. -/
def TimeContextEq (x y : Stage) : Prop :=
  ∀ (n : Nat) (z : Stage), E (productStage (time n x) z) = E (productStage (time n y) z)

local notation "Ceq" => TimeContextEq hw0 hw1 hsmall hd hs

theorem timeContext_refl (x : Stage) : Ceq x x := fun _ _ => rfl

theorem timeContext_symm {x y : Stage} (h : Ceq x y) : Ceq y x :=
  fun n z => (h n z).symm

theorem timeContext_trans {x y z : Stage} (h : Ceq x y) (k : Ceq y z) : Ceq x z :=
  fun n test => (h n test).trans (k n test)

/-- Saturation under forward time supplies stability by an index shift. -/
theorem timeContext_time (m : Nat) {x y : Stage} (h : Ceq x y) :
    Ceq (time m x) (time m y) := by
  intro n z
  simpa only [← time_add] using h (n+m) z

/-- The zero-time unit test ties this relation to the original physical state. -/
theorem timeContext_embed {x y : Stage} (h : Ceq x y) : E x = E y := by
  simpa only [time_zero, product_unit_right hw0 hw1 hsmall hd hs] using h 0 unitStage

theorem timeContext_product_left {x y : Stage} (h : Ceq x y) (u : Stage) :
    Ceq (productStage x u) (productStage y u) := by
  intro n z
  simp only [time_product, product_assoc hw0 hw1 hsmall hd hs]
  exact h n (productStage (time n u) z)

private theorem product_rotate (a b c : Stage) :
    E (productStage (productStage a b) c) = E (productStage b (productStage c a)) :=
  (product_assoc hw0 hw1 hsmall hd hs a b c).trans
    ((product_comm hw0 hw1 hsmall hd hs a (productStage b c)).trans
      (product_assoc hw0 hw1 hsmall hd hs b c a))

theorem timeContext_product_right {x y : Stage} (h : Ceq x y) (u : Stage) :
    Ceq (productStage u x) (productStage u y) := by
  intro n z
  simp only [time_product]
  exact (product_rotate hw0 hw1 hsmall hd hs (time n u) (time n x) z).trans
    ((h n (productStage z (time n u))).trans
      (product_rotate hw0 hw1 hsmall hd hs (time n u) (time n y) z).symm)

theorem timeContext_product {x x' y y' : Stage} (hx : Ceq x x') (hy : Ceq y y') :
    Ceq (productStage x y) (productStage x' y') :=
  timeContext_trans hw0 hw1 hsmall hd hs
    (timeContext_product_left hw0 hw1 hsmall hd hs hx y)
    (timeContext_product_right hw0 hw1 hsmall hd hs hy x')

open YMGap.Continuum.BF4WilsonSpatialUnionLinear
  (completedAdd completedSmul completedAdd_embedStage completedSmul_embedStage)

/-- The existing intrinsic sum law gives an exact stage identity. -/
theorem time_sum (n : Nat) (x y : Stage) :
    time n (sumStage x y) = sumStage (time n x) (time n y) := by
  change (⟨max x.base y.base, _, advance n
    (sum (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _)))⟩ : Stage) =
    ⟨max x.base y.base, _, sum (advance n (atBase x (Nat.le_max_left _ _)))
      (advance n (atBase y (Nat.le_max_right _ _)))⟩
  rw [BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_sum]

theorem time_smul (n : Nat) (c : Q') (x : Stage) :
    time n (smulStage c x) = smulStage c (time n x) := rfl

theorem product_sum_left (x y z : Stage) :
    E (productStage (sumStage x y) z) =
      E (sumStage (productStage x z) (productStage y z)) := by
  calc
    E (productStage (sumStage x y) z) =
        completedAdd hw0 hw1 hsmall hd hs (E (productStage z x)) (E (productStage z y)) :=
      (product_comm hw0 hw1 hsmall hd hs (sumStage x y) z).trans
        ((product_sum_right hw0 hw1 hsmall hd hs z x y).trans
          (completedAdd_embedStage hw0 hw1 hsmall hd hs (productStage z x) (productStage z y)).symm)
    _ = completedAdd hw0 hw1 hsmall hd hs (E (productStage x z)) (E (productStage y z)) := by
      rw [product_comm hw0 hw1 hsmall hd hs z x, product_comm hw0 hw1 hsmall hd hs z y]
    _ = E (sumStage (productStage x z) (productStage y z)) :=
      completedAdd_embedStage hw0 hw1 hsmall hd hs _ _

theorem timeContext_sum {x x' y y' : Stage} (hx : Ceq x x') (hy : Ceq y y') :
    Ceq (sumStage x y) (sumStage x' y') := by
  intro n z
  simp only [time_sum, product_sum_left hw0 hw1 hsmall hd hs,
    ← completedAdd_embedStage hw0 hw1 hsmall hd hs]
  rw [hx n z, hy n z]

theorem timeContext_smul (c : Q') {x y : Stage} (h : Ceq x y) :
    Ceq (smulStage c x) (smulStage c y) := by
  intro n z
  simp only [time_smul, product_smul_left hw0 hw1 hsmall hd hs,
    ← completedSmul_embedStage hw0 hw1 hsmall hd hs]
  exact congrArg (completedSmul hw0 hw1 hsmall hd hs c) (h n z)

#print axioms product
#print axioms chart_product
#print axioms inclusion_product
#print axioms advance_product
#print axioms productStage
#print axioms atBase_product
#print axioms time_product
#print axioms commonChart
#print axioms commonChart_product
#print axioms commonChart_sum
#print axioms commonChart_smul
#print axioms commonChart_unit
#print axioms embedStage_eq_of_common_source
#print axioms product_comm
#print axioms product_assoc
#print axioms product_sum_right
#print axioms product_smul_left
#print axioms product_unit_right
#print axioms product_unit_left
#print axioms TimeContextEq
#print axioms timeContext_refl
#print axioms timeContext_symm
#print axioms timeContext_trans
#print axioms timeContext_time
#print axioms timeContext_embed
#print axioms timeContext_product_left
#print axioms timeContext_product_right
#print axioms timeContext_product
#print axioms time_sum
#print axioms time_smul
#print axioms product_sum_left
#print axioms timeContext_sum
#print axioms timeContext_smul

end YMGap.Continuum.BF4WilsonSpatialUnionProduct
