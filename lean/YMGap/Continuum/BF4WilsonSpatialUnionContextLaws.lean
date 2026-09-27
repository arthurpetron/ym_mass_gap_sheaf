/-
# Algebraic identities under every supported time context

Finite common-chart coefficient identities are retained under the test
multiplier before they descend to the existing physical completion. Thus
the laws below hold for TimeContextEq, not just for embedded state equality.
No multiplication of arbitrary completed or OS-null states is asserted.

These are fixed-spacing supported Wilson laws. They neither identify a
canonical reflected OS root nor construct a continuum observable algebra.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionProduct

namespace YMGap.Continuum.BF4WilsonSpatialUnionContextLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionProduct
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (chart_advance_unit)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix (prefix_mul_one)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Advancing the unit changes its raw radius tag but not its polynomial. -/
theorem commonChart_time_unit (N H n : Nat) (hN : 1 ≤ N) :
    commonChart N H (time n unitStage) hN = .one := by
  simp only [commonChart, atBase_time, atBase_unit, chart_advance_unit]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "Ceq" => TimeContextEq hw0 hw1 hsmall hd hs

/-- A source identity valid in every advanced common chart survives every
supported multiplier. The finite common bounds are computed from the three
actual stages; no bound for an entire completed stream is chosen. -/
theorem context_of_common_source (x y : Stage)
    (identity : ∀ (n N H : Nat)
      (hx : (time n x).base ≤ N) (hy : (time n y).base ≤ N),
      (time n x).value.radius ≤ H → (time n y).value.radius ≤ H →
      PaddedPolynomialCoeffEqv ((H+1)*(baseLinks N).length)
        (sourcePolynomial (commonChart N H (time n x) hx))
        (sourcePolynomial (commonChart N H (time n y) hy))) : Ceq x y := by
  intro n test
  let a := time n x
  let b := time n y
  let N := max (max a.base b.base) test.base
  let H := max (max a.value.radius b.value.radius) test.value.radius
  have ha : a.base ≤ N := by dsimp [N]; omega
  have hb : b.base ≤ N := by dsimp [N]; omega
  have ht : test.base ≤ N := Nat.le_max_right _ _
  have haH : a.value.radius ≤ H := by dsimp [H]; omega
  have hbH : b.value.radius ≤ H := by dsimp [H]; omega
  have htH : test.value.radius ≤ H := Nat.le_max_right _ _
  apply embedStage_eq_of_common_source hw0 hw1 hsmall hd hs _ _ N H
    (Nat.max_le.mpr ⟨ha,ht⟩) (Nat.max_le.mpr ⟨hb,ht⟩)
    (Nat.max_le.mpr ⟨haH,htH⟩) (Nat.max_le.mpr ⟨hbH,htH⟩)
  rw [commonChart_product N H a test ha ht haH htH,
    commonChart_product N H b test hb ht hbH htH]
  exact (identity n N H ha hb haH hbH).mul (PaddedPolynomialCoeffEqv.refl _ _)

theorem context_product_comm (x y : Stage) :
    Ceq (productStage x y) (productStage y x) := by
  apply context_of_common_source hw0 hw1 hsmall hd hs
  intro n N H
  rw [time_product n x y, time_product n y x]
  intro hb hb' hr hr'
  have hx : (time n x).base ≤ N := Nat.le_trans (Nat.le_max_left _ _) hb
  have hy : (time n y).base ≤ N := Nat.le_trans (Nat.le_max_right _ _) hb
  have hxH : (time n x).value.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) hr
  have hyH : (time n y).value.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) hr
  rw [commonChart_product N H (time n x) (time n y) hx hy hxH hyH,
    commonChart_product N H (time n y) (time n x) hy hx hyH hxH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_comm _ _)

theorem context_product_assoc (x y z : Stage) :
    Ceq (productStage (productStage x y) z) (productStage x (productStage y z)) := by
  apply context_of_common_source hw0 hw1 hsmall hd hs
  intro n N H
  rw [time_product n (productStage x y) z,
    time_product n x (productStage y z), time_product n x y, time_product n y z]
  intro hb hb' hr hr'
  have hxy : (productStage (time n x) (time n y)).base ≤ N :=
    Nat.le_trans (Nat.le_max_left _ _) hb
  have hx : (time n x).base ≤ N := Nat.le_trans (Nat.le_max_left _ _) hxy
  have hy : (time n y).base ≤ N := Nat.le_trans (Nat.le_max_right _ _) hxy
  have hz : (time n z).base ≤ N := Nat.le_trans (Nat.le_max_right _ _) hb
  have hxyH : (productStage (time n x) (time n y)).value.radius ≤ H :=
    Nat.le_trans (Nat.le_max_left _ _) hr
  have hxH : (time n x).value.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) hxyH
  have hyH : (time n y).value.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) hxyH
  have hzH : (time n z).value.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) hr
  have hyz := Nat.max_le.mpr ⟨hy,hz⟩
  have hyzH := Nat.max_le.mpr ⟨hyH,hzH⟩
  rw [commonChart_product N H (productStage (time n x) (time n y)) (time n z)
      hxy hz hxyH hzH,
    commonChart_product N H (time n x) (productStage (time n y) (time n z))
      hx hyz hxH hyzH,
    commonChart_product N H (time n x) (time n y) hx hy hxH hyH,
    commonChart_product N H (time n y) (time n z) hy hz hyH hzH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)

theorem context_product_unit_right (x : Stage) : Ceq (productStage x unitStage) x := by
  apply context_of_common_source hw0 hw1 hsmall hd hs
  intro n N H
  rw [time_product n x unitStage]
  intro hb hx hr hxH
  have hu : (time n unitStage).base ≤ N := Nat.le_trans (Nat.le_max_right _ _) hb
  have huH : (time n unitStage).value.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) hr
  rw [commonChart_product N H (time n x) (time n unitStage) hx hu hxH huH,
    commonChart_time_unit]
  exact PaddedPolynomialCoeffEqv.of_prefix (prefix_mul_one _ _)

theorem context_product_unit_left (x : Stage) : Ceq (productStage unitStage x) x :=
  timeContext_trans hw0 hw1 hsmall hd hs
    (context_product_comm hw0 hw1 hsmall hd hs unitStage x)
    (context_product_unit_right hw0 hw1 hsmall hd hs x)

/-- Unitality holds in the tested relation, not as equality of radius tags. -/
theorem context_time_unit (n : Nat) : Ceq (time n unitStage) unitStage := by
  apply context_of_common_source hw0 hw1 hsmall hd hs
  intro m N H hx hy hxH hyH
  simp only [← time_add, commonChart_time_unit]
  exact PaddedPolynomialCoeffEqv.refl _ _

theorem context_product_sum_right (x y z : Stage) :
    Ceq (productStage x (sumStage y z))
      (sumStage (productStage x y) (productStage x z)) := by
  apply context_of_common_source hw0 hw1 hsmall hd hs
  intro n N H
  rw [time_product n x (sumStage y z),
    time_sum n (productStage x y) (productStage x z),
    time_sum n y z, time_product n x y, time_product n x z]
  intro hb hb' hr hr'
  have hx : (time n x).base ≤ N := Nat.le_trans (Nat.le_max_left _ _) hb
  have hyz : (sumStage (time n y) (time n z)).base ≤ N :=
    Nat.le_trans (Nat.le_max_right _ _) hb
  have hy : (time n y).base ≤ N := Nat.le_trans (Nat.le_max_left _ _) hyz
  have hz : (time n z).base ≤ N := Nat.le_trans (Nat.le_max_right _ _) hyz
  have hxH : (time n x).value.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) hr
  have hyzH : (sumStage (time n y) (time n z)).value.radius ≤ H :=
    Nat.le_trans (Nat.le_max_right _ _) hr
  have hyH : (time n y).value.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) hyzH
  have hzH : (time n z).value.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) hyzH
  have hxy := Nat.max_le.mpr ⟨hx,hy⟩
  have hxz := Nat.max_le.mpr ⟨hx,hz⟩
  have hxyH := Nat.max_le.mpr ⟨hxH,hyH⟩
  have hxzH := Nat.max_le.mpr ⟨hxH,hzH⟩
  rw [commonChart_product N H (time n x) (sumStage (time n y) (time n z))
      hx hyz hxH hyzH,
    commonChart_sum N H (productStage (time n x) (time n y))
      (productStage (time n x) (time n z)) hxy hxz hxyH hxzH,
    commonChart_sum N H (time n y) (time n z) hy hz hyH hzH,
    commonChart_product N H (time n x) (time n y) hx hy hxH hyH,
    commonChart_product N H (time n x) (time n z) hx hz hxH hzH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)

theorem context_product_smul_left (c : Q') (x y : Stage) :
    Ceq (productStage (smulStage c x) y) (smulStage c (productStage x y)) := by
  apply context_of_common_source hw0 hw1 hsmall hd hs
  intro n N H
  rw [time_product n (smulStage c x) y,
    time_smul n c x, time_smul n c (productStage x y), time_product n x y]
  intro hb hb' hr hr'
  have hx : (time n x).base ≤ N := Nat.le_trans (Nat.le_max_left _ _) hb
  have hy : (time n y).base ≤ N := Nat.le_trans (Nat.le_max_right _ _) hb
  have hxH : (time n x).value.radius ≤ H := Nat.le_trans (Nat.le_max_left _ _) hr
  have hyH : (time n y).value.radius ≤ H := Nat.le_trans (Nat.le_max_right _ _) hr
  rw [commonChart_product N H (smulStage c (time n x)) (time n y) hx hy hxH hyH,
    commonChart_smul, commonChart_smul,
    commonChart_product N H (time n x) (time n y) hx hy hxH hyH]
  exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.polyMul_smul_left c _ _)

end YMGap.Continuum.BF4WilsonSpatialUnionContextLaws

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.commonChart_time_unit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_of_common_source
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_product_comm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_product_assoc
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_product_unit_right
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_product_unit_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_time_unit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_product_sum_right
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionContextLaws.context_product_smul_left
