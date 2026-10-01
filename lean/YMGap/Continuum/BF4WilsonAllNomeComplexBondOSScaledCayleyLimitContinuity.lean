/-
# Explicit zero-parameter continuity on supplied physical Wilson-bond Rows

The original Rows provide a computed second-core approximation.  Its graph
output has a rational norm ceiling from that same represented source.  The
finite dyadic Cayley-product bound and the already constructed all-Rows
product limit then give a positive rational radius at every positive
tolerance.  No quotient representative, uniform source cap, full-real
parameter, or physical-time calibration is selected or asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance inner inner_value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore
  (first first_output_value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (coreSource coreSource_near productValue product_near_core)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (preimageCeiling preimageCeiling_nonnegative preimageNorm_le_ceiling)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity
  (product_domain_distance_le_four)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedInner_time_contraction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
  (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
  (derivativeAction_norm_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "N" => BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound.normSq hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)))

/-- The first actual graph output is bounded by the original preimage norm:
one time contraction and one derivative contraction on each component. -/
theorem first_output_norm_le_preimage
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy) :
    RCle (N (output hw0 hw1 (first hw0 hw1 Y)))
      (BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound.preimageNorm hw0 hw1 Y) := by
  have h₁ := RCle_trans
    (completedInner_time_contraction hw0 hw1 1 (derivativeAction hw0 hw1 (Class Y.1)))
    (derivativeAction_norm_bound hw0 hw1 (Class Y.1))
  have h₂ := RCle_trans
    (completedInner_time_contraction hw0 hw1 1 (derivativeAction hw0 hw1 (Class Y.2)))
    (derivativeAction_norm_bound hw0 hw1 (Class Y.2))
  change RCle (inner hw0 hw1
    (output hw0 hw1 (first hw0 hw1 Y))
    (output hw0 hw1 (first hw0 hw1 Y))).1 _
  rw [inner_value,BF4WilsonAllNomeComplexification.inner,first_output_value]
  exact RCadd_le_add h₁ h₂

theorem first_output_norm_le_ceiling
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy) :
    RCle (N (output hw0 hw1 (first hw0 hw1 Y)))
      (rat (preimageCeiling hw0 hw1 Y)) :=
  RCle_trans (first_output_norm_le_preimage hw0 hw1 Y)
    (preimageNorm_le_ceiling hw0 hw1 Y)

private def oneSixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- A deliberately small input tolerance; the existing core-density
constructor applies its own further one-sixteenth factor. -/
def inputTolerance (e : Q') : Q' := oneSixteenth*e

theorem inputTolerance_pos (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < inputTolerance e := Q'.mul_pos (by decide) he

def core (X : R) (e : Q') := coreSource hw0 hw1 X (inputTolerance e)

def outputCeiling (X : R) (e : Q') : Q' :=
  preimageCeiling hw0 hw1 (core hw0 hw1 X e)

theorem outputCeiling_nonnegative (X : R) (e : Q') :
    (0 : Q') ≤ outputCeiling hw0 hw1 X e :=
  preimageCeiling_nonnegative hw0 hw1 (core hw0 hw1 X e)

private def oneTwoFiftySix : Q' := Q'.mkPos 1 256 (by decide)

def bridgeTolerance (e : Q') : Q' := oneTwoFiftySix*e

theorem bridgeTolerance_pin (e : Q') :
    Q'.eqv
      (BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.tolerance
        (inputTolerance e)) (bridgeTolerance e) := by
  change Q'.eqv ((Q'.mkPos 1 16 (by decide))*(oneSixteenth*e))
    (oneTwoFiftySix*e)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ e
      (by decide : Q'.eqv ((Q'.mkPos 1 16 (by decide))*oneSixteenth)
        oneTwoFiftySix))

theorem bridgeTolerance_pos (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < bridgeTolerance e :=
  Q'.mul_pos (by decide) he

def radiusBudget (X : R) (e : Q') : Q' :=
  (4*outputCeiling hw0 hw1 X e + bridgeTolerance e)+1

theorem radiusBudget_nonnegative (X : R) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') ≤ radiusBudget hw0 hw1 X e := by
  unfold radiusBudget
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) (outputCeiling_nonnegative hw0 hw1 X e))
      (Q'.le_of_lt (bridgeTolerance_pos e he)))
    Q'.zero_le_one

/-- All data are computed from supplied original Rows and tolerance. -/
def radius (X : R) (e : Q') (he : (0 : Q') < e) : Q' :=
  linearTolerance (radiusBudget hw0 hw1 X e)
    (radiusBudget_nonnegative hw0 hw1 X e he) (bridgeTolerance e)

theorem radius_positive (X : R) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < radius hw0 hw1 X e he :=
  linearTolerance_pos _ _ (bridgeTolerance_pos e he)

private theorem bridgeTolerance_twentyTwo (e : Q') (he : (0 : Q') < e) :
    22*bridgeTolerance e ≤ e := by
  have hcoeff : 22*oneTwoFiftySix ≤ (1 : Q') := by decide
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ e hcoeff (Q'.le_of_lt he)
  have hform : Q'.eqv (22*bridgeTolerance e)
      ((22*oneTwoFiftySix)*e) :=
    poly_identity_of_normal_eq
      (.mul (.const 22) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 22) (.var 0)) (.var 1))
      (by decide) (fun | 0 => oneTwoFiftySix | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hform)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.one_mul_eqv e)))

private theorem radius_square_budget (X : R) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t) (htr : t ≤ radius hw0 hw1 X e he) :
    4*(t*t)*outputCeiling hw0 hw1 X e ≤ bridgeTolerance e := by
  let q := bridgeTolerance e
  let c := outputCeiling hw0 hw1 X e
  let B := radiusBudget hw0 hw1 X e
  have hc : (0 : Q') ≤ c := outputCeiling_nonnegative hw0 hw1 X e
  have hq : (0 : Q') ≤ q := Q'.le_of_lt (bridgeTolerance_pos e he)
  have hr : (0 : Q') ≤ radius hw0 hw1 X e he := Q'.le_of_lt (radius_positive hw0 hw1 X e he)
  have hB : (0 : Q') ≤ B := radiusBudget_nonnegative hw0 hw1 X e he
  have hB0 : 4*c ≤ B := by
    unfold B radiusBudget
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (4*c) q hq)
      (Q'.add_le_self_of_nonneg (4*c+q) 1 Q'.zero_le_one)
  have hqB : q ≤ B+1 := by
    have h := Q'.add_le_self_of_nonneg q (4*c) (Q'.mul_nonneg _ _ (by decide) hc)
    have h' : q ≤ 4*c+q := Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_comm_eqv q (4*c)))
    exact Q'.le_trans' _ _ _ h'
      (Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg (4*c+q) 1 Q'.zero_le_one)
        (Q'.add_le_self_of_nonneg ((4*c+q)+1) 1 Q'.zero_le_one))
  have hr1 : radius hw0 hw1 X e he ≤ 1 :=
    Q'.divPos_le_of_le_mul q (B+1)
      (BF4ExactSlabThermodynamicPolynomialContinuity.positiveBudget B hB)
      (Q'.le_trans' _ _ _ hqB (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))))
  have ht1 : t ≤ 1 := Q'.le_trans' _ _ _ htr hr1
  have htt : t*t ≤ t :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ t ht1 (Q'.le_of_lt ht))
      (Q'.le_of_eqv (Q'.one_mul_eqv t))
  have hBT : B*t ≤ B*(radius hw0 hw1 X e he) :=
    Q'.mul_le_mul_of_nonneg_left _ _ B htr hB
  have hbudget : B*(radius hw0 hw1 X e he) ≤ q :=
    linearTolerance_budget B hB (bridgeTolerance_pos e he)
  have hfirst : (4*c)*(t*t) ≤ (4*c)*t :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htt
      (Q'.mul_nonneg _ _ (by decide) hc)
  have hsecond : (4*c)*t ≤ B*t :=
    Q'.mul_le_mul_of_nonneg_right _ _ t hB0 (Q'.le_of_lt ht)
  have halgebra : Q'.eqv (4*(t*t)*c) ((4*c)*(t*t)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 4) (.mul (.var 0) (.var 0))) (.var 1))
      (.mul (.mul (.const 4) (.var 1)) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => t | _ => c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv halgebra)
    (Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_trans' _ _ _ hBT hbudget)))

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro eps heps
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b eps (Q'.le_of_lt heps))⟩

private theorem three_bridge (a b c d : H) (q : Q')
    (hab : RCle (D a b) (rat q))
    (hbc : RCle (D b c) (rat q))
    (hcd : RCle (D c d) (rat q)) :
    RCle (D a d) (rat (10*q)) := by
  have hinner := RCle_trans (distance_triangle hw0 hw1 b c d)
    (RCadd_le_add (RCadd_le_add hbc hbc) (RCadd_le_add hcd hcd))
  have houter := RCle_trans (distance_triangle hw0 hw1 a b d)
    (RCadd_le_add (RCadd_le_add hab hab) (RCadd_le_add hinner hinner))
  have hcoeff : RCadd (RCadd (rat q) (rat q))
      (RCadd
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))
        (RCadd (RCadd (rat q) (rat q)) (RCadd (rat q) (rat q)))) =
      rat (10*q) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0))
          (.add
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
            (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))))
        (.mul (.const 10) (.var 0))
        (by decide) (fun _ => q)))
  rwa [hcoeff] at houter

/-- Uniform-in-product-depth bound on each supplied original Rows class. -/
theorem finite_product_near_identity (X : R) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t)
    (htr : t ≤ radius hw0 hw1 X e he) (n : Nat) :
    RCle (D (productValue hw0 hw1 X t ht n) (ofRows hw0 hw1 X))
      (rat (10*bridgeTolerance e)) := by
  let eta := inputTolerance e
  let q := bridgeTolerance e
  let Y := core hw0 hw1 X e
  let d := first hw0 hw1 Y
  have he' : (0 : Q') < eta := inputTolerance_pos e he
  have hnear : RCle (D (ofRows hw0 hw1 X) (input hw0 hw1 d)) (rat q) :=
    by
      have h := coreSource_near hw0 hw1 X eta he'
      have hp : rat
          (BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.tolerance eta) = rat q :=
        Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
          (fun _ => bridgeTolerance_pin e))
      rwa [hp] at h
  have hnear' : RCle (D (input hw0 hw1 d) (ofRows hw0 hw1 X)) (rat q) := by
    rw [distance_symm]
    exact hnear
  have hproduct : RCle (D (productValue hw0 hw1 X t ht n)
      (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.product hw0 hw1 Y t ht n))
      (rat q) := by
    have h := product_near_core hw0 hw1 X eta he' t ht n
    have hp : rat
        (BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.tolerance eta) = rat q :=
      Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
        (fun _ => bridgeTolerance_pin e))
    rwa [hp] at h
  have hgraph := product_domain_distance_le_four hw0 hw1 t ht d n
  have hcap := first_output_norm_le_ceiling hw0 hw1 Y
  have hs0 : (0 : Q') ≤ 4*(t*t) :=
    Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 4)
      (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))
  have hscale := RCscale_mono hs0 hcap
  have hbudget := radius_square_budget hw0 hw1 X e he t ht htr
  have hgraph' : RCle
      (D (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.product
        hw0 hw1 Y t ht n) (input hw0 hw1 d)) (rat q) := by
    have h := RCle_trans hgraph hscale
    change RCle
      (D (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.product
        hw0 hw1 Y t ht n) (input hw0 hw1 d))
      (RCscale (4*(t*t)) (rat (outputCeiling hw0 hw1 X e))) at h
    have hrat : RCscale (4*(t*t)) (rat (outputCeiling hw0 hw1 X e)) =
        rat ((4*(t*t))*outputCeiling hw0 hw1 X e) :=
      Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
    rw [hrat] at h
    exact RCle_trans h (rat_le hbudget)
  exact three_bridge hw0 hw1 _ _ _ _ q hproduct hgraph' hnear'

/-- Constructed rational zero-parameter radius for the ACTUAL all-Rows
dyadic Cayley limit.  Every modulus and graph approximation comes from X. -/
theorem limitMap_near_identity_ofRows (X : R) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t)
    (htr : t ≤ radius hw0 hw1 X e he) :
    RCle (D (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X))
      (ofRows hw0 hw1 X)) (rat e) := by
  let q := bridgeTolerance e
  have hq : (0 : Q') < q := bridgeTolerance_pos e he
  let n := BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.productLimitRate
    hw0 hw1 X t ht q
  have hlimit : RCle (D (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X))
      (productValue hw0 hw1 X t ht n)) (rat q) := by
    rw [distance_symm]
    exact limitMap_bound hw0 hw1 X t ht q hq n (Nat.le_refl n)
  have hfinite := finite_product_near_identity hw0 hw1 X e he t ht htr n
  have htri := RCle_trans (distance_triangle hw0 hw1
      (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X))
      (productValue hw0 hw1 X t ht n) (ofRows hw0 hw1 X))
    (RCadd_le_add (RCadd_le_add hlimit hlimit)
      (RCadd_le_add hfinite hfinite))
  have hcoef : RCadd (RCadd (rat q) (rat q))
      (RCadd (rat (10*q)) (rat (10*q))) = rat (22*q) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0))
          (.add (.mul (.const 10) (.var 0)) (.mul (.const 10) (.var 0))))
        (.mul (.const 22) (.var 0)) (by decide) (fun _ => q)))
  rw [hcoef] at htri
  exact RCle_trans htri (rat_le (bridgeTolerance_twentyTwo e he))

/-- The positive radius is retained as data, not hidden behind existence. -/
def continuityCertificate (X : R) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', (0 : Q') < r ∧
      (∀ (t : Q') (ht : (0 : Q') < t), t ≤ r →
        RCle (D (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X))
          (ofRows hw0 hw1 X)) (rat e)) :=
  ⟨radius hw0 hw1 X e he,radius_positive hw0 hw1 X e he,
    fun t ht htr => limitMap_near_identity_ofRows hw0 hw1 X e he t ht htr⟩

#print axioms first_output_norm_le_preimage
#print axioms first_output_norm_le_ceiling
#print axioms radius
#print axioms radius_positive
#print axioms finite_product_near_identity
#print axioms limitMap_near_identity_ofRows
#print axioms continuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
