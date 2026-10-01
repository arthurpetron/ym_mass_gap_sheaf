/-
# Constructed dyadic Cayley-product limits on the original represented core

The consecutive estimate is proved for the actual products, not supplied as
an analytic field. Original Cauchy preimages give computable rational norm
ceilings. The geometric all-tail theorem constructs original physical limit
Rows together with an explicit convergence modulus, without quotient choice.

Nome and width remain fixed. This does not extend the limit to every physical
class, prove a continuous group law, or identify its parameter with physical
time or the transfer logarithm. The continuum Clay target remains open.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (pairingData)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows distance distance_value value
    limitRows limitRate limit_bound)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq preimageNorm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (product productRows productRows_pin product_consecutive_norm_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (quarter cauchyOfConsecutive distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "YType" =>
  CRealSeminormCompletion.SquaredSeminorm.Cauchy D ×
    CRealSeminormCompletion.SquaredSeminorm.Cauchy D
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Same carrier, same squared distance, same actual additive difference. -/
theorem distance_eq_norm_difference (x y : H) :
    distance hw0 hw1 x y = normSq hw0 hw1 (diff hw0 hw1 x y) := by
  change distance hw0 hw1 x y = RCadd
    (BF4WilsonAllNomeBondOSCompletion.bondCompletedInner hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x.1
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y.1))
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x.1
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y.1)))
    (BF4WilsonAllNomeBondOSCompletion.bondCompletedInner hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x.2
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y.2))
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x.2
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y.2)))
  rw [distance_value]
  simp only [value,bondValue_inner,bondValue_add,bondValue_negate,
    BF4WilsonAllNomeDistance.completedDist,BF4WilsonAllNomeLinear.completedSub]

/-- Computed from the TWO supplied ORIGINAL Cauchy streams. This is not a
uniform bound over sources or a bound on the smoothed physical input. -/
def preimageCeiling (Y : YType) : Q' := normCeiling PD Y.1 + normCeiling PD Y.2

theorem preimageCeiling_nonnegative (Y : YType) : (0 : Q') ≤ preimageCeiling hw0 hw1 Y :=
  Q'.zero_le_add _ _ (normCeiling_nonnegative PD Y.1) (normCeiling_nonnegative PD Y.2)

theorem preimageNorm_le_ceiling (Y : YType) :
    RCle (preimageNorm hw0 hw1 Y) (rat (preimageCeiling hw0 hw1 Y)) :=
  RCadd_le_add (completedInner_diagonal_le_normCeiling PD Y.1)
    (completedInner_diagonal_le_normCeiling PD Y.2)

def productBudget (Y : YType) (t : Q') : Q' :=
  (22*((t*t)*(t*t)))*preimageCeiling hw0 hw1 Y

theorem productBudget_nonnegative (Y : YType) (t : Q') (ht : (0 : Q') < t) :
    (0 : Q') ≤ productBudget hw0 hw1 Y t :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))
        (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))))
    (preimageCeiling_nonnegative hw0 hw1 Y)

private theorem scalar_budget (p c q : Q') :
    Q'.eqv (((22*p)*q)*c) (((22*p)*c)*q) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.mul (.const 22) (.var 0)) (.var 2)) (.var 1))
    (.mul (.mul (.mul (.const 22) (.var 0)) (.var 1)) (.var 2))
    (by decide) (fun | 0 => p | 1 => c | _ => q)

theorem productRows_consecutive_bound (Y : YType) (t : Q') (ht : (0 : Q') < t)
    (n : Nat) :
    RCle (distance hw0 hw1 (ofRows hw0 hw1 (productRows hw0 hw1 Y t ht n))
      (ofRows hw0 hw1 (productRows hw0 hw1 Y t ht (n+1))))
      (rat (productBudget hw0 hw1 Y t * quarter^n)) := by
  have hlocal := product_consecutive_norm_le hw0 hw1 Y t ht n
  have hs : (0 : Q') ≤ (22*((t*t)*(t*t)))*quarter^n :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))
          (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))))
      (Q'.pow_nonneg quarter (by decide) n)
  have hcap := RCscale_mono hs (preimageNorm_le_ceiling hw0 hw1 Y)
  have h := RCle_trans hlocal hcap
  have hc : RCscale ((22*((t*t)*(t*t)))*quarter^n)
      (rat (preimageCeiling hw0 hw1 Y)) =
      rat (productBudget hw0 hw1 Y t * quarter^n) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      scalar_budget ((t*t)*(t*t)) (preimageCeiling hw0 hw1 Y) (quarter^n)))
  rw [hc] at h
  rw [productRows_pin,productRows_pin,distance_symm,distance_eq_norm_difference]
  exact h

/-- An ACTUAL product Cauchy sequence, not an assumed analytic certificate. -/
def productSequence (Y : YType) (t : Q') (ht : (0 : Q') < t) :
    CauchySequence hw0 hw1 (width := width) :=
  cauchyOfConsecutive hw0 hw1 (productRows hw0 hw1 Y t ht)
    (productBudget hw0 hw1 Y t) (productBudget_nonnegative hw0 hw1 Y t ht)
    (productRows_consecutive_bound hw0 hw1 Y t ht)

def productLimitRows (Y : YType) (t : Q') (ht : (0 : Q') < t) :
    Rows hw0 hw1 (width := width) := limitRows hw0 hw1 (productSequence hw0 hw1 Y t ht)

def productLimitRate (Y : YType) (t : Q') (ht : (0 : Q') < t) : Q' → Nat :=
  limitRate hw0 hw1 (productSequence hw0 hw1 Y t ht)

theorem productLimit_bound (Y : YType) (t : Q') (ht : (0 : Q') < t)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : productLimitRate hw0 hw1 Y t ht e ≤ n) :
    RCle (distance hw0 hw1 (product hw0 hw1 Y t ht n)
      (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht))) (rat e) := by
  have h := limit_bound hw0 hw1 (productSequence hw0 hw1 Y t ht) e he n hn
  change RCle (distance hw0 hw1 (ofRows hw0 hw1 (productRows hw0 hw1 Y t ht n))
    (ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht))) (rat e) at h
  rw [productRows_pin] at h
  exact h

def productLimitCertificate (Y : YType) (t : Q') (ht : (0 : Q') < t) :
    Σ' X : Rows hw0 hw1 (width := width), Σ' rate : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
        RCle (distance hw0 hw1 (product hw0 hw1 Y t ht n) (ofRows hw0 hw1 X)) (rat e) :=
  ⟨productLimitRows hw0 hw1 Y t ht,productLimitRate hw0 hw1 Y t ht,
    productLimit_bound hw0 hw1 Y t ht⟩

#print axioms distance_eq_norm_difference
#print axioms preimageCeiling
#print axioms preimageCeiling_nonnegative
#print axioms preimageNorm_le_ceiling
#print axioms productBudget
#print axioms productRows_consecutive_bound
#print axioms productSequence
#print axioms productLimitRows
#print axioms productLimitRate
#print axioms productLimit_bound
#print axioms productLimitCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
