/-
# Dyadic Cayley-product limits for every supplied original physical Row

The represented second core has a checked product Cauchy modulus.  The
existing Type-valued density certificate, exact finite Cayley isometry and
two squared triangles extend that modulus to each supplied original physical
Rows object.  The approximating second-core source and its norm-dependent
core cutoff are computed from the input Rows and requested tolerance.

Nome and width remain fixed.  This does not identify the dyadic parameter
with physical time, produce a continuum Hilbert space or calibrate mass.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreDensity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows ofState rowState value
    value_injective value_ofRows value_ofState distance limitRows limitRate limit_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (input)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore (first)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreDensity
  (pairSources pairSources_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
  (iterate iterateRows iterateRows_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos product)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison
  (iterate_diff iterate_norm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (distance_eq_norm_difference productSequence)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_triangle distance_symm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound (normSq)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def oneSixteenth : Q' := Q'.mkPos 1 16 (by decide)

def tolerance (e : Q') : Q' := oneSixteenth*e

theorem tolerance_positive (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < tolerance e := Q'.mul_pos (by decide) he

def densityIndex (e : Q') : Nat := (tolerance e).den

/-- The actual second-core preimage chosen by the supplied physical Rows. -/
def coreSource (X : Rows hw0 hw1 (width := width)) (e : Q') :=
  pairSources hw0 hw1 X (densityIndex e)

theorem coreSource_near (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    RCle (D (ofRows hw0 hw1 X)
      (input hw0 hw1 (first hw0 hw1 (coreSource hw0 hw1 X e))))
      (rat (tolerance e)) := by
  have h := pairSources_bound hw0 hw1 X (densityIndex e)
  have hsmall : Q'.invSucc (densityIndex e) ≤ tolerance e :=
    HalfPow.invSucc_den_le (tolerance e) (tolerance_positive e he)
  have hrat : RCle (rat (Q'.invSucc (densityIndex e))) (rat (tolerance e)) := by
    intro eps heps
    exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ hsmall
      (Q'.add_le_self_of_nonneg (tolerance e) eps (Q'.le_of_lt heps))⟩
  rw [distance_symm] at h
  exact RCle_trans h hrat

/-- The computed state behind any supplied Rows is still its original state. -/
theorem ofRows_eq_ofState_rowState (X : Rows hw0 hw1 (width := width)) :
    ofRows hw0 hw1 X = ofState hw0 hw1 (rowState hw0 hw1 X) := by
  apply value_injective hw0 hw1
  rw [value_ofRows,value_ofState]

/-- Dyadic products of arbitrary represented physical Rows, not just core
inputs.  Each finite product retains two original represented rows. -/
def productRows (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) (n : Nat) : Rows hw0 hw1 (width := width) :=
  iterateRows hw0 hw1 (step t n) (step_pos t ht n)
    (rowState hw0 hw1 X) (2^n)

def productValue (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) (n : Nat) : H :=
  iterate hw0 hw1 (step t n) (step_pos t ht n) (ofRows hw0 hw1 X) (2^n)

theorem productRows_pin (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    ofRows hw0 hw1 (productRows hw0 hw1 X t ht n) =
      productValue hw0 hw1 X t ht n := by
  unfold productRows productValue
  rw [iterateRows_pin,← ofRows_eq_ofState_rowState hw0 hw1 X]

/-- Squared distance is preserved by each actual finite Cayley power. -/
theorem iterate_distance (s : Q') (hs : (0 : Q') < s)
    (x y : H) (k : Nat) :
    D (iterate hw0 hw1 s hs x k) (iterate hw0 hw1 s hs y k) = D x y := by
  rw [distance_eq_norm_difference hw0 hw1,
    ← iterate_diff hw0 hw1 s hs x y k,
    iterate_norm hw0 hw1 s hs (diff hw0 hw1 x y) k,
    ← distance_eq_norm_difference hw0 hw1]

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro eps heps
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b eps (Q'.le_of_lt heps))⟩

theorem product_near_core (X : Rows hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (t : Q') (ht : (0 : Q') < t) (n : Nat) :
    RCle (D (productValue hw0 hw1 X t ht n)
      (product hw0 hw1 (coreSource hw0 hw1 X e) t ht n))
      (rat (tolerance e)) := by
  unfold productValue product
  rw [iterate_distance]
  exact coreSource_near hw0 hw1 X e he

/-- Three insertions of the same auxiliary second-core state cost exactly
six endpoint copies and four core copies of a squared-distance budget. -/
private theorem three_bridge (a b c d : H) (q : Q')
    (hab : RCle (D a b) (rat q))
    (hbc : RCle (D b c) (rat q))
    (hcd : RCle (D c d) (rat q)) :
    RCle (D a d) (rat (10*q)) := by
  have hinner := RCle_trans (distance_triangle hw0 hw1 b c d)
    (RCadd_le_add (RCadd_le_add hbc hbc) (RCadd_le_add hcd hcd))
  have houter := RCle_trans (distance_triangle hw0 hw1 a b d)
    (RCadd_le_add (RCadd_le_add hab hab) (RCadd_le_add hinner hinner))
  have hcoef : RCadd (RCadd (rat q) (rat q))
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
  rw [hcoef] at houter
  exact houter

private theorem ten_tolerances_le (e : Q') (he : (0 : Q') < e) :
    10*tolerance e ≤ e := by
  have h := Q'.mul_le_mul_of_nonneg_right
    (10*oneSixteenth) 1 e (by decide) (Q'.le_of_lt he)
  have ha : Q'.eqv (10*tolerance e) ((10*oneSixteenth)*e) :=
    poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 10) (.var 0)) (.var 1))
      (by decide) (fun | 0 => oneSixteenth | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv e)))

/-- The source-dependent core modulus is computed after choosing a single
precision-dependent original preimage; no countable choice is used. -/
def productModulus (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) (e : Q') : Nat :=
  (productSequence hw0 hw1 (coreSource hw0 hw1 X e) t ht).modulus (tolerance e)

def productSequence (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) : CauchySequence hw0 hw1 (width := width) where
  seq := productRows hw0 hw1 X t ht
  modulus := productModulus hw0 hw1 X t ht
  bound := by
    intro e he m n hm hn
    let Y := coreSource hw0 hw1 X e
    let q := tolerance e
    have hnearM := product_near_core hw0 hw1 X e he t ht m
    have hnearN := product_near_core hw0 hw1 X e he t ht n
    have hcore := (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit.productSequence
      hw0 hw1 Y t ht).bound q (tolerance_positive e he) m n hm hn
    change RCle
      (D (ofRows hw0 hw1
        (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.productRows hw0 hw1 Y t ht m))
        (ofRows hw0 hw1
          (BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.productRows hw0 hw1 Y t ht n)))
      (rat q) at hcore
    rw [BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.productRows_pin,
      BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.productRows_pin] at hcore
    rw [productRows_pin,productRows_pin]
    have hreverse : RCle
        (D (product hw0 hw1 Y t ht n) (productValue hw0 hw1 X t ht n))
        (rat q) := by
      rw [distance_symm]
      exact hnearN
    have h := three_bridge hw0 hw1
      (productValue hw0 hw1 X t ht m)
      (product hw0 hw1 Y t ht m)
      (product hw0 hw1 Y t ht n)
      (productValue hw0 hw1 X t ht n)
      q hnearM hcore hreverse
    exact RCle_trans h (rat_le (ten_tolerances_le e he))

def productLimitRows (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) : Rows hw0 hw1 (width := width) :=
  limitRows hw0 hw1 (productSequence hw0 hw1 X t ht)

def productLimitRate (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) : Q' → Nat :=
  limitRate hw0 hw1 (productSequence hw0 hw1 X t ht)

theorem productLimit_bound (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : productLimitRate hw0 hw1 X t ht e ≤ n) :
    RCle (D (productValue hw0 hw1 X t ht n)
      (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))) (rat e) := by
  have h := limit_bound hw0 hw1 (productSequence hw0 hw1 X t ht) e he n hn
  change RCle (D (ofRows hw0 hw1 (productRows hw0 hw1 X t ht n))
    (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht))) (rat e) at h
  rw [productRows_pin] at h
  exact h

def productLimitCertificate (X : Rows hw0 hw1 (width := width))
    (t : Q') (ht : (0 : Q') < t) :
    Σ' Y : Rows hw0 hw1 (width := width), Σ' rate : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
        RCle (D (productValue hw0 hw1 X t ht n) (ofRows hw0 hw1 Y)) (rat e) :=
  ⟨productLimitRows hw0 hw1 X t ht,productLimitRate hw0 hw1 X t ht,
    productLimit_bound hw0 hw1 X t ht⟩

#print axioms tolerance
#print axioms densityIndex
#print axioms coreSource
#print axioms coreSource_near
#print axioms ofRows_eq_ofState_rowState
#print axioms productRows
#print axioms productValue
#print axioms productRows_pin
#print axioms iterate_distance
#print axioms product_near_core
#print axioms productModulus
#print axioms productSequence
#print axioms productLimitRows
#print axioms productLimitRate
#print axioms productLimit_bound
#print axioms productLimitCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
