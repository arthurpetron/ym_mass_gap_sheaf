/-
# Actual inverse of the original physical Cayley-product limit

Physical conjugation turns each finite Cayley product into its actual
inverse. Its SAME-distance isometry transfers the already computed forward
rate to an inverse-limit witness. Original Rows are constructed, not selected
from quotient classes. Nome and width stay fixed; no time-addition law,
physical-time calibration, Hamiltonian or continuum claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConjugation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitLinear

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConjugation
  (conjugate conjugate_involutive conjugate_distance conjugateRows
    conjugateRows_pin conjugate_cayley_conjugate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productLimitRows productLimitRate iterate_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows limitMap_bound productLimit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
  (limitMap_injective)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "K" => conjugate hw0 hw1
local notation "D" => distance hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "Inv" => BF4WilsonAllNomeComplexBondOSScaledCayley.inverse hw0 hw1

private theorem iterate_cayley (t : Q') (ht : (0 : Q') < t) (x : H) (n : Nat) :
    iterate hw0 hw1 t ht (C t ht x) n = C t ht (iterate hw0 hw1 t ht x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterate]
      rw [ih]

private theorem conjugate_cayley (t : Q') (ht : (0 : Q') < t) (x : H) :
    K (C t ht x) = Inv t ht (K x) := by
  have h := conjugate_cayley_conjugate hw0 hw1 t ht (K x)
  simpa only [conjugate_involutive] using h

/-- An actual finite product followed by its conjugate inverse is identity. -/
theorem iterate_conjugate_inverse_right (t : Q') (ht : (0 : Q') < t)
    (x : H) (n : Nat) :
    iterate hw0 hw1 t ht (K (iterate hw0 hw1 t ht (K x) n)) n = x := by
  induction n with
  | zero => exact conjugate_involutive hw0 hw1 x
  | succ n ih =>
      change C t ht (iterate hw0 hw1 t ht
        (K (C t ht (iterate hw0 hw1 t ht (K x) n))) n) = x
      rw [conjugate_cayley,← iterate_cayley,
        BF4WilsonAllNomeComplexBondOSScaledCayley.inverse_right,ih]

/-- The actual inverse candidate uses the constructed limit on this SAME H. -/
def inverseMap (t : Q') (ht : (0 : Q') < t) (x : H) : H := K (F t ht (K x))

/-- Supplied original Rows give constructed inverse-output Rows without choice. -/
def inverseRows (X : R) (t : Q') (ht : (0 : Q') < t) : R :=
  conjugateRows hw0 hw1
    (productLimitRows hw0 hw1 (conjugateRows hw0 hw1 X) t ht)

theorem inverseRows_pin (X : R) (t : Q') (ht : (0 : Q') < t) :
    ofRows hw0 hw1 (inverseRows hw0 hw1 X t ht) =
      inverseMap hw0 hw1 t ht (ofRows hw0 hw1 X) := by
  unfold inverseRows inverseMap
  rw [conjugateRows_pin,← limitMap_ofRows,conjugateRows_pin]

/-- Exact finite inversion transports the existing forward rate, unchanged. -/
theorem inverseRows_product_distance (X : R) (t : Q') (ht : (0 : Q') < t)
    (n : Nat) :
    D (productValue hw0 hw1 (inverseRows hw0 hw1 X t ht) t ht n)
        (ofRows hw0 hw1 X) =
      D (productValue hw0 hw1 (conjugateRows hw0 hw1 X) t ht n)
        (F t ht (ofRows hw0 hw1 (conjugateRows hw0 hw1 X))) := by
  let s := step t n
  have hs := step_pos t ht n
  have hi := iterate_conjugate_inverse_right hw0 hw1 s hs
    (ofRows hw0 hw1 X) (2^n)
  calc
    D (productValue hw0 hw1 (inverseRows hw0 hw1 X t ht) t ht n)
        (ofRows hw0 hw1 X) =
      D (iterate hw0 hw1 s hs (ofRows hw0 hw1 (inverseRows hw0 hw1 X t ht)) (2^n))
        (iterate hw0 hw1 s hs (K (iterate hw0 hw1 s hs (K (ofRows hw0 hw1 X))
          (2^n))) (2^n)) := by
            change D (iterate hw0 hw1 s hs _ (2^n)) _ = _
            rw [hi]
    _ = D (ofRows hw0 hw1 (inverseRows hw0 hw1 X t ht))
        (K (iterate hw0 hw1 s hs (K (ofRows hw0 hw1 X)) (2^n))) :=
      iterate_distance hw0 hw1 s hs _ _ (2^n)
    _ = D (K (F t ht (K (ofRows hw0 hw1 X))))
        (K (iterate hw0 hw1 s hs (K (ofRows hw0 hw1 X)) (2^n))) := by
      rw [inverseRows_pin]
      rfl
    _ = D (F t ht (K (ofRows hw0 hw1 X)))
        (iterate hw0 hw1 s hs (K (ofRows hw0 hw1 X)) (2^n)) :=
      conjugate_distance hw0 hw1 _ _
    _ = D (productValue hw0 hw1 (conjugateRows hw0 hw1 X) t ht n)
        (F t ht (ofRows hw0 hw1 (conjugateRows hw0 hw1 X))) := by
      rw [distance_symm]
      simp only [productValue,conjugateRows_pin]
      rfl

/-- The constructed limit map has an actual right inverse on EVERY class. -/
theorem limitMap_inverse_right (t : Q') (ht : (0 : Q') < t) (x : H) :
    F t ht (inverseMap hw0 hw1 t ht x) = x := by
  rcases x with ⟨x,y⟩
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  change F t ht (inverseMap hw0 hw1 t ht (ofRows hw0 hw1 (X,Y))) =
    ofRows hw0 hw1 (X,Y)
  rw [← inverseRows_pin,limitMap_ofRows]
  apply productLimit_unique hw0 hw1 (inverseRows hw0 hw1 (X,Y) t ht) (X,Y) t ht
    (productLimitRate hw0 hw1 (conjugateRows hw0 hw1 (X,Y)) t ht)
  intro e he n hn
  rw [inverseRows_product_distance]
  exact limitMap_bound hw0 hw1 (conjugateRows hw0 hw1 (X,Y)) t ht e he n hn

/-- Injectivity converts the actual right inverse into a two-sided inverse. -/
theorem limitMap_inverse_left (t : Q') (ht : (0 : Q') < t) (x : H) :
    inverseMap hw0 hw1 t ht (F t ht x) = x := by
  apply limitMap_injective hw0 hw1 t ht
  exact limitMap_inverse_right hw0 hw1 t ht (F t ht x)

/-- A constructive preimage, not a Prop-level existence with erased data. -/
def preimage (t : Q') (ht : (0 : Q') < t) (x : H) :
    Σ' y : H, F t ht y = x :=
  ⟨inverseMap hw0 hw1 t ht x,limitMap_inverse_right hw0 hw1 t ht x⟩

#print axioms iterate_conjugate_inverse_right
#print axioms inverseMap
#print axioms inverseRows
#print axioms inverseRows_pin
#print axioms inverseRows_product_distance
#print axioms limitMap_inverse_right
#print axioms limitMap_inverse_left
#print axioms preimage

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInverse
