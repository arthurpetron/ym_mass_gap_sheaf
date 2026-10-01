/-
# Choice-free physical quotient map from the actual Cayley-product limit

The original represented product limits are unique in the SAME physical
distance. Equal input Rows classes therefore have equal output classes.
Quotient.lift₂ constructs a map on EVERY original complex bond class without
selecting representatives. Supplied Rows retain their computed approximation
rate. Rational parameter normalization changes no actual limit map.

Nome and width remain fixed. This is not a group law, surjectivity theorem,
physical-time identification, Hamiltonian calibration or continuum claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows ofState rowState value
    value_injective value_ofRows value_ofState rowsOfState ofRows_rowsOfState
    distance distance_value sectorSequence limitRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productRows productRows_pin productSequence productLimitRows
    productLimitRate productLimit_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter
  (iterate_parameter_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The existing represented completion has unique physical limits. The
modulus is supplied as Type-level data, not extracted from an existential. -/
theorem rows_limit_unique (C : CauchySequence hw0 hw1 (width := width))
    (Y : R) (rate : Q' → Nat)
    (h : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (D (ofRows hw0 hw1 (C.seq n)) (ofRows hw0 hw1 Y)) (rat e)) :
    ofRows hw0 hw1 (limitRows hw0 hw1 C) = ofRows hw0 hw1 Y := by
  apply value_injective hw0 hw1
  rw [limitRows,ofRows_rowsOfState,value_ofState,value_ofRows]
  apply BF4WilsonAllNomeComplexTimeSector.limit_unique hw0 hw1
    (sectorSequence hw0 hw1 C) (rowState hw0 hw1 Y) rate
  intro e he n hn
  have hy := h e he n hn
  rw [distance_value,value_ofRows,value_ofRows] at hy
  exact hy

/-- A limit of the ACTUAL products is identified in the original physical
quotient; no replacement norm or auxiliary carrier is used. -/
theorem productLimit_unique (X Y : R) (t : Q') (ht : (0 : Q') < t)
    (rate : Q' → Nat)
    (h : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (D (productValue hw0 hw1 X t ht n) (ofRows hw0 hw1 Y)) (rat e)) :
    ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht) = ofRows hw0 hw1 Y := by
  apply rows_limit_unique hw0 hw1 (productSequence hw0 hw1 X t ht) Y rate
  intro e he n hn
  change RCle (D (ofRows hw0 hw1 (productRows hw0 hw1 X t ht n))
    (ofRows hw0 hw1 Y)) (rat e)
  rw [productRows_pin]
  exact h e he n hn

/-- Equivalent input Rows give equal ACTUAL limit classes. -/
theorem productLimit_congr (t : Q') (ht : (0 : Q') < t) {X Y : R}
    (hXY : ofRows hw0 hw1 X = ofRows hw0 hw1 Y) :
    ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht) =
      ofRows hw0 hw1 (productLimitRows hw0 hw1 Y t ht) := by
  apply productLimit_unique hw0 hw1 X (productLimitRows hw0 hw1 Y t ht)
    t ht (productLimitRate hw0 hw1 Y t ht)
  intro e he n hn
  have hp : productValue hw0 hw1 X t ht n = productValue hw0 hw1 Y t ht n :=
    congrArg (fun x => iterate hw0 hw1 (step t n) (step_pos t ht n) x (2^n)) hXY
  rw [hp]
  exact productLimit_bound hw0 hw1 Y t ht e he n hn

/-- The two original row quotients are eliminated by a proved quotient lift,
never by choosing a representative. The limit map acts on EVERY class. -/
def limitMap (t : Q') (ht : (0 : Q') < t) (x : H) : H :=
  Quotient.lift₂
    (fun X Y => ofRows hw0 hw1 (productLimitRows hw0 hw1 (X,Y) t ht))
    (fun _ _ _ _ hX hY => productLimit_congr hw0 hw1 t ht
      (Prod.ext (Quotient.sound hX) (Quotient.sound hY))) x.1 x.2

theorem limitMap_ofRows (t : Q') (ht : (0 : Q') < t) (X : R) :
    limitMap hw0 hw1 t ht (ofRows hw0 hw1 X) =
      ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht) := rfl

/-- The original computed rate remains available whenever Rows are supplied.
No modulus is selected from a bare quotient class. -/
theorem limitMap_bound (X : R) (t : Q') (ht : (0 : Q') < t)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : productLimitRate hw0 hw1 X t ht e ≤ n) :
    RCle (D (productValue hw0 hw1 X t ht n)
      (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X))) (rat e) := by
  rw [limitMap_ofRows]
  exact productLimit_bound hw0 hw1 X t ht e he n hn

/-- Equivalent rational outer parameters give equal limit maps on EVERY
physical class, not a group or physical-time law. -/
theorem limitMap_parameter_congr {s t : Q'} (hs : (0 : Q') < s)
    (ht : (0 : Q') < t) (hst : Q'.eqv s t) (x : H) :
    limitMap hw0 hw1 s hs x = limitMap hw0 hw1 t ht x := by
  rcases x with ⟨x,y⟩
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  change ofRows hw0 hw1 (productLimitRows hw0 hw1 (X,Y) s hs) =
    ofRows hw0 hw1 (productLimitRows hw0 hw1 (X,Y) t ht)
  apply productLimit_unique hw0 hw1 (X,Y)
    (productLimitRows hw0 hw1 (X,Y) t ht) s hs (productLimitRate hw0 hw1 (X,Y) t ht)
  intro e he n hn
  have hp : productValue hw0 hw1 (X,Y) s hs n = productValue hw0 hw1 (X,Y) t ht n :=
    iterate_parameter_congr hw0 hw1 (step_pos s hs n) (step_pos t ht n)
      (Q'.mul_eqv_congr_right s t (HalfPow.half^n) hst) (ofRows hw0 hw1 (X,Y)) (2^n)
  rw [hp]
  exact productLimit_bound hw0 hw1 (X,Y) t ht e he n hn

#print axioms rows_limit_unique
#print axioms productLimit_unique
#print axioms productLimit_congr
#print axioms limitMap
#print axioms limitMap_ofRows
#print axioms limitMap_bound
#print axioms limitMap_parameter_congr

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
