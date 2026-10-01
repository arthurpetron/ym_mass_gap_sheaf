/-
# Original Euclidean action commutes with the constructed Cayley limit

The finite Cayley products commute with the original positive-time action on
the SAME physical complex Wilson bond completion.  Acting on supplied Rows
preserves their constructive range witnesses.  The original product modulus
and the physical time contraction identify the two actual limits without a
second analytic input or a chosen quotient representative.

Nome and width remain fixed.  This is neither full-real time nor a physical
spacing, transfer-logarithm, or continuum-QFT identification.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanCommutation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows rowsOfState rowState ofRows_rowsOfState
    value value_injective value_ofRows value_ofState distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts
  (step step_pos)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productLimitRows productLimitRate productLimit_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows productLimit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanCommutation
  (iterate_action_commute)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Retain BOTH original time-sector range witnesses before quotienting. -/
def actionRows (s : PositiveTime) (X : R) : R :=
  rowsOfState hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.action hw0 hw1 s (rowState hw0 hw1 X))

theorem actionRows_pin (s : PositiveTime) (X : R) :
    ofRows hw0 hw1 (actionRows hw0 hw1 s X) =
      S (timeValue s) (ofRows hw0 hw1 X) := by
  apply value_injective hw0 hw1
  rw [actionRows,ofRows_rowsOfState,value_ofState,
    BF4WilsonAllNomeComplexBondOSTime.action_value,value_ofRows]
  change
    (positiveAction hw0 hw1 s (rowState hw0 hw1 X).1.val,
      positiveAction hw0 hw1 s (rowState hw0 hw1 X).2.val) =
    (BF4WilsonAllNomePositiveTimePins.realTimeAction hw0 hw1 (timeValue s)
      (rowState hw0 hw1 X).1.val,
     BF4WilsonAllNomePositiveTimePins.realTimeAction hw0 hw1 (timeValue s)
      (rowState hw0 hw1 X).2.val)
  simp only [realTimeAction_pin]

/-- The SAME original product modulus controls Euclidean images of the
actual products; physical time is contractive in the original bond distance. -/
theorem product_action_limit_bound (s : PositiveTime) (X : R)
    (t : Q') (ht : (0 : Q') < t) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : productLimitRate hw0 hw1 X t ht e ≤ n) :
    RCle
      (D (productValue hw0 hw1 (actionRows hw0 hw1 s X) t ht n)
        (ofRows hw0 hw1
          (actionRows hw0 hw1 s (productLimitRows hw0 hw1 X t ht))))
      (rat e) := by
  have hproduct : productValue hw0 hw1 (actionRows hw0 hw1 s X) t ht n =
      S (timeValue s) (productValue hw0 hw1 X t ht n) := by
    unfold productValue
    rw [actionRows_pin,iterate_action_commute]
  rw [hproduct,actionRows_pin]
  exact RCle_trans
    (BF4WilsonAllNomeComplexBondOSTime.action_distance_bound hw0 hw1
      (timeValue s) (productValue hw0 hw1 X t ht n)
      (ofRows hw0 hw1 (productLimitRows hw0 hw1 X t ht)))
    (productLimit_bound hw0 hw1 X t ht e he n hn)

/-- The computed represented limits, not a conditional continuity field,
intertwine original Euclidean and Cayley time. -/
theorem limitMap_action_commute_ofRows (t : Q') (ht : (0 : Q') < t)
    (s : PositiveTime) (X : R) :
    limitMap hw0 hw1 t ht (S (timeValue s) (ofRows hw0 hw1 X)) =
      S (timeValue s) (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X)) := by
  let L := productLimitRows hw0 hw1 X t ht
  have hlimits :
      ofRows hw0 hw1
          (productLimitRows hw0 hw1 (actionRows hw0 hw1 s X) t ht) =
        ofRows hw0 hw1 (actionRows hw0 hw1 s L) := by
    apply productLimit_unique hw0 hw1 (actionRows hw0 hw1 s X)
      (actionRows hw0 hw1 s L) t ht (productLimitRate hw0 hw1 X t ht)
    intro e he n hn
    exact product_action_limit_bound hw0 hw1 s X t ht e he n hn
  calc
    limitMap hw0 hw1 t ht (S (timeValue s) (ofRows hw0 hw1 X)) =
        limitMap hw0 hw1 t ht (ofRows hw0 hw1 (actionRows hw0 hw1 s X)) :=
      congrArg (limitMap hw0 hw1 t ht) (actionRows_pin hw0 hw1 s X).symm
    _ = ofRows hw0 hw1
          (productLimitRows hw0 hw1 (actionRows hw0 hw1 s X) t ht) :=
      limitMap_ofRows hw0 hw1 t ht (actionRows hw0 hw1 s X)
    _ = ofRows hw0 hw1 (actionRows hw0 hw1 s L) := hlimits
    _ = S (timeValue s) (ofRows hw0 hw1 L) := actionRows_pin hw0 hw1 s L
    _ = S (timeValue s) (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X)) :=
      congrArg (S (timeValue s)) (limitMap_ofRows hw0 hw1 t ht X).symm

/-- Original positive Euclidean time commutes with the ACTUAL Cayley-product
limit on EVERY complex physical bond class at fixed nome and width. -/
theorem limitMap_action_commute (t : Q') (ht : (0 : Q') < t)
    (s : PositiveTime) (x : H) :
    limitMap hw0 hw1 t ht (S (timeValue s) x) =
      S (timeValue s) (limitMap hw0 hw1 t ht x) := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  exact limitMap_action_commute_ofRows hw0 hw1 t ht s (X,Y)

#print axioms actionRows
#print axioms actionRows_pin
#print axioms product_action_limit_bound
#print axioms limitMap_action_commute_ofRows
#print axioms limitMap_action_commute

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanLimit
