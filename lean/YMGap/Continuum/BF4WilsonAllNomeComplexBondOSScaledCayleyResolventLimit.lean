/-
# Actual Cayley time commutes with the ORIGINAL positive resolvent

The componentwise original resolvent is contractive in the physical bond
distance. Its represented state factory retains both original range witnesses.
Finite Cayley commutation therefore passes through the ACTUAL rational-product
and positive-real limits, using the unchanged original convergence rates.

The consumer is maximal-graph transport for the constructed signed-time group:
the unit resolvent reconstructs a domain witness from input plus output.
Nome and width remain fixed. This is not a physical spacing calibration,
changing-family survival, continuum QFT or mass-gap theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime sample)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue_distance bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (bondValue_sub)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
  (resolvent resolvent_sub norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeScaledResolventNeumannLimit
  (scaledResolventState scaledResolventState_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows rowsOfState rowState ofRows_rowsOfState)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
  (pairResolvent cayley_pairResolvent_commute)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productValue productLimitRows productLimitRate productLimit_bound
    ofRows_eq_ofState_rowState)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows productLimit_unique rows_limit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (sample_positive timeRows timeRows_pin timeSequence timeLimitRows
    timeLimitRate timeLimit_bound positiveAction positiveAction_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction positiveRealAction_pin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "J" => pairResolvent hw0 hw1
local notation "D" => BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem real_distance_sub_norm (x y : RH) :
    bondCompletedDistance hw0 hw1 x y =
      bondCompletedInner hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x y)
        (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x y) := by
  rw [bondValue_distance,bondValue_inner,bondValue_sub]
  rfl

private theorem real_resolvent_distance_bound (s : Q') (hs : (0 : Q') < s)
    (x y : RH) :
    RCle (bondCompletedDistance hw0 hw1
      (resolvent hw0 hw1 s hs x) (resolvent hw0 hw1 s hs y))
      (bondCompletedDistance hw0 hw1 x y) := by
  rw [real_distance_sub_norm,real_distance_sub_norm,← resolvent_sub]
  exact norm_bound hw0 hw1 s hs _

/-- The original resolvent contracts the SAME two-component physical distance. -/
theorem pairResolvent_distance_bound (s : Q') (hs : (0 : Q') < s) (x y : H) :
    RCle (D (J s hs x) (J s hs y)) (D x y) :=
  RCadd_le_add (real_resolvent_distance_bound hw0 hw1 s hs x.1 y.1)
    (real_resolvent_distance_bound hw0 hw1 s hs x.2 y.2)

/-- Construct BOTH original range-bearing resolvent states before quotienting. -/
def resolventRows (s : Q') (hs : (0 : Q') < s) (X : R) : R :=
  rowsOfState hw0 hw1
    (scaledResolventState hw0 hw1 s hs (rowState hw0 hw1 X).1,
     scaledResolventState hw0 hw1 s hs (rowState hw0 hw1 X).2)

theorem resolventRows_pin (s : Q') (hs : (0 : Q') < s) (X : R) :
    ofRows hw0 hw1 (resolventRows hw0 hw1 s hs X) = J s hs (ofRows hw0 hw1 X) := by
  rw [resolventRows,ofRows_rowsOfState,ofRows_eq_ofState_rowState]
  apply Prod.ext <;> exact scaledResolventState_pin hw0 hw1 s hs _

theorem iterate_pairResolvent_commute (s t : Q')
    (hs : (0 : Q') < s) (ht : (0 : Q') < t) (x : H) (n : Nat) :
    iterate hw0 hw1 t ht (J s hs x) n = J s hs (iterate hw0 hw1 t ht x n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate,ih,cayley_pairResolvent_commute]
      rfl

/-- Resolvent images reuse the ORIGINAL product rate, with no loss. -/
theorem product_resolvent_limit_bound (s : Q') (hs : (0 : Q') < s) (X : R)
    (t : Q') (ht : (0 : Q') < t) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : productLimitRate hw0 hw1 X t ht e ≤ n) :
    RCle (D (productValue hw0 hw1 (resolventRows hw0 hw1 s hs X) t ht n)
      (ofRows hw0 hw1 (resolventRows hw0 hw1 s hs
        (productLimitRows hw0 hw1 X t ht)))) (rat e) := by
  unfold productValue
  rw [resolventRows_pin,iterate_pairResolvent_commute,resolventRows_pin]
  exact RCle_trans (pairResolvent_distance_bound hw0 hw1 s hs _ _)
    (productLimit_bound hw0 hw1 X t ht e he n hn)

theorem limitMap_pairResolvent_commute_ofRows (s t : Q')
    (hs : (0 : Q') < s) (ht : (0 : Q') < t) (X : R) :
    limitMap hw0 hw1 t ht (J s hs (ofRows hw0 hw1 X)) =
      J s hs (limitMap hw0 hw1 t ht (ofRows hw0 hw1 X)) := by
  let L := productLimitRows hw0 hw1 X t ht
  have hlimits := productLimit_unique hw0 hw1 (resolventRows hw0 hw1 s hs X)
    (resolventRows hw0 hw1 s hs L) t ht (productLimitRate hw0 hw1 X t ht)
    (product_resolvent_limit_bound hw0 hw1 s hs X t ht)
  rw [← resolventRows_pin hw0 hw1 s hs X,limitMap_ofRows,hlimits,
    resolventRows_pin,← limitMap_ofRows]

/-- EVERY original class; no representative is selected for a modulus. -/
theorem limitMap_pairResolvent_commute (s t : Q')
    (hs : (0 : Q') < s) (ht : (0 : Q') < t) (x : H) :
    limitMap hw0 hw1 t ht (J s hs x) = J s hs (limitMap hw0 hw1 t ht x) := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  exact limitMap_pairResolvent_commute_ofRows hw0 hw1 s t hs ht (X,Y)

/-- Positive-real samples retain the ORIGINAL time-limit rate unchanged. -/
theorem time_resolvent_limit_bound (s : Q') (hs : (0 : Q') < s)
    (time : PositiveTime) (X : R) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : timeLimitRate hw0 hw1 time X e ≤ n) :
    RCle (D (ofRows hw0 hw1 (timeRows hw0 hw1 time
        (resolventRows hw0 hw1 s hs X) n))
      (ofRows hw0 hw1 (resolventRows hw0 hw1 s hs
        (timeLimitRows hw0 hw1 time X)))) (rat e) := by
  rw [timeRows_pin,resolventRows_pin,limitMap_pairResolvent_commute,
    resolventRows_pin,← timeRows_pin]
  exact RCle_trans (pairResolvent_distance_bound hw0 hw1 s hs _ _)
    (timeLimit_bound hw0 hw1 time X e he n hn)

theorem positiveAction_pairResolvent_commute_ofRows (s : Q') (hs : (0 : Q') < s)
    (time : PositiveTime) (X : R) :
    positiveAction hw0 hw1 time (J s hs (ofRows hw0 hw1 X)) =
      J s hs (positiveAction hw0 hw1 time (ofRows hw0 hw1 X)) := by
  let L := timeLimitRows hw0 hw1 time X
  have hlimits := rows_limit_unique hw0 hw1
    (timeSequence hw0 hw1 time (resolventRows hw0 hw1 s hs X))
    (resolventRows hw0 hw1 s hs L) (timeLimitRate hw0 hw1 time X)
    (time_resolvent_limit_bound hw0 hw1 s hs time X)
  change ofRows hw0 hw1 (timeLimitRows hw0 hw1 time
    (resolventRows hw0 hw1 s hs X)) =
    ofRows hw0 hw1 (resolventRows hw0 hw1 s hs L) at hlimits
  rw [← resolventRows_pin hw0 hw1 s hs X,positiveAction_ofRows,hlimits,
    resolventRows_pin,← positiveAction_ofRows]

theorem positiveAction_pairResolvent_commute (s : Q') (hs : (0 : Q') < s)
    (time : PositiveTime) (x : H) :
    positiveAction hw0 hw1 time (J s hs x) = J s hs (positiveAction hw0 hw1 time x) := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  exact positiveAction_pairResolvent_commute_ofRows hw0 hw1 s hs time (X,Y)

theorem positiveRealAction_pairResolvent_commute (s : Q') (hs : (0 : Q') < s)
    (time : PositiveTimeValue) (x : H) :
    positiveRealAction hw0 hw1 time (J s hs x) =
      J s hs (positiveRealAction hw0 hw1 time x) := by
  refine Quotient.inductionOn time ?_
  intro t
  exact positiveAction_pairResolvent_commute hw0 hw1 s hs t x

#print axioms pairResolvent_distance_bound
#print axioms resolventRows
#print axioms resolventRows_pin
#print axioms iterate_pairResolvent_commute
#print axioms product_resolvent_limit_bound
#print axioms limitMap_pairResolvent_commute_ofRows
#print axioms limitMap_pairResolvent_commute
#print axioms time_resolvent_limit_bound
#print axioms positiveAction_pairResolvent_commute_ofRows
#print axioms positiveAction_pairResolvent_commute
#print axioms positiveRealAction_pairResolvent_commute

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit
