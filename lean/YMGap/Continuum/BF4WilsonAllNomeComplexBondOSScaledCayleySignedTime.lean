/-
# Signed-time action on the ORIGINAL completed physical Wilson bond

Represent time as a difference of supplied positive-real values, not by a
decided sign. The ACTUAL positive action and its computed inverse produce
the difference action. Equality of numerical differences gives equality
of crossed positive sums; actual composition and inverse laws then prove
representation independence. No physical operator is imported from the
legacy numerical-time carrier.

The full Hermitian pairing, complex scalar witnesses and original carrier
are retained. This is fixed nome and width; continuity, maximal-generator
identification, physical spacing/scaling and continuum Yang--Mills do not
follow from the algebraic signed-time laws alone.
-/

import YMGap.Continuum.SignedRealTimeData
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeLinear

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue)
open YMGap.Continuum.SignedRealTimeData
  (TimePair SignedTimeValue pairValue pairSetoid ofPair addPair negPair)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition
  (positiveRealAction_addTime positiveRealAction_commute)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
  (positiveRealAction_pairing_preserved positiveRealAction_distance
    positiveRealAction_injective)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse
  (inverseRealAction positiveRealAction_inverse_right positiveRealAction_inverse_left)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeLinear
  (positiveRealAction_add positiveRealAction_smul)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "I" => inner hw0 hw1
local notation "D" => distance hw0 hw1
local notation "U" => positiveRealAction hw0 hw1
local notation "V" => inverseRealAction hw0 hw1
local notation "P" => BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1

/-- Commutation with the computed inverse is derived by actual injectivity,
not supplied as a domain or group-law field. -/
theorem positive_inverse_commute (s t : PositiveTimeValue) (x : H) :
    U s (V t x) = V t (U s x) := by
  apply positiveRealAction_injective hw0 hw1 t
  rw [positiveRealAction_commute hw0 hw1 t s,
    positiveRealAction_inverse_right,positiveRealAction_inverse_right]

theorem inverse_addTime (s t : PositiveTimeValue) (x : H) :
    V (P s t) x = V s (V t x) := by
  apply positiveRealAction_injective hw0 hw1 (P s t)
  rw [positiveRealAction_inverse_right,positiveRealAction_addTime,
    positive_inverse_commute,positiveRealAction_inverse_right,
    positiveRealAction_inverse_right]

theorem inverse_pairing_preserved (s : PositiveTimeValue) (x y : H) :
    I (V s x) (V s y) = I x y := by
  calc
    I (V s x) (V s y) = I (U s (V s x)) (U s (V s y)) :=
      (positiveRealAction_pairing_preserved hw0 hw1 s _ _).symm
    _ = I x y := by rw [positiveRealAction_inverse_right,positiveRealAction_inverse_right]

theorem inverse_distance (s : PositiveTimeValue) (x y : H) :
    D (V s x) (V s y) = D x y := by
  calc
    D (V s x) (V s y) = D (U s (V s x)) (U s (V s y)) :=
      (positiveRealAction_distance hw0 hw1 s _ _).symm
    _ = D x y := by rw [positiveRealAction_inverse_right,positiveRealAction_inverse_right]

theorem inverse_add_state (s : PositiveTimeValue) (x y : H) :
    V s (A x y) = A (V s x) (V s y) := by
  apply positiveRealAction_injective hw0 hw1 s
  rw [positiveRealAction_inverse_right,positiveRealAction_add,
    positiveRealAction_inverse_right,positiveRealAction_inverse_right]

theorem inverse_smul (s : PositiveTimeValue) (a b : CReal)
    (ca : QCauchy a.approx) (cb : QCauchy b.approx) (x : H) :
    V s (S a b ca cb x) = S a b ca cb (V s x) := by
  apply positiveRealAction_injective hw0 hw1 s
  rw [positiveRealAction_inverse_right,positiveRealAction_smul,
    positiveRealAction_inverse_right]

/-- Actual difference action; neither time component nor inverse is chosen. -/
def pairAction (p : TimePair) (x : H) : H := U p.1 (V p.2 x)

theorem positive_sum_pairAction_cancel (r : PositiveTimeValue) (p : TimePair) (x : H) :
    U (P r p.2) (pairAction hw0 hw1 p x) = U (P r p.1) x := by
  rw [pairAction,positiveRealAction_addTime,
    positiveRealAction_commute hw0 hw1 p.2 p.1,
    positiveRealAction_inverse_right,positiveRealAction_addTime]

/-- Numerical equality of differences meets actual positive composition.
No quotient representative or real-sign decision is selected. -/
theorem pairAction_congr (p q : TimePair) (h : pairValue p = pairValue q) (x : H) :
    pairAction hw0 hw1 p x = pairAction hw0 hw1 q x := by
  have hcross := SignedRealTimeData.pair_value_cross p q h
  apply positiveRealAction_injective hw0 hw1 (P p.2 q.2)
  calc
    U (P p.2 q.2) (pairAction hw0 hw1 p x) = U (P q.2 p.1) x := by
      rw [BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime_comm p.2 q.2]
      exact positive_sum_pairAction_cancel hw0 hw1 q.2 p x
    _ = U (P p.1 q.2) x := by
      rw [BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime_comm q.2 p.1]
    _ = U (P q.1 p.2) x := congrArg (fun t => U t x) hcross
    _ = U (P p.2 q.1) x := by
      rw [BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime_comm q.1 p.2]
    _ = U (P p.2 q.2) (pairAction hw0 hw1 q x) :=
      (positive_sum_pairAction_cancel hw0 hw1 p.2 q x).symm

/-- Representation-independent signed action on EVERY original class. -/
def signedAction (t : SignedTimeValue) (x : H) : H :=
  Quotient.lift (fun p => pairAction hw0 hw1 p x)
    (fun p q h => pairAction_congr hw0 hw1 p q h x) t

theorem signedAction_ofPair (p : TimePair) (x : H) :
    signedAction hw0 hw1 (ofPair p) x = pairAction hw0 hw1 p x := rfl

theorem pairAction_addPair (p q : TimePair) (x : H) :
    pairAction hw0 hw1 (addPair p q) x =
      pairAction hw0 hw1 p (pairAction hw0 hw1 q x) := by
  unfold pairAction addPair
  rw [positiveRealAction_addTime,inverse_addTime,
    positive_inverse_commute hw0 hw1 q.1 p.2]

theorem signedAction_addTime (s t : SignedTimeValue) (x : H) :
    signedAction hw0 hw1 (SignedRealTimeData.addTime s t) x =
      signedAction hw0 hw1 s (signedAction hw0 hw1 t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro p q
  exact pairAction_addPair hw0 hw1 p q x

theorem signedAction_zero (x : H) :
    signedAction hw0 hw1 SignedRealTimeData.zeroTime x = x :=
  positiveRealAction_inverse_right hw0 hw1 SignedRealTimeData.unitPositive x

/-- The signed construction EXACTLY recovers the original positive-real
action; it is not merely a compatible replacement. -/
theorem signedAction_positiveTime (s : PositiveTimeValue) (x : H) :
    signedAction hw0 hw1 (SignedRealTimeData.positiveTime s) x = U s x := by
  change U (P s SignedRealTimeData.unitPositive)
    (V SignedRealTimeData.unitPositive x) = U s x
  rw [positiveRealAction_addTime,positiveRealAction_inverse_right]

/-- Actual signed action for any real with its supplied computational modulus.
The numerical producer constructs a positive difference without a sign test. -/
def suppliedRealAction (r : CReal) (cr : QCauchy r.approx) (x : H) : H :=
  signedAction hw0 hw1 (SignedRealTimeData.ofSuppliedReal r cr) x

theorem suppliedRealAction_congr (r s : CReal)
    (cr : QCauchy r.approx) (cs : QCauchy s.approx) (h : Equiv r s) (x : H) :
    suppliedRealAction hw0 hw1 r cr x = suppliedRealAction hw0 hw1 s cs x := by
  have ht : SignedRealTimeData.ofSuppliedReal r cr =
      SignedRealTimeData.ofSuppliedReal s cs := by
    apply SignedRealTimeData.realValue_injective
    rw [SignedRealTimeData.realValue_ofSuppliedReal,
      SignedRealTimeData.realValue_ofSuppliedReal]
    exact Quotient.sound h
  exact congrArg (fun t => signedAction hw0 hw1 t x) ht

theorem pairAction_negPair (p : TimePair) (x : H) :
    pairAction hw0 hw1 (negPair p) (pairAction hw0 hw1 p x) = x := by
  unfold pairAction negPair
  rw [positiveRealAction_inverse_left,positiveRealAction_inverse_right]

theorem signedAction_neg_left (t : SignedTimeValue) (x : H) :
    signedAction hw0 hw1 (SignedRealTimeData.negTime t) (signedAction hw0 hw1 t x) = x := by
  refine Quotient.inductionOn t ?_
  intro p
  exact pairAction_negPair hw0 hw1 p x

theorem signedAction_neg_right (t : SignedTimeValue) (x : H) :
    signedAction hw0 hw1 t (signedAction hw0 hw1 (SignedRealTimeData.negTime t) x) = x := by
  refine Quotient.inductionOn t ?_
  intro p
  exact pairAction_negPair hw0 hw1 (negPair p) x

theorem signedAction_pairing_preserved (t : SignedTimeValue) (x y : H) :
    I (signedAction hw0 hw1 t x) (signedAction hw0 hw1 t y) = I x y := by
  refine Quotient.inductionOn t ?_
  intro p
  change I (U p.1 (V p.2 x)) (U p.1 (V p.2 y)) = _
  rw [positiveRealAction_pairing_preserved,inverse_pairing_preserved]

theorem signedAction_distance (t : SignedTimeValue) (x y : H) :
    D (signedAction hw0 hw1 t x) (signedAction hw0 hw1 t y) = D x y := by
  refine Quotient.inductionOn t ?_
  intro p
  change D (U p.1 (V p.2 x)) (U p.1 (V p.2 y)) = _
  rw [positiveRealAction_distance,inverse_distance]

theorem signedAction_add_state (t : SignedTimeValue) (x y : H) :
    signedAction hw0 hw1 t (A x y) = A (signedAction hw0 hw1 t x) (signedAction hw0 hw1 t y) := by
  refine Quotient.inductionOn t ?_
  intro p
  change U p.1 (V p.2 (A x y)) = _
  rw [inverse_add_state,positiveRealAction_add]
  rfl

theorem signedAction_smul (t : SignedTimeValue) (a b : CReal)
    (ca : QCauchy a.approx) (cb : QCauchy b.approx) (x : H) :
    signedAction hw0 hw1 t (S a b ca cb x) = S a b ca cb (signedAction hw0 hw1 t x) := by
  refine Quotient.inductionOn t ?_
  intro p
  change U p.1 (V p.2 (S a b ca cb x)) = _
  rw [inverse_smul,positiveRealAction_smul]
  rfl

/-- Exact zero-time displacement reduces to nearby POSITIVE parameters,
including when both parameters are large. This is the continuity consumer. -/
theorem pairAction_displacement (p : TimePair) (x : H) :
    D (pairAction hw0 hw1 p x) x = D (U p.1 x) (U p.2 x) := by
  calc
    D (pairAction hw0 hw1 p x) x =
        D (U p.2 (pairAction hw0 hw1 p x)) (U p.2 x) :=
      (positiveRealAction_distance hw0 hw1 p.2 _ _).symm
    _ = D (U p.1 x) (U p.2 x) := by
      rw [pairAction,positiveRealAction_commute hw0 hw1 p.2 p.1,
        positiveRealAction_inverse_right]

#print axioms positive_inverse_commute
#print axioms inverse_addTime
#print axioms inverse_pairing_preserved
#print axioms inverse_distance
#print axioms inverse_add_state
#print axioms inverse_smul
#print axioms pairAction
#print axioms positive_sum_pairAction_cancel
#print axioms pairAction_congr
#print axioms signedAction
#print axioms signedAction_ofPair
#print axioms pairAction_addPair
#print axioms signedAction_addTime
#print axioms signedAction_zero
#print axioms signedAction_positiveTime
#print axioms suppliedRealAction
#print axioms suppliedRealAction_congr
#print axioms pairAction_negPair
#print axioms signedAction_neg_left
#print axioms signedAction_neg_right
#print axioms signedAction_pairing_preserved
#print axioms signedAction_distance
#print axioms signedAction_add_state
#print axioms signedAction_smul
#print axioms pairAction_displacement

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
