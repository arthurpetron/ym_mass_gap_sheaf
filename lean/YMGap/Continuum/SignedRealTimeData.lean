/-
# Signed numerical time from pairs of represented positive times

A signed time is a difference of two already constructed positive-real-time
values.  The quotient identifies precisely pairs with the same ORIGINAL `RC`
value. Each real with SUPPLIED QCauchy data has a computed positive difference.
No physical operator, real-sign decision or bare-real modulus selector is supplied.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SignedRealTimeData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue)

local notation "pv" => BF4ExactSlabThermodynamicPositiveTimePins.realValue
local notation "pa" => BF4ExactSlabThermodynamicPositiveRealSemigroup.addTime

/-- Both components retain their existing Type-level positive-time data. -/
abbrev TimePair := PositiveTimeValue × PositiveTimeValue

def pairValue (p : TimePair) : RC := RCsub (pv p.1) (pv p.2)

private theorem rc_sub_cross (a b c d : RC)
    (h : RCsub a b = RCsub c d) : RCadd a d = RCadd c b := by
  have left : RCadd (RCsub a b) (RCadd b d) = RCadd a d := by
    refine Quotient.inductionOn₃ a b d ?_
    intro A C D
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.var 2)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => A.approx n | 1 => C.approx n | _ => D.approx n)))
  have right : RCadd (RCsub c d) (RCadd b d) = RCadd c b := by
    refine Quotient.inductionOn₃ c d b ?_
    intro C D A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.var 1)))
        (.add (.var 0) (.var 2))
        (by decide) (fun | 0 => C.approx n | 1 => D.approx n | _ => A.approx n)))
  calc
    RCadd a d = RCadd (RCsub a b) (RCadd b d) := left.symm
    _ = RCadd (RCsub c d) (RCadd b d) := congrArg (fun z => RCadd z (RCadd b d)) h
    _ = RCadd c b := right

/-- Equality of differences implies equality of the crossed POSITIVE sums,
using only existing positive-time value injectivity. -/
theorem pair_value_cross (p q : TimePair) (h : pairValue p = pairValue q) :
    pa p.1 q.2 = pa q.1 p.2 := by
  apply BF4ExactSlabThermodynamicPositiveTimePins.realValue_injective
  rw [BF4ExactSlabThermodynamicPositiveRealSemigroup.realValue_addTime,
    BF4ExactSlabThermodynamicPositiveRealSemigroup.realValue_addTime]
  exact rc_sub_cross _ _ _ _ h

/-- The quotient relation is exactly equality of the existing numerical
constructive-real differences. -/
def pairSetoid : Setoid TimePair where
  r p q := pairValue p = pairValue q
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

def SignedTimeValue : Type := Quotient pairSetoid

def ofPair (p : TimePair) : SignedTimeValue := Quotient.mk pairSetoid p

def realValue : SignedTimeValue → RC :=
  Quotient.lift pairValue (fun _ _ h => h)

theorem realValue_ofPair (p : TimePair) : realValue (ofPair p) = pairValue p := rfl

theorem realValue_injective (s t : SignedTimeValue)
    (h : realValue s = realValue t) : s = t := by
  revert h
  refine Quotient.inductionOn₂ s t ?_
  intro p q h
  exact Quotient.sound h

def addPair (p q : TimePair) : TimePair := (pa p.1 q.1,pa p.2 q.2)

private theorem rc_sub_add (a b c d : RC) :
    RCsub (RCadd a c) (RCadd b d) =
      RCadd (RCsub a b) (RCsub c d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  change Quotient.mk crealSetoid
      (CReal.sub (CReal.add A C) (CReal.add B D)) =
    Quotient.mk crealSetoid
      (CReal.add (CReal.sub A B) (CReal.sub C D))
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 2) (.neg (.var 3))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))

/-- Pairwise positive addition is exactly original signed RC addition. -/
theorem pairValue_add (p q : TimePair) :
    pairValue (addPair p q) = RCadd (pairValue p) (pairValue q) := by
  unfold pairValue addPair
  rw [BF4ExactSlabThermodynamicPositiveRealSemigroup.realValue_addTime,
    BF4ExactSlabThermodynamicPositiveRealSemigroup.realValue_addTime]
  change RCsub (RCadd (pv p.1) (pv q.1)) (RCadd (pv p.2) (pv q.2)) =
    RCadd (RCsub (pv p.1) (pv p.2)) (RCsub (pv q.1) (pv q.2))
  exact rc_sub_add _ _ _ _

def negPair (p : TimePair) : TimePair := (p.2,p.1)

private theorem rc_neg_sub (a b : RC) :
    RCsub b a = RCsub RCzero (RCsub a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  change Quotient.mk crealSetoid (CReal.sub B A) =
    Quotient.mk crealSetoid (CReal.sub CReal.czero (CReal.sub A B))
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 1) (.neg (.var 0)))
      (.add (.const 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

theorem pairValue_neg (p : TimePair) :
    pairValue (negPair p) = RCsub RCzero (pairValue p) := by
  unfold pairValue negPair
  change RCsub (pv p.2) (pv p.1) =
    RCsub RCzero (RCsub (pv p.1) (pv p.2))
  exact rc_neg_sub _ _

theorem pairValue_diagonal (a : PositiveTimeValue) :
    pairValue (a,a) = RCzero := by
  unfold pairValue
  refine Quotient.inductionOn (pv a) ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => A.approx n)))

def addTime : SignedTimeValue → SignedTimeValue → SignedTimeValue :=
  Quotient.lift₂ (fun p q => ofPair (addPair p q))
    (fun p p' q q' hp hq => Quotient.sound (by
      change pairValue (addPair p p') = pairValue (addPair q q')
      change pairValue p = pairValue q at hp
      change pairValue p' = pairValue q' at hq
      rw [pairValue_add,pairValue_add,hp,hq]))

theorem addTime_pin (p q : TimePair) :
    addTime (ofPair p) (ofPair q) = ofPair (addPair p q) := rfl

theorem realValue_addTime (s t : SignedTimeValue) :
    realValue (addTime s t) = RCadd (realValue s) (realValue t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro p q
  exact pairValue_add p q

def negTime : SignedTimeValue → SignedTimeValue :=
  Quotient.lift (fun p => ofPair (negPair p))
    (fun p q h => Quotient.sound (by
      change pairValue (negPair p) = pairValue (negPair q)
      change pairValue p = pairValue q at h
      rw [pairValue_neg,pairValue_neg,h]))

theorem negTime_pin (p : TimePair) : negTime (ofPair p) = ofPair (negPair p) := rfl

theorem realValue_negTime (s : SignedTimeValue) :
    realValue (negTime s) = RCsub RCzero (realValue s) := by
  refine Quotient.inductionOn s ?_
  intro p
  exact pairValue_neg p

def unitPositive : PositiveTimeValue :=
  timeValue (rational 1 (by decide))

def zeroTime : SignedTimeValue := ofPair (unitPositive,unitPositive)

theorem realValue_zeroTime : realValue zeroTime = RCzero := pairValue_diagonal unitPositive

/-- A positive time is represented by its sum with the fixed positive unit,
minus that same unit.  No zero-valued positive presentation is required. -/
def positiveTime (s : PositiveTimeValue) : SignedTimeValue :=
  ofPair (pa s unitPositive,unitPositive)

private theorem rc_add_sub_cancel (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

theorem realValue_positiveTime (s : PositiveTimeValue) :
    realValue (positiveTime s) = pv s := by
  change RCsub (pv (pa s unitPositive)) (pv unitPositive) = pv s
  rw [BF4ExactSlabThermodynamicPositiveRealSemigroup.realValue_addTime]
  exact rc_add_sub_cancel _ _

/-- The supplied modulus, not the legacy propositional real Cauchy field,
is the only input for shifting an arbitrary supplied real to positive time. -/
def shift (r : CReal) (cr : QCauchy r.approx) : Q' :=
  Q'.abs (r.approx (cr.M 1)) + 2

private theorem shift_positive (r : CReal) (cr : QCauchy r.approx) :
    (0 : Q') < shift r cr := by
  unfold shift
  have hle : (2 : Q') ≤ Q'.abs (r.approx (cr.M 1)) + 2 := by
    have hh := Q'.add_le_add_right 0 (Q'.abs (r.approx (cr.M 1))) 2
      (Q'.abs_nonneg _)
    rw [Q'.zero_add'] at hh
    exact hh
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < (2 : Q')) hle

private theorem shift_floor (a b : Q') (hab : a ≤ b+1) :
    (1 : Q') ≤ b+(Q'.abs a+2) := by
  have h0 : (0 : Q') ≤ a+Q'.abs a := by
    have hh := Q'.add_le_add_right (-a) (Q'.abs a) a (Q'.neg_le_abs a)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_add_self_eqv a))
      (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have h1 : (1 : Q') ≤ (a+Q'.abs a)+1 := by
    have hh := Q'.add_le_add_right 0 (a+Q'.abs a) 1 h0
    rw [Q'.zero_add'] at hh
    exact hh
  have h2 := Q'.add_le_add_right a (b+1) (Q'.abs a) hab
  have h3 := Q'.add_le_add_right _ _ 1 h2
  have hreorder : Q'.eqv (((b+1)+Q'.abs a)+1) (b+(Q'.abs a+2)) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.const 1)) (.var 1)) (.const 1))
      (.add (.var 0) (.add (.var 1) (.const 2)))
      (by decide) (fun | 0 => b | _ => Q'.abs a)
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv hreorder))

private def constantCauchy (q : Q') : QCauchy (CReal.ofQ' q).approx where
  M := fun _ => 0
  bound := fun e he _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg q e (Q'.le_of_lt he),
      Q'.add_le_self_of_nonneg q e (Q'.le_of_lt he)⟩

/-- An actual positive presentation of `r + shift`, with floor one after
the input modulus at tolerance one. -/
def shiftedPositive (r : CReal) (cr : QCauchy r.approx) :
    PositiveRealDyadicTimeData.PositiveTime where
  real := CReal.add r (CReal.ofQ' (shift r cr))
  cauchy := BF4ExactSlabPlaquetteRealScalarAlgebra.scalarAddCauchy
    r (CReal.ofQ' (shift r cr)) cr (constantCauchy (shift r cr))
  floor := 1
  floor_positive := by decide
  start := cr.M 1
  lower := by
    intro n hn
    have hc := cr.bound 1 (by decide) (cr.M 1) n (Nat.le_refl _) hn
    change (1 : Q') ≤ r.approx n + shift r cr
    exact shift_floor _ _ hc.1

/-- A positive rational presentation of the computed shift. -/
def shiftedRight (r : CReal) (cr : QCauchy r.approx) :
    PositiveTimeValue :=
  timeValue (rational (shift r cr) (shift_positive r cr))

def ofSuppliedReal (r : CReal) (cr : QCauchy r.approx) : SignedTimeValue :=
  ofPair (timeValue (shiftedPositive r cr),shiftedRight r cr)

/-- Every real with supplied Type-level QCauchy data is represented by an
explicit positive difference in the ORIGINAL `RC` numerical quotient. -/
theorem realValue_ofSuppliedReal (r : CReal) (cr : QCauchy r.approx) :
    realValue (ofSuppliedReal r cr) = Quotient.mk crealSetoid r := by
  change RCsub
      (Quotient.mk crealSetoid (CReal.add r (CReal.ofQ' (shift r cr))))
      (Quotient.mk crealSetoid (CReal.ofQ' (shift r cr))) =
    Quotient.mk crealSetoid r
  rw [← CReal.RCadd_mk]
  exact rc_add_sub_cancel _ _

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.var 0) (.const 0)) (.var 0)
      (by decide) (fun _ => A.approx n)))

private theorem rc_add_neg (a : RC) : RCadd a (RCsub RCzero a) = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.const 0) (.neg (.var 0)))) (.const 0)
      (by decide) (fun _ => A.approx n)))

theorem addTime_comm (s t : SignedTimeValue) : addTime s t = addTime t s := by
  apply realValue_injective
  rw [realValue_addTime,realValue_addTime]
  exact BF4ExactSlabThermodynamicBernsteinWords.add_comm _ _

theorem addTime_assoc (s t u : SignedTimeValue) :
    addTime (addTime s t) u = addTime s (addTime t u) := by
  apply realValue_injective
  rw [realValue_addTime,realValue_addTime,realValue_addTime,realValue_addTime]
  exact BF4ExactSlabThermodynamicBernsteinWords.add_assoc _ _ _

theorem addTime_zero (s : SignedTimeValue) : addTime s zeroTime = s := by
  apply realValue_injective
  rw [realValue_addTime,realValue_zeroTime]
  exact rc_add_zero _

theorem addTime_neg (s : SignedTimeValue) : addTime s (negTime s) = zeroTime := by
  apply realValue_injective
  rw [realValue_addTime,realValue_negTime,realValue_zeroTime]
  exact rc_add_neg _

#print axioms TimePair
#print axioms pairValue
#print axioms pair_value_cross
#print axioms pairSetoid
#print axioms SignedTimeValue
#print axioms realValue_injective
#print axioms pairValue_add
#print axioms pairValue_neg
#print axioms pairValue_diagonal
#print axioms addTime
#print axioms realValue_addTime
#print axioms negTime
#print axioms realValue_negTime
#print axioms zeroTime
#print axioms realValue_zeroTime
#print axioms positiveTime
#print axioms realValue_positiveTime
#print axioms shift
#print axioms shiftedPositive
#print axioms shiftedRight
#print axioms ofSuppliedReal
#print axioms realValue_ofSuppliedReal
#print axioms addTime_comm
#print axioms addTime_assoc
#print axioms addTime_zero
#print axioms addTime_neg

end YMGap.Continuum.SignedRealTimeData
