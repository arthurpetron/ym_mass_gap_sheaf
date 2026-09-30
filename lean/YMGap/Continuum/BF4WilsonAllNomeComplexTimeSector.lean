/-
# Witnessed complex continuous-time sector on the original Wilson carrier

Two original range witnesses define a subspace of the EXISTING complex
completion. Its inner product and scalar operations are literally the old
ones. Cauchy limits retain both witnesses, with a computed combined modulus.
The original positive-real-time action preserves this sector, is complex
linear and contractive, and has an explicit zero-time continuity radius.

Equality compares underlying original vectors, not witness records. No
representative is selected from a quotient. This constructs complex-sector
compatibility, NOT its physical OS identification, a resolvent, a scaling
estimate, or a continuum quantum field theory.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4WilsonAllNomeComplexification
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition

namespace YMGap.Continuum.BF4WilsonAllNomeComplexTimeSector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure
  (positiveAction_preservesRange)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
  (realRadius realRadius_positive real_smallTime)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RealState" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "VC" => BF4WilsonAllNomeComplexification.ComplexCarrier hw0 hw1 width
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "d" => completedDist hw0 hw1

/-- Both original range witnesses remain computational data. -/
abbrev State := RealState × RealState

def val (x : State hw0 hw1 (width := width)) : VC := (x.1.val,x.2.val)

def stateSetoid : Setoid (State hw0 hw1 (width := width)) where
  r x y := val hw0 hw1 x = val hw0 hw1 y
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩

def zero : State hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeTimeSector.zero hw0 hw1,BF4WilsonAllNomeTimeSector.zero hw0 hw1)

def add (x y : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeTimeSector.add hw0 hw1 x.1 y.1,
   BF4WilsonAllNomeTimeSector.add hw0 hw1 x.2 y.2)

def smul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : State hw0 hw1 (width := width)) : State hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeTimeSector.add hw0 hw1
    (BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 s cs x.1)
    (BF4WilsonAllNomeTimeSector.negate hw0 hw1
      (BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 t ct x.2)),
   BF4WilsonAllNomeTimeSector.add hw0 hw1
    (BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 t ct x.1)
    (BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 s cs x.2))

def inner (x y : State hw0 hw1 (width := width)) :=
  BF4WilsonAllNomeComplexification.inner hw0 hw1 width (val hw0 hw1 x) (val hw0 hw1 y)

/-- Squared distance, the sum of the two ORIGINAL completed distances. -/
def distance (x y : State hw0 hw1 (width := width)) : RC :=
  RCadd (d x.1.val y.1.val) (d x.2.val y.2.val)

theorem val_zero : val hw0 hw1 (zero hw0 hw1 (width := width)) =
    BF4WilsonAllNomeComplexification.complexZero hw0 hw1 width := rfl

theorem val_add (x y : State hw0 hw1 (width := width)) :
    val hw0 hw1 (add hw0 hw1 x y) =
      BF4WilsonAllNomeComplexification.complexAdd hw0 hw1 width (val hw0 hw1 x) (val hw0 hw1 y) := rfl

theorem val_smul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : State hw0 hw1 (width := width)) : val hw0 hw1 (smul hw0 hw1 s t cs ct x) =
      BF4WilsonAllNomeComplexification.complexSmul hw0 hw1 width s t cs ct (val hw0 hw1 x) := rfl

theorem inner_conj_symm (x y : State hw0 hw1 (width := width)) :
    inner hw0 hw1 x y = BF4WilsonAllNomeComplexification.valueConj (inner hw0 hw1 y x) :=
  BF4WilsonAllNomeComplexification.inner_conj_symm hw0 hw1 width _ _

theorem inner_smul_right (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x y : State hw0 hw1 (width := width)) :
    inner hw0 hw1 x (smul hw0 hw1 s t cs ct y) =
      BF4WilsonAllNomeComplexification.valueMul
        (BF4WilsonAllNomeComplexification.scalarValue s t) (inner hw0 hw1 x y) := by
  unfold inner
  rw [val_smul]
  exact BF4WilsonAllNomeComplexification.inner_smul_right hw0 hw1 width s t cs ct _ _

theorem inner_posdef (x : State hw0 hw1 (width := width)) :
    (inner hw0 hw1 x x).1 = RCzero ↔ val hw0 hw1 x = val hw0 hw1 (zero hw0 hw1) :=
  BF4WilsonAllNomeComplexification.inner_posdef hw0 hw1 width _

theorem inner_nonnegative (x : State hw0 hw1 (width := width)) :
    RCnonneg (inner hw0 hw1 x x).1 :=
  BF4WilsonAllNomeComplexification.inner_nonnegative hw0 hw1 width _

theorem inner_add_right (x y z : State hw0 hw1 (width := width)) :
    inner hw0 hw1 x (add hw0 hw1 y z) =
      BF4WilsonAllNomeComplexification.valueAdd (inner hw0 hw1 x y) (inner hw0 hw1 x z) := by
  unfold inner
  rw [val_add]
  exact BF4WilsonAllNomeComplexification.inner_add_right hw0 hw1 width _ _ _

/-- The convergence metric is exactly the ORIGINAL complex norm of the
difference, not a separately postulated topology. -/
theorem distance_norm_pin (x y : State hw0 hw1 (width := width)) :
    distance hw0 hw1 x y =
      (BF4WilsonAllNomeComplexification.inner hw0 hw1 width
        (completedSub hw0 hw1 x.1.val y.1.val,completedSub hw0 hw1 x.2.val y.2.val)
        (completedSub hw0 hw1 x.1.val y.1.val,completedSub hw0 hw1 x.2.val y.2.val)).1 := rfl

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (A.approx n)))

theorem distance_fst_le (x y : State hw0 hw1 (width := width)) :
    RCle (d x.1.val y.1.val) (distance hw0 hw1 x y) := by
  have h := RCadd_le_add (RCle_refl (d x.1.val y.1.val))
    (completedDist_nonnegative hw0 hw1 x.2.val y.2.val)
  rw [rc_add_zero] at h
  exact h

theorem distance_snd_le (x y : State hw0 hw1 (width := width)) :
    RCle (d x.2.val y.2.val) (distance hw0 hw1 x y) := by
  have h := RCadd_le_add (completedDist_nonnegative hw0 hw1 x.1.val y.1.val)
    (RCle_refl (d x.2.val y.2.val))
  rw [rc_zero_add] at h
  exact h

/-- A SINGLE supplied modulus for the genuine complex squared distance. -/
structure CauchySequence where
  seq : Nat → State hw0 hw1 (width := width)
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ m n,
    modulus e ≤ m → modulus e ≤ n →
      RCle (distance hw0 hw1 (seq m) (seq n)) (rat e)

def realSequence (C : CauchySequence hw0 hw1 (width := width)) :
    BF4WilsonAllNomeTimeSector.CauchySequence hw0 hw1 (width := width) where
  seq := fun n => (C.seq n).1
  modulus := C.modulus
  bound := fun e he m n hm hn => RCle_trans
    (distance_fst_le hw0 hw1 _ _) (C.bound e he m n hm hn)

def imagSequence (C : CauchySequence hw0 hw1 (width := width)) :
    BF4WilsonAllNomeTimeSector.CauchySequence hw0 hw1 (width := width) where
  seq := fun n => (C.seq n).2
  modulus := C.modulus
  bound := fun e he m n hm hn => RCle_trans
    (distance_snd_le hw0 hw1 _ _) (C.bound e he m n hm hn)

def limit (C : CauchySequence hw0 hw1 (width := width)) : State hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeTimeSector.limit hw0 hw1 (realSequence hw0 hw1 C),
   BF4WilsonAllNomeTimeSector.limit hw0 hw1 (imagSequence hw0 hw1 C))

def limitRate (C : CauchySequence hw0 hw1 (width := width)) (e : Q') : Nat :=
  max (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (realSequence hw0 hw1 C) (HalfPow.half*e))
    (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (imagSequence hw0 hw1 C) (HalfPow.half*e))

private theorem half_budget (e : Q') :
    RCadd (rat (HalfPow.half*e)) (rat (HalfPow.half*e)) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves e))

theorem limit_bound (C : CauchySequence hw0 hw1 (width := width)) (e : Q')
    (he : (0 : Q') < e) (n : Nat) (hn : limitRate hw0 hw1 C e ≤ n) :
    RCle (distance hw0 hw1 (C.seq n) (limit hw0 hw1 C)) (rat e) := by
  have h := RCadd_le_add
    (BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 (realSequence hw0 hw1 C)
      _ (ExpNeg.half_mul_pos _ he) n (Nat.le_trans (Nat.le_max_left _ _) hn))
    (BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 (imagSequence hw0 hw1 C)
      _ (ExpNeg.half_mul_pos _ he) n (Nat.le_trans (Nat.le_max_right _ _) hn))
  rw [half_budget] at h
  exact h

theorem limit_unique (C : CauchySequence hw0 hw1 (width := width))
    (z : State hw0 hw1 (width := width)) (rate : Q' → Nat)
    (h : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (distance hw0 hw1 (C.seq n) z) (rat e)) :
    val hw0 hw1 (limit hw0 hw1 C) = val hw0 hw1 z := by
  apply Prod.ext
  · exact BF4WilsonAllNomeTimeSector.limit_unique hw0 hw1 (realSequence hw0 hw1 C)
      z.1.val rate (fun e he n hn => RCle_trans (distance_fst_le hw0 hw1 _ _) (h e he n hn))
  · exact BF4WilsonAllNomeTimeSector.limit_unique hw0 hw1 (imagSequence hw0 hw1 C)
      z.2.val rate (fun e he n hn => RCle_trans (distance_snd_le hw0 hw1 _ _) (h e he n hn))

def limitCertificate (C : CauchySequence hw0 hw1 (width := width)) :
    Σ' x : State hw0 hw1 (width := width), Σ' rate : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
        RCle (distance hw0 hw1 (C.seq n) x) (rat e) :=
  ⟨limit hw0 hw1 C,limitRate hw0 hw1 C,limit_bound hw0 hw1 C⟩

/-- Actual original positive-time images, WITH both original range witnesses. -/
def action (t : PositiveTime) (x : State hw0 hw1 (width := width)) :
    State hw0 hw1 (width := width) :=
  (⟨positiveAction hw0 hw1 t x.1.val,positiveAction_preservesRange hw0 hw1 t x.1.range⟩,
   ⟨positiveAction hw0 hw1 t x.2.val,positiveAction_preservesRange hw0 hw1 t x.2.range⟩)

theorem action_sum (s t : PositiveTime) (x : State hw0 hw1 (width := width)) :
    val hw0 hw1 (action hw0 hw1 (PositiveRealDyadicTimeAddition.sumTime s t) x) =
      val hw0 hw1 (action hw0 hw1 s (action hw0 hw1 t x)) := by
  apply Prod.ext <;> exact BF4WilsonAllNomePositiveTimeComposition.positiveAction_sum hw0 hw1 s t _

/-- Equality is independent of the represented time, its floor and modulus. -/
theorem action_time_congr (s t : PositiveTime) (h : Equiv s.real t.real)
    (x : State hw0 hw1 (width := width)) :
    val hw0 hw1 (action hw0 hw1 s x) = val hw0 hw1 (action hw0 hw1 t x) := by
  apply Prod.ext <;> exact BF4WilsonAllNomePositiveTimePins.positiveAction_time_congr hw0 hw1 s t h _

/-- Positive integers recover the EXISTING complex transfer, with its
original time unit. No physical-time calibration is inferred. -/
theorem action_original (n : Nat) (hn : 0 < n) (x : State hw0 hw1 (width := width)) :
    val hw0 hw1 (action hw0 hw1
      (BF4ExactSlabThermodynamicPositiveTimePins.dyadicTime ⟨0,n⟩ hn) x) =
      BF4WilsonAllNomeComplexification.complexTime hw0 hw1 width n (val hw0 hw1 x) := by
  apply Prod.ext <;> exact BF4WilsonAllNomePositiveTimePins.positiveAction_original hw0 hw1 n hn _

theorem action_add (t : PositiveTime) (x y : State hw0 hw1 (width := width)) :
    val hw0 hw1 (action hw0 hw1 t (add hw0 hw1 x y)) =
      val hw0 hw1 (add hw0 hw1 (action hw0 hw1 t x) (action hw0 hw1 t y)) := by
  apply Prod.ext <;> exact positiveAction_add hw0 hw1 t _ _

theorem action_smul (t : PositiveTime) (a b : CReal)
    (ca : QCauchy a.approx) (cb : QCauchy b.approx) (x : State hw0 hw1 (width := width)) :
    val hw0 hw1 (action hw0 hw1 t (smul hw0 hw1 a b ca cb x)) =
      val hw0 hw1 (smul hw0 hw1 a b ca cb (action hw0 hw1 t x)) := by
  simp only [val,action,smul,BF4WilsonAllNomeTimeSector.add,
    BF4WilsonAllNomeTimeSector.realSmul,BF4WilsonAllNomeTimeSector.negate,
    completedNeg,positiveAction_add,positiveAction_smul,positiveAction_realSmul]

theorem action_symmetric (t : PositiveTime) (x y : State hw0 hw1 (width := width)) :
    inner hw0 hw1 (action hw0 hw1 t x) y = inner hw0 hw1 x (action hw0 hw1 t y) := by
  simp only [inner,val,action,BF4WilsonAllNomeComplexification.inner,positiveAction_symmetric]

theorem action_nonnegative (t : PositiveTime) (x : State hw0 hw1 (width := width)) :
    RCnonneg (inner hw0 hw1 x (action hw0 hw1 t x)).1 := by
  have h := RCadd_le_add (positiveAction_nonnegative hw0 hw1 t x.1.val)
    (positiveAction_nonnegative hw0 hw1 t x.2.val)
  rw [rc_add_zero] at h
  exact h

theorem action_distance_bound (t : PositiveTime) (x y : State hw0 hw1 (width := width)) :
    RCle (distance hw0 hw1 (action hw0 hw1 t x) (action hw0 hw1 t y))
      (distance hw0 hw1 x y) := RCadd_le_add
  (positiveAction_distance_bound hw0 hw1 t x.1.val y.1.val)
  (positiveAction_distance_bound hw0 hw1 t x.2.val y.2.val)

def continuityRadius (x : State hw0 hw1 (width := width)) (e : Q') : Q' :=
  Q'.min' (realRadius hw0 hw1 x.1.range (HalfPow.half*e))
    (realRadius hw0 hw1 x.2.range (HalfPow.half*e))

theorem continuityRadius_positive (x : State hw0 hw1 (width := width)) (e : Q') :
    (0 : Q') < continuityRadius hw0 hw1 x e := by
  unfold continuityRadius Q'.min'
  split <;> exact realRadius_positive hw0 hw1 _ _

theorem smallTime (x : State hw0 hw1 (width := width)) (e : Q') (he : (0 : Q') < e)
    (t : PositiveTime) (ht : RCle (realValue (timeValue t)) (rat (continuityRadius hw0 hw1 x e))) :
    RCle (distance hw0 hw1 (action hw0 hw1 t x) x) (rat e) := by
  have hl := real_smallTime hw0 hw1 x.1.range (HalfPow.half*e) (ExpNeg.half_mul_pos _ he) t
    (RCle_trans ht (leEv_le_ofQ'_of_approx_le (fun _ => Q'.min_le_left' _ _)))
  have hr := real_smallTime hw0 hw1 x.2.range (HalfPow.half*e) (ExpNeg.half_mul_pos _ he) t
    (RCle_trans ht (leEv_le_ofQ'_of_approx_le (fun _ => Q'.min_le_right' _ _)))
  rw [BF4WilsonAllNomePositiveTimePins.realTimeAction_pin] at hl hr
  have h := RCadd_le_add hl hr
  rw [half_budget] at h
  exact h

def continuityCertificate (x : State hw0 hw1 (width := width)) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (distance hw0 hw1 (action hw0 hw1 t x) x) (rat e)) :=
  ⟨continuityRadius hw0 hw1 x e,continuityRadius_positive hw0 hw1 x e,smallTime hw0 hw1 x e he⟩

#print axioms stateSetoid
#print axioms zero
#print axioms add
#print axioms smul
#print axioms val_zero
#print axioms val_add
#print axioms val_smul
#print axioms inner_conj_symm
#print axioms inner_smul_right
#print axioms inner_posdef
#print axioms inner_nonnegative
#print axioms inner_add_right
#print axioms distance_norm_pin
#print axioms distance_fst_le
#print axioms distance_snd_le
#print axioms limit_bound
#print axioms limitCertificate
#print axioms limit_unique
#print axioms action
#print axioms action_sum
#print axioms action_time_congr
#print axioms action_original
#print axioms action_add
#print axioms action_smul
#print axioms action_symmetric
#print axioms action_nonnegative
#print axioms action_distance_bound
#print axioms continuityRadius_positive
#print axioms smallTime
#print axioms continuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexTimeSector
