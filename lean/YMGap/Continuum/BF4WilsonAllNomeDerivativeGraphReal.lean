/-
# Real-time Taylor estimate on the witnessed original derivative graph

The graph's supplied input and derivative representatives produce remainder
rows on the SAME original Wilson carrier. The checked dyadic graph Taylor
bound passes to their limit for every supplied positive real time, retaining
the time-squared factor and an explicit radius. No uniform preimage bound,
log-series identification, or generator claim is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh
import YMGap.Continuum.BF4WilsonAllNomeRealDerivative
import YMGap.Continuum.BF4WilsonAllNomeRowLinear
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeRowLinear
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (action_embed)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh
open YMGap.Continuum.BF4WilsonAllNomeRealDerivative (pairing_converges)
open YMGap.Continuum.CRealSeminormPairingCompletion (representativeInner)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Order passage compares constructed limits; no witness is extracted. -/
private theorem limit_le_of_eventual {a b : Nat → CReal} {L M : CReal}
    (ha : ConvergesTo a L) (hb : ConvergesTo b M) (N : Nat)
    (h : ∀ n, N ≤ n → leEv (a n) (b n)) : leEv L M := by
  have shift {f : Nat → CReal} {l : CReal} (hf : ConvergesTo f l) :
      ConvergesTo (fun n => f (max n N)) l := by
    intro epsilon he
    obtain ⟨K, hK⟩ := hf epsilon he
    exact ⟨K, fun n hn => hK (max n N) (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le (shift ha) (shift hb)
    (fun n => h (max n N) (Nat.le_max_right _ _))

/-- The actual Taylor remainder at a witnessed graph point. -/
def realRemainder (D : PositiveTime) (u v : V) : V :=
  Sub (Sub u (realTimeAction hw0 hw1 (timeValue D) u))
    (completedRealSmul hw0 hw1 D.real D.cauchy v)

theorem realRemainder_time_congr (D E : PositiveTime)
    (h : Equiv D.real E.real) (u v : V) :
    realRemainder hw0 hw1 D u v = realRemainder hw0 hw1 E u v := by
  have ht : timeValue D = timeValue E := Quotient.sound h
  unfold realRemainder
  rw [ht, completedRealSmul_congr hw0 hw1 _ _ _ _ h]

/-- The actual original rows for the graph remainder. -/
def remainderRows (D : PositiveTime) (U V' : (PD).Cauchy) :
    RepresentedCauchy hw0 hw1 (width := width) :=
  differenceRows hw0 hw1
    (differenceRows hw0 hw1
      (constantRows hw0 hw1 U)
      (timeRows hw0 hw1 D U))
    (scalarRows hw0 hw1 (approximationReal D) (approximationCauchy D) V')

theorem remainderRows_pin (D : PositiveTime) (U V' : (PD).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (remainderRows hw0 hw1 D U V') n =
      BF4WilsonAllNomeDerivativeGraphMesh.remainder hw0 hw1
        (approximation D n).depth (approximation D n).steps (Class U) (Class V') := by
  unfold remainderRows
  rw [differenceRows_pin, differenceRows_pin, constantRows_point, timeRows_pin,
    scalarRows_pin, action_embed]
  rfl

theorem remainderRows_limit (D : PositiveTime) (U V' : (PD).Cauchy) :
    limit hw0 hw1 (remainderRows hw0 hw1 D U V') =
      realRemainder hw0 hw1 D (Class U) (Class V') := by
  unfold remainderRows
  rw [rowLimit_difference, rowLimit_difference, limit_constantRows, scalarRows_limit,
    completedRealSmul_congr hw0 hw1 _ _ _ D.cauchy (approximationReal_equiv D)]
  rfl

/-- Half the graph mesh radius leaves room for the positive-real dyadic
approximants eventually to lie in the checked graph Taylor radius. -/
def realRadius {U V' : (PD).Cauchy}
    (G : GraphLimit hw0 hw1 (Class U) (Class V'))
    (preimages : Nat → (PD).Cauchy)
    (_hpin : ∀ n, Class (preimages n) = G.source n) (epsilon : Q') : Q' :=
  HalfPow.half * BF4WilsonAllNomeDerivativeGraphMesh.radius
    hw0 hw1 G preimages epsilon

theorem realRadius_positive {U V' : (PD).Cauchy}
    (G : GraphLimit hw0 hw1 (Class U) (Class V'))
    (preimages : Nat → (PD).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n) (epsilon : Q') :
    (0 : Q') < realRadius hw0 hw1 G preimages hpin epsilon :=
  ExpNeg.half_mul_pos _
    (BF4WilsonAllNomeDerivativeGraphMesh.radius_positive hw0 hw1 G preimages epsilon)

/-- A Taylor bound at the supplied graph point on every sufficiently small
positive real increment, with its square-time factor intact. -/
theorem real_taylor_bound {U V' : (PD).Cauchy}
    (G : GraphLimit hw0 hw1 (Class U) (Class V'))
    (preimages : Nat → (PD).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (D : PositiveTime)
    (ht : RCle (realValue (timeValue D))
      (rat (realRadius hw0 hw1 G preimages hpin epsilon))) :
    RCle (B (realRemainder hw0 hw1 D (Class U) (Class V'))
      (realRemainder hw0 hw1 D (Class U) (Class V')))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D)))
        (rat epsilon)) := by
  have htime : Quotient.mk crealSetoid (approximationReal D) = realValue (timeValue D) :=
    Quotient.sound (approximationReal_equiv D)
  have hap : RCle (Quotient.mk crealSetoid (approximationReal D))
      (rat (realRadius hw0 hw1 G preimages hpin epsilon)) := by
    rw [htime]
    exact ht
  change leEv (approximationReal D)
    (ofQ' (realRadius hw0 hw1 G preimages hpin epsilon)) at hap
  obtain ⟨N, hN⟩ := hap
    (realRadius hw0 hw1 G preimages hpin epsilon)
    (realRadius_positive hw0 hw1 G preimages hpin epsilon)
  have hsmall (n : Nat) (hn : N ≤ n) :
      value (approximation D n) ≤ BF4WilsonAllNomeDerivativeGraphMesh.radius
        hw0 hw1 G preimages epsilon :=
    Q'.le_trans' _ _ _ (hN n hn)
      (Q'.le_of_eqv (ExpNeg.two_halves
        (BF4WilsonAllNomeDerivativeGraphMesh.radius hw0 hw1 G preimages epsilon)))
  let R := remainderRows hw0 hw1 D U V'
  have hleft := pairing_converges hw0 hw1 R R
  have hright : ConvergesTo
      (fun n => CReal.mul (CReal.mul (ofQ' (value (approximation D n)))
        (ofQ' (value (approximation D n)))) (ofQ' epsilon))
      (CReal.mul (CReal.mul (approximationReal D) (approximationReal D)) (ofQ' epsilon)) :=
    convergesTo_mul_general
      (convergesTo_mul_general (convergesTo_self (approximationReal D))
        (convergesTo_self (approximationReal D))) (convergesTo_const _)
  have h := limit_le_of_eventual hleft hright N (by
    intro n hn
    change RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 R n))
      (rat ((value (approximation D n) * value (approximation D n)) * epsilon))
    rw [show R = remainderRows hw0 hw1 D U V' from rfl, remainderRows_pin]
    exact BF4WilsonAllNomeDerivativeGraphMesh.mesh_taylor_bound
      hw0 hw1 G preimages hpin epsilon he
      (approximation D n).depth (approximation D n).steps (hsmall n hn))
  change RCle (B (limit hw0 hw1 R) (limit hw0 hw1 R))
    (RCmul (RCmul (Quotient.mk crealSetoid (approximationReal D))
      (Quotient.mk crealSetoid (approximationReal D))) (rat epsilon)) at h
  rw [show R = remainderRows hw0 hw1 D U V' from rfl, remainderRows_limit, htime] at h
  exact h

/-- Explicit real Taylor radius for the supplied graph point and its supplied
preimage stream. -/
def realTaylorCertificate {U V' : (PD).Cauchy}
    (G : GraphLimit hw0 hw1 (Class U) (Class V'))
    (preimages : Nat → (PD).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ D : PositiveTime,
        RCle (realValue (timeValue D)) (rat r) →
          RCle (B (realRemainder hw0 hw1 D (Class U) (Class V'))
            (realRemainder hw0 hw1 D (Class U) (Class V')))
            (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D)))
              (rat epsilon))) :=
  ⟨realRadius hw0 hw1 G preimages hpin epsilon,
    realRadius_positive hw0 hw1 G preimages hpin epsilon,
    fun D ht => real_taylor_bound hw0 hw1 G preimages hpin epsilon he D ht⟩

#print axioms realRemainder
#print axioms realRemainder_time_congr
#print axioms remainderRows
#print axioms remainderRows_pin
#print axioms remainderRows_limit
#print axioms realRadius
#print axioms realRadius_positive
#print axioms real_taylor_bound
#print axioms realTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal
