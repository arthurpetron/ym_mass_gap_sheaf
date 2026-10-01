/-
# Constructed positive-real Cayley time on the original physical bond

Supplied positive constructive-real time data provide positive rational
samples and an explicit numerical Cauchy modulus. The original rational
Cayley limit's source-dependent parameter radius turns that modulus into
an actual physical Rows Cauchy sequence. Its existing completion returns
original range-bearing limit Rows, not an assumed analytic time image.

Input-row congruence constructs a map on EVERY original physical class.
Positive rational time recovers the original Cayley limit exactly. Time
presentation independence and the real addition law are separate joins.
Nome and width stay fixed; no generator or physical-spacing calibration,
changing-family survival, continuum QFT or mass gap is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity
import YMGap.Continuum.PositiveRealDyadicTimeData

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime sample sample_lower rational)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows CauchySequence ofRows distance limitRows limitRate limit_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit
  (productLimitRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap limitMap_ofRows rows_limit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity
  (radius radius_positive)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity
  (parameter_close_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit (distance_self)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem sample_positive (time : PositiveTime) (n : Nat) :
    (0 : Q') < sample time n :=
  ClusteringImpliesGap.lt_of_lt_of_le time.floor_positive (sample_lower time n)

/-- The irrelevant nonpositive-tolerance branch is decidable rational data.
The positive branch is exactly the original source-derived radius. -/
def parameterRadius (X : R) (e : Q') : Q' :=
  if he : (0 : Q') < e then radius hw0 hw1 X e he else 1

theorem parameterRadius_pin (X : R) (e : Q') (he : (0 : Q') < e) :
    parameterRadius hw0 hw1 X e = radius hw0 hw1 X e he := by
  simp only [parameterRadius,dif_pos he]

/-- Each time sample has already constructed ORIGINAL product-limit Rows. -/
def timeRows (time : PositiveTime) (X : R) (n : Nat) : R :=
  productLimitRows hw0 hw1 X (sample time n) (sample_positive time n)

theorem timeRows_pin (time : PositiveTime) (X : R) (n : Nat) :
    ofRows hw0 hw1 (timeRows hw0 hw1 time X n) =
      limitMap hw0 hw1 (sample time n) (sample_positive time n) (ofRows hw0 hw1 X) := rfl

/-- Compose the supplied numerical modulus with the ORIGINAL source radius. -/
def timeModulus (time : PositiveTime) (X : R) (e : Q') : Nat :=
  time.cauchy.M (parameterRadius hw0 hw1 X e)

theorem timeRows_cauchy (time : PositiveTime) (X : R) (e : Q')
    (he : (0 : Q') < e) (m n : Nat)
    (hm : timeModulus hw0 hw1 time X e ≤ m)
    (hn : timeModulus hw0 hw1 time X e ≤ n) :
    RCle (D (ofRows hw0 hw1 (timeRows hw0 hw1 time X m))
      (ofRows hw0 hw1 (timeRows hw0 hw1 time X n))) (rat e) := by
  have hr := radius_positive hw0 hw1 X e he
  have hm' : time.cauchy.M (radius hw0 hw1 X e he) ≤ m := by
    simpa only [timeModulus,parameterRadius_pin hw0 hw1 X e he] using hm
  have hn' : time.cauchy.M (radius hw0 hw1 X e he) ≤ n := by
    simpa only [timeModulus,parameterRadius_pin hw0 hw1 X e he] using hn
  have htime := time.cauchy.bound (radius hw0 hw1 X e he) hr
    (time.start+m) (time.start+n)
    (Nat.le_trans hm' (Nat.le_add_left _ _))
    (Nat.le_trans hn' (Nat.le_add_left _ _))
  rw [timeRows_pin,timeRows_pin]
  exact parameter_close_bound hw0 hw1 X e he (sample time m) (sample time n)
    (sample_positive time m) (sample_positive time n) htime.1 htime.2

/-- The all-tail bound is in the SAME physical bond distance. -/
def timeSequence (time : PositiveTime) (X : R) :
    CauchySequence hw0 hw1 (width := width) where
  seq := timeRows hw0 hw1 time X
  modulus := timeModulus hw0 hw1 time X
  bound := timeRows_cauchy hw0 hw1 time X

def timeLimitRows (time : PositiveTime) (X : R) : R :=
  limitRows hw0 hw1 (timeSequence hw0 hw1 time X)

def timeLimitRate (time : PositiveTime) (X : R) : Q' → Nat :=
  limitRate hw0 hw1 (timeSequence hw0 hw1 time X)

theorem timeLimit_bound (time : PositiveTime) (X : R) (e : Q')
    (he : (0 : Q') < e) (n : Nat) (hn : timeLimitRate hw0 hw1 time X e ≤ n) :
    RCle (D (ofRows hw0 hw1 (timeRows hw0 hw1 time X n))
      (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X))) (rat e) :=
  limit_bound hw0 hw1 (timeSequence hw0 hw1 time X) e he n hn

/-- Actual time-output Rows and convergence rate remain Type-level data. -/
def timeLimitCertificate (time : PositiveTime) (X : R) :
    Σ' Y : R, Σ' rate : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
        RCle (D (ofRows hw0 hw1 (timeRows hw0 hw1 time X n))
          (ofRows hw0 hw1 Y)) (rat e) :=
  ⟨timeLimitRows hw0 hw1 time X,timeLimitRate hw0 hw1 time X,
    timeLimit_bound hw0 hw1 time X⟩

theorem timeLimit_congr (time : PositiveTime) {X Y : R}
    (h : ofRows hw0 hw1 X = ofRows hw0 hw1 Y) :
    ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X) =
      ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y) := by
  apply rows_limit_unique hw0 hw1 (timeSequence hw0 hw1 time X)
    (timeLimitRows hw0 hw1 time Y) (timeLimitRate hw0 hw1 time Y)
  intro e he n hn
  change RCle (D (ofRows hw0 hw1 (timeRows hw0 hw1 time X n))
    (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time Y))) (rat e)
  rw [timeRows_pin,h,← timeRows_pin hw0 hw1 time Y n]
  exact timeLimit_bound hw0 hw1 time Y e he n hn

/-- Paired quotient lift, never arbitrary representative selection. -/
def positiveAction (time : PositiveTime) (x : H) : H :=
  Quotient.lift₂ (fun X Y => ofRows hw0 hw1 (timeLimitRows hw0 hw1 time (X,Y)))
    (fun _ _ _ _ hX hY => timeLimit_congr hw0 hw1 time
      (Prod.ext (Quotient.sound hX) (Quotient.sound hY))) x.1 x.2

theorem positiveAction_ofRows (time : PositiveTime) (X : R) :
    positiveAction hw0 hw1 time (ofRows hw0 hw1 X) =
      ofRows hw0 hw1 (timeLimitRows hw0 hw1 time X) := rfl

/-- Constant rational samples recover the ACTUAL original rational limit. -/
theorem positiveAction_rational (q : Q') (hq : (0 : Q') < q) (x : H) :
    positiveAction hw0 hw1 (rational q hq) x = limitMap hw0 hw1 q hq x := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  change positiveAction hw0 hw1 (rational q hq) (ofRows hw0 hw1 (X,Y)) =
    limitMap hw0 hw1 q hq (ofRows hw0 hw1 (X,Y))
  rw [positiveAction_ofRows,limitMap_ofRows]
  apply rows_limit_unique hw0 hw1 (timeSequence hw0 hw1 (rational q hq) (X,Y))
    (productLimitRows hw0 hw1 (X,Y) q hq) (fun _ => 0)
  intro e he n hn
  change RCle (D (ofRows hw0 hw1 (productLimitRows hw0 hw1 (X,Y) q hq))
    (ofRows hw0 hw1 (productLimitRows hw0 hw1 (X,Y) q hq))) (rat e)
  rw [distance_self]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

#print axioms sample_positive
#print axioms parameterRadius_pin
#print axioms timeRows_pin
#print axioms timeModulus
#print axioms timeRows_cauchy
#print axioms timeSequence
#print axioms timeLimit_bound
#print axioms timeLimitCertificate
#print axioms timeLimit_congr
#print axioms positiveAction
#print axioms positiveAction_ofRows
#print axioms positiveAction_rational

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
