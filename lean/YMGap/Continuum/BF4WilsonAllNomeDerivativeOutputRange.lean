/-
# The actual derivative output lies in the witnessed original time-range closure

Only the INPUT range witness and the actual dyadic state-quotient limit
are supplied. At depth n, approximate the input tightly enough to absorb
the explicit quotient distance factor, and use the quotient of that
original time preimage. A diagonal with the derivative-limit modulus
constructs the OUTPUT range witness. No transfer inverse, uniform
preimage norm bound, or quotient representative selection is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeStateQuotientDistance
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphQuotient

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeOutputRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation
open YMGap.Continuum.BF4WilsonAllNomeStateQuotientDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
  (preimageRepresentative quotient_time_image)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
  (graphOfQuotientLimit graphOfEquation_representative_pin equationRealTaylorCertificate)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum (inverseSumRepresentative)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal (realRemainder)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Q" => stateQuotient hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- A depth-dependent input error budget, compensating for the actual
normalized quotient's increasing squared-distance factor. -/
def sourceTolerance (n : Nat) : Q' :=
  linearTolerance (quotientCap n) (quotientCap_nonnegative n) (Q'.invSucc n)

theorem sourceTolerance_positive (n : Nat) : (0 : Q') < sourceTolerance n :=
  linearTolerance_pos _ _ (Q'.invSucc_pos n)

def outputPreimage {u : V} (R : RangeLimit hw0 hw1 u) (n : Nat) : (D).Cauchy :=
  preimageRepresentative hw0 hw1 n (R.preimage (R.modulus (sourceTolerance n)))

/-- Its T-image is close to the nth ACTUAL state quotient, not a surrogate. -/
theorem outputPreimage_close {u : V} (R : RangeLimit hw0 hw1 u) (n : Nat) :
    RCle (dist (T 1 (Class (outputPreimage hw0 hw1 R n))) (Q n u))
      (rat (Q'.invSucc n)) := by
  unfold outputPreimage
  rw [quotient_time_image]
  have hi := R.bound (sourceTolerance n) (sourceTolerance_positive n)
    (R.modulus (sourceTolerance n)) (Nat.le_refl _)
  have hq := stateQuotient_distance_bound hw0 hw1 n
    (T 1 (Class (R.preimage (R.modulus (sourceTolerance n))))) u
  have h := RCle_trans hq (RCscale_mono (quotientCap_nonnegative n) hi)
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    linearTolerance_budget (quotientCap n) (quotientCap_nonnegative n) (Q'.invSucc_pos n)))

/-- Construct the derivative's range witness: it is no longer a premise. -/
def outputRange {u v : V} (R : RangeLimit hw0 hw1 u) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n u) v) (rat e)) : RangeLimit hw0 hw1 v where
  preimage := outputPreimage hw0 hw1 R
  modulus := fun e => max (modulus (quarter e)) (quarter e).den
  bound := by
    intro e he n hn
    let delta := quarter e
    have hd : (0 : Q') < delta := quarter_positive he
    have hdelta : Q'.invSucc n ≤ delta :=
      Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le delta hd)
    have hfirst : RCle
        (dist (T 1 (Class (outputPreimage hw0 hw1 R n))) (Q n u)) (rat delta) :=
      RCle_trans (outputPreimage_close hw0 hw1 R n)
        (leEv_le_ofQ'_of_approx_le (fun _ => hdelta))
    have hsecond := bound delta hd n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have h := RCle_trans (completedDist_triangle hw0 hw1 _ (Q n u) v)
      (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
    rwa [four_quarters] at h

/-- The actual derivative limit on the witnessed input sector constructs
the original graph without a separate output-range assumption. -/
def graphOfDerivative {u v : V} (R : RangeLimit hw0 hw1 u) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n u) v) (rat e)) : GraphLimit hw0 hw1 u v :=
  graphOfQuotientLimit hw0 hw1 R (outputRange hw0 hw1 R modulus bound) modulus bound

theorem graphOfDerivative_representative_pin (U : (D).Cauchy) {v : V}
    (R : RangeLimit hw0 hw1 (Class U)) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) v) (rat e)) (n : Nat) :
    Class (inverseSumRepresentative hw0 hw1 n U) =
      (graphOfDerivative hw0 hw1 R modulus bound).source n :=
  graphOfEquation_representative_pin hw0 hw1 U R
    (outputRange hw0 hw1 R modulus bound)
    (derivative_equation_of_quotient_limit hw0 hw1 (Class U) v modulus bound) n

/-- Return the graph AND its original source representatives as data for
the reverse derivative compiler, not merely a proposition of existence. -/
def representedGraphOfDerivative (U : (D).Cauchy) {v : V}
    (R : RangeLimit hw0 hw1 (Class U)) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) v) (rat e)) :
    Σ' G : GraphLimit hw0 hw1 (Class U) v,
      Σ' preimages : Nat → (D).Cauchy,
        ∀ n, Class (preimages n) = G.source n :=
  ⟨graphOfDerivative hw0 hw1 R modulus bound,
    (fun n => inverseSumRepresentative hw0 hw1 n U),
    graphOfDerivative_representative_pin hw0 hw1 U R modulus bound⟩

/-- Reverse data for the represented graph criterion: the INPUT sector
witness and the actual quotient-limit modulus are both constructed. -/
def derivativeDataOfGraph {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (hpin : ∀ n, Class (preimages n) = G.source n) :
    (RangeLimit hw0 hw1 u) ×'
      (Σ' modulus : Q' → Nat,
        ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
          RCle (dist (Q n u) v) (rat e)) :=
  ⟨BF4WilsonAllNomeDerivativeGraphRange.inputRange hw0 hw1 G preimages hpin,
    BF4WilsonAllNomeDerivativeGraphQuotient.stateQuotientModulus hw0 hw1 G preimages,
    BF4WilsonAllNomeDerivativeGraphQuotient.stateQuotient_bound hw0 hw1 G preimages hpin⟩

/-- A root-sequence derivative on this sector yields the actual Taylor
estimate at EVERY sufficiently small supplied positive real time. -/
def derivativeRealTaylorCertificate (U V' : (D).Cauchy)
    (R : RangeLimit hw0 hw1 (Class U)) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) (Class V')) (rat e))
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (B (realRemainder hw0 hw1 t (Class U) (Class V'))
          (realRemainder hw0 hw1 t (Class U) (Class V')))
          (RCmul (RCmul (realValue (timeValue t)) (realValue (timeValue t)))
            (rat epsilon))) :=
  equationRealTaylorCertificate hw0 hw1 U V' R
    (outputRange hw0 hw1 R modulus bound)
    (derivative_equation_of_quotient_limit hw0 hw1 (Class U) (Class V') modulus bound)
    epsilon he

#print axioms sourceTolerance
#print axioms sourceTolerance_positive
#print axioms outputPreimage
#print axioms outputPreimage_close
#print axioms outputRange
#print axioms graphOfDerivative
#print axioms graphOfDerivative_representative_pin
#print axioms representedGraphOfDerivative
#print axioms derivativeDataOfGraph
#print axioms derivativeRealTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeOutputRange
