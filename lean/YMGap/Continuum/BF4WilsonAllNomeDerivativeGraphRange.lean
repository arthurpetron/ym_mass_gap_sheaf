/-
# Both coordinates of a represented original derivative graph lie in the
# witnessed original positive-time range closure

The graph source stream is accompanied by supplied original Cauchy
representatives. For the output, each row uses a computed quotient depth
and the quotient's explicit original T(1)-preimage. No representatives or
inverse time images are selected from existential propositions.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The graph's first coordinate already has the supplied original time
preimages; its graph modulus is a range-closure modulus verbatim. -/
def inputRange {input output : V} (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n) :
    RangeLimit hw0 hw1 input where
  preimage := preimages
  modulus := G.modulus
  bound := by
    intro e he n hn
    rw [hpin n]
    exact (G.bound e he n hn).1

/-- One finite quotient depth is computed from each supplied source row.
The resulting original preimage may have an arbitrarily large norm. -/
def outputPreimage {input output : V} (_G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy) (n : Nat) : (D).Cauchy :=
  preimageRepresentative hw0 hw1
    (derivativeRate hw0 hw1 (preimages n) (Q'.invSucc n)) (preimages n)

theorem outputPreimage_time_pin {input output : V}
    (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy) (n : Nat) :
    T 1 (Class (outputPreimage hw0 hw1 G preimages n)) =
      differenceQuotient hw0 hw1
        (derivativeRate hw0 hw1 (preimages n) (Q'.invSucc n))
        (Class (preimages n)) :=
  quotient_time_image hw0 hw1 _ (preimages n)

/-- The second coordinate has explicit original T(1)-preimages too. A
single synchronized index makes both the graph error and quotient error
at most one quarter of the requested squared-distance tolerance. -/
def outputRange {input output : V} (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n) :
    RangeLimit hw0 hw1 output where
  preimage := outputPreimage hw0 hw1 G preimages
  modulus := fun e => max (G.modulus (quarter e)) (quarter e).den
  bound := by
    intro e he n hn
    let delta := quarter e
    have hd : (0 : Q') < delta := quarter_positive he
    have hg := (G.bound delta hd n
      (Nat.le_trans (Nat.le_max_left _ _) hn)).2
    have hq : RCle
        (dist (T 1 (Class (outputPreimage hw0 hw1 G preimages n)))
          (A (G.source n))) (rat (Q'.invSucc n)) := by
      rw [outputPreimage_time_pin,← hpin n,derivativeAction_pin]
      exact derivative_bound hw0 hw1 (preimages n) (Q'.invSucc n)
        (Q'.invSucc_pos n) _ (Nat.le_refl _)
    have hdelta : Q'.invSucc n ≤ delta :=
      Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le delta hd)
    have hfirst : RCle
        (dist (T 1 (Class (outputPreimage hw0 hw1 G preimages n)))
          (A (G.source n))) (rat delta) :=
      RCle_trans hq (leEv_le_ofQ'_of_approx_le (fun _ => hdelta))
    have h := RCle_trans
      (completedDist_triangle hw0 hw1 _ (A (G.source n)) output)
      (RCadd_le_add (RCadd_le_add hfirst hfirst)
        (RCadd_le_add hg hg))
    rwa [four_quarters] at h

#print axioms inputRange
#print axioms outputPreimage
#print axioms outputPreimage_time_pin
#print axioms outputRange

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphRange
