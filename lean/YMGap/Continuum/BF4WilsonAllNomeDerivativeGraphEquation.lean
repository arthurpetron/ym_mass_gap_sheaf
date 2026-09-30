/-
# Constructing the original derivative graph from its equation

For explicitly represented time-range limits u and v, Au=T(1)v suffices:
the finite inverse sums of u supply graph rows whose two errors are exactly
the defect-power tails. Both range witnesses are retained. The equation is
not claimed sufficient on the whole carrier, with its actual boundary kernel.

The resulting graph has literal Cauchy source representatives when u does,
so it feeds the existing positive-real-time Taylor certificate without choice.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
import YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphRange

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws (completedSub_self)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (completedSub_zero)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit defectModulus defect_small)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange (inverseSum)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
open YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh (sub_sub_exchange)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal (realRemainder)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem sub_error (x y : V) : dist (Sub x y) x = B y y := by
  calc
    dist (Sub x y) x = dist (Sub x y) (Sub x Z) := by rw [completedSub_zero]
    _ = dist Z y := by
      unfold completedDist
      rw [sub_sub_exchange,completedSub_self,completedSub_zero]
    _ = B y y := by rw [completedDist_symm,dist_zero_right]

/-- The converse data are constructed from every represented graph witness:
both coordinate range moduli, together with the exact original equation. -/
def equationDataOfGraph {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (hpin : ∀ n, Class (preimages n) = G.source n) :
    (RangeLimit hw0 hw1 u) ×' (RangeLimit hw0 hw1 v) ×' (A u = T 1 v) :=
  ⟨BF4WilsonAllNomeDerivativeGraphRange.inputRange hw0 hw1 G preimages hpin,
    BF4WilsonAllNomeDerivativeGraphRange.outputRange hw0 hw1 G preimages hpin,
    (BF4WilsonAllNomeDerivativeGraph.graph_time_pin hw0 hw1 G).symm⟩

/-- An explicit graph constructor, not an inverse operator or a claim of
whole-carrier density. Both coordinate tail witnesses are necessary here. -/
def graphOfEquation {u v : V} (Ru : RangeLimit hw0 hw1 u)
    (Rv : RangeLimit hw0 hw1 v) (h : A u = T 1 v) : GraphLimit hw0 hw1 u v where
  source := fun n => inverseSum hw0 hw1 n u
  modulus := fun e => max (defectModulus hw0 hw1 Ru e) (defectModulus hw0 hw1 Rv e)
  bound := by
    intro e he n hn
    constructor
    · rw [time_inverseSum_sub,sub_error]
      exact defect_small hw0 hw1 Ru e he n (Nat.le_trans (Nat.le_max_left _ _) hn)
    · rw [derivativeAction_inverseSum_of_equation hw0 hw1 n u v h,sub_error]
      exact defect_small hw0 hw1 Rv e he n (Nat.le_trans (Nat.le_max_right _ _) hn)

/-- The source stream is represented by finite operations on the supplied
original input representative, with no selection of quotient preimages. -/
theorem graphOfEquation_representative_pin (U : (D).Cauchy) {v : V}
    (Ru : RangeLimit hw0 hw1 (Class U)) (Rv : RangeLimit hw0 hw1 v)
    (h : A (Class U) = T 1 v) (n : Nat) :
    Class (inverseSumRepresentative hw0 hw1 n U) =
      (graphOfEquation hw0 hw1 Ru Rv h).source n :=
  inverseSumRepresentative_pin hw0 hw1 n U

/-- A supplied actual dyadic quotient limit yields the graph on the two
explicitly witnessed coordinate sectors. No maximal ambient-domain claim. -/
def graphOfQuotientLimit {u v : V} (Ru : RangeLimit hw0 hw1 u)
    (Rv : RangeLimit hw0 hw1 v) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ k, modulus e ≤ k →
      RCle (dist (stateQuotient hw0 hw1 k u) v) (rat e)) : GraphLimit hw0 hw1 u v :=
  graphOfEquation hw0 hw1 Ru Rv
    (derivative_equation_of_quotient_limit hw0 hw1 u v modulus bound)

/-- The equation now feeds an actual all-small-positive-real-time Taylor
certificate, with its computed radius, on the SAME original carrier. -/
def equationRealTaylorCertificate (U V' : (D).Cauchy)
    (Ru : RangeLimit hw0 hw1 (Class U)) (Rv : RangeLimit hw0 hw1 (Class V'))
    (h : A (Class U) = T 1 (Class V')) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (B (realRemainder hw0 hw1 t (Class U) (Class V'))
          (realRemainder hw0 hw1 t (Class U) (Class V')))
          (RCmul (RCmul (realValue (timeValue t)) (realValue (timeValue t)))
            (rat epsilon))) :=
  BF4WilsonAllNomeDerivativeGraphReal.realTaylorCertificate hw0 hw1
    (graphOfEquation hw0 hw1 Ru Rv h) (fun n => inverseSumRepresentative hw0 hw1 n U)
    (graphOfEquation_representative_pin hw0 hw1 U Ru Rv h) epsilon he

#print axioms sub_error
#print axioms equationDataOfGraph
#print axioms graphOfEquation
#print axioms graphOfEquation_representative_pin
#print axioms graphOfQuotientLimit
#print axioms equationRealTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
