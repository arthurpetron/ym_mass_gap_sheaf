/-
# Constructive real scaling of the represented original derivative graph

The bounded derivative-on-preimages A is real-linear by its existing
symmetry and the original real-bilinear pairing. Real-linear range witnesses
and the exact equation Au=T(1)v then construct the scaled derivative graph.
For every represented graph, the result also returns original source
representatives via the proved finite inverse-sum construction.

This is actual real scaling of the witnessed graph, not an assumed domain
law, a scalar extension to another carrier, or physical Hamiltonian
identification. The existing quotient Domain is not redefined here.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphRealLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeLinear (realSmul)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
  (graphOfEquation equationDataOfGraph)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
  (inverseSumRepresentative inverseSumRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRange (inverseSum)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "RS" => completedRealSmul hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Original symmetry gives real homogeneity without a new scalar limit
estimate or identification with the regularized logarithm. -/
theorem derivativeAction_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    A (RS s cs x) = RS s cs (A x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [derivativeAction_symmetric,completedInner_realSmul_left,
    completedInner_realSmul_left,derivativeAction_symmetric]

/-- Real scaling preserves the exact original two-coordinate equation. -/
theorem realScale_equation (s : CReal) (cs : QCauchy s.approx)
    {u v : V} (h : A u = T 1 v) : A (RS s cs u) = T 1 (RS s cs v) := by
  rw [derivativeAction_realSmul,completedTime_realSmul,h]

/-- Real homogeneity of the graph on its explicitly witnessed sector. The
preimage stream and convergence modulus are constructed by the equation criterion. -/
def realScale (s : CReal) (cs : QCauchy s.approx)
    {u v : V} (Ru : RangeLimit hw0 hw1 u) (Rv : RangeLimit hw0 hw1 v)
    (h : A u = T 1 v) : GraphLimit hw0 hw1 (RS s cs u) (RS s cs v) :=
  graphOfEquation hw0 hw1 (realSmul hw0 hw1 s cs Ru) (realSmul hw0 hw1 s cs Rv)
    (realScale_equation hw0 hw1 s cs h)

/-- The scaled source representatives are finite original inverse sums of
the representative computed from the scaled input-range witness. -/
theorem realScale_source_pin (s : CReal) (cs : QCauchy s.approx)
    {u v : V} (Ru : RangeLimit hw0 hw1 u) (Rv : RangeLimit hw0 hw1 v)
    (h : A u = T 1 v) (n : Nat) :
    Class (inverseSumRepresentative hw0 hw1 n
      (representative hw0 hw1 (realSmul hw0 hw1 s cs Ru))) =
      (realScale hw0 hw1 s cs Ru Rv h).source n := by
  change Class (inverseSumRepresentative hw0 hw1 n
    (representative hw0 hw1 (realSmul hw0 hw1 s cs Ru))) =
      inverseSum hw0 hw1 n (RS s cs u)
  rw [inverseSumRepresentative_pin,representative_pin]

/-- Every original represented graph is closed under supplied-modulus real
scaling, with a new represented graph returned rather than merely asserted. -/
def representedRealScale (s : CReal) (cs : QCauchy s.approx)
    {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (hpin : ∀ n, Class (preimages n) = G.source n) :
    Σ' H : GraphLimit hw0 hw1 (RS s cs u) (RS s cs v),
      Σ' sources : Nat → (D).Cauchy, ∀ n, Class (sources n) = H.source n := by
  let data := equationDataOfGraph hw0 hw1 G preimages hpin
  exact ⟨realScale hw0 hw1 s cs data.1 data.2.1 data.2.2,
    (fun n => inverseSumRepresentative hw0 hw1 n
      (representative hw0 hw1 (realSmul hw0 hw1 s cs data.1))),
    realScale_source_pin hw0 hw1 s cs data.1 data.2.1 data.2.2⟩

#print axioms derivativeAction_realSmul
#print axioms realScale_equation
#print axioms realScale
#print axioms realScale_source_pin
#print axioms representedRealScale

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphRealLinear
