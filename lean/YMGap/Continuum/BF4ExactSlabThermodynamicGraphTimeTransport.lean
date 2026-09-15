/-
# The ORIGINAL action preserves the actual derivative graph

The existing positive-real-time action commutes with every actual dyadic
quotient. Its contraction preserves the supplied derivative rate, so the
proved exact-domain theorem puts (A_t u,A_t v) in the SAME graph J u=T2 v.
The original output representatives and rate are retained as data.

The old real-scalar action also commutes with time. Hence the Taylor
remainder is transported exactly, and contraction preserves the ORIGINAL
Taylor radius uniformly along the entire positive-time orbit. The same
centered form gap holds there. No alternative generator or carrier is used.

Fixed SU(2), nome 1/1024, original REAL completion, fixed spacing and
T2-time units. This is not a physical Hamiltonian/spectral-interface
inhabitant, spacing calibration, continuum QFT or all-group Clay theorem.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes (generator)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action_embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay (defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction (outputRepresentative outputRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation (GraphPoint)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph
open YMGap.Continuum.BF4ExactSlabThermodynamicGraphRealDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeDomain

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem time_generator (t : PositiveTimeValue) (depth : Nat) (u : Completion) :
    realTimeAction t (generator depth u)=generator depth (realTimeAction t u) := by
  have h := realTimeAction_commutes t (timeValue (dyadicTime ⟨depth,1⟩ (by decide : 0<(1 : Nat)))) u
  simp only [realTimeAction_dyadic,action_embed] at h
  exact h

theorem quotient_time (t : PositiveTimeValue) (depth : Nat) (u : Completion) :
    quotient depth (realTimeAction t u)=realTimeAction t (quotient depth u) := by
  unfold quotient defect
  rw [realTimeAction_smul,realTimeAction_sub,time_generator]

/-- Translation does not enlarge the actual derivative's convergence modulus. -/
theorem transported_quotient_bound (t : PositiveTimeValue) (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : rate U V epsilon≤n) :
    RCle (completedDist (quotient n (realTimeAction t (point U))) (realTimeAction t (point V))) (rat epsilon) := by
  rw [quotient_time]
  exact RCle_trans (realTimeAction_distance_contraction t _ _) (quotient_bound U V h epsilon he n hn)

theorem represented_graph_invariant (D : PositiveTime) (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V)) :
    derivativeAction (realTimeAction (timeValue D) (point U))=
      twoStepTransfer (realTimeAction (timeValue D) (point V)) :=
  graph_of_quotient_bound (outputRepresentative D U) (realTimeAction (timeValue D) (point V))
    (rate U V) (transported_quotient_bound (timeValue D) U V h)

theorem graph_invariant (t : PositiveTimeValue) (u v : Completion)
    (h : derivativeAction u=twoStepTransfer v) :
    derivativeAction (realTimeAction t u)=twoStepTransfer (realTimeAction t v) := by
  revert h
  refine Quotient.inductionOn t ?_
  intro D
  refine Quotient.inductionOn₂ u v ?_
  exact represented_graph_invariant D

/-- Actual state AND actual image are translated by the same original action. -/
def GraphPoint.time (p : GraphPoint) (t : PositiveTimeValue) : GraphPoint where
  state := realTimeAction t p.state
  image := realTimeAction t p.image
  equation := graph_invariant t p.state p.image p.equation

theorem GraphPoint.time_state (p : GraphPoint) (t : PositiveTimeValue) :
    (GraphPoint.time p t).state=realTimeAction t p.state := rfl

theorem GraphPoint.time_image (p : GraphPoint) (t : PositiveTimeValue) :
    (GraphPoint.time p t).image=realTimeAction t p.image := rfl

theorem GraphPoint.time_addTime (p : GraphPoint) (s t : PositiveTimeValue) :
    GraphPoint.time p (addTime s t)=GraphPoint.time (GraphPoint.time p t) s := by
  cases p
  simp only [GraphPoint.time,realTimeAction_addTime]

def graphTransportData (D : PositiveTime) (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V)) :
    Σ' U' : seminorm.Cauchy, Σ' V' : seminorm.Cauchy,
      ((point U')=realTimeAction (timeValue D) (point U)) ×'
      ((point V')=realTimeAction (timeValue D) (point V)) ×'
      (derivativeAction (point U')=twoStepTransfer (point V')) ×'
      (∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate U V epsilon≤n →
        RCle (completedDist (quotient n (point U')) (point V')) (rat epsilon)) :=
  ⟨outputRepresentative D U,outputRepresentative D V,rfl,rfl,
    represented_graph_invariant D U V h,transported_quotient_bound (timeValue D) U V h⟩

theorem time_realSmul (t : PositiveTimeValue) (s : CReal) (cs : QCauchy s.approx) (u : Completion) :
    realTimeAction t (completedRealSmul s cs u)=completedRealSmul s cs (realTimeAction t u) := by
  apply completed_eq_of_pairings
  intro z
  rw [realTimeAction_symmetric,completedInner_realSmul_left,completedInner_realSmul_left,realTimeAction_symmetric]

theorem remainder_time (t : PositiveTimeValue) (D : PositiveTime) (u v : Completion) :
    remainder D (realTimeAction t u) (realTimeAction t v)=realTimeAction t (remainder D u v) := by
  unfold remainder
  rw [realTimeAction_sub,realTimeAction_sub,time_realSmul,realTimeAction_commutes t (timeValue D)]

/-- The original radius is valid uniformly at EVERY positive base time. -/
theorem transported_taylor_bound (t : PositiveTimeValue) (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) (D : PositiveTime)
    (ht : RCle (realValue (timeValue D)) (rat (radius U V epsilon))) :
    RCle (B (remainder D (realTimeAction t (point U)) (realTimeAction t (point V)))
      (remainder D (realTimeAction t (point U)) (realTimeAction t (point V))))
      (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon)) := by
  rw [remainder_time]
  exact RCle_trans (realTimeAction_contraction t _) (real_taylor_bound U V h epsilon he D ht)

def orbitTaylorCertificate (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' r : Q', ((0 : Q')<r) ×'
      (∀ t : PositiveTimeValue,∀ D : PositiveTime,RCle (realValue (timeValue D)) (rat r) →
        RCle (B (remainder D (realTimeAction t (point U)) (realTimeAction t (point V)))
          (remainder D (realTimeAction t (point U)) (realTimeAction t (point V))))
          (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon))) :=
  ⟨radius U V epsilon,radius_positive U V epsilon,fun t D ht => transported_taylor_bound t U V h epsilon he D ht⟩

theorem GraphPoint.orbit_form_gap (p : GraphPoint) (t : PositiveTimeValue)
    (h : B p.state completedUnit=RCzero) :
    RCle (RCscale HalfPow.half (B (realTimeAction t p.state) (realTimeAction t p.state)))
      (B (realTimeAction t p.image) (realTimeAction t p.state)) :=
  BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.form_gap
    (GraphPoint.time p t) (realTimeAction_complement t p.state h)

end YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.time_generator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.quotient_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.transported_quotient_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.represented_graph_invariant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.graph_invariant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.GraphPoint.time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.GraphPoint.time_state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.GraphPoint.time_image
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.GraphPoint.time_addTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.graphTransportData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.time_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.remainder_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.transported_taylor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.orbitTaylorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeTransport.GraphPoint.orbit_form_gap
