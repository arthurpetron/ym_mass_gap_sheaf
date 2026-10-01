/-
# Original Euclidean time preserves the physical derivative graph

Both range witnesses of an original sector domain point are transported by
the already constructed positive-time action. The actual derivative/time
commutation proves its graph equation. Quotient descent then transports every
real physical-domain class, and hence the complex physical domain.

The full intrinsic adjoint graph is preserved on the SAME carrier. No new
analytic assumption, logarithm identity, spacing calibration or continuum
Hamiltonian is supplied.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativePositiveTimeCommutation
import YMGap.Continuum.BF4WilsonAllNomeSectorEqualTimeBoundary
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivativeTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeDerivativePositiveTimeCommutation
  (derivativeAction_positiveAction_commutes)
open YMGap.Continuum.BF4WilsonAllNomeSectorEqualTimeBoundary
  (positiveAction_time_one_commutes)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint domainSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (sectorActionRep bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (input_mk output_mk bondValue_input_mk bondValue_output_mk)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output AdjointPair adjointDomain adjointDomain_input
    adjointDomain_output domain_adjoint)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "P" => DomainPoint hw0 hw1 (width := width)
local notation "RD" => BF4WilsonAllNomeBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "H" => BF4WilsonAllNomeComplexBondOSCompletion.ComplexBondCompletion
  hw0 hw1 (width := width)
local notation "RI" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "RO" => BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
local notation "RS" => BF4WilsonAllNomeBondOSRealTime.action hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
local notation "Class" => Quotient.mk (domainSetoid hw0 hw1 (width := width))

/-- Both supplied original range witnesses survive before quotienting.
The graph equation is proved by ACTUAL derivative/time commutation. -/
def timePoint (s : PositiveTime) (p : P) : P where
  input := sectorActionRep hw0 hw1 s p.input
  output := sectorActionRep hw0 hw1 s p.output
  equation := by
    change derivativeAction hw0 hw1 (positiveAction hw0 hw1 s p.input.val) =
      completedTime hw0 hw1 1 (positiveAction hw0 hw1 s p.output.val)
    rw [derivativeAction_positiveAction_commutes,p.equation,
      positiveAction_time_one_commutes]

/-- Equality of original inputs is respected; no representative is chosen. -/
def realTimeDomain (s : PositiveTime) (d : RD) : RD :=
  Quotient.lift (fun p => Class (timePoint hw0 hw1 s p))
    (fun _ _ h => Quotient.sound (congrArg (positiveAction hw0 hw1 s) h)) d

theorem realTimeDomain_input (s : PositiveTime) (d : RD) :
    RI (realTimeDomain hw0 hw1 s d) = RS (timeValue s) (RI d) := by
  refine Quotient.inductionOn d ?_
  intro p
  apply bondValue_injective hw0 hw1
  change bondValue hw0 hw1 (RI (Class (timePoint hw0 hw1 s p))) =
    bondValue hw0 hw1 (RS (timeValue s) (RI (Class p)))
  rw [bondValue_input_mk,BF4WilsonAllNomeBondOSRealTime.action_value,
    bondValue_input_mk,realTimeAction_pin]
  rfl

theorem realTimeDomain_output (s : PositiveTime) (d : RD) :
    RO (realTimeDomain hw0 hw1 s d) = RS (timeValue s) (RO d) := by
  refine Quotient.inductionOn d ?_
  intro p
  apply bondValue_injective hw0 hw1
  change bondValue hw0 hw1 (RO (Class (timePoint hw0 hw1 s p))) =
    bondValue hw0 hw1 (RS (timeValue s) (RO (Class p)))
  rw [bondValue_output_mk,BF4WilsonAllNomeBondOSRealTime.action_value,
    bondValue_output_mk,realTimeAction_pin]
  rfl

/-- Time transport on every actual complex physical-domain class. -/
def timeDomain (s : PositiveTime) (d : D) : D :=
  (realTimeDomain hw0 hw1 s d.1,realTimeDomain hw0 hw1 s d.2)

theorem timeDomain_input (s : PositiveTime) (d : D) :
    input hw0 hw1 (timeDomain hw0 hw1 s d) =
      S (timeValue s) (input hw0 hw1 d) :=
  Prod.ext (realTimeDomain_input hw0 hw1 s d.1)
    (realTimeDomain_input hw0 hw1 s d.2)

theorem timeDomain_output (s : PositiveTime) (d : D) :
    output hw0 hw1 (timeDomain hw0 hw1 s d) =
      S (timeValue s) (output hw0 hw1 d) :=
  Prod.ext (realTimeDomain_output hw0 hw1 s d.1)
    (realTimeDomain_output hw0 hw1 s d.2)

/-- EVERY intrinsic physical adjoint pair is transported into the same
graph, via its already constructed actual domain class. -/
theorem timeAction_adjoint_pair (s : PositiveTime) (u v : H)
    (h : AdjointPair hw0 hw1 u v) :
    AdjointPair hw0 hw1 (S (timeValue s) u) (S (timeValue s) v) := by
  have hpair := domain_adjoint hw0 hw1
    (timeDomain hw0 hw1 s (adjointDomain hw0 hw1 u v))
  rw [timeDomain_input,timeDomain_output,
    adjointDomain_input hw0 hw1 u v h,adjointDomain_output hw0 hw1 u v h] at hpair
  exact hpair

#print axioms timePoint
#print axioms realTimeDomain
#print axioms realTimeDomain_input
#print axioms realTimeDomain_output
#print axioms timeDomain
#print axioms timeDomain_input
#print axioms timeDomain_output
#print axioms timeAction_adjoint_pair

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivativeTime
