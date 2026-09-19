/-
# Concrete finite physical SU(2) completed-carrier realization

The physical BF4 Markov/GNS module already constructs a finite carrier, its
completed transfer, the normalized stationary vacuum, and the vacuum
orthogonal complement.  This file packages those objects into one explicit
realization record and defines same-object correlations from the record's own
transfer.  The constructor is unconditional at each finite `(w,K,half)`;
strict contraction remains a separately supplied analytic certificate.

No thermodynamic or continuum limit, QFT reconstruction, all-group result, or
Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCompletedCarrierRealization

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion

abbrev Carrier (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Type :=
  CentralPhysicalGNSCompletion w hw K half

abbrev CarrierData (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : GNSData :=
  (centralPhysicalSmulGNS w hw K half).toGNSData

/-! ## The forward carrier/transfer/vacuum package -/

/-- One finite physical SU(2) carrier realization.  Every field is an actual
finite BF4/GNS object; no strict gap is hidden in this package. -/
structure ConcretePhysicalSU2CompletedCarrier
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Type 1 where
  carrier : Type
  transfer : carrier → carrier
  vacuum : carrier

/-! ## The concrete constructor -/

/-- The literal physical BF4 Markov transfer and stationary vacuum inhabit the
carrier package at every finite cutoff and half extent. -/
def concretePhysicalSU2CompletedCarrier
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    ConcretePhysicalSU2CompletedCarrier w hw K half where
  carrier := Carrier w hw K half
  transfer := centralPhysicalCompletedMarkovTransfer w hw K half
  vacuum := centralPhysicalCompletedVacuum w hw K half

theorem concrete_vacuum_inner_self_eq_one
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (CarrierData w hw K half).cinnerCompl
        (centralPhysicalCompletedVacuum w hw K half)
        (centralPhysicalCompletedVacuum w hw K half) =
      Quotient.mk CReal.crealSetoid CReal.cone :=
  centralPhysicalCompletedVacuum_inner_self_eq_one w hw K half

theorem concrete_transfer_selfAdjoint
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (x y : Carrier w hw K half) :
    (CarrierData w hw K half).cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half x) y =
      (CarrierData w hw K half).cinnerCompl x
        (centralPhysicalCompletedMarkovTransfer w hw K half y) :=
  centralPhysicalCompletedMarkovTransfer_selfAdjoint w hw K half x y

theorem concrete_transfer_positive
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (x : Carrier w hw K half) :
    CReal.RCnonneg
      ((CarrierData w hw K half).cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half x) x) :=
  centralPhysicalCompletedMarkovTransfer_positive w hw K half x

theorem concrete_transfer_contraction
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (x : Carrier w hw K half) :
    CReal.RCle
      ((CarrierData w hw K half).cinnerCompl
        (centralPhysicalCompletedMarkovTransfer w hw K half x)
        (centralPhysicalCompletedMarkovTransfer w hw K half x))
      ((CarrierData w hw K half).cinnerCompl x x) :=
  centralPhysicalCompletedMarkovTransfer_contraction w hw K half x

theorem concrete_vacuum_fixed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    centralPhysicalCompletedMarkovTransfer w hw K half
        (centralPhysicalCompletedVacuum w hw K half) =
      centralPhysicalCompletedVacuum w hw K half :=
  centralPhysicalCompletedMarkovTransfer_vacuum_fixed w hw K half

theorem concrete_vacuum_orthogonal_preserved
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {x : Carrier w hw K half}
    (hx : (CarrierData w hw K half).cinnerCompl x
      (centralPhysicalCompletedVacuum w hw K half) = CReal.RCzero) :
    (CarrierData w hw K half).cinnerCompl
      (centralPhysicalCompletedMarkovTransfer w hw K half x)
      (centralPhysicalCompletedVacuum w hw K half) = CReal.RCzero := by
  exact centralPhysicalCompletedVacuumOrthogonal_preserved w hw K half hx

/-! ## Same-object correlation on the concrete package -/

def concreteSameObjectCorrelation
    (w : Q') (hw : (0 : Q') ≤ w) (K half n : Nat)
    (x : Carrier w hw K half) : CReal.RC :=
  (CarrierData w hw K half).cinnerCompl
    (centralPhysicalCompletedMarkovPower w hw K half n x) x

theorem concreteSameObjectCorrelation_zero
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (x : Carrier w hw K half) :
    concreteSameObjectCorrelation w hw K half 0 x =
      (CarrierData w hw K half).cinnerCompl x x := by
  rfl

/-- The concrete correlator is the same-object coefficient of the physical
transfer recorded by the package, not a second abstract observable. -/
theorem concreteSameObjectCorrelation_eq_physical
    (w : Q') (hw : (0 : Q') ≤ w) (K half n : Nat)
    (x : Carrier w hw K half) :
    concreteSameObjectCorrelation w hw K half n x =
      (CarrierData w hw K half).cinnerCompl
        (centralPhysicalCompletedMarkovPower w hw K half n x) x :=
  rfl

/-! ## Conditional decay consequence -/

/-- Any separately supplied completed form-gap certificate controls the
packaged same-object correlation square on the same physical carrier. -/
theorem concrete_sameObjectCorrelationSq_decay_of_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (n : Nat) (x : Carrier w hw K half)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half x) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectCorrelation w hw K half n x)
        (concreteSameObjectCorrelation w hw K half n x))
      (CReal.RCmul
        (CReal.RCscale ((rate * rate) ^ n)
          ((CarrierData w hw K half).cinnerCompl x x))
        ((CarrierData w hw K half).cinnerCompl x x)) := by
  exact centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap
    hw K half gap n x x horthogonal

end YMGap.Continuum.BF4PhysicalCompletedCarrierRealization

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concretePhysicalSU2CompletedCarrier
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_vacuum_inner_self_eq_one
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_transfer_selfAdjoint
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_transfer_positive
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_transfer_contraction
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_vacuum_fixed
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_vacuum_orthogonal_preserved
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concreteSameObjectCorrelation_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concreteSameObjectCorrelation_eq_physical
#print axioms
  YMGap.Continuum.BF4PhysicalCompletedCarrierRealization.concrete_sameObjectCorrelationSq_decay_of_form_gap
