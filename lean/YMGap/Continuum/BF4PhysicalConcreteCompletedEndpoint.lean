/-
# Concrete completed physical BF4 endpoint

The finite physical BF4 route already constructs one completed GNS carrier at
each matched scale.  This module packages that carrier, its macro transfer,
normalized vacuum, vacuum-complement preservation, and same-object coefficient
into one explicit certificate.  The certificate is inhabited directly from
the existing constructions; it does not contain the cross-model map to the
strong OS endpoint.  Thus the remaining comparison obligation is kept
separate rather than being hidden in an abstract endpoint record.

This is finite physical SU(2) matched-stage data.  It is not a thermodynamic
limit, a continuum QFT, or the Clay mass-gap theorem.
-/

import YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator

namespace YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. The concrete carrier and its named operations -/

abbrev Carrier (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Type :=
  CentralPhysicalGNSCompletion w hw K half

def transfer (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    Carrier w hw K half → Carrier w hw K half :=
  centralPhysicalCompletedMarkovTransfer w hw K half

def vacuum (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    Carrier w hw K half :=
  centralPhysicalCompletedVacuum w hw K half

def vacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (vector : Carrier w hw K half) : Prop :=
  CentralPhysicalCompletedVacuumOrthogonal w hw K half vector

def observable
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (value : EdgeLabelling → Q') : Carrier w hw K half :=
  centralPhysicalCompletedObservable w hw K half value

/-! ## 2. The concrete endpoint certificate -/

/-- All finite physical endpoint facts needed by a later comparison map.

Every operation in this record is fixed by the definitions above.  The
fields are laws of the actual completed physical carrier, not existential
placeholders for a continuum construction. -/
structure ConcreteEndpoint
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Type 1 where
  vacuum_norm :
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (vacuum w hw K half) (vacuum w hw K half) =
      Quotient.mk CReal.crealSetoid CReal.cone
  transfer_vacuum_fixed :
    transfer w hw K half (vacuum w hw K half) = vacuum w hw K half
  transfer_selfAdjoint : ∀ x y,
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (transfer w hw K half x) y =
      (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        x (transfer w hw K half y)
  transfer_positive : ∀ x,
    CReal.RCnonneg
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (transfer w hw K half x) x)
  transfer_contraction : ∀ x,
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (transfer w hw K half x) (transfer w hw K half x))
      ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl x x)
  vacuum_orthogonal_preserved : ∀ x,
    vacuumOrthogonal w hw K half x →
      vacuumOrthogonal w hw K half (transfer w hw K half x)
  dense_inner : ∀ left right,
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (observable w hw K half left) (observable w hw K half right) =
      physicalConstantRC
        (centralPhysicalWeightedInner w hw K half left right)
  dense_mean_zero_vacuum_orthogonal : ∀ value,
    CentralPhysicalMeanZero w hw K half value →
      vacuumOrthogonal w hw K half (observable w hw K half value)
  dense_same_object : ∀ value,
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (observable w hw K half value)
        (transfer w hw K half (observable w hw K half value)) =
      physicalConstantRC
        (centralPhysicalJointQuadratic w hw K half value)

/-! ## 3. Direct construction from the existing physical endpoint -/

/-- The certificate is inhabited at every finite physical BF4 stage. -/
def ConcreteEndpoint.ofExisting
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    ConcreteEndpoint w hw K half where
  vacuum_norm :=
    centralPhysicalCompletedVacuum_inner_self_eq_one w hw K half
  transfer_vacuum_fixed :=
    centralPhysicalCompletedMarkovTransfer_vacuum_fixed w hw K half
  transfer_selfAdjoint := by
    intro x y
    exact centralPhysicalCompletedMarkovTransfer_selfAdjoint w hw K half x y
  transfer_positive := by
    intro x
    exact centralPhysicalCompletedMarkovTransfer_positive w hw K half x
  transfer_contraction := by
    intro x
    exact centralPhysicalCompletedMarkovTransfer_contraction w hw K half x
  vacuum_orthogonal_preserved := by
    intro x hx
    exact centralPhysicalCompletedVacuumOrthogonal_preserved w hw K half hx
  dense_inner := by
    intro left right
    exact centralPhysicalCompletedObservable_inner w hw K half left right
  dense_mean_zero_vacuum_orthogonal := by
    intro value hmean
    exact centralPhysicalCompletedObservable_vacuumOrthogonal
      w hw K half value hmean
  dense_same_object := by
    intro value
    exact centralPhysicalCompletedObservable_macroCoefficient
      w hw K half value

end YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint

#print axioms
  YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint.ConcreteEndpoint
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint.ConcreteEndpoint.ofExisting
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint.ConcreteEndpoint.dense_same_object
