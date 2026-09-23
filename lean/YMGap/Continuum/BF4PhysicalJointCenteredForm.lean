/-
# Exact finite centering identity on the reflected physical joint form

The reflected-joint form is the one-step form `B(a,Pb)` on the same finite
carrier.  This module supplies the missing unit witness for its stationary
vacuum and instantiates the generic GNS centering identity.  It is an exact
finite rational statement; it does not construct arbitrary-vector density or
any thermodynamic, continuum, or Clay conclusion.
-/

import YMGap.Continuum.BF4PhysicalJointCauchyMean

namespace YMGap.Continuum.BF4PhysicalJointCenteredForm

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointCauchyMean
open YMGap.Continuum.BF4PhysicalJointCenteredKernel
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- The reflected-joint form has unit norm on the stationary vacuum. -/
theorem physicalJoint_vacuum_unit
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    ((physicalJointSmulGNS w hw K half).toGNSData.B
      centralPhysicalVacuumCarrier centralPhysicalVacuumCarrier) ≈ 1 := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  have hfixed : D.rad
      (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
      centralPhysicalVacuumCarrier :=
    centralPhysicalVacuumCarrier_rad_fixed w hw K half
  have hform : D.B
      (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
      centralPhysicalVacuumCarrier ≈
      D.B centralPhysicalVacuumCarrier centralPhysicalVacuumCarrier :=
    D.B_welldef hfixed (D.rad_refl centralPhysicalVacuumCarrier)
  have hbase : D.B centralPhysicalVacuumCarrier centralPhysicalVacuumCarrier ≈ 1 := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalSmulGNS_B_eq w hw K half
          centralPhysicalVacuumCarrier centralPhysicalVacuumCarrier))
      (centralPhysicalWeightedInner_vacuum_one w hw K half)
  change D.B
    centralPhysicalVacuumCarrier
      (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier) ≈ 1
  exact Q'.eqv_trans _ _ _
    (D.B_symm _ _)
    (Q'.eqv_trans _ _ _ hform hbase)

/-- The joint vacuum pairing of a finite observable is the same stationary
mean used by the central physical carrier. -/
theorem physicalJoint_vacuum_pairing_eq_stationaryMean
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    ((physicalJointSmulGNS w hw K half).toGNSData.B
      observable centralPhysicalVacuumCarrier) ≈
      centralPhysicalStationaryMean w hw K half observable := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  have hfixed : D.rad
      (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier)
      centralPhysicalVacuumCarrier :=
    centralPhysicalVacuumCarrier_rad_fixed w hw K half
  have hform : D.B observable
      (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier) ≈
      D.B observable centralPhysicalVacuumCarrier :=
    D.B_welldef (D.rad_refl observable) hfixed
  have hmean : D.B observable centralPhysicalVacuumCarrier ≈
      centralPhysicalStationaryMean w hw K half observable := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (centralPhysicalSmulGNS_B_eq w hw K half observable
          centralPhysicalVacuumCarrier))
      (centralPhysicalWeightedInner_vacuum_right w hw K half observable)
  change D.B observable
    (centralPhysicalMarkovApply w hw K half centralPhysicalVacuumCarrier) ≈ _
  exact Q'.eqv_trans _ _ _ hform hmean

/-- The literal finite centered observable is the GNS subtraction using the
stationary mean, and hence also using the joint-form vacuum pairing. -/
theorem physicalJointCenteredObservable_veq_sub_smul
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    let D := (physicalJointSmulGNS w hw K half).toGNSData
    let mean := D.B observable centralPhysicalVacuumCarrier
    D.veq
      (physicalJointCenteredObservable w hw K half observable)
      (D.sub observable (D.smul mean centralPhysicalVacuumCarrier)) := by
  dsimp only
  let D := (physicalJointSmulGNS w hw K half).toGNSData
  let jointMean := D.B observable centralPhysicalVacuumCarrier
  let stationaryMean := centralPhysicalStationaryMean w hw K half observable
  have hcentral : D.veq
      (physicalJointCenteredObservable w hw K half observable)
      (D.sub observable (D.smul stationaryMean centralPhysicalVacuumCarrier)) := by
    exact centralPhysicalCenteredObservable_veq_sub_smul
      w hw K half observable
  have hmean : jointMean ≈ stationaryMean :=
    physicalJoint_vacuum_pairing_eq_stationaryMean w hw K half observable
  have hscaled : D.veq
      (D.smul stationaryMean centralPhysicalVacuumCarrier)
      (D.smul jointMean centralPhysicalVacuumCarrier) := by
    intro state
    exact Q'.mul_eqv_congr_right stationaryMean jointMean
      (centralPhysicalVacuumCarrier state) (Q'.eqv_symm hmean)
  have hsub : D.veq
      (D.sub observable (D.smul stationaryMean centralPhysicalVacuumCarrier))
      (D.sub observable (D.smul jointMean centralPhysicalVacuumCarrier)) := by
    exact D.add_congr (D.veq_refl observable) (D.neg_congr hscaled)
  exact D.veq_trans hcentral hsub

/-- Exact stationary centering subtracts the squared joint-vacuum pairing from
the reflected-joint diagonal form. -/
theorem physicalJoint_centered_diag_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    let D := (physicalJointSmulGNS w hw K half).toGNSData
    let mean := D.B observable centralPhysicalVacuumCarrier
    D.B (D.sub observable (D.smul mean centralPhysicalVacuumCarrier))
        (D.sub observable (D.smul mean centralPhysicalVacuumCarrier)) ≈
      D.B observable observable + -(mean * mean) := by
  dsimp only
  let D := (physicalJointSmulGNS w hw K half).toGNSData
  let mean := D.B observable centralPhysicalVacuumCarrier
  exact gns_centered_diag_eqv D observable centralPhysicalVacuumCarrier mean
    (Q'.eqv_refl mean)
    (physicalJoint_vacuum_unit w hw K half)

#print axioms physicalJoint_vacuum_unit
#print axioms physicalJoint_vacuum_pairing_eq_stationaryMean
#print axioms physicalJointCenteredObservable_veq_sub_smul
#print axioms physicalJoint_centered_diag_eqv

end YMGap.Continuum.BF4PhysicalJointCenteredForm
