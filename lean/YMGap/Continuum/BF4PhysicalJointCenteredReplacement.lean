/-
# Exact-centered representative certificate for the physical joint completion

The finite joint centering algebra gives an explicit centered stage for every
raw carrier element.  This module isolates the remaining arbitrary-completion
input: a Cauchy representative, a null-close witness to the original class,
and stagewise agreement with those centered stages.  Such a certificate
implies the existing exact vacuum-complement replacement, but it is not
constructed here and does not assert joint density or a continuum gap.
-/

import YMGap.Continuum.BF4PhysicalJointCenteredForm

namespace YMGap.Continuum.BF4PhysicalJointCenteredReplacement

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointCenteredKernel
open YMGap.Continuum.BF4PhysicalJointCenteredForm
open YMGap.Continuum.BF4PhysicalJointFormGapExtension
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- The exact centered subtraction at one finite joint stage. -/
def physicalJointCenteredStage
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') : EdgeLabelling → Q' :=
  let D := (physicalJointSmulGNS w hw K half).toGNSData
  D.sub observable
    (D.smul (D.B observable centralPhysicalVacuumCarrier)
      centralPhysicalVacuumCarrier)

/-- Every exact centered stage is joint-vacuum orthogonal. -/
theorem physicalJointCenteredStage_vacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    PhysicalJointVacuumOrthogonal w hw K half
      (embedV (physicalJointSmulGNS w hw K half).toGNSData
        (physicalJointCenteredStage w hw K half observable)) := by
  let D := (physicalJointSmulGNS w hw K half).toGNSData
  let centered := physicalJointCenteredObservable w hw K half observable
  let stage := physicalJointCenteredStage w hw K half observable
  have hveq : D.veq centered stage := by
    exact physicalJointCenteredObservable_veq_sub_smul
      w hw K half observable
  have hrad : D.rad centered stage := rad_of_veq D hveq
  have hembed : embedV D centered = embedV D stage :=
    Quotient.sound (embed_null_of_rad D hrad)
  have hcenter : PhysicalJointVacuumOrthogonal w hw K half (embedV D centered) :=
    physicalJointCenteredObservable_vacuumOrthogonal w hw K half observable
  unfold PhysicalJointVacuumOrthogonal at hcenter ⊢
  rw [← hembed]
  exact hcenter

/-- A generic minimal constructive input for centering an arbitrary completed
representative.  The representative and null-close fields are the missing
Cauchy/range data; `centered` records exact stagewise agreement. -/
structure ExactCenteredCauchyReplacement
    (D : GNSData) (stages : Nat → D.V) (original : CauchyGNS D) : Type where
  representative : CauchyGNS D
  close : CauchyNull D original representative
  centered : ∀ n : Nat, D.veq (representative.seq n) (stages n)

/-- Specialization of the generic centering certificate to the physical joint
carrier and its exact stage-centered subtraction. -/
abbrev ExactPhysicalJointCenteredCauchyReplacement
    {w : Q'} {hw : (0 : Q') ≤ w} (K half : Nat)
    (original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData) : Type :=
  ExactCenteredCauchyReplacement
    (physicalJointSmulGNS w hw K half).toGNSData
    (fun n => physicalJointCenteredStage w hw K half (original.seq n))
    original

/-- The centered Cauchy certificate supplies the existing exact-kernel
replacement interface used by the completed form-gap theorem. -/
def ExactPhysicalJointCenteredCauchyReplacement.toVacuumComplementReplacement
    {w : Q'} {hw : (0 : Q') ≤ w} (K half : Nat)
    (original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData)
    (certificate : ExactPhysicalJointCenteredCauchyReplacement K half original) :
    ExactPhysicalJointVacuumComplementReplacement hw K half original where
  representative := certificate.representative
  close := certificate.close
  stageInKernel := by
    intro n
    let D := (physicalJointSmulGNS w hw K half).toGNSData
    let stage := physicalJointCenteredStage w hw K half (original.seq n)
    have hstage := physicalJointCenteredStage_vacuumOrthogonal
      w hw K half (original.seq n)
    have hrad : D.rad (certificate.representative.seq n) stage :=
      rad_of_veq D (certificate.centered n)
    have hembed : embedV D (certificate.representative.seq n) = embedV D stage :=
      Quotient.sound (embed_null_of_rad D hrad)
    unfold PhysicalJointVacuumOrthogonal at hstage ⊢
    rw [hembed]
    exact hstage

/-- The centered-representative certificate feeds directly into the existing
completed reflected-joint form-gap theorem. -/
theorem physicalJoint_completed_form_gap_of_centered_certificate
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData)
    (certificate : ExactPhysicalJointCenteredCauchyReplacement K half original) :
    CReal.RCle
      ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointTransfer w hw K half
          (Quotient.mk
            (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
            original))
        (Quotient.mk
          (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
          original))
      (CReal.RCscale rate
        ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (Quotient.mk
            (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
            original)
          (Quotient.mk
            (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
            original))) := by
  exact physicalJoint_completed_form_gap_of_replacement
    hw K half gap original
    (ExactPhysicalJointCenteredCauchyReplacement.toVacuumComplementReplacement
      K half original certificate)

/-- The centered-density obligation: every vacuum-orthogonal completed class
must be supplied with a Cauchy representative carrying the exact centered-stage
certificate. -/
def ExactPhysicalJointCenteredDensity
    {w : Q'} {hw : (0 : Q') ≤ w} (K half : Nat) : Type :=
  ∀ original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData,
    PhysicalJointVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
        original) →
      ExactPhysicalJointCenteredCauchyReplacement K half original

/-- A centered-density witness is sufficient for the existing exact density
interface consumed by the completed form-gap theorem. -/
def ExactPhysicalJointCenteredDensity.toVacuumComplementDensity
    {w : Q'} {hw : (0 : Q') ≤ w} (K half : Nat)
    (density : ExactPhysicalJointCenteredDensity (w := w) (hw := hw) K half) :
    ExactPhysicalJointVacuumComplementDensity hw K half :=
  fun original horthogonal =>
    ExactPhysicalJointCenteredCauchyReplacement.toVacuumComplementReplacement
      K half original (density original horthogonal)

#print axioms physicalJointCenteredStage
#print axioms physicalJointCenteredStage_vacuumOrthogonal
#print axioms ExactPhysicalJointCenteredCauchyReplacement.toVacuumComplementReplacement
#print axioms physicalJoint_completed_form_gap_of_centered_certificate
#print axioms ExactPhysicalJointCenteredDensity.toVacuumComplementDensity

end YMGap.Continuum.BF4PhysicalJointCenteredReplacement
