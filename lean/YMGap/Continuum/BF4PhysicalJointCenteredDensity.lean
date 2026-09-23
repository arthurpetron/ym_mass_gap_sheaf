/-
# Constructed centered density on the SAME physical joint completion

Subtract each stage's exact joint-vacuum pairing times the unit vacuum.
Orthogonal-projection nonexpansiveness preserves the original Cauchy modulus;
the already-proved mean convergence makes this representative null-close to
the original vacuum-orthogonal class. No reverse comparison, inverse transfer,
or additional analytic density hypothesis is used.

Consequently a supplied central completed strict form bound extends to the
entire physical joint vacuum complement. The strict central estimate remains
an input. No uniform scaling estimate, continuum construction, physical mass,
all-group theorem or Clay conclusion is asserted.
-/

import YMGap.Continuum.BF4PhysicalJointCenteredReplacement
import YMGap.Continuum.GNSUnitVacuumCenteredCauchy

namespace YMGap.Continuum.BF4PhysicalJointCenteredDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSUnitVacuumCenteredCauchy
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointCauchyMean
open YMGap.Continuum.BF4PhysicalJointCenteredForm
open YMGap.Continuum.BF4PhysicalJointCenteredReplacement
open YMGap.Continuum.BF4PhysicalJointFormGapExtension
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion

/-- The previously unsupplied exact-centered density certificate is constructed
on the original physical joint carrier, with the original Cauchy modulus. -/
def exactPhysicalJointCenteredDensity
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    ExactPhysicalJointCenteredDensity (w := w) (hw := hw) K half := by
  intro original horthogonal
  let D := (physicalJointSmulGNS w hw K half).toGNSData
  have hunit := physicalJoint_vacuum_unit w hw K half
  have hmean := physicalJointCauchyMeanSeq_converges_zero
    w hw K half original horthogonal
  exact {
    representative := centeredCauchy D centralPhysicalVacuumCarrier hunit original
    close := (centeredNullModulus D centralPhysicalVacuumCarrier
      hunit original hmean).toCauchyNull
    centered := fun n => D.veq_refl _ }

/-- Density no longer needs to be assumed: only the actual strict central
form bound remains as input to the whole joint-completion conclusion. -/
def physicalJointCompletedVacuumFormGap_of_central_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate) :
    PhysicalJointCompletedVacuumFormGap w hw K half rate :=
  physicalJointCompletedVacuumFormGapOfDensity hw K half gap
    (ExactPhysicalJointCenteredDensity.toVacuumComplementDensity K half
      (exactPhysicalJointCenteredDensity w hw K half))

#print axioms exactPhysicalJointCenteredDensity
#print axioms physicalJointCompletedVacuumFormGap_of_central_form_gap

end YMGap.Continuum.BF4PhysicalJointCenteredDensity
