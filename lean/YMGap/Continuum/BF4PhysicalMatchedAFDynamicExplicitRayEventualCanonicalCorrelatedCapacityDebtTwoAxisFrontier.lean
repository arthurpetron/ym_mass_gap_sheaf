/-
# Two-axis frontier for matched dynamic correlated capacity debt

The matched physical construction has two distinct limiting indices:

* `physicalScale` follows the AF trajectory and controls the physical lattice
  spacing; and
* `cutoffOffset` recedes the finite carrier at one fixed physical scale and
  controls capacity-debt persistence.

Both axes admit inverse-square interfaces, but one cannot be substituted for
the other.  This module packages the exact connected frontier: AF
identification constructs the known physical-spacing inverse-square tail,
while an independently supplied family of capacity-debt inverse-square
controls constructs one cutoff tail at every physical scale.

No capacity estimate, AF identification, tail allowance, initial closure,
continuum theory, or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTwoAxisFrontier

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.QuadraticRateErrorTailControl

/-! ## 1. The known AF physical-scale tail -/

/-- Identification of the exact matched scalar trajectory with one proved AF
schedule.  This controls the physical-scale axis only. -/
structure MatchedPhysicalDynamicAFTrajectoryIdentification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing) : Type 1 where
  certificate : AFTrajectoryCertificate
  couplingIdentification : ShiftedAFTrajectoryIdentification
    certificate trajectory.coupling

def MatchedPhysicalDynamicAFTrajectoryIdentification.physicalSpacingInverseSquare
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (data : MatchedPhysicalDynamicAFTrajectoryIdentification trajectory) :
    InverseSquareSpacingTail
      trajectory.toAdaptiveScalarTrajectory.transferSpacing 0 := by
  exact spacingInverseSquareTailOfAFTrajectory
    spacing trajectory.coupling trajectory.coupling_pos
    trajectory.coupling_le_window data.certificate
    data.couplingIdentification

/-! ## 2. The still-open cutoff tail at every physical scale -/

/-- One inverse-square cutoff-debt control for every physical scale.  The
coefficient and cutoff offset may depend on physical scale; no uniformity is
silently asserted. -/
structure MatchedEventualCanonicalCapacityDebtCutoffInverseSquareFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) : Type 1 where
  control : forall physicalScale,
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale

def MatchedEventualCanonicalCapacityDebtCutoffInverseSquareFamily.toTotalDeficitTails
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    (data : MatchedEventualCanonicalCapacityDebtCutoffInverseSquareFamily
      trajectory transitionStart)
    (physicalScale : Nat) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  (data.control physicalScale).toTotalDeficitTail

/-! ## 3. The observable-connected two-axis input -/

/-- Both axes required by the present matched path.  This is a conjunction,
not an implication from AF spacing to cutoff debt. -/
structure MatchedEventualCanonicalCapacityDebtTwoAxisControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) : Type 1 where
  physicalScale : MatchedPhysicalDynamicAFTrajectoryIdentification trajectory
  cutoffScale : MatchedEventualCanonicalCapacityDebtCutoffInverseSquareFamily
    trajectory transitionStart

def MatchedEventualCanonicalCapacityDebtTwoAxisControl.physicalSpacingTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    (data : MatchedEventualCanonicalCapacityDebtTwoAxisControl
      trajectory transitionStart) :
    InverseSquareSpacingTail
      trajectory.toAdaptiveScalarTrajectory.transferSpacing 0 :=
  data.physicalScale.physicalSpacingInverseSquare

def MatchedEventualCanonicalCapacityDebtTwoAxisControl.cutoffDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    (data : MatchedEventualCanonicalCapacityDebtTwoAxisControl
      trajectory transitionStart)
    (physicalScale : Nat) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  data.cutoffScale.toTotalDeficitTails physicalScale

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTwoAxisFrontier

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTwoAxisFrontier.MatchedPhysicalDynamicAFTrajectoryIdentification.physicalSpacingInverseSquare
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTwoAxisFrontier.MatchedEventualCanonicalCapacityDebtCutoffInverseSquareFamily.toTotalDeficitTails
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTwoAxisFrontier.MatchedEventualCanonicalCapacityDebtTwoAxisControl.physicalSpacingTail
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTwoAxisFrontier.MatchedEventualCanonicalCapacityDebtTwoAxisControl.cutoffDeficitTail
