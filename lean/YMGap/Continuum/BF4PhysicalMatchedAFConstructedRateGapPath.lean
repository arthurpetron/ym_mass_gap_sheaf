/-
# The matched AF path through the constructed finite-base Poincare rates

Every fixed finite canonical BF4 vacuum carrier already has a constructive
positive-edge Poincare rate.  Row total variation is not the right way to
make those rates uniform: its exact mass-normalized coefficient is already
larger than one at cutoff two, even though the cancellation-preserving
signed form has the verified rate `49/50` there.

The surviving quantity is therefore the signed-form rate itself.  At each
matched physical scale this module asks for one strict rational `q_j` above
the already constructed Poincare rate of every finite base carrier.  The
existing cofinal bridge then contracts the actual completed canonical
vacuum-sector transfer at exactly `q_j`.  No rowwise total-variation or
global Doeblin premise is introduced.

After that construction, the only dimensionful estimate is

    lower * a_j <= 1 - q_j <= upper * a_j.

It gives a positive physical gap floor and controls the same-object completed
connected correlator through the existing observable pin.  No uniform rate
bound, matched cubic law, spacing envelope, observable pin, continuum
carrier, continuum Yang--Mills theory, or Clay conclusion is inhabited here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget is used.

The subsequent module
`BF4PhysicalCutoffVacuumSectorConstructedRateNoGo` proves that this specific
producer is uninhabited: its global all-pairs path ceiling grows along the
spin-cube ray while its global floor is at most one.  The definitions here are
retained as an exact compiler boundary and must not be treated as an open
candidate route.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath

namespace YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail

/-! ## 1. Cancellation-preserving producer on the matched trajectory -/

/-- At every physical scale, one strict rate bounds the explicit Poincare
rate already constructed on every finite base carrier.  Uniformity in the
representation cutoff is a field of the datum, rather than an unqualified
claim in the conclusion.  The later constructed-rate no-go theorem proves
that this structure has no inhabitant. -/
structure MatchedPhysicalConstructedRateGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  rate : Nat -> Q'
  uniformConstructedRateBound : forall scale,
    FixedNomeUniformConstructedVacuumSectorRateBound
      (trajectory.nome scale)
      (trajectory.nome_pos scale)
      (trajectory.nome_lt_one scale)
      0
      (rate scale)

namespace MatchedPhysicalConstructedRateGapProducer

/-- The actual completed canonical vacuum-sector contraction obtained from
the common upper bound on all constructed finite-base rates. -/
def completedGapAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory)
    (scale : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
    (producer.uniformConstructedRateBound scale).toVacuumSectorCenteredStrictGap

/-- Package the scale-indexed completed contractions on the exact matched
nome and physical spacing. -/
def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := trajectory.nome
  nome_pos := trajectory.nome_pos
  nome_lt_one := trajectory.nome_lt_one
  transferSpacing := matchedPhysicalDynamicSpacing spacing
    trajectory.coupling trajectory.coupling_pos
    trajectory.coupling_le_window
  transferSpacingToZero := trajectory.transferSpacingToZero
  completedGap := producer.completedGapAt

/-- The completed norm rate is definitionally the common constructed-rate
ceiling supplied at that physical scale. -/
@[simp] theorem completedGapAt_rate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory)
    (scale : Nat) :
    (producer.completedGapAt scale).rate = producer.rate scale :=
  rfl

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toCompletedFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-- The lattice margin of the same completed transfer is exactly the defect
of the cancellation-preserving signed-form rate. -/
@[simp] theorem toCompletedFamily_latticeMargin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale =
      (1 : Q') - producer.rate scale :=
  rfl

/-! ## 2. The remaining physical scaling estimate -/

/-- Two-sided scaling of the cancellation-preserving lattice margin.  The
lower inequality is the positive physical-mass content; the upper inequality
prevents a fixed lattice-unit gap from being mislabeled as a continuum mass. -/
structure MarginScaling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory) :
    Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  upper_pos : (0 : Q') < upper
  lowerScale : forall scale,
    lower * spacing.a (trajectory.coupling scale) <=
      (1 : Q') - producer.rate scale
  upperScale : forall scale,
    (1 : Q') - producer.rate scale <=
      upper * spacing.a (trajectory.coupling scale)

namespace MarginScaling

/-- The signed-form margin estimate is a physical rate band on the
definitionally same completed transfer family. -/
def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConstructedRateGapProducer trajectory}
    (scaling : MarginScaling producer) :
    DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily where
  floor := scaling.lower
  floor_pos := scaling.lower_pos
  ceiling := scaling.upper
  ceiling_pos := scaling.upper_pos
  lowerRate := scaling.lowerScale
  upperRate := scaling.upperScale

/-- Scalar continuum-gap export from the same matched completed transfer.
This remains an interface theorem, not a continuum Yang--Mills model. -/
def toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConstructedRateGapProducer trajectory}
    (scaling : MarginScaling producer) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  scaling.toPhysicalRateBand.toContinuumGapTheorem

end MarginScaling

/-! ## 3. Observable-connected consequences -/

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConstructedRateGapProducer trajectory) :
    Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

def physicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConstructedRateGapProducer trajectory}
    (pin : SameObjectObservablePin producer) :
    PhysicalSeparator :=
  pin.toPhysicalSeparator

/-- The pinned connected correlator is controlled by the same completed
transfer whose rate is the common finite-base Poincare ceiling. -/
theorem connectedCorrSq_control
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConstructedRateGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (O : pin.Obs) (hO : pin.GaugeInvariantLocal O)
    (scale n : Nat) :
    pin.connectedCorrSq scale O n <=
      pin.amplitude O * ((producer.rate scale) ^ n) := by
  simpa only [completedGapAt_rate] using
    pin.connectedCorrSq_control O hO scale n

def physicalGapFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConstructedRateGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (scaling : MarginScaling producer) :
    PhysicalGapFloor (physicalSeparator pin)
      producer.toCompletedFamily.transferSpacing.spacing
      producer.toCompletedFamily.transferSpacing.spacing_pos :=
  pin.toPhysicalGapFloor scaling.toPhysicalRateBand

end MatchedPhysicalConstructedRateGapProducer

end YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.completedGapAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.completedGapAt_rate
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.toCompletedFamily_latticeMargin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.MarginScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.MarginScaling.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.connectedCorrSq_control
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConstructedRateGapPath.MatchedPhysicalConstructedRateGapProducer.physicalGapFloor
