/-
# The matched AF path through the exact mass-normalized row rate

The spin-ray/off-ray Dirichlet route compares the physical joint with the
unnormalized stationary product on one closed component.  Its conversion from
pairwise variance to a centered form therefore carries the stationary mass of
that component.  There is a shorter alternative already available at fixed
nome: compare the joint directly with the component-conditioned product

    pi(x) * pi(y) / mass(component).

The sharp finite coefficient for that comparison is
`centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate`.  A cofinal
strict upper bound for this literal coefficient contracts the same completed
canonical vacuum-sector transfer, with no separate sector-mass floor.

This file makes that alternative dynamic and pins it to the exact matched AF
nome and physical spacing.  After the finite normalized-row producer is
supplied, the only scalar continuum estimate is the transparent one

    lower * a_j <= 1 - rate_j <= upper * a_j.

The resulting decay remains the same-object completed autocorrelation through
the existing observable pin.  No cofinal normalized-row producer, matched
cubic law, spacing envelope, observable pin, continuum carrier, continuum
Yang--Mills theory, or Clay conclusion is inhabited here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorExactMassNormalizedRowRate
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail

/-! ## 1. One mass-loss-free producer on the exact matched trajectory -/

/-- At every physical scale, supply one strict cofinal upper bound for the
literal mass-normalized row rate of the exact matched BF4 block weight.

Unlike the ray/off-ray Dirichlet producer, this record contains no lower bound
on the unconditioned mass of the canonical vacuum component. -/
structure MatchedPhysicalMassNormalizedRowGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  rate : Nat -> Q'
  exactRateBound : forall scale,
    FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound
      (trajectory.nome scale)
      (Q'.le_of_lt (trajectory.nome_pos scale))
      0
      (rate scale)

namespace MatchedPhysicalMassNormalizedRowGapProducer

/-- The literal completed canonical vacuum-sector contraction produced at one
matched physical scale. -/
def completedGapAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory)
    (scale : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0
    (producer.exactRateBound scale).toVacuumSectorCenteredStrictGap

/-- Forget the finite row proof only after it has constructed the actual
completed carrier and transfer at every scale. -/
def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := trajectory.nome
  nome_pos := trajectory.nome_pos
  nome_lt_one := trajectory.nome_lt_one
  transferSpacing := matchedPhysicalDynamicSpacing spacing
    trajectory.coupling trajectory.coupling_pos
    trajectory.coupling_le_window
  transferSpacingToZero := trajectory.transferSpacingToZero
  completedGap := producer.completedGapAt

/-- The completed norm rate is exactly the supplied cofinal normalized-row
coefficient; there is no intervening sector-mass or path-congestion scalar. -/
@[simp] theorem completedGapAt_rate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory)
    (scale : Nat) :
    (producer.completedGapAt scale).rate = producer.rate scale :=
  rfl

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toCompletedFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-- The lattice margin of the actual completed transfer is literally the
defect of the sharp normalized-row coefficient from one. -/
@[simp] theorem toCompletedFamily_latticeMargin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.latticeMargin scale =
      (1 : Q') - producer.rate scale :=
  rfl

/-! ## 2. The sole remaining scalar estimate -/

/-- Two-sided physical scaling of the literal normalized-row margin.  These
are precisely the estimates needed for a finite nonzero physical gap and a
vanishing one-step lattice margin. -/
structure MarginScaling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory) :
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

/-- The direct normalized-row margin estimate is already a physical rate band
on the definitionally same completed transfer. -/
def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory}
    (scaling : MarginScaling producer) :
    DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily where
  floor := scaling.lower
  floor_pos := scaling.lower_pos
  ceiling := scaling.upper
  ceiling_pos := scaling.upper_pos
  lowerRate := scaling.lowerScale
  upperRate := scaling.upperScale

def toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory}
    (scaling : MarginScaling producer) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  scaling.toPhysicalRateBand.toContinuumGapTheorem

end MarginScaling

/-! ## 3. The observable-connected downstream path -/

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory) :
    Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

def physicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory}
    (pin : SameObjectObservablePin producer) :
    PhysicalSeparator :=
  pin.toPhysicalSeparator

/-- The pinned rational connected correlator is controlled by the same
completed transfer whose rate is the mass-normalized row coefficient. -/
theorem connectedCorrSq_control
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory}
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
    {producer : MatchedPhysicalMassNormalizedRowGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (scaling : MarginScaling producer) :
    PhysicalGapFloor (physicalSeparator pin)
      producer.toCompletedFamily.transferSpacing.spacing
      producer.toCompletedFamily.transferSpacing.spacing_pos :=
  pin.toPhysicalGapFloor scaling.toPhysicalRateBand

end MatchedPhysicalMassNormalizedRowGapProducer

end YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.completedGapAt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.completedGapAt_rate
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.toCompletedFamily_latticeMargin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.MarginScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.MarginScaling.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.connectedCorrSq_control
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFMassNormalizedRowGapPath.MatchedPhysicalMassNormalizedRowGapProducer.physicalGapFloor
