/-
# Dynamic adaptive transition products on the common completed BF4 path

The adaptive transition-product compiler exposes the viable local analytic
producer at one fixed nome.  The source-independent dynamic completed-family
interface carries the actual completed transfer, physical spacing, and
same-object moments at every physical scale.  This module connects those two
layers without changing routes, rates, carriers, or downstream consumers.

A scale-wise cofinal adaptive transition-product family is first converted
losslessly to adaptive conditional congestion, then to routed capacity and
the existing off-ray residual coercivity.  Only after that construction is
the finite proof route erased into the common dynamic completed family.  Its
normalized strength law is consequently the same local ray/residual strength
already used by the physical-rate and observable compilers.

No dynamic adaptive product family, strength band, observable pin, continuum
handoff, continuum Yang--Mills theory, or Clay conclusion is inhabited here.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate

/-! ## 1. Scale-wise adaptive local producer -/

/-- At every physical scale, retain the same nome, spacing, spin-ray
capacity, adaptive routes, and multiplicity-aware transition-product bound
that will construct the completed transfer. -/
structure DynamicSpinCubeOffRayAdaptiveTransitionProductFamily : Type 1 where
  nome : Nat → Q'
  nome_pos : ∀ scale, (0 : Q') < nome scale
  nome_lt_one : ∀ scale, nome scale < (1 : Q')
  transferSpacing : PhysicalSpacing
  transferSpacingToZero : SpacingToZero transferSpacing
  rayCapacity : ∀ scale,
    FixedNomeCofinalSpinCubeRayCapacity (nome_pos scale)
  transitionProduct : ∀ scale,
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      (nome_pos scale) (rayCapacity scale)

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- Lossless conditional-congestion view at one physical scale. -/
def adaptiveConditionalCongestionAt
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion
      (family.nome_pos scale) (family.rayCapacity scale) :=
  (family.transitionProduct scale).toAdaptiveConditionalCongestion

/-- Lossless routed joint-capacity view at one physical scale. -/
def adaptiveRoutingCapacityAt
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity
      (family.nome_pos scale) (family.rayCapacity scale) :=
  (family.adaptiveConditionalCongestionAt scale).toAdaptiveRoutingCapacity

/-- The exact existing residual-coercivity consumer at one scale. -/
def residualCoercivityAt
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scale : Nat) :
    FixedNomeCofinalSpinCubeOffRayResidualCoercivity
      (family.nome_pos scale) (family.rayCapacity scale) :=
  (family.adaptiveRoutingCapacityAt scale).toCofinalResidualCoercivity

/-- Join the adaptive analytic producer to the previously established local
dynamic source.  No completed object has yet been forgotten. -/
def toResidualCoercivityFamily
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) :
    DynamicSpinCubeOffRayResidualCoercivityFamily where
  nome := family.nome
  nome_pos := family.nome_pos
  nome_lt_one := family.nome_lt_one
  transferSpacing := family.transferSpacing
  transferSpacingToZero := family.transferSpacingToZero
  rayCapacity := family.rayCapacity
  residualCoercivity := family.residualCoercivityAt

/-- The source-independent family of actual completed carriers and
transfers.  Every downstream same-object moment is taken on this family. -/
def toCompletedFamily
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) :
    DynamicVacuumSectorCompletedFamily 0 :=
  family.toResidualCoercivityFamily.toCompletedFamily

/-- The exact normalized strength law of the same completed transfer. -/
def toNormalizedStrengthLaw
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) :
    DynamicVacuumSectorNormalizedStrengthLaw family.toCompletedFamily :=
  family.toResidualCoercivityFamily.toNormalizedStrengthLaw

/-- The independent two-sided physical scaling input, now attached to the
same transfer produced by the adaptive transition-product route. -/
abbrev StrengthBand
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  DynamicVacuumSectorStrengthBand family.toNormalizedStrengthLaw

def physicalRateBand
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (band : family.StrengthBand) :
    DynamicVacuumSectorPhysicalRateBand family.toCompletedFamily :=
  band.toPhysicalRateBand

/-- Scalar physical-gap export from the same local adaptive source.  This is
not a continuum carrier or Yang--Mills construction. -/
def toContinuumGapTheorem
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    (band : family.StrengthBand) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  band.toContinuumGapTheorem

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveConditionalCongestionAt
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveRoutingCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.residualCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toResidualCoercivityFamily
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toNormalizedStrengthLaw
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toContinuumGapTheorem
