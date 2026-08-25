/-
# Automatic support proxy on the matched eventual canonical ray

The arbitrary-nome support-aware BF4 construction provides a positive lower
proxy for the exact routed finite capacity margin.  This module specializes
that construction to the canonical routing at the exact matched physical
nome and every offset beyond a selected scale-dependent cofinal start.

The proxy uses the literal supported conditional-kernel floor and literal
routed-load maximum.  Its positivity and its comparison into the same exact
finite margin are inherited without changing the nome, cutoff, routing, load,
or kernel.  This separate checked boundary also keeps later persistence types
from repeatedly normalizing the finite support construction.

No variation or persistence estimate is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy

local infix:50 " ≈ " => Q'.eqv

/-- The literal canonical routing used by the exact matched finite margin at
one scale and one offset beyond the selected cofinal start. -/
def matchedEventualCanonicalRoutingAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :=
  canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
    (trajectory.nome scale)
    (Q'.le_of_lt (trajectory.nome_pos scale))
    (transitionStart scale + offset)

/-- Half the supported conditional-kernel floor divided by one plus the exact
routed-load maximum, at the matched nome and cutoff. -/
def matchedEventualCanonicalSupportCapacityMarginLower
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)

theorem matchedEventualCanonicalSupportCapacityMarginLower_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalSupportCapacityMarginLower
        trajectory transitionStart scale offset :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_pos
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)

theorem matchedEventualCanonicalSupportCapacityMarginLower_le_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    matchedEventualCanonicalSupportCapacityMarginLower
        trajectory transitionStart scale offset <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
          (trajectory.nome scale)
          (Q'.le_of_lt (trajectory.nome_pos scale))
          (transitionStart scale + offset)) :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_finiteCapacityMargin
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)

/-- The exact support construction inhabits the matched lower-proxy
interface; callers no longer choose a proxy or its comparison proof. -/
def matchedEventualCanonicalSupportMarginLowerProxy
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) :
    MatchedEventualCanonicalMarginLowerProxy trajectory transitionStart where
  marginLower :=
    matchedEventualCanonicalSupportCapacityMarginLower
      trajectory transitionStart
  marginLower_pos :=
    matchedEventualCanonicalSupportCapacityMarginLower_pos
      trajectory transitionStart
  marginLower_le_exact :=
    matchedEventualCanonicalSupportCapacityMarginLower_le_exact
      trajectory transitionStart

/-! ## A proof-bearing opaque boundary for the exact support debt -/

/-- One compact rational representative carrying its kernel-checked equality
to the exact matched support debt.  The equality field prevents the opaque
boundary from changing the physical stream. -/
structure MatchedEventualCanonicalSupportCapacityDebtValue
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) : Type where
  value : Q'
  value_eqv : value ≈
    matchedEventualCanonicalCapacityDebt
      (matchedEventualCanonicalSupportMarginLowerProxy
        trajectory transitionStart)
      scale offset

/-- Seal the already explicit rational term so later dependent variation
types do not repeatedly normalize its finite supported carrier.  The body is
fully kernel checked and the result carries its exact setoid equality. -/
opaque matchedEventualCanonicalSupportCapacityDebtValue
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    MatchedEventualCanonicalSupportCapacityDebtValue
      trajectory transitionStart scale offset := {
  value :=
    matchedEventualCanonicalCapacityDebt
      (matchedEventualCanonicalSupportMarginLowerProxy
        trajectory transitionStart)
      scale offset
  value_eqv := Q'.eqv_refl _
}

/-- The compact rational support-debt stream used by analytic variation
certificates. -/
def matchedEventualCanonicalSupportCapacityDebt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) : Q' :=
  (matchedEventualCanonicalSupportCapacityDebtValue
    trajectory transitionStart scale offset).value

theorem matchedEventualCanonicalSupportCapacityDebt_eqv_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) :
    matchedEventualCanonicalSupportCapacityDebt
        trajectory transitionStart scale offset ≈
      matchedEventualCanonicalCapacityDebt
        (matchedEventualCanonicalSupportMarginLowerProxy
          trajectory transitionStart)
        scale offset :=
  (matchedEventualCanonicalSupportCapacityDebtValue
    trajectory transitionStart scale offset).value_eqv

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy.matchedEventualCanonicalSupportCapacityMarginLower_pos
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy.matchedEventualCanonicalSupportCapacityMarginLower_le_exact
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy.matchedEventualCanonicalSupportMarginLowerProxy
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy.matchedEventualCanonicalSupportCapacityDebtValue
#print axioms YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy.matchedEventualCanonicalSupportCapacityDebt_eqv_exact
