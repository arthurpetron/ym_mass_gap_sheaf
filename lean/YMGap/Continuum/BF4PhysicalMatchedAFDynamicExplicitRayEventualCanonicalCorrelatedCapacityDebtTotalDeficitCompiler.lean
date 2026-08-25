/-
# One total-deficit compiler for matched dynamic correlated capacity debt

The exact matched finite-deficit compiler exposes four regional scalar
streams.  Their pointwise sum is one nonnegative stream on the same matched
capacity-debt observable.  This module proves both directions needed for a
modular analytic campaign:

* four independently constructed regional tail controls add to one total
  tail control; and
* one total tail control dominates each regional stream and therefore
  reconstructs all four regional tail interfaces.

Thus the four estimates may be developed in parallel, while the serial proof
path may consume one observable-connected analytic certificate.  No total
tail witness, tail allowance, initial closure, continuum theory, or Clay
conclusion is supplied.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

private theorem right_le_sum
    (left right : Q') (hleft : (0 : Q') <= left) :
    right <= left + right := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg right left hleft)
    (Q'.le_of_eqv (Q'.add_comm_eqv right left))

private def antitoneTailControlOfPointwiseLe
    {lower upper : Nat -> Q'}
    (upperTail : AntitoneTailControl upper)
    (pointwise : forall offset, lower offset <= upper offset) :
    AntitoneTailControl lower where
  tailRate := upperTail.tailRate
  tailRate_antitone := upperTail.tailRate_antitone
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    exact Q'.le_trans' _ _ _
      (ExpNeg.finSum_le_finSum_of_termwise
        (fun offset => lower (start + offset))
        (fun offset => upper (start + offset))
        (fun offset => pointwise (start + offset)) length)
      (upperTail.tailBound epsilon epsilon_pos start start_bound length)

/-! ## 1. One exact total stream with four regional diagnostics -/

def matchedEventualCanonicalCapacityDebtTotalDeficit
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale offset +
    (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset +
      (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset +
        matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset))

theorem matchedEventualCanonicalCapacityDebtTotalDeficit_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalCapacityDebtTotalDeficit
      trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalCapacityDebtTotalDeficit
  exact Q'.zero_le_add _ _
    (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
      trajectory transitionStart physicalScale offset)
    (Q'.zero_le_add _ _
      (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset)
      (Q'.zero_le_add _ _
        (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset)
        (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_le_total
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset <=
      matchedEventualCanonicalCapacityDebtTotalDeficit
        trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalCapacityDebtTotalDeficit
  exact Q'.add_le_self_of_nonneg _ _
    (Q'.zero_le_add _ _
      (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset)
      (Q'.zero_le_add _ _
        (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset)
        (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_le_total
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset <=
      matchedEventualCanonicalCapacityDebtTotalDeficit
        trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalCapacityDebtTotalDeficit
  have hright :
      matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset <=
        matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset +
          (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
              trajectory transitionStart physicalScale offset +
            matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
              trajectory transitionStart physicalScale offset) :=
    Q'.add_le_self_of_nonneg _ _
      (Q'.zero_le_add _ _
        (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset)
        (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset))
  exact Q'.le_trans' _ _ _ hright
    (right_le_sum _ _
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset))

theorem matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_le_total
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset <=
      matchedEventualCanonicalCapacityDebtTotalDeficit
        trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalCapacityDebtTotalDeficit
  have hnew :
      matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset <=
        matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset +
          matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset :=
    Q'.add_le_self_of_nonneg _ _
      (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset)
  have holdNew :
      matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset <=
        matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset +
          (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
              trajectory transitionStart physicalScale offset +
            matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
              trajectory transitionStart physicalScale offset) :=
    Q'.le_trans' _ _ _ hnew
      (right_le_sum _ _
        (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset))
  exact Q'.le_trans' _ _ _ holdNew
    (right_le_sum _ _
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset))

theorem matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_le_total
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset <=
      matchedEventualCanonicalCapacityDebtTotalDeficit
        trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalCapacityDebtTotalDeficit
  have hnew :
      matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset <=
        matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset +
          matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset :=
    right_le_sum _ _
      (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset)
  have holdNew :
      matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale offset <=
        matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
            trajectory transitionStart physicalScale offset +
          (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
              trajectory transitionStart physicalScale offset +
            matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
              trajectory transitionStart physicalScale offset) :=
    Q'.le_trans' _ _ _ hnew
      (right_le_sum _ _
        (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale offset))
  exact Q'.le_trans' _ _ _ holdNew
    (right_le_sum _ _
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
        trajectory transitionStart physicalScale offset))

/-! ## 2. Four regional tails contract to one total tail -/

/-- The one serial analytic certificate after the four regional deficits have
been exposed. -/
structure MatchedEventualCanonicalCapacityDebtTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  tailControl : AntitoneTailControl
    (matchedEventualCanonicalCapacityDebtTotalDeficit
      trajectory transitionStart physicalScale)

def matchedEventualCanonicalCapacityDebtTotalDeficitTailOfRegionalTails
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (transport : MatchedEventualCanonicalTransportedCapacityDebtDeficitTail
      trajectory transitionStart physicalScale)
    (oldNew : MatchedEventualCanonicalOldNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewOldCapacityDebtDeficitTail
      trajectory transitionStart physicalScale)
    (newNew : MatchedEventualCanonicalNewNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := by
    unfold matchedEventualCanonicalCapacityDebtTotalDeficit
    exact addAntitoneTailControl transport.tailControl
      (addAntitoneTailControl oldNew.tailControl
        (addAntitoneTailControl newOld.tailControl newNew.tailControl))

/-! ## 3. One total tail reconstructs the four regional tails -/

def MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toTransportedTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalTransportedCapacityDebtDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := antitoneTailControlOfPointwiseLe data.tailControl
    (fun offset =>
      matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_le_total
        trajectory transitionStart physicalScale offset)

def MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toOldNewTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalOldNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := antitoneTailControlOfPointwiseLe data.tailControl
    (fun offset =>
      matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_le_total
        trajectory transitionStart physicalScale offset)

def MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toNewOldTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewOldCapacityDebtDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := antitoneTailControlOfPointwiseLe data.tailControl
    (fun offset =>
      matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_le_total
        trajectory transitionStart physicalScale offset)

def MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toNewNewTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := antitoneTailControlOfPointwiseLe data.tailControl
    (fun offset =>
      matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_le_total
        trajectory transitionStart physicalScale offset)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalCapacityDebtTotalDeficit
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalCapacityDebtTotalDeficit_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_le_total
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.matchedEventualCanonicalCapacityDebtTotalDeficitTailOfRegionalTails
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toTransportedTail
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toOldNewTail
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toNewOldTail
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler.MatchedEventualCanonicalCapacityDebtTotalDeficitTail.toNewNewTail
