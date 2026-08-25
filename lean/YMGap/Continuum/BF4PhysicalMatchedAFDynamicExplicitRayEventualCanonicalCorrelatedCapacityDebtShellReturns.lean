/-
# Explicit return points for matched correlated-debt shell faces

The canonical next-to-current index recoding searches the embedded current
carrier and otherwise returns the vacuum index zero.  On a coordinate proved
new, that fallback is the literal selected return point.  Thus the three
matched shell faces return respectively to `(recoveredOld, 0)`,
`(0, recoveredOld)`, and `(0, 0)`.

Return-explicit envelope types compile back to the same face, shell, and full
correlated-debt interfaces without changing the observable.  No return
estimate, tail allowance, initial closure, continuum theory, or Clay result
is supplied.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Non-image search returns the explicit fallback -/

theorem firstMappedPreimageOr_eq_fallback_of_not_mem_map
    (map : Nat -> Nat) (fallback target : Nat) :
    forall items : List Nat,
      target ∉ items.map map ->
        firstMappedPreimageOr map fallback target items = fallback
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead : map head ≠ target := by
        intro heq
        apply hnot
        rw [List.map_cons]
        exact List.mem_cons.mpr (Or.inl heq.symm)
      simp only [firstMappedPreimageOr, hhead, if_false]
      apply firstMappedPreimageOr_eq_fallback_of_not_mem_map
      intro htail
      apply hnot
      rw [List.map_cons]
      exact List.mem_cons.mpr (Or.inr htail)

theorem matchedEventualCanonicalNextIndexToCurrent_eq_zero_of_newShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat)
    (hindex : MatchedEventualCanonicalIndexInNewShell
      trajectory transitionStart physicalScale offset index) :
    matchedEventualCanonicalNextIndexToCurrent
        trajectory transitionStart physicalScale offset index = 0 := by
  unfold matchedEventualCanonicalNextIndexToCurrent
  exact firstMappedPreimageOr_eq_fallback_of_not_mem_map
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale offset)
    0 index
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale offset)
    hindex.2

/-! ## 2. Literal return pairs for the three faces -/

def matchedEventualCanonicalOldNewReturnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Nat × Nat :=
  (matchedEventualCanonicalNextIndexToCurrent
      trajectory transitionStart physicalScale offset pair.1, 0)

def matchedEventualCanonicalNewOldReturnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Nat × Nat :=
  (0, matchedEventualCanonicalNextIndexToCurrent
      trajectory transitionStart physicalScale offset pair.2)

def matchedEventualCanonicalNewNewReturnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (_trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (_transitionStart : Nat -> Nat)
    (_physicalScale _offset : Nat)
    (_pair : Nat × Nat) : Nat × Nat :=
  (0, 0)

theorem matchedEventualCanonicalNextPairToCurrent_eq_oldNewReturn
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair) :
    matchedEventualCanonicalNextPairToCurrent
        trajectory transitionStart physicalScale offset pair =
      matchedEventualCanonicalOldNewReturnPair
        trajectory transitionStart physicalScale offset pair := by
  apply Prod.ext
  · rfl
  · exact matchedEventualCanonicalNextIndexToCurrent_eq_zero_of_newShell
      trajectory transitionStart physicalScale offset pair.2 hpair.2

theorem matchedEventualCanonicalNextPairToCurrent_eq_newOldReturn
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair) :
    matchedEventualCanonicalNextPairToCurrent
        trajectory transitionStart physicalScale offset pair =
      matchedEventualCanonicalNewOldReturnPair
        trajectory transitionStart physicalScale offset pair := by
  apply Prod.ext
  · exact matchedEventualCanonicalNextIndexToCurrent_eq_zero_of_newShell
      trajectory transitionStart physicalScale offset pair.1 hpair.1
  · rfl

theorem matchedEventualCanonicalNextPairToCurrent_eq_newNewReturn
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair) :
    matchedEventualCanonicalNextPairToCurrent
        trajectory transitionStart physicalScale offset pair =
      matchedEventualCanonicalNewNewReturnPair
        trajectory transitionStart physicalScale offset pair := by
  apply Prod.ext
  · exact matchedEventualCanonicalNextIndexToCurrent_eq_zero_of_newShell
      trajectory transitionStart physicalScale offset pair.1 hpair.1
  · exact matchedEventualCanonicalNextIndexToCurrent_eq_zero_of_newShell
      trajectory transitionStart physicalScale offset pair.2 hpair.2

theorem matchedEventualCanonicalOldNewReturnPair_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair) :
    matchedEventualCanonicalOldNewReturnPair
        trajectory transitionStart physicalScale offset pair ∈
      matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale offset := by
  rw [← matchedEventualCanonicalNextPairToCurrent_eq_oldNewReturn
    trajectory transitionStart physicalScale offset pair hpair]
  exact matchedEventualCanonicalNextPairToCurrent_mem
    trajectory transitionStart physicalScale offset pair

theorem matchedEventualCanonicalNewOldReturnPair_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair) :
    matchedEventualCanonicalNewOldReturnPair
        trajectory transitionStart physicalScale offset pair ∈
      matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale offset := by
  rw [← matchedEventualCanonicalNextPairToCurrent_eq_newOldReturn
    trajectory transitionStart physicalScale offset pair hpair]
  exact matchedEventualCanonicalNextPairToCurrent_mem
    trajectory transitionStart physicalScale offset pair

theorem matchedEventualCanonicalNewNewReturnPair_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair) :
    matchedEventualCanonicalNewNewReturnPair
        trajectory transitionStart physicalScale offset pair ∈
      matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale offset := by
  rw [← matchedEventualCanonicalNextPairToCurrent_eq_newNewReturn
    trajectory transitionStart physicalScale offset pair hpair]
  exact matchedEventualCanonicalNextPairToCurrent_mem
    trajectory transitionStart physicalScale offset pair

/-! ## 3. Return-explicit analytic envelopes -/

structure MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_return : forall offset pair,
    MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalOldNewReturnPair
              trajectory transitionStart physicalScale offset pair) +
          variation offset

structure MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_return : forall offset pair,
    MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNewOldReturnPair
              trajectory transitionStart physicalScale offset pair) +
          variation offset

structure MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_return : forall offset pair,
    MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNewNewReturnPair
              trajectory transitionStart physicalScale offset pair) +
          variation offset

def MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope.toFaceEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalOldNewCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  next_le_current := by
    intro offset pair hpair
    rw [matchedEventualCanonicalNextPairToCurrent_eq_oldNewReturn
      trajectory transitionStart physicalScale offset pair hpair]
    exact data.next_le_return offset pair hpair

def MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope.toFaceEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewOldCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  next_le_current := by
    intro offset pair hpair
    rw [matchedEventualCanonicalNextPairToCurrent_eq_newOldReturn
      trajectory transitionStart physicalScale offset pair hpair]
    exact data.next_le_return offset pair hpair

def MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope.toFaceEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewNewCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  next_le_current := by
    intro offset pair hpair
    rw [matchedEventualCanonicalNextPairToCurrent_eq_newNewReturn
      trajectory transitionStart physicalScale offset pair hpair]
    exact data.next_le_return offset pair hpair

/-! ## 4. Explicit returns rejoin the same correlated path -/

def matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfReturns
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (oldNew : MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newNew : MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewShellCapacityDebtEnvelope
      trajectory transitionStart physicalScale :=
  matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfFaces
    oldNew.toFaceEnvelope newOld.toFaceEnvelope newNew.toFaceEnvelope

def matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndReturns
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (transport : MatchedEventualCanonicalTransportedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (oldNew : MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (newNew : MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale :=
  matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell
    transport
    (matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfReturns
      oldNew newOld newNew)

def matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndReturns
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (transport : forall physicalScale,
      MatchedEventualCanonicalTransportedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (oldNew : forall physicalScale,
      MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (newOld : forall physicalScale,
      MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (newNew : forall physicalScale,
      MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndReturns
                (transport physicalScale)
                (oldNew physicalScale) (newOld physicalScale)
                (newNew physicalScale)))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    DynamicVacuumSectorCompletedFamily 0 :=
  matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamily
    trajectory transitionStart
    (fun physicalScale =>
      matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndReturns
        (transport physicalScale)
        (oldNew physicalScale) (newOld physicalScale)
        (newNew physicalScale))
    tailAllowance tailAllowance_pos initial_closure

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.firstMappedPreimageOr_eq_fallback_of_not_mem_map
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.matchedEventualCanonicalNextIndexToCurrent_eq_zero_of_newShell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.matchedEventualCanonicalNextPairToCurrent_eq_oldNewReturn
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.matchedEventualCanonicalNextPairToCurrent_eq_newOldReturn
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.matchedEventualCanonicalNextPairToCurrent_eq_newNewReturn
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfReturns
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns.matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndReturns
