/-
# Split the exact used raw edges into persistent and cutoff-activated support

The old--new denominator is now the genuine later raw kernel on exactly the
mapped current rows used by the observable.  This module classifies those rows
by a decidable current-cutoff question:

* persistent rows already have a positive current physical kernel entry;
* activated rows become positive only after opening the next cutoff.

For persistent rows, the existing adjacent-cutoff cylinder-retention theorem
turns one half of the current kernel into a lower bound for the later mapped
kernel whenever the corrected-slab increment is at most one.  After the
capacity half-factor, this gives an explicit twice-halved retained capacity.
Activated rows retain their exact later used-edge floor.  The minimum of the
two positive floors bounds the unchanged active-row raw-kernel floor and hence
compiles to the exact old--new dyadic schedule.

This is the causal support split, not its asymptotic solution.  No growth law
for either moving floor is supplied, and no claim is made that the canonical
loop-erased routing avoids activated edges.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowRawKernelFloor

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowRawKernelFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem listPositiveMinOne_le_one_local
    {A : Type} (value : A -> Q') : forall items : List A,
      listPositiveMinOne value items <= 1
  | [] => Q'.le_refl' 1
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value tail)

private theorem lower_le_listPositiveMinOne_local
    {A : Type} (value : A -> Q') (lower : Q') : forall items : List A,
      lower <= 1 ->
      (forall item, item ∈ items -> lower <= value item) ->
      lower <= listPositiveMinOne value items
  | [], hlower, _ => hlower
  | head :: tail, hlower, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value head <= listPositiveMinOne value tail
      · rw [if_pos hle]
        exact hall head List.mem_cons_self
      · rw [if_neg hle]
        exact lower_le_listPositiveMinOne_local value lower tail hlower
          (fun item hitem =>
            hall item (List.mem_cons_of_mem head hitem))

/-! ## 1. Decidable support classification on the exact active rows -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  centralPhysicalFiniteKernel
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset) 0 pair.1 pair.2

def matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairB
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Bool :=
  decide ((0 : Q') <
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairB
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Bool :=
  decide (¬ (0 : Q') <
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair)

def matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List (Nat × Nat) :=
  (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset).filter
    (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairB
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List (Nat × Nat) :=
  (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset).filter
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairB
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPair_mem_and_currentKernel_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset ∧
      (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  have hfiltered := List.mem_filter.mp hpair
  constructor
  · exact hfiltered.1
  · unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairB
      at hfiltered
    exact of_decide_eq_true hfiltered.2

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPair_mem_and_currentKernel_not_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset ∧
      ¬ (0 : Q') <
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  have hfiltered := List.mem_filter.mp hpair
  constructor
  · exact hfiltered.1
  · unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairB
      at hfiltered
    exact of_decide_eq_true hfiltered.2

/-! ## 2. Persistent rows receive the exact adjacent-cutoff retention -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  HalfPow.half *
    (HalfPow.half *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnPersistentPair_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  have hcurrent :=
    (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPair_mem_and_currentKernel_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair).2
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
  exact Q'.mul_pos (by decide) (Q'.mul_pos (by decide) hcurrent)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacity_le_mappedRawKernelCapacity
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)
    (hincrement :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset <=
        (1 : Q')) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  let base := matchedEventualCanonicalCurrentCutoff
    transitionStart physicalScale cutoffOffset
  let later := matchedEventualCanonicalLaterCutoff
    transitionStart physicalScale cutoffOffset
  have hbaseLater : base <= later :=
    matchedEventualCanonicalCurrentCutoff_le_laterCutoff
      transitionStart physicalScale cutoffOffset
  have hretained :=
    half_mul_centralPhysicalFinitePulledKernel_le_of_increment_le_one
      (w := trajectory.nome physicalScale)
      (hw := Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (base := base) (anchor := base) (later := later) (half := 0)
      (Nat.le_refl base) hbaseLater hincrement
      hmembers.1 hmembers.2
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    hretained (by decide)
  unfold centralPhysicalFinitePulledKernel at hscaled
  dsimp [base, later, matchedEventualCanonicalCurrentCutoff,
    matchedEventualCanonicalLaterCutoff] at hscaled
  rw [centralPhysicalFiniteCutoffIndexMap_self hmembers.1,
    centralPhysicalFiniteCutoffIndexMap_self hmembers.2] at hscaled
  simpa only [
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair,
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge,
    matchedEventualCanonicalCurrentPairToNext,
    matchedEventualCanonicalCurrentIndexToNext,
    matchedEventualCanonicalCurrentCutoff,
    matchedEventualCanonicalLaterCutoff, Nat.add_assoc] using hscaled

/-! ## 3. Independent positive floors on the two support classes -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listPositiveMinOne
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
  apply listPositiveMinOne_pos
  intro pair hpair
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnPersistentPair_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listPositiveMinOne
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
  apply listPositiveMinOne_pos
  intro pair hpair
  have hactive :=
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPair_mem_and_currentKernel_not_pos
      trajectory transitionStart physicalScale cutoffOffset pair hpair).1
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnActiveCurrentPair_pos
      trajectory transitionStart physicalScale cutoffOffset pair hactive

/-- The two independently provable support floors contract through one minimum.
The empty-list fallback is `1` on either branch, so no nonemptiness premise is
hidden in the split. -/
def matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  Q'.min'
    (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
    Q'.min'
  by_cases hle :
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset <=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset
  · rw [if_pos hle]
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor_pos
        trajectory transitionStart physicalScale cutoffOffset
  · rw [if_neg hle]
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_pos
        trajectory transitionStart physicalScale cutoffOffset

/-! ## 4. The split floor bounds the unchanged exact active-row floor -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_le_activeRowRawKernelCapacityFloor
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hincrement :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset <=
        (1 : Q')) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
  apply lower_le_listPositiveMinOne_local
  · exact Q'.le_trans' _ _ _
      (Q'.min_le_left' _ _)
      (listPositiveMinOne_le_one_local
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset))
  · intro pair hactive
    let current :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCurrentRawKernelOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair
    by_cases hcurrent : (0 : Q') < current
    · have hpersistent : pair ∈
          matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
            trajectory transitionStart physicalScale cutoffOffset := by
        apply List.mem_filter.mpr
        constructor
        · exact hactive
        · unfold
            matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairB
          exact decide_eq_true hcurrent
      have hfloor :=
        listPositiveMinOne_le_of_mem
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentActiveCurrentPairs
            trajectory transitionStart physicalScale cutoffOffset)
          pair hpersistent
      have hcarrier :=
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
          trajectory transitionStart physicalScale cutoffOffset pair hactive).1
      have hretained :=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacity_le_mappedRawKernelCapacity
          trajectory transitionStart physicalScale cutoffOffset pair hcarrier hincrement
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ (Q'.min_le_left' _ _) hfloor)
        hretained
    · have hactivated : pair ∈
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
            trajectory transitionStart physicalScale cutoffOffset := by
        apply List.mem_filter.mpr
        constructor
        · exact hactive
        · unfold
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairB
          exact decide_eq_true hcurrent
      have hfloor :=
        listPositiveMinOne_le_of_mem
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
            trajectory transitionStart physicalScale cutoffOffset)
          pair hactivated
      exact Q'.le_trans' _ _ _ (Q'.min_le_right' _ _) hfloor

/-! ## 5. Parallel floor certificates contract to the exact dyadic schedule -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset *
      Q'.recipPos
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_pos
          trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathEnvelope_le_supportSplitPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hincrement :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset <=
        (1 : Q')) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  let splitFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  let activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset
  have hsplitPos : (0 : Q') < splitFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hactivePos : (0 : Q') < activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelCapacityFloor_pos
      trajectory transitionStart physicalScale cutoffOffset
  have hsplitActive : splitFloor <= activeFloor :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_le_activeRowRawKernelCapacityFloor
      trajectory transitionStart physicalScale cutoffOffset hincrement
  have hreciprocal :
      Q'.recipPos activeFloor hactivePos <=
        Q'.recipPos splitFloor hsplitPos :=
    recipPos_antitone splitFloor activeFloor hsplitPos hactivePos hsplitActive
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hreciprocal
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_supportSplitPathEnvelope
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (hincrement :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset <=
        (1 : Q')) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_activeRowRawKernelFloorPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathEnvelope_le_supportSplitPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset hincrement)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_supportSplitPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hincrement :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset <=
        (1 : Q'))
    (hpayment :
      dyad candidate *
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
              trajectory transitionStart physicalScale cutoffOffset + 1) <=
        invSqTerm offset offset_at_least_two cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      candidate := by
  have henvelope :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveRowRawKernelFloorPathEnvelope_le_supportSplitPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset hincrement
  have hdenominator := Q'.add_le_add_right _ _ 1 henvelope
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominator
    (dyad_nonneg candidate)
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_activeRowRawKernelFloorPayment
      trajectory transitionStart physicalScale offset offset_at_least_two
      cutoffOffset candidate (Q'.le_trans' _ _ _ hscaled hpayment)

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSupportSplitDyadicLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  precisionIntercept : Nat
  increment_le_one : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset <=
      (1 : Q')
  supportSplit_payment : forall cutoffOffset,
    dyad (precisionIntercept + cutoffOffset) *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitPathAmplificationEnvelope
            trajectory transitionStart physicalScale cutoffOffset + 1) <=
      invSqTerm offset offset_at_least_two cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSupportSplitDyadicLinearData.toLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSupportSplitDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
      trajectory transitionStart physicalScale offset offset_at_least_two where
  precisionIntercept := data.precisionIntercept
  precision_le := by
    intro cutoffOffset
    exact
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_supportSplitPayment
        trajectory transitionStart physicalScale offset offset_at_least_two
        cutoffOffset (data.precisionIntercept + cutoffOffset)
        (data.increment_le_one cutoffOffset)
        (data.supportSplit_payment cutoffOffset)
  start_absorbs_fixed_tail_cost := data.start_absorbs_fixed_tail_cost

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceRetainedCurrentRawKernelCapacity_le_mappedRawKernelCapacity
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFacePersistentRetainedRawKernelCapacityFloor_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedRawKernelCapacityFloor_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_pos
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceSupportSplitRawKernelCapacityFloor_le_activeRowRawKernelCapacityFloor
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_le_supportSplitPathEnvelope
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_supportSplitPayment
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabSupportSplitDyadicLinearData.toLinearData

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
