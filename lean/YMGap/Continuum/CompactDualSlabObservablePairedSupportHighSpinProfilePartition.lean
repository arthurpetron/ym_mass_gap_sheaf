/-
# Total-mass/core partition for arbitrary-coupling observable peeling

The profiled accepted peel exposes two aggregate counters.  This module uses
their sum, rather than the exterior counter alone, as the geometric mass key:

  key(source) = (exteriorMass + coreMass, coreMass).

The first coordinate is the old complete trace mass and hence retains the
observable separation floor.  The second coordinate lies in the explicit
representation-cutoff-independent range

  0 .. 2 * faceCount * threshold.

For one fixed terminal and key, the complete observable source fiber is
bounded by the previously proved two-rate profile.  The final section rewrites
that coefficient exactly as a geometric total-mass factor times a bounded
core-inflation factor.

Constructive contract: finite filters, deterministic fibers, the profiled
well-founded peel, and exact rational arithmetic only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfilePartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Deterministic profile coordinates -/

def slabObservablePairTargetSupportHighSpinProfileTerminal
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) : SlabAcceptedTwoReplicaState D :=
  (slabObservablePairTargetSupportCanonicalHighSpinProfile
    D rootFaceId targetFaceId htarget source.1 source.2).1

def slabObservablePairTargetSupportHighSpinProfileExterior
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) : Nat :=
  (slabObservablePairTargetSupportCanonicalHighSpinProfile
    D rootFaceId targetFaceId htarget source.1 source.2).2.2.1

def slabObservablePairTargetSupportHighSpinProfileCore
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) : Nat :=
  (slabObservablePairTargetSupportCanonicalHighSpinProfile
    D rootFaceId targetFaceId htarget source.1 source.2).2.2.2

def slabObservablePairTargetSupportHighSpinProfileMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) : Nat :=
  slabObservablePairTargetSupportHighSpinProfileExterior
      D rootFaceId targetFaceId htarget source +
    slabObservablePairTargetSupportHighSpinProfileCore
      D rootFaceId targetFaceId htarget source

def slabObservablePairTargetSupportHighSpinProfileKey
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) : Nat × Nat :=
  (slabObservablePairTargetSupportHighSpinProfileMass
      D rootFaceId targetFaceId htarget source,
    slabObservablePairTargetSupportHighSpinProfileCore
      D rootFaceId targetFaceId htarget source)

def slabObservablePairTargetSupportHighSpinProfileCoreBound
    (D : SlabPhysicalData) : Nat :=
  2 * D.faceEdges.length * anchorPaidExteriorThreshold D.coupling

/-- The new total-mass coordinate is literally the pre-existing complete
canonical trace mass. -/
theorem slabObservablePairTargetSupportHighSpinProfileMass_eq_traceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) :
    slabObservablePairTargetSupportHighSpinProfileMass
        D rootFaceId targetFaceId htarget source =
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 := by
  have hforget :=
    slabObservablePairTargetSupportCanonicalHighSpinProfile_terminal_trace
      D rootFaceId targetFaceId htarget source.1 source.2
  have htrace := congrArg Prod.snd hforget
  have hprofile := slabAcceptedPairCanonicalHighSpinProfile_traceMass
    D (anchorPaidExteriorThreshold D.coupling)
      (slabTwoReplicaTargetSupportComponent D.extent
        source.1.1.1.1 source.1.2.1.1 targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget source.1 source.2 faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState source.1)
  unfold slabObservablePairTargetSupportHighSpinProfileMass
    slabObservablePairTargetSupportHighSpinProfileExterior
    slabObservablePairTargetSupportHighSpinProfileCore
    slabObservablePairTargetSupportCanonicalHighSpinProfile
  rw [← htrace]
  exact hprofile.symm

/-- Once total mass and core mass are displayed, the exterior counter is
their natural-number difference. -/
theorem slabObservablePairTargetSupportHighSpinProfileExterior_eq_sub
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) (mass core : Nat)
    (hmass : slabObservablePairTargetSupportHighSpinProfileMass
      D rootFaceId targetFaceId htarget source = mass)
    (hcore : slabObservablePairTargetSupportHighSpinProfileCore
      D rootFaceId targetFaceId htarget source = core) :
    slabObservablePairTargetSupportHighSpinProfileExterior
      D rootFaceId targetFaceId htarget source = mass - core := by
  unfold slabObservablePairTargetSupportHighSpinProfileMass at hmass
  omega

/-! ## 2. Finite key carrier -/

def slabObservablePairTargetSupportHighSpinProfileKeyCarrier
    (D : SlabPhysicalData) (floor : Nat) : List (Nat × Nat) :=
  cartesian
    (slabObservablePairedSupportPaidMasses D floor)
    (List.range
      (slabObservablePairTargetSupportHighSpinProfileCoreBound D + 1))

private theorem range_nodup_local :
    forall count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

theorem slabObservablePairTargetSupportHighSpinProfileKeyCarrier_nodup
    (D : SlabPhysicalData) (floor : Nat) :
    (slabObservablePairTargetSupportHighSpinProfileKeyCarrier
      D floor).Nodup := by
  unfold slabObservablePairTargetSupportHighSpinProfileKeyCarrier
  apply cartesian_nodup
  · exact List.filter_sublist.nodup (range_nodup_local _)
  · exact range_nodup_local _

/-- Every source above the geometric floor lands in the total-mass/core
rectangle. -/
theorem slabObservablePairTargetSupportHighSpinProfileKey_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId floor : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId)
    (hfloor : floor <=
      slabObservablePairTargetSupportHighSpinProfileMass
        D rootFaceId targetFaceId htarget source) :
    slabObservablePairTargetSupportHighSpinProfileKey
        D rootFaceId targetFaceId htarget source ∈
      slabObservablePairTargetSupportHighSpinProfileKeyCarrier D floor := by
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · have htraceFloor : floor <=
        slabAcceptedPairedPeelTraceMass
          (slabObservablePairTargetSupportCanonicalPeeling
            D rootFaceId targetFaceId htarget source.1 source.2).2 := by
      rw [← slabObservablePairTargetSupportHighSpinProfileMass_eq_traceMass
        D rootFaceId targetFaceId htarget source]
      exact hfloor
    have hcanonical :=
      slabObservablePairTargetSupportCanonicalPeelingKey_mem
        D rootFaceId targetFaceId floor htarget source htraceFloor
    have hmass :=
      (mem_cartesian_iff _ _ _).mp hcanonical |>.1
    change slabObservablePairTargetSupportHighSpinProfileMass
        D rootFaceId targetFaceId htarget source ∈
      slabObservablePairedSupportPaidMasses D floor
    rw [slabObservablePairTargetSupportHighSpinProfileMass_eq_traceMass]
    change slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 ∈
      slabObservablePairedSupportPaidMasses D floor at hmass
    exact hmass
  · apply List.mem_range.mpr
    exact Nat.lt_succ_of_le
      (slabObservablePairTargetSupportCanonicalHighSpinProfile_core_le
        D rootFaceId targetFaceId htarget source.1 source.2)

/-! ## 3. One fixed terminal/total-mass/core fiber -/

/-- The fixed-counter theorem, reindexed by total mass and core mass while
retaining the full observable entropy carrier. -/
theorem slabObservablePairTargetSupportHighSpinProfile_fixedTerminalMassCore_weight_sum_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (mass core : Nat)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      slabObservablePairTargetSupportHighSpinProfileTerminal
        D rootFaceId targetFaceId htarget source = terminal)
    (hmass : forall source, source ∈ sources ->
      slabObservablePairTargetSupportHighSpinProfileMass
        D rootFaceId targetFaceId htarget source = mass)
    (hcore : forall source, source ∈ sources ->
      slabObservablePairTargetSupportHighSpinProfileCore
        D rootFaceId targetFaceId htarget source = core) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        sources <=
      (slabObservablePairedGlobalEntropyAnchorRatio ^ (mass - core) *
          slabObservablePairedGlobalCoreFactor ^ core) *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  apply
    slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalCounters_weight_sum_le
      D hw0 hw1 rootFaceId targetFaceId htarget terminal
        (mass - core) core sources hsources
  · intro source hsource
    exact hterminal source hsource
  · intro source hsource
    exact slabObservablePairTargetSupportHighSpinProfileExterior_eq_sub
      D rootFaceId targetFaceId htarget source mass core
        (hmass source hsource) (hcore source hsource)
  · intro source hsource
    exact hcore source hsource

/-! ## 4. Exact total-mass normalization -/

/-- The finite inflation paid by one truncated-core mass unit after extracting
the global geometric total-mass rate. -/
def slabObservablePairedGlobalCoreInflationBase : Q' :=
  Q'.ofNat 64000000

theorem slabObservablePairedGlobalCoreFactor_eqv_rate_mul_inflation :
    slabObservablePairedGlobalCoreFactor ≈
      slabObservablePairedGlobalEntropyAnchorRatio *
        slabObservablePairedGlobalCoreInflationBase := by
  unfold slabObservablePairedGlobalCoreFactor
    slabObservablePairedGlobalEntropyAnchorRatio
    slabObservablePairedGlobalCoreInflationBase
    slabObservablePairedGlobalEntropyBase
    anchorFaceCoefficient
  decide

private theorem mul_pow_eqv_local (left right : Q') : forall exponent : Nat,
    left ^ exponent * right ^ exponent ≈ (left * right) ^ exponent
  | 0 => Q'.one_mul_eqv 1
  | exponent + 1 => by
      refine Q'.eqv_trans _
        ((left * right) * (left ^ exponent * right ^ exponent)) _ ?_ ?_
      · exact YMGap.Continuum.PartitionUpperBound.mul_four_mid'
          left (left ^ exponent) right (right ^ exponent)
      · exact Q'.mul_eqv_congr_left (left * right) _ _
          (mul_pow_eqv_local left right exponent)

private theorem pow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : forall exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      simp only [Q'.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ h)
        (Q'.mul_eqv_congr_left _ _ _
          (pow_eqv_congr_local h exponent))

/-- Exact coefficient normalization at a realizable key. -/
theorem slabObservablePairedGlobalHighSpinProfileRate_eqv_totalMassCore
    (mass core : Nat) (hcore : core <= mass) :
    slabObservablePairedGlobalEntropyAnchorRatio ^ (mass - core) *
        slabObservablePairedGlobalCoreFactor ^ core ≈
      slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
        slabObservablePairedGlobalCoreInflationBase ^ core := by
  have hmass : (mass - core) + core = mass := by omega
  have hcoreFactor :=
    slabObservablePairedGlobalCoreFactor_eqv_rate_mul_inflation
  have hcorePower :
      slabObservablePairedGlobalCoreFactor ^ core ≈
        slabObservablePairedGlobalEntropyAnchorRatio ^ core *
          slabObservablePairedGlobalCoreInflationBase ^ core := by
    refine Q'.eqv_trans _
      ((slabObservablePairedGlobalEntropyAnchorRatio *
          slabObservablePairedGlobalCoreInflationBase) ^ core) _ ?_ ?_
    · exact pow_eqv_congr_local hcoreFactor core
    · exact Q'.eqv_symm
        (mul_pow_eqv_local slabObservablePairedGlobalEntropyAnchorRatio
          slabObservablePairedGlobalCoreInflationBase core)
  refine Q'.eqv_trans _
    (slabObservablePairedGlobalEntropyAnchorRatio ^ (mass - core) *
      (slabObservablePairedGlobalEntropyAnchorRatio ^ core *
        slabObservablePairedGlobalCoreInflationBase ^ core)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hcorePower
  refine Q'.eqv_trans _
    ((slabObservablePairedGlobalEntropyAnchorRatio ^ (mass - core) *
        slabObservablePairedGlobalEntropyAnchorRatio ^ core) *
      slabObservablePairedGlobalCoreInflationBase ^ core) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (slabObservablePairedGlobalEntropyAnchorRatio ^ (mass - core))
        (slabObservablePairedGlobalEntropyAnchorRatio ^ core)
        (slabObservablePairedGlobalCoreInflationBase ^ core))) ?_
  have hpow :
      slabObservablePairedGlobalEntropyAnchorRatio ^ (mass - core) *
          slabObservablePairedGlobalEntropyAnchorRatio ^ core ≈
        slabObservablePairedGlobalEntropyAnchorRatio ^ mass :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.pow_add_eqv slabObservablePairedGlobalEntropyAnchorRatio
          (mass - core) core))
      (Q'.eqv_of_eq
        (congrArg
          (fun exponent =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ exponent)
          hmass))
  exact Q'.mul_eqv_congr_right _ _ _ hpow

#print axioms slabObservablePairTargetSupportHighSpinProfileMass_eq_traceMass
#print axioms slabObservablePairTargetSupportHighSpinProfileExterior_eq_sub
#print axioms slabObservablePairTargetSupportHighSpinProfileKeyCarrier_nodup
#print axioms slabObservablePairTargetSupportHighSpinProfileKey_mem
#print axioms slabObservablePairTargetSupportHighSpinProfile_fixedTerminalMassCore_weight_sum_le
#print axioms slabObservablePairedGlobalCoreFactor_eqv_rate_mul_inflation
#print axioms slabObservablePairedGlobalHighSpinProfileRate_eqv_totalMassCore

end YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfilePartition
