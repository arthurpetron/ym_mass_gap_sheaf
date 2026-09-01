/-
# Physical-mass shells for the BF4 off-ray root resistance load

Canonical simple-path length is a valid finite partition statistic, but the
generic component-search path is not known to descend in physical spin mass.
This module replaces that statistic by the literal total twice-spin mass of
the source configuration.  For a fixed directed edge, the actual off-ray
edge-user states are partitioned exactly by that physical mass.

The remaining analytic input is separated into a physical-mass entropy bound
and a pointwise stationary-resistance decay bound on the same literal shell.
If their product ratio is below one, constructive finite summation compiles
them to the existing off-ray congestion certificate and, with any cofinal ray
capacity, to the full simple-routing certificate.

No entropy or decay estimate is inhabited here.  In particular, the
pointwise bound must still control the resistance of the selected canonical
path.  No continuum or Clay conclusion is asserted.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal physical mass and its finite shell range -/

/-- Total twice-spin mass on the actual corrected-slab physical faces of the
indexed lower-half BF4 state. -/
def centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : Nat :=
  listNatWeight
    (centralPhysicalFiniteStateAt w hw K 0 state)
    (slabPhysicalFaceEdges (centralExtent 0))

private def listNatMax : List Nat → Nat
  | [] => 0
  | head :: tail => max head (listNatMax tail)

private theorem le_listNatMax_of_mem :
    ∀ {value : Nat} {values : List Nat},
      value ∈ values → value ≤ listNatMax values
  | _, [], hmem => absurd hmem List.not_mem_nil
  | value, head :: tail, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        exact Nat.le_max_left _ _
      · exact Nat.le_trans
          (le_listNatMax_of_mem htail)
          (Nat.le_max_right _ _)

/-- One plus the largest literal physical mass in the full off-ray carrier.
This is an exact finite range, not a claimed cutoff-uniform bound. -/
def centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Nat :=
  listNatMax
      ((centralLowerExcitedSpinCubeOffRayIndices w hw K).map
        (centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass w hw K)) + 1

theorem centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass_lt_shellCount
    {w : Q'} {hw : (0 : Q') ≤ w} {K state : Nat}
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass w hw K state <
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount w hw K := by
  have hmem : centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
      w hw K state ∈
      (centralLowerExcitedSpinCubeOffRayIndices w hw K).map
        (centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass w hw K) :=
    List.mem_map.mpr ⟨state, hstate, rfl⟩
  have hle := le_listNatMax_of_mem hmem
  unfold centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
  omega

/-! ## 2. Exact edge-user mass shells -/

def centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
    (w : Q') (hw : (0 : Q') ≤ w)
    (K source target shell : Nat) : List Nat :=
  (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
      w hw K source target).filter
    (fun state => decide
      (centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
        w hw K state = shell))

def centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
    (w : Q') (hw : (0 : Q') ≤ w)
    (K source target shell : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
    (centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
      w hw K source target shell)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail_eqv_physicalMassShellSum
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
        w hw K source target ≈
      listQSum
        (centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
          w hw K source target)
        (List.range
          (centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
            w hw K)) := by
  let items := centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
    w hw K source target
  let value := centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w hw K
  let shell := centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass w hw K
  let bound := centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
    w hw K
  have hshellBound : ∀ state, state ∈ items → shell state < bound := by
    intro state hstate
    have hparts :=
      mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hstate
    exact
      centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass_lt_shellCount
        hparts.1
  have hpartition :=
    listQSum_shell_partition value shell items bound hshellBound
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
    centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
  exact Q'.eqv_symm hpartition

/-! ## 3. Factorized physical-mass shell input and compiler -/

/-- Separate entropy and pointwise stationary-resistance bounds on the literal
physical-mass shell of users of a fixed directed edge. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  entropyAmplitude : Q'
  entropyBase : Q'
  loadAmplitude : Q'
  loadRatio : Q'
  budget : Q'
  entropyAmplitude_nonnegative : (0 : Q') ≤ entropyAmplitude
  entropyBase_nonnegative : (0 : Q') ≤ entropyBase
  loadAmplitude_nonnegative : (0 : Q') ≤ loadAmplitude
  loadRatio_nonnegative : (0 : Q') ≤ loadRatio
  combinedRatio_lt_one : entropyBase * loadRatio < (1 : Q')
  budget_nonnegative : (0 : Q') ≤ budget
  geometric_step :
    entropyAmplitude * loadAmplitude +
        (entropyBase * loadRatio) * budget ≤ budget
  shellCardinality_le : ∀ K, start ≤ K → ∀ source target (shell : Nat),
    shell < centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
      w (Q'.le_of_lt hw) K →
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
          w (Q'.le_of_lt hw) K source target shell).length ≤
      entropyAmplitude * entropyBase ^ shell
  stateLoad_le : ∀ K, start ≤ K → ∀ source target (shell state : Nat),
    shell < centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
      w (Q'.le_of_lt hw) K →
    state ∈ centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
      w (Q'.le_of_lt hw) K source target shell →
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w (Q'.le_of_lt hw) K state ≤
      loadAmplitude * loadRatio ^ shell

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound

theorem shellLoad_le_combined
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound hw)
    (K : Nat) (hK : family.start ≤ K) (source target shell : Nat)
    (hshell : shell <
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        w (Q'.le_of_lt hw) K) :
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
        w (Q'.le_of_lt hw) K source target shell ≤
      (family.entropyAmplitude * family.loadAmplitude) *
        (family.entropyBase * family.loadRatio) ^ shell := by
  let states :=
    centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
      w (Q'.le_of_lt hw) K source target shell
  let value :=
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
      w (Q'.le_of_lt hw) K
  let pointBound := family.loadAmplitude * family.loadRatio ^ shell
  have hpointBound0 : (0 : Q') ≤ pointBound := by
    exact Q'.mul_nonneg _ _ family.loadAmplitude_nonnegative
      (Q'.pow_nonneg family.loadRatio family.loadRatio_nonnegative shell)
  have hsum : listQSum value states ≤
      Q'.ofNat states.length * pointBound := by
    apply listQSum_le_length_mul_of_bound value hpointBound0 states
    intro state hstate
    exact family.stateLoad_le K hK source target shell state hshell hstate
  have hcardinality : Q'.ofNat states.length ≤
      family.entropyAmplitude * family.entropyBase ^ shell := by
    exact family.shellCardinality_le K hK source target shell hshell
  have hscaled : Q'.ofNat states.length * pointBound ≤
      (family.entropyAmplitude * family.entropyBase ^ shell) *
        pointBound :=
    Q'.mul_le_mul_of_nonneg_right _ _ pointBound
      hcardinality hpointBound0
  have hfactor :
      (family.entropyAmplitude * family.entropyBase ^ shell) *
          pointBound ≈
        (family.entropyAmplitude * family.loadAmplitude) *
          (family.entropyBase * family.loadRatio) ^ shell := by
    unfold pointBound
    calc
      (family.entropyAmplitude * family.entropyBase ^ shell) *
            (family.loadAmplitude * family.loadRatio ^ shell) ≈
          family.entropyAmplitude *
            (family.entropyBase ^ shell *
              (family.loadAmplitude * family.loadRatio ^ shell)) :=
        Q'.mul_assoc_eqv _ _ _
      _ ≈ family.entropyAmplitude *
            ((family.entropyBase ^ shell * family.loadAmplitude) *
              family.loadRatio ^ shell) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      _ ≈ family.entropyAmplitude *
            ((family.loadAmplitude * family.entropyBase ^ shell) *
              family.loadRatio ^ shell) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_comm_eqv _ _))
      _ ≈ family.entropyAmplitude *
            (family.loadAmplitude *
              (family.entropyBase ^ shell * family.loadRatio ^ shell)) :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_assoc_eqv _ _ _)
      _ ≈ (family.entropyAmplitude * family.loadAmplitude) *
            (family.entropyBase ^ shell * family.loadRatio ^ shell) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      _ ≈ (family.entropyAmplitude * family.loadAmplitude) *
            (family.entropyBase * family.loadRatio) ^ shell :=
        Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (mul_pow_eqv family.entropyBase family.loadRatio shell))
  unfold
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfactor))

theorem flowLoad_le_budget
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K source target ≤ family.budget := by
  let count := centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
    w (Q'.le_of_lt hw) K
  let shellLoad :=
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgePhysicalMassShellLoad
      w (Q'.le_of_lt hw) K source target
  let geometric : Nat → Q' := fun shell =>
    (family.entropyAmplitude * family.loadAmplitude) *
      (family.entropyBase * family.loadRatio) ^ shell
  have hflow :=
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
      w (Q'.le_of_lt hw) K source target
  have hpartition :=
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail_eqv_physicalMassShellSum
      w (Q'.le_of_lt hw) K source target
  have hshell : listQSum shellLoad (List.range count) ≤
      listQSum geometric (List.range count) := by
    apply listQSum_mono
    intro shell hshell
    exact family.shellLoad_le_combined K hK source target shell
      (List.mem_range.mp hshell)
  have hgeometric : listQSum geometric (List.range count) ≈
      finSum geometric count :=
    listQSum_range_eqv_finSum geometric count
  have hbudget : finSum geometric count ≤ family.budget :=
    geometric_tail_closure
      (family.entropyAmplitude * family.loadAmplitude)
      (family.entropyBase * family.loadRatio) family.budget
      (Q'.mul_nonneg _ _ family.entropyBase_nonnegative
        family.loadRatio_nonnegative)
      family.budget_nonnegative family.geometric_step count
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hflow hpartition))
    (Q'.le_trans' _ _ _ hshell
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hgeometric) hbudget))

def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw where
  start := family.start
  bound := family.budget
  bound_nonnegative := family.budget_nonnegative
  flowLoad_le := family.flowLoad_le_budget

/-- Physical-mass entropy and pointwise load decay, together with any cofinal
ray capacity, construct the exact full-sector simple-routing certificate. -/
def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  fixedNomeCofinalSimpleRootResistanceCongestionBound_of_ray_offRay
    ray family.toResistanceCongestionBound

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell.centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass_lt_shellCount
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell.centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail_eqv_physicalMassShellSum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound.shellLoad_le_combined
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound.flowLoad_le_budget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound.toResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound.toSimpleRootResistanceCongestionBound
