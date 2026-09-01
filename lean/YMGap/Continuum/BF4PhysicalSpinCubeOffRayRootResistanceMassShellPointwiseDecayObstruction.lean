/-
# Shell-local obstruction to pointwise BF4 resistance-load decay

The exact row identity implies that every nonzero off-ray source pays at
least one unit of stationary-weight times canonical-path resistance.  Every
literal directed-edge user is automatically nonzero, so this module
transports that lower bound unconditionally to the physical-mass edge-user
shells and to both pointwise-decay interfaces.

Consequently, an upper envelope `L * q^mass` can hold on a nonzero occupied
shell only while it remains at least one.  In particular, geometric
stationary decay cannot by itself overcome the reciprocal-kernel resistance
on arbitrarily high occupied shells.  Closing the localized congestion route
therefore requires a uniform edge-user truncation/bounded-sharing theorem or
a different routing mechanism; no such theorem is claimed here.

No continuum or Clay conclusion is asserted.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction
open YMGap.Continuum.FiniteBoolGraphSimplePaths

/-! ## 1. Every literal shell member is nonzero and costs at least one -/

private theorem positiveKernelChainIn_last_mem_vertices
    {State : Type} {kernel : State → State → Q'} {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      last ∈ PositiveKernelChainIn.vertices path
  | _, _, PositiveKernelChainIn.refl state => List.mem_cons_self
  | first, _last, PositiveKernelChainIn.step _positive _nextMem rest =>
      List.mem_cons_of_mem first
        (positiveKernelChainIn_last_mem_vertices rest)

private theorem positiveKernelChainIn_directedEdges_eq_nil_of_self_of_vertices_nodup
    {State : Type} {kernel : State → State → Q'} {support : List State} :
    ∀ {first last : State}
      (path : PositiveKernelChainIn kernel support first last),
      first = last →
      (PositiveKernelChainIn.vertices path).Nodup →
      PositiveKernelChainIn.directedEdges path = []
  | _, _, PositiveKernelChainIn.refl _, _, _ => rfl
  | first, last, PositiveKernelChainIn.step _positive _nextMem rest,
      heq, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have hlast : last ∈ PositiveKernelChainIn.vertices rest :=
        positiveKernelChainIn_last_mem_vertices rest
      have hfirst : first ∈ PositiveKernelChainIn.vertices rest := by
        rw [heq]
        exact hlast
      exact False.elim (hparts.1 hfirst)

private theorem centralLowerExcitedSpinCubeOffRayRootPositivePath_vertices_nodup
    {w : Q'} {hw : (0 : Q') ≤ w} {K state : Nat}
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    (PositiveKernelChainIn.vertices
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)).Nodup := by
  unfold centralLowerExcitedSpinCubeOffRayRootPositivePath
    centralPhysicalFiniteVacuumSectorSimplePositivePath
  rw [PositiveKernelChainIn.vertices_ofSupportedWalk]
  exact
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w hw K 0 state 0 (List.mem_filter.mp hstate).1
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)).nodup

theorem centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellState_ne_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target shell state : Nat}
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell) :
    state ≠ 0 := by
  have hedgeState := (List.mem_filter.mp hstate).1
  obtain ⟨hoffRay, hedge⟩ :=
    mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hedgeState
  intro heq
  have hnil :=
    positiveKernelChainIn_directedEdges_eq_nil_of_self_of_vertices_nodup
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hoffRay)
      heq
      (centralLowerExcitedSpinCubeOffRayRootPositivePath_vertices_nodup hoffRay)
  rw [hnil] at hedge
  exact List.not_mem_nil hedge

theorem one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target shell state : Nat}
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell) :
    (1 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w hw K state := by
  have hedge := (List.mem_filter.mp hstate).1
  obtain ⟨hoffRay, _hedge⟩ :=
    mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hedge
  exact one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w hw K state hoffRay
      (centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellState_ne_zero
        hstate)

/-! ## 2. Necessary lower bounds on every proposed decay envelope -/

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay

theorem one_le_decayEnvelope_of_shell_member
    {w : Q'} {hw : (0 : Q') < w}
    (decay :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
        hw)
    (K : Nat) (hK : decay.start ≤ K)
    (source target shell state : Nat)
    (hshell : shell <
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        w (Q'.le_of_lt hw) K)
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w (Q'.le_of_lt hw) K source target shell) :
    (1 : Q') ≤ decay.loadAmplitude * decay.loadRatio ^ shell := by
  exact Q'.le_trans' _
    (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
      w (Q'.le_of_lt hw) K state) _
    (one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
      hstate)
    (decay.stateLoad_le K hK source target shell state hshell hstate)

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay

theorem one_le_factorizedEnvelope_of_shell_member
    {w : Q'} {hw : (0 : Q') < w}
    (factorized :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay
        hw)
    (K : Nat) (hK : factorized.start ≤ K)
    (source target shell state : Nat)
    (hshell : shell <
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        w (Q'.le_of_lt hw) K)
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w (Q'.le_of_lt hw) K source target shell) :
    (1 : Q') ≤
      (factorized.stationaryAmplitude * factorized.resistanceAmplitude) *
        (factorized.stationaryRatio * factorized.resistanceRatio) ^ shell := by
  exact
    YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.one_le_decayEnvelope_of_shell_member
      factorized.toPhysicalMassStateLoadDecay
      K hK source target shell state hshell hstate

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellState_ne_zero
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.one_le_decayEnvelope_of_shell_member
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay.one_le_factorizedEnvelope_of_shell_member
