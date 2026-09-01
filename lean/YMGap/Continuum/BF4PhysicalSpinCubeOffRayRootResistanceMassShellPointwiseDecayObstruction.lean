/-
# Shell-local obstruction to pointwise BF4 resistance-load decay

The exact row identity implies that every nonzero off-ray source pays at
least one unit of stationary-weight times canonical-path resistance.  This
module transports that lower bound to the literal physical-mass edge-user
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
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMomentObstruction

/-! ## 1. Every nonzero literal shell member costs at least one -/

theorem one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target shell state : Nat}
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell)
    (hne : state ≠ 0) :
    (1 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w hw K state := by
  have hedge := (List.mem_filter.mp hstate).1
  obtain ⟨hoffRay, _hedge⟩ :=
    mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hedge
  exact one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w hw K state hoffRay hne

/-! ## 2. Necessary lower bounds on every proposed decay envelope -/

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay

theorem one_le_decayEnvelope_of_nonzero_shell_member
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
        w (Q'.le_of_lt hw) K source target shell)
    (hne : state ≠ 0) :
    (1 : Q') ≤ decay.loadAmplitude * decay.loadRatio ^ shell := by
  exact Q'.le_trans' _
    (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
      w (Q'.le_of_lt hw) K state) _
    (one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
      hstate hne)
    (decay.stateLoad_le K hK source target shell state hshell hstate)

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay

theorem one_le_factorizedEnvelope_of_nonzero_shell_member
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
        w (Q'.le_of_lt hw) K source target shell)
    (hne : state ≠ 0) :
    (1 : Q') ≤
      (factorized.stationaryAmplitude * factorized.resistanceAmplitude) *
        (factorized.stationaryRatio * factorized.resistanceRatio) ^ shell := by
  exact
    YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.one_le_decayEnvelope_of_nonzero_shell_member
      factorized.toPhysicalMassStateLoadDecay
      K hK source target shell state hshell hstate hne

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.one_le_centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_of_mem_physicalMassShell
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.one_le_decayEnvelope_of_nonzero_shell_member
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellPointwiseDecayObstruction.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay.one_le_factorizedEnvelope_of_nonzero_shell_member
