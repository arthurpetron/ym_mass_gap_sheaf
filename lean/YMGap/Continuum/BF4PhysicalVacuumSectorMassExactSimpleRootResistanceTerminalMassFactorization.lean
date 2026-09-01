/-
# Exact stationary-mass factorization of BF4 terminal demand

The terminal-demand obstruction is a weighted statement, not intrinsically a
cardinality statement.  For any positive root routing, this module factors the
exact demand on a terminal edge `(source, 0)` as

  2 * (stationary mass of the actual terminal fiber)
      / kernel(source, 0).

Consequently every cofinal simple-routing congestion certificate uniformly
bounds this mass-to-conductance ratio on the actual normalized terminal
fibers.  The positive central-face raw-sharing compiler supplies the same
bound for its loop-erased routing, but this does not identify those normalized
fibers with the repaired raw face-zero fibers: a raw prefix may meet the
vacuum before its assigned terminal spoke, and loop erasure may then change
the final predecessor.

Thus the theorem below separates the necessary weighted normalized
obligation from the stronger raw-fiber cardinality hypothesis used by the
current sufficient compiler.  No uniform mass bound, congestion certificate,
finite gap, physical scaling, continuum theory, or Clay conclusion is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawTerminalFiber

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact mass carried by an actual terminal fiber -/

/-- Stationary mass of the states whose selected root path actually ends
through `(source, 0)`.  The fiber belongs to the supplied routing; in
particular, for a loop-erased routing it is not definitionally the raw
assignment fiber. -/
def centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteWeight w hw K 0)
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber routing source)

/-! ## 2. Terminal demand is exactly twice mass times reciprocal conductance -/

theorem terminalFiberResistanceDemand_eqv_mass_mul_reciprocal_add_self
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw K 0 source 0) :
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand
        routing source hpositive ≈
      let mass :=
        centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
          routing source
      let reciprocal :=
        Q'.recipPos
          (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
      mass * reciprocal + mass * reciprocal := by
  let weight := centralPhysicalFiniteWeight w hw K 0
  let fiber :=
    centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiber routing source
  let reciprocal :=
    Q'.recipPos
      (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
  change
    listQSum
        (fun state =>
          weight state * reciprocal + weight state * reciprocal)
        fiber ≈
      listQSum weight fiber * reciprocal +
        listQSum weight fiber * reciprocal
  exact Q'.eqv_trans _ _ _
    (listQSum_add
      (fun state => weight state * reciprocal)
      (fun state => weight state * reciprocal)
      fiber)
    (Q'.add_eqv_congr'
      (listQSum_mul_right weight reciprocal fiber)
      (listQSum_mul_right weight reciprocal fiber))

/-- The exact stationary-mass-to-conductance quantity is a necessary lower
bound on the routed flow load of the actual terminal edge. -/
theorem terminalFiberStationaryMassReciprocal_le_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw K 0 source 0) :
    let mass :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        routing source
    let reciprocal :=
      Q'.recipPos
        (centralPhysicalFiniteKernel w hw K 0 source 0) hpositive
    mass * reciprocal + mass * reciprocal ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        routing source 0 := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (terminalFiberResistanceDemand_eqv_mass_mul_reciprocal_add_self
          routing source hpositive)))
    (centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberResistanceDemand_le_flowLoad
      routing source hpositive)

/-! ## 3. Every cofinal congestion certificate pays the same quantity -/

namespace FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound

theorem terminalFiberStationaryMassReciprocal_le_bound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
        hw)
    (K : Nat) (hK : family.start ≤ K) (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0) :
    let routing := family.routing K hK
    let mass :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        routing source
    let reciprocal :=
      Q'.recipPos
        (centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source 0) hpositive
    mass * reciprocal + mass * reciprocal ≤ family.bound := by
  exact Q'.le_trans' _ _ _
    (terminalFiberStationaryMassReciprocal_le_flowLoad
      (family.routing K hK) source hpositive)
    (family.flowLoad_le K hK source 0)

end FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound

/-! ## 4. The current raw compiler bounds normalized, not raw-label, fibers -/

namespace FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad

theorem normalizedTerminalFiberStationaryMassReciprocal_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad hw)
    (K : Nat) (hK : family.start ≤ K) (source : Nat)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 source 0) :
    let routing :=
      simplePositiveCentralFaceRouting hw K
        (Nat.le_trans family.start_positive hK)
    let mass :=
      centralPhysicalFiniteVacuumSectorSimpleRootTerminalFiberStationaryMass
        routing source
    let reciprocal :=
      Q'.recipPos
        (centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source 0) hpositive
    mass * reciprocal + mass * reciprocal ≤
      family.sharingBound * family.stateLoadBound := by
  exact Q'.le_trans' _ _ _
    (terminalFiberStationaryMassReciprocal_le_flowLoad
      (simplePositiveCentralFaceRouting hw K
        (Nat.le_trans family.start_positive hK))
      source hpositive)
    (family.flowLoad_le_product K hK source 0)

end FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization.terminalFiberResistanceDemand_eqv_mass_mul_reciprocal_add_self
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization.terminalFiberStationaryMassReciprocal_le_flowLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization.FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound.terminalFiberStationaryMassReciprocal_le_bound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalMassFactorization.FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad.normalizedTerminalFiberStationaryMassReciprocal_le_product
