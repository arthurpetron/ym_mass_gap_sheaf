/-
# A first resistance moment for BF4 off-ray root congestion

The resistance-flow compiler attaches the same load

    stationaryWeight(state) * pathResistance(state, vacuum)

to every directed edge of the selected simple path.  Because that path has
no repeated directed edge, one fixed edge receives at most this load from
each state.  Summing over the off-ray carrier therefore bounds every local
congestion by the first stationary resistance moment, without the extra path
length hidden in the total-occurrence traffic bound.

A cutoff-uniform bound on this scalar moment compiles to the existing
off-ray resistance-congestion certificate and, at every fixed subunit nome,
to the full cofinal posterior conditional-variance fraction using the already
proved arbitrary-spin ray.

No uniform moment bound is constructed here.  In particular, the analytic
summability estimate, physical scaling, continuum measure, OS/GNS
reconstruction, and Clay theorem remain open.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactExplicitRayOffRayResistanceGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem centralPhysicalFiniteWeight_nonnegative_local
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteWeight w hw K 0 state := by
  exact centralPhysicalRowMarginal_nonnegative hw K 0
    (centralPhysicalFiniteStateAt w hw K 0 state)

/-! ## 1. One state contributes to one directed edge at most once -/

theorem centralLowerExcitedSpinCubeOffRayRootPositivePath_directedEdges_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat)
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    (PositiveKernelChainIn.directedEdges
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)).Nodup := by
  unfold centralLowerExcitedSpinCubeOffRayRootPositivePath
  exact centralPhysicalFiniteVacuumSectorRootSimplePath_directedEdges_nodup
    w hw K 0 state (List.mem_filter.mp hstate).1

private theorem weightedDirectedEdgeLoad_constantMap_le_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (hnodup : edges.Nodup)
    (load : Q') (hload : (0 : Q') ≤ load)
    (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≤ load := by
  have heq : weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≈
      if (source, target) ∈ edges then load else 0 := by
    induction edges with
    | nil => exact Q'.eqv_refl 0
    | cons edge rest ih =>
        have hparts := List.nodup_cons.mp hnodup
        simp only [weightedDirectedEdgeLoad, List.map_cons, listQSum,
          weightedDirectedEdgeIndicator]
        by_cases hhead : edge = (source, target)
        · rw [if_pos hhead]
          have hnotmem : (source, target) ∉ rest := by
            intro hmem
            exact hparts.1 (hhead ▸ hmem)
          have hmem : (source, target) ∈ edge :: rest :=
            List.mem_cons.mpr (Or.inl hhead.symm)
          rw [if_pos hmem]
          have htail : weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0 :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then load else 0) _
              (ih hparts.2)
              (by rw [if_neg hnotmem]; exact Q'.eqv_refl 0)
          change load + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ load
          exact Q'.eqv_trans _ (load + 0) _
            (Q'.add_eqv_congr_left load _ _ htail)
            (Q'.eqv_of_eq (Q'.add_zero' load))
        · rw [if_neg hhead]
          have hne : (source, target) ≠ edge := fun hedge => hhead hedge.symm
          by_cases htailMem : (source, target) ∈ rest
          · have hmem : (source, target) ∈ edge :: rest :=
              List.mem_cons_of_mem edge htailMem
            rw [if_pos hmem]
            have htail : weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ load :=
              Q'.eqv_trans _
                (if (source, target) ∈ rest then load else 0) _
                (ih hparts.2)
                (by rw [if_pos htailMem]; exact Q'.eqv_refl load)
            change 0 + weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ load
            exact Q'.eqv_trans _ (0 + load) _
              (Q'.add_eqv_congr_left 0 _ _ htail)
              (Q'.eqv_of_eq (Q'.zero_add' load))
          · have hnotmem : (source, target) ∉ edge :: rest := by
              intro hmem
              rcases List.mem_cons.mp hmem with hedge | hrest
              · exact hne hedge
              · exact htailMem hrest
            rw [if_neg hnotmem]
            have htail : weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ 0 :=
              Q'.eqv_trans _
                (if (source, target) ∈ rest then load else 0) _
                (ih hparts.2)
                (by rw [if_neg htailMem]; exact Q'.eqv_refl 0)
            change 0 + weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ 0
            exact Q'.eqv_trans _ (0 + 0) _
              (Q'.add_eqv_congr_left 0 _ _ htail)
              (Q'.eqv_of_eq (Q'.zero_add' 0))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
  by_cases hmem : (source, target) ∈ edges
  · rw [if_pos hmem]
    exact Q'.le_refl' load
  · rw [if_neg hmem]
    exact hload

/-! ## 2. The first stationary resistance moment -/

def centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : Q' :=
  if hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K then
    centralPhysicalFiniteWeight w hw K 0 state *
      PositiveKernelChainIn.resistance
        (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)
  else 0

theorem centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w hw K state := by
  unfold centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
  by_cases hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K
  · rw [dif_pos hstate]
    exact Q'.mul_nonneg _ _
      (centralPhysicalFiniteWeight_nonnegative_local w hw K state)
      (PositiveKernelChainIn.resistance_nonnegative
        (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate))
  · rw [dif_neg hstate]
    exact Q'.le_refl' 0

theorem centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathLoad_le_stateLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K state source target : Nat) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
          w hw K state)
        source target ≤
      centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w hw K state := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
  by_cases hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K
  · rw [dif_pos hstate, dif_pos hstate]
    let path := centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate
    let load := centralPhysicalFiniteWeight w hw K 0 state *
      PositiveKernelChainIn.resistance path
    have hload0 : (0 : Q') ≤ load :=
      Q'.mul_nonneg _ _
        (centralPhysicalFiniteWeight_nonnegative_local w hw K state)
        (PositiveKernelChainIn.resistance_nonnegative path)
    exact weightedDirectedEdgeLoad_constantMap_le_local
      (PositiveKernelChainIn.directedEdges path)
      (centralLowerExcitedSpinCubeOffRayRootPositivePath_directedEdges_nodup
        w hw K state hstate)
      load hload0 source target
  · rw [dif_neg hstate, dif_neg hstate]
    exact Q'.le_refl' 0

/-- Sum of `stationaryWeight * selectedPathResistance` over the literal
off-ray carrier. -/
def centralLowerExcitedSpinCubeOffRayRootResistanceMoment
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
    (centralLowerExcitedSpinCubeOffRayIndices w hw K)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceMoment_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceMoment w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceMoment
  apply listQSum_nonnegative_on
  intro state _hstate
  exact centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_nonnegative
    w hw K state

theorem centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_stateLoadSum
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target ≈
      listQSum
        (fun state =>
          weightedDirectedEdgeLoad
            (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
              w hw K state)
            source target)
        (centralLowerExcitedSpinCubeOffRayIndices w hw K) := by
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowOccurrences
    weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

/-- Every local directed-edge congestion is bounded by the first resistance
moment.  Unlike the total-traffic bound, this estimate does not multiply one
state's load by the length of its simple path. -/
theorem centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_moment
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w hw K source target ≤
      centralLowerExcitedSpinCubeOffRayRootResistanceMoment w hw K := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_stateLoadSum
        w hw K source target))
    (by
      unfold centralLowerExcitedSpinCubeOffRayRootResistanceMoment
      apply listQSum_mono
      intro state _hstate
      exact
        centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathLoad_le_stateLoad
          w hw K state source target)

/-! ## 3. A scalar cofinal moment bound reaches the full gap compiler -/

/-- A scalar first-resistance-moment bound, uniform beyond one representation
cutoff.  This is a sufficient analytic producer, not an inhabitant. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  bound : Q'
  bound_nonnegative : (0 : Q') ≤ bound
  moment_le : ∀ K, start ≤ K →
    centralLowerExcitedSpinCubeOffRayRootResistanceMoment
        w (Q'.le_of_lt hw) K ≤ bound

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound

/-- A uniform first-moment estimate implies the exact pointwise resistance-
congestion certificate. -/
def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw where
  start := family.start
  bound := family.bound
  bound_nonnegative := family.bound_nonnegative
  flowLoad_le := fun K hK source target =>
    Q'.le_trans' _ _ _
      (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_moment
        w (Q'.le_of_lt hw) K source target)
      (family.moment_le K hK)

/-- At a fixed subunit nome, the scalar moment bound compiles through the
proved arbitrary-spin ray to the full cofinal posterior-variance fraction. -/
def toConditionalVarianceFraction
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound hw0) :=
  fixedNomeMassExactExplicitRayOffRayResistanceConditionalVarianceFraction
    hw0 hw1 family.toResistanceCongestionBound

end FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound

#print axioms centralLowerExcitedSpinCubeOffRayRootPositivePath_directedEdges_nodup
#print axioms centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathLoad_le_stateLoad
#print axioms centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_le_moment
#print axioms
  FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound.toResistanceCongestionBound
#print axioms
  FixedNomeCofinalSpinCubeOffRayRootResistanceMomentBound.toConditionalVarianceFraction

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
