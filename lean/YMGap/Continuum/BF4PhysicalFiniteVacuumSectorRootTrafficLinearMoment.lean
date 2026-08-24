/-
# A first-length-moment ceiling for physical vacuum-root traffic

The raw total-traffic ceiling counts every directed occurrence of every root
path.  Since the loop-erased path attached to one state is vertex-simple, a
fixed directed edge occurs at most once on that path.  Consequently the local
root-flow load pays only

  sum_state 2 * weight(state) * pathLength(state),

not the corresponding second length moment hidden in total traffic.

This module proves that sharper coefficient-independent ceiling, constructs a
strictly positive finite capacity from it, and isolates one cofinal scalar
ratio whose inhabitant would compile through the existing root-capacity and
mass-floor machinery to the actual completed vacuum-sector contraction.

No cofinal ratio is inhabited here.  No thermodynamic/continuum limit,
continuum QFT, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → lower x ≤ upper x) →
      listQSum lower xs ≤ listQSum upper xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h =>
      Q'.add_le_add
        (h x List.mem_cons_self)
        (listQSum_mono_local lower upper xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-! ## 1. Every simple state path charges a directed edge at most once -/

private theorem directedEdges_ofSupportedWalk_local
    {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool)
    (kernel : State → State → Q') (support : List State)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      adjacent first next = true → (0 : Q') < kernel first next) :
    ∀ {first last : State} (hfirst : first ∈ support)
      (path : FiniteBoolGraphSimplePaths.Walk
        (supportedEdge adjacent support) first last),
      PositiveKernelChainIn.directedEdges
          (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
            adjacent kernel support edgePositive hfirst path) =
        FiniteBoolGraphSimplePaths.Walk.directedEdges path
  | _, _, _, FiniteBoolGraphSimplePaths.Walk.single _ => rfl
  | first, _, hfirst,
      FiniteBoolGraphSimplePaths.Walk.cons hedge rest => by
      have hparts := (Bool.and_eq_true _ _).mp hedge
      have hnext : rest.start ∈ support := of_decide_eq_true hparts.2
      simp only [
        BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk,
        PositiveKernelChainIn.directedEdges,
        FiniteBoolGraphSimplePaths.Walk.directedEdges]
      exact congrArg (List.cons (first, rest.start))
        (directedEdges_ofSupportedWalk_local
          adjacent kernel support edgePositive hnext rest)

theorem centralPhysicalFiniteVacuumSectorRootSimplePath_directedEdges_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    (PositiveKernelChainIn.directedEdges
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K half state 0 hstate
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w hw K half))).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorSimplePositivePath
  rw [directedEdges_ofSupportedWalk_local]
  exact FiniteBoolGraphSimplePaths.Walk.directedEdges_nodup_of_vertices_nodup
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w hw K half)).walk
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w hw K half)).nodup

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
          have hne : (source, target) ≠ edge := fun heq => hhead heq.symm
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

/-! ## 2. The first weighted path-length moment -/

/-- The doubled load contributed by one state before selecting a directed
edge.  It contains one, rather than two, powers of the root-path length. -/
def centralPhysicalFiniteVacuumSectorRootStateLinearLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K half state : Nat) : Q' :=
  if hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half then
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    let singleLoad := centralPhysicalFiniteWeight w hw K half state *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    singleLoad + singleLoad
  else 0

theorem centralPhysicalFiniteVacuumSectorRootStateLinearLoad_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half state : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorRootStateLinearLoad
      w hw K half state := by
  unfold centralPhysicalFiniteVacuumSectorRootStateLinearLoad
  by_cases hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half
  · rw [dif_pos hstate]
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    have hsingle : (0 : Q') ≤
        centralPhysicalFiniteWeight w hw K half state *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path) :=
      Q'.mul_nonneg _ _
        (centralPhysicalRowMarginal_nonnegative hw K half
          (centralPhysicalFiniteStateAt w hw K half state))
        (Q'.ofNat_le_ofNat (Nat.zero_le _))
    exact Q'.zero_le_add _ _ hsingle hsingle
  · rw [dif_neg hstate]
    exact Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorRootWeightedPathLoad_le_stateLinearLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K half state source target : Nat) :
    weightedDirectedEdgeLoad
        (centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
          w hw K half state) source target ≤
      centralPhysicalFiniteVacuumSectorRootStateLinearLoad
        w hw K half state := by
  unfold centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
    centralPhysicalFiniteVacuumSectorRootStateLinearLoad
  by_cases hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half
  · rw [dif_pos hstate, dif_pos hstate]
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K half state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K half)
    let singleLoad := centralPhysicalFiniteWeight w hw K half state *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    have hsingle : (0 : Q') ≤ singleLoad := by
      unfold singleLoad
      exact Q'.mul_nonneg _ _
        (centralPhysicalRowMarginal_nonnegative hw K half
          (centralPhysicalFiniteStateAt w hw K half state))
        (Q'.ofNat_le_ofNat (Nat.zero_le _))
    exact weightedDirectedEdgeLoad_constantMap_le_local
      (PositiveKernelChainIn.directedEdges path)
      (centralPhysicalFiniteVacuumSectorRootSimplePath_directedEdges_nodup
        w hw K half state hstate)
      (singleLoad + singleLoad)
      (Q'.zero_le_add _ _ hsingle hsingle) source target
  · rw [dif_neg hstate, dif_neg hstate]
    exact Q'.le_refl' 0

/-- The exact doubled first weighted path-length moment. -/
def centralPhysicalFiniteVacuumSectorRootLinearMoment
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteVacuumSectorRootStateLinearLoad w hw K half)
    (centralPhysicalFiniteVacuumSectorIndices w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootLinearMoment_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorRootLinearMoment
      w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootLinearMoment
  exact listQSum_nonnegative_on _ _
    (fun state _ =>
      centralPhysicalFiniteVacuumSectorRootStateLinearLoad_nonnegative
        w hw K half state)

theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_eqv_statePathLoadSum
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootFlowLoad
        w hw K half source target ≈
      listQSum
        (fun state => weightedDirectedEdgeLoad
          (centralPhysicalFiniteVacuumSectorRootWeightedPathOccurrences
            w hw K half state) source target)
        (centralPhysicalFiniteVacuumSectorIndices w hw K half) := by
  unfold centralPhysicalFiniteVacuumSectorRootFlowLoad
    centralPhysicalFiniteVacuumSectorRootFlowOccurrences
    weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

/-- Every local directed root-flow load is bounded by the first weighted
path-length moment. -/
theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_le_linearMoment
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootFlowLoad
        w hw K half source target ≤
      centralPhysicalFiniteVacuumSectorRootLinearMoment w hw K half := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralPhysicalFiniteVacuumSectorRootFlowLoad_eqv_statePathLoadSum
        w hw K half source target))
    (by
      unfold centralPhysicalFiniteVacuumSectorRootLinearMoment
      apply listQSum_mono_local
      intro state _hstate
      exact
        centralPhysicalFiniteVacuumSectorRootWeightedPathLoad_le_stateLinearLoad
          w hw K half state source target)

def centralPhysicalFiniteVacuumSectorRootLinearCost
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorRootLinearMoment w hw K half

theorem centralPhysicalFiniteVacuumSectorRootLinearCost_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorRootLinearCost
      w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootLinearCost
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorRootLinearMoment_nonnegative
      w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_le_linearCost
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootFlowLoad
        w hw K half source target ≤
      centralPhysicalFiniteVacuumSectorRootLinearCost w hw K half := by
  have hload :=
    centralPhysicalFiniteVacuumSectorRootFlowLoad_le_linearMoment
      w hw K half source target
  have hpad : centralPhysicalFiniteVacuumSectorRootLinearMoment w hw K half ≤
      centralPhysicalFiniteVacuumSectorRootLinearCost w hw K half := by
    unfold centralPhysicalFiniteVacuumSectorRootLinearCost
    have hadd := Q'.add_le_add_right (0 : Q') 1
      (centralPhysicalFiniteVacuumSectorRootLinearMoment w hw K half)
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hload hpad

/-! ## 3. The linear scalar ratio compiles to local root capacity -/

structure CentralPhysicalFiniteVacuumSectorRootLinearRatioAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Type 1 where
  delta : Q'
  delta_pos : (0 : Q') < delta
  ratio_bound :
    delta * centralPhysicalFiniteVacuumSectorRootLinearCost
        w (Q'.le_of_lt hw) K half ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K half

namespace CentralPhysicalFiniteVacuumSectorRootLinearRatioAt

def toRootTrafficCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (ratio : CentralPhysicalFiniteVacuumSectorRootLinearRatioAt hw K half) :
    CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt hw K half where
  delta := ratio.delta
  delta_pos := ratio.delta_pos
  edge_capacity := fun source hsource target htarget => by
    let load := centralPhysicalFiniteVacuumSectorRootFlowLoad
      w (Q'.le_of_lt hw) K half source target
    have hload0 : (0 : Q') ≤ load :=
      centralPhysicalFiniteVacuumSectorRootFlowLoad_nonnegative
        w (Q'.le_of_lt hw) K half source target
    by_cases hloadPos : (0 : Q') < load
    · have hloadCost : load ≤
          centralPhysicalFiniteVacuumSectorRootLinearCost
            w (Q'.le_of_lt hw) K half :=
        centralPhysicalFiniteVacuumSectorRootFlowLoad_le_linearCost
          w (Q'.le_of_lt hw) K half source target
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ ratio.delta
        hloadCost (Q'.le_of_lt ratio.delta_pos)
      have hkernelPos :=
        centralPhysicalFiniteVacuumSectorRootFlowLoad_pos_implies_kernel_pos
          hw K half source target hloadPos
      have hfloor :=
        centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
          w (Q'.le_of_lt hw) K half source target
          hsource htarget hkernelPos
      exact Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ ratio.ratio_bound hfloor)
    · have hloadNonpos : load ≤ 0 := q_nonpos_of_not_pos_local hloadPos
      have hloadZero : load ≈ 0 := Q'.eqv_of_le_le hloadNonpos hload0
      have hkernel0 : (0 : Q') ≤ centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K half source target := by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K half _ _
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv
          (Q'.eqv_trans _ (ratio.delta * 0) _
            (Q'.mul_eqv_congr_left ratio.delta _ _ hloadZero)
            (Q'.mul_zero_eqv ratio.delta)))
        hkernel0

end CentralPhysicalFiniteVacuumSectorRootLinearRatioAt

/-! ## 4. A positive finite ratio and the exact cofinal frontier -/

def centralPhysicalFiniteVacuumSectorRootLinearDelta
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorRootLinearCost
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorRootLinearCost_pos
      w (Q'.le_of_lt hw) K half)

theorem centralPhysicalFiniteVacuumSectorRootLinearDelta_pos
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorRootLinearDelta hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootLinearDelta
  exact Q'.divPos_pos _ _ _
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      w (Q'.le_of_lt hw) K half)

def centralPhysicalFiniteVacuumSectorRootFiniteLinearRatioAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    CentralPhysicalFiniteVacuumSectorRootLinearRatioAt hw K half where
  delta := centralPhysicalFiniteVacuumSectorRootLinearDelta hw K half
  delta_pos := centralPhysicalFiniteVacuumSectorRootLinearDelta_pos hw K half
  ratio_bound := by
    exact Q'.le_of_eqv
      (Q'.divPos_mul_eqv
        (centralPhysicalFiniteVacuumSectorEdgeFloor
          w (Q'.le_of_lt hw) K half)
        (centralPhysicalFiniteVacuumSectorRootLinearCost
          w (Q'.le_of_lt hw) K half)
        (centralPhysicalFiniteVacuumSectorRootLinearCost_pos
          w (Q'.le_of_lt hw) K half))

/-- One common scalar comparison between the first length moment and the
minimum used edge implies the exact cofinal local root capacity. -/
structure FixedNomeCofinalVacuumRootLinearRatio
    {w : Q'} (hw : (0 : Q') < w) (half : Nat) : Type 1 where
  start : Nat
  delta : Q'
  delta_pos : (0 : Q') < delta
  ratio_bound : ∀ K, start ≤ K →
    delta * centralPhysicalFiniteVacuumSectorRootLinearCost
        w (Q'.le_of_lt hw) K half ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K half

namespace FixedNomeCofinalVacuumRootLinearRatio

def toRootTrafficCapacity
    {w : Q'} {hw : (0 : Q') < w} {half : Nat}
    (family : FixedNomeCofinalVacuumRootLinearRatio hw half) :
    FixedNomeCofinalVacuumRootTrafficCapacity hw half where
  start := family.start
  delta := family.delta
  delta_pos := family.delta_pos
  edge_capacity := fun K hK => by
    let ratio : CentralPhysicalFiniteVacuumSectorRootLinearRatioAt hw K half :=
      { delta := family.delta
        delta_pos := family.delta_pos
        ratio_bound := family.ratio_bound K hK }
    exact
      (@CentralPhysicalFiniteVacuumSectorRootLinearRatioAt.toRootTrafficCapacityAt
        w hw K half ratio).edge_capacity

/-- The first-length-moment scalar frontier reaches the actual completed
physical vacuum-sector contraction through the already closed compiler path. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (family : FixedNomeCofinalVacuumRootLinearRatio hw0 half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap.FixedNomeCofinalVacuumRootTrafficCapacity.toCompletedStrictContractionData
    hw0 hw1 half family.toRootTrafficCapacity

end FixedNomeCofinalVacuumRootLinearRatio

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.centralPhysicalFiniteVacuumSectorRootSimplePath_directedEdges_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.centralPhysicalFiniteVacuumSectorRootWeightedPathLoad_le_stateLinearLoad
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.centralPhysicalFiniteVacuumSectorRootFlowLoad_le_linearMoment
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.CentralPhysicalFiniteVacuumSectorRootLinearRatioAt.toRootTrafficCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.centralPhysicalFiniteVacuumSectorRootFiniteLinearRatioAt
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.FixedNomeCofinalVacuumRootLinearRatio.toRootTrafficCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.FixedNomeCofinalVacuumRootLinearRatio.toCompletedStrictContractionData
