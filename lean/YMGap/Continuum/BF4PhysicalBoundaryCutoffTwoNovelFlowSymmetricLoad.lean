/-
# Orientation-free load for the cutoff-two novel BF4 flow

The literal novel canonical flow is directed, and the preceding obstruction
shows that it necessarily contains positive occurrences sourced at genuinely
new states.  This module removes the inessential orientation asymmetry at the
level where the Poincare form is consumed.

For every directed edge, average its load with the load of the reverse edge.
The averaged load is symmetric.  Because the finite Dirichlet form sums both
orientations and the squared coefficient difference is symmetric, this
averaging preserves the loaded Dirichlet form exactly.  Thus it also preserves
the proved novel pairwise-variance bound.

The allocated physical kernel is symmetric on the retained carrier.  Hence a
capacity comparison for an old-to-new edge pays the reverse new-to-old edge
automatically.  The remaining oriented certificate has only old--old,
old-to-new, and new--new fields; no new-to-old field is needed.  This removes
the new-source obstruction for cross-block edges, but it does not control
new--new edges and supplies no uniform capacity estimate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic exact symmetrization of a directed Dirichlet joint -/

private theorem coefficientDifferenceSquare_symm
    {State : Type} (coefficient : State → Q')
    (left right : State) :
    (coefficient left + -coefficient right) *
        (coefficient left + -coefficient right) ≈
      (coefficient right + -coefficient left) *
        (coefficient right + -coefficient left) := by
  q_ring

private theorem finiteJointDirichletBlock_joint_congr_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (first second : State → State → Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        first left right ≈ second left right) :
    finiteJointDirichletBlock
        leftStates rightStates coefficient first ≈
      finiteJointDirichletBlock
        leftStates rightStates coefficient second := by
  unfold finiteJointDirichletBlock
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_right _ _ _
    (hjoint left hleft right hright)

private theorem finiteJointDirichletBlock_add_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (first second : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => first left right + second left right) ≈
      finiteJointDirichletBlock leftStates rightStates coefficient first +
        finiteJointDirichletBlock
          leftStates rightStates coefficient second := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            first left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)) +
              second left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.add_mul_eqv _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            first left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates +
        listQSum
          (fun right =>
            second left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact listQSum_add _ _ rightStates
  · exact listQSum_add _ _ leftStates

private theorem finiteJointDirichletBlock_scale_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        scale * listQSum
          (fun right =>
            joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          scale *
            (joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

/-- Transposing a directed joint does not change its full square-carrier
Dirichlet form. -/
theorem finiteJointDirichletBlock_transpose_eqv
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock states states coefficient
        (fun left right => joint right left) ≈
      finiteJointDirichletBlock states states coefficient joint := by
  let term : State → State → Q' := fun left right =>
    joint right left *
      ((coefficient right + -coefficient left) *
        (coefficient right + -coefficient left))
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum (fun left => listQSum (term left) states) states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.mul_eqv_congr_left (joint right left) _ _
      (coefficientDifferenceSquare_symm coefficient left right)
  exact Q'.eqv_symm (listQSum_swap term states states)

/-- Averaging a directed joint with its transpose preserves the full
square-carrier Dirichlet form exactly. -/
theorem finiteJointDirichletBlock_averageTranspose_eqv
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock states states coefficient
        (fun left right =>
          HalfPow.half * joint left right +
            HalfPow.half * joint right left) ≈
      finiteJointDirichletBlock states states coefficient joint := by
  refine Q'.eqv_trans _
    (finiteJointDirichletBlock states states coefficient
        (fun left right => HalfPow.half * joint left right) +
      finiteJointDirichletBlock states states coefficient
        (fun left right => HalfPow.half * joint right left)) _ ?_ ?_
  · exact finiteJointDirichletBlock_add_joint_local
      states states coefficient _ _
  refine Q'.eqv_trans _
    (HalfPow.half *
        finiteJointDirichletBlock states states coefficient joint +
      HalfPow.half *
        finiteJointDirichletBlock states states coefficient
          (fun left right => joint right left)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (finiteJointDirichletBlock_scale_joint_local
        states states coefficient HalfPow.half joint)
      (finiteJointDirichletBlock_scale_joint_local
        states states coefficient HalfPow.half
        (fun left right => joint right left))
  refine Q'.eqv_trans _
    (HalfPow.half *
        finiteJointDirichletBlock states states coefficient joint +
      HalfPow.half *
        finiteJointDirichletBlock states states coefficient joint) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (finiteJointDirichletBlock_transpose_eqv
          states coefficient joint))
  exact ExpNeg.two_halves
    (finiteJointDirichletBlock states states coefficient joint)

/-! ## 2. The exact symmetric novel load -/

/-- Arithmetic average of the two directed loads on one unoriented edge. -/
def cutoffTwoNovelSymmetricEdgeLoad
    (later source target : Nat) : Q' :=
  HalfPow.half * cutoffTwoNovelSimpleEdgeLoad later source target +
    HalfPow.half * cutoffTwoNovelSimpleEdgeLoad later target source

theorem cutoffTwoNovelSymmetricEdgeLoad_symm
    (later source target : Nat) :
    cutoffTwoNovelSymmetricEdgeLoad later source target ≈
      cutoffTwoNovelSymmetricEdgeLoad later target source := by
  unfold cutoffTwoNovelSymmetricEdgeLoad
  exact Q'.add_comm_eqv _ _

theorem cutoffTwoNovelSymmetricEdgeLoad_nonnegative
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoNovelSymmetricEdgeLoad later source target := by
  unfold cutoffTwoNovelSymmetricEdgeLoad
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target))
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later target source))

def cutoffTwoNovelSymmetricRawLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)
    coefficient (cutoffTwoNovelSymmetricEdgeLoad later)

/-- Symmetrizing the flow load is exactly energy-neutral. -/
theorem cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_original
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelSymmetricRawLoadedDirichlet later coefficient ≈
      cutoffTwoNovelSimpleRawLoadedDirichlet later coefficient := by
  have haverage := finiteJointDirichletBlock_averageTranspose_eqv
    (cutoffTwoEdgeLoadFullStates later) coefficient
    (cutoffTwoNovelSimpleEdgeLoad later)
  unfold cutoffTwoNovelSymmetricRawLoadedDirichlet
    cutoffTwoNovelSymmetricEdgeLoad
    cutoffTwoNovelSimpleRawLoadedDirichlet
    BF4PhysicalFiniteVacuumSectorPathEdgeLoad.finiteWeightedOccurrenceLoadedDirichlet
  refine Q'.eqv_trans _
    (finiteJointDirichletBlock
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later)
      coefficient (cutoffTwoNovelSimpleEdgeLoad later)) _ haverage ?_
  exact finiteJointDirichletBlock_joint_congr_local
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later) coefficient _ _
    (fun source _ target _ =>
      Q'.eqv_symm
        (Q'.mul_one_eqv
          (cutoffTwoNovelSimpleEdgeLoad later source target)))

/-- The already proved novel variance estimate survives exact load
symmetrization with no loss of coercivity strength. -/
theorem cutoffTwoNovelPairwiseVariance_le_symmetricRawLoadedDirichlet
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelPairwiseVariance later coefficient ≤
      cutoffTwoNovelSymmetricRawLoadedDirichlet later coefficient := by
  exact Q'.le_trans' _ _ _
    (cutoffTwoNovelPairwiseVariance_le_rawLoadedDirichlet
      later coefficient)
    (Q'.ge_of_eqv
      (cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_original
        later coefficient))

/-! ## 3. Symmetric physical capacity and cross-edge reorientation -/

theorem cutoffTwoEdgeLoadKernel_symm
    {later source target : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoEdgeLoadKernel later source target ≈
      cutoffTwoEdgeLoadKernel later target source := by
  have hsourcePositive := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) later 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) later 0 hsource)
  have htargetPositive := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) later 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) later 0 htarget)
  unfold cutoffTwoEdgeLoadKernel centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_symm
    (mem_centralPositiveHalfStates_iff.mp hsourcePositive).1
    (mem_centralPositiveHalfStates_iff.mp htargetPositive).1

theorem cutoffTwoNovelAllocatedKernel_symm
    {later source target : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoNovelAllocatedKernel later source target ≈
      cutoffTwoNovelAllocatedKernel later target source := by
  have hkernel := cutoffTwoEdgeLoadKernel_symm hsource htarget
  unfold cutoffTwoNovelAllocatedKernel
  by_cases hsourceOld : source ∈ cutoffTwoEdgeLoadOldStates later
  · by_cases htargetOld : target ∈ cutoffTwoEdgeLoadOldStates later
    · rw [dif_pos ⟨hsourceOld, htargetOld⟩,
        dif_pos ⟨htargetOld, hsourceOld⟩]
      exact Q'.mul_eqv_congr_left HalfPow.half _ _ hkernel
    · rw [dif_neg (fun h => htargetOld h.2),
        dif_neg (fun h => htargetOld h.1)]
      exact hkernel
  · rw [dif_neg (fun h => hsourceOld h.1),
      dif_neg (fun h => hsourceOld h.2)]
    exact hkernel

/-- A symmetry-reduced pointwise capacity certificate.  Cross-block capacity
is requested only in the old-to-new orientation. -/
structure CutoffTwoNovelSymmetricOrientedCapacityAt
    (later : Nat) : Type 1 where
  old_old : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target
  old_new : ∀ source,
    source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target
  new_new : ∀ source,
    source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target

namespace CutoffTwoNovelSymmetricOrientedCapacityAt

/-- The missing new-to-old field is an exact consequence of load and capacity
symmetry. -/
theorem new_old
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadNewStates later)
    (target : Nat)
    (htarget : target ∈ cutoffTwoEdgeLoadOldStates later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricEdgeLoad later source target ≤
      cutoffTwoNovelAllocatedKernel later source target := by
  have hsourceFull : source ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp hsource).1
  have htargetFull : target ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp htarget).1
  have hreversed := capacity.old_new target htarget source hsource
  have hleft :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later source target ≈
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricEdgeLoad later target source :=
    Q'.mul_eqv_congr_left cutoffTwoNovelSimpleFlowCoercivityFloor _ _
      (cutoffTwoNovelSymmetricEdgeLoad_symm later source target)
  have hright :
      cutoffTwoNovelAllocatedKernel later target source ≈
        cutoffTwoNovelAllocatedKernel later source target :=
    cutoffTwoNovelAllocatedKernel_symm htargetFull hsourceFull
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hreversed (Q'.le_of_eqv hright))

end CutoffTwoNovelSymmetricOrientedCapacityAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.finiteJointDirichletBlock_transpose_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.finiteJointDirichletBlock_averageTranspose_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.cutoffTwoNovelSymmetricEdgeLoad_symm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_original
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.cutoffTwoNovelPairwiseVariance_le_symmetricRawLoadedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.cutoffTwoNovelAllocatedKernel_symm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.CutoffTwoNovelSymmetricOrientedCapacityAt.new_old
