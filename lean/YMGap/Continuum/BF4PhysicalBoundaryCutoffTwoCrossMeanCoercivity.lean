/-
# Cross-block means and kernel coercivity at the cutoff-two boundary

The cross stationary-product Dirichlet block has a precise statistical
meaning.  For two weighted lists it is the sum of the two internal-square
terms, scaled by the opposite block masses, minus twice the product of the
block means.  Under global centering the two block means cancel, so this last
term becomes positive and measures separation of the old and new block means.

This module proves that rectangular identity constructively and specializes
it to the growing cutoff-two physical sector.  It also proves that a local
old/new kernel minorization implies the cross-coercivity field used by the
two-block Dirichlet gluing compiler.

No positive uniform minorization, within-block coercivity, mass floor, or
cofinal family is constructed.  In particular no completed gap inhabitant,
thermodynamic/continuum limit, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic rectangular stationary-product identity -/

private def finiteRectDoubleSum {Left Right : Type}
    (leftStates : List Left) (rightStates : List Right)
    (term : Left → Right → Q') : Q' :=
  listQSum (fun left => listQSum (term left) rightStates) leftStates

private theorem finiteRectDoubleSum_add
    {Left Right : Type}
    (leftStates : List Left) (rightStates : List Right)
    (first second : Left → Right → Q') :
    finiteRectDoubleSum leftStates rightStates
        (fun left right => first left right + second left right) ≈
      finiteRectDoubleSum leftStates rightStates first +
        finiteRectDoubleSum leftStates rightStates second := by
  unfold finiteRectDoubleSum
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (first left) rightStates +
          listQSum (second left) rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact listQSum_add (first left) (second left) rightStates
  · exact listQSum_add _ _ leftStates

private theorem listQSum_neg_local {State : Type}
  (value : State → Q') : ∀ states : List State,
    listQSum (fun state => -(value state)) states ≈
      -(listQSum value states)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left (-(value head)) _ _
          (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

/-- A directed rectangular stationary-product edge energy is exactly the two
opposite-mass-scaled block squares minus twice the product of block means. -/
theorem finiteWeightedDirichletBlock_eqv_mass_square_mean
    {State : Type}
    (leftStates rightStates : List State)
    (weight coefficient : State → Q') :
    finiteJointDirichletBlock
        leftStates rightStates coefficient
        (finiteStationaryProductJoint weight) ≈
      (finiteWeightedSquare leftStates weight coefficient *
          finiteWeightedMass rightStates weight +
        finiteWeightedMass leftStates weight *
          finiteWeightedSquare rightStates weight coefficient) +
      (-(finiteListWeightedMean leftStates weight coefficient *
          finiteListWeightedMean rightStates weight coefficient) +
        -(finiteListWeightedMean leftStates weight coefficient *
          finiteListWeightedMean rightStates weight coefficient)) := by
  let leftSquare : State → Q' := fun state =>
    weight state * (coefficient state * coefficient state)
  let rightSquare : State → Q' := fun state =>
    weight state * (coefficient state * coefficient state)
  let leftMean : State → Q' := fun state =>
    coefficient state * weight state
  let rightMean : State → Q' := fun state =>
    coefficient state * weight state
  let termLeft : State → State → Q' := fun left right =>
    leftSquare left * weight right
  let termRight : State → State → Q' := fun left right =>
    weight left * rightSquare right
  let termCross : State → State → Q' := fun left right =>
    (-(leftMean left)) * rightMean right
  have hentry :
      finiteJointDirichletBlock
          leftStates rightStates coefficient
          (finiteStationaryProductJoint weight) ≈
        finiteRectDoubleSum leftStates rightStates
          (fun left right =>
            (termLeft left right + termRight left right) +
              (termCross left right + termCross left right)) := by
    unfold finiteJointDirichletBlock finiteRectDoubleSum
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold finiteStationaryProductJoint termLeft termRight termCross
      leftSquare rightSquare leftMean rightMean
    q_ring
  have hsplit :
      finiteRectDoubleSum leftStates rightStates
          (fun left right =>
            (termLeft left right + termRight left right) +
              (termCross left right + termCross left right)) ≈
        (finiteRectDoubleSum leftStates rightStates termLeft +
          finiteRectDoubleSum leftStates rightStates termRight) +
        (finiteRectDoubleSum leftStates rightStates termCross +
          finiteRectDoubleSum leftStates rightStates termCross) := by
    refine Q'.eqv_trans _
      (finiteRectDoubleSum leftStates rightStates
          (fun left right => termLeft left right + termRight left right) +
        finiteRectDoubleSum leftStates rightStates
          (fun left right => termCross left right + termCross left right)) _
      (finiteRectDoubleSum_add leftStates rightStates _ _) ?_
    exact Q'.add_eqv_congr'
      (finiteRectDoubleSum_add leftStates rightStates termLeft termRight)
      (finiteRectDoubleSum_add leftStates rightStates termCross termCross)
  have hleft :
      finiteRectDoubleSum leftStates rightStates termLeft ≈
        finiteWeightedSquare leftStates weight coefficient *
          finiteWeightedMass rightStates weight := by
    unfold finiteRectDoubleSum termLeft leftSquare
      finiteWeightedSquare finiteWeightedMass
    exact listQSum_product
      (fun state => weight state *
        (coefficient state * coefficient state))
      weight leftStates rightStates
  have hright :
      finiteRectDoubleSum leftStates rightStates termRight ≈
        finiteWeightedMass leftStates weight *
          finiteWeightedSquare rightStates weight coefficient := by
    unfold finiteRectDoubleSum termRight rightSquare
      finiteWeightedSquare finiteWeightedMass
    exact listQSum_product weight
      (fun state => weight state *
        (coefficient state * coefficient state))
      leftStates rightStates
  have hcross :
      finiteRectDoubleSum leftStates rightStates termCross ≈
        -(finiteListWeightedMean leftStates weight coefficient *
          finiteListWeightedMean rightStates weight coefficient) := by
    unfold finiteRectDoubleSum termCross
    refine Q'.eqv_trans _
      (listQSum (fun state => -(leftMean state)) leftStates *
        listQSum rightMean rightStates) _ ?_ ?_
    · exact listQSum_product
        (fun state => -(leftMean state)) rightMean
        leftStates rightStates
    refine Q'.eqv_trans _
      (-(listQSum leftMean leftStates) *
        listQSum rightMean rightStates) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (listQSum_neg_local leftMean leftStates)
    unfold finiteListWeightedMean leftMean rightMean
    exact Q'.neg_mul_eqv _ _
  exact Q'.eqv_trans _ _ _ hentry
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hleft hright)
        (Q'.add_eqv_congr' hcross hcross)))

/-! ## 2. Physical old/new masses, means, and squares -/

def cutoffTwoOldMass (later : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoNewMass (later : Nat) : Q' :=
  finiteWeightedMass
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoOldMean
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteListWeightedMean
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)
    coefficient

def cutoffTwoNewMean
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteListWeightedMean
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)
    coefficient

def cutoffTwoOldSquare
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedSquare
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)
    coefficient

def cutoffTwoNewSquare
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedSquare
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0)
    coefficient

theorem cutoffTwoOldNewPairwiseVariance_eqv_mass_square_mean
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoOldNewPairwiseVariance later coefficient ≈
      (cutoffTwoOldSquare later coefficient * cutoffTwoNewMass later +
        cutoffTwoOldMass later * cutoffTwoNewSquare later coefficient) +
      (-(cutoffTwoOldMean later coefficient *
          cutoffTwoNewMean later coefficient) +
        -(cutoffTwoOldMean later coefficient *
          cutoffTwoNewMean later coefficient)) := by
  unfold cutoffTwoOldNewPairwiseVariance cutoffTwoOldSquare
    cutoffTwoNewMass cutoffTwoOldMass cutoffTwoNewSquare
    cutoffTwoOldMean cutoffTwoNewMean
  exact finiteWeightedDirichletBlock_eqv_mass_square_mean _ _ _ _

theorem cutoffTwoNewOldPairwiseVariance_eqv_mass_square_mean
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNewOldPairwiseVariance later coefficient ≈
      (cutoffTwoNewSquare later coefficient * cutoffTwoOldMass later +
        cutoffTwoNewMass later * cutoffTwoOldSquare later coefficient) +
      (-(cutoffTwoNewMean later coefficient *
          cutoffTwoOldMean later coefficient) +
        -(cutoffTwoNewMean later coefficient *
          cutoffTwoOldMean later coefficient)) := by
  unfold cutoffTwoNewOldPairwiseVariance cutoffTwoOldSquare
    cutoffTwoNewMass cutoffTwoOldMass cutoffTwoNewSquare
    cutoffTwoOldMean cutoffTwoNewMean
  exact finiteWeightedDirichletBlock_eqv_mass_square_mean _ _ _ _

/-- Global centering is exactly cancellation of the old and new block means. -/
theorem cutoffTwoOldMean_add_newMean_eqv_zero
    (later : Nat) (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    cutoffTwoOldMean later coefficient +
        cutoffTwoNewMean later coefficient ≈ 0 := by
  have hsplit :=
    centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new
      cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient
  unfold cutoffTwoFullSectorWeightedMean at hcenter
  unfold cutoffTwoOldMean cutoffTwoNewMean finiteListWeightedMean
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsplit) hcenter

private theorem left_eqv_neg_of_add_eqv_zero
    {left right : Q'} (hsum : left + right ≈ 0) :
    left ≈ -right := by
  have hstart : left ≈ (-right) + (left + -(-right)) :=
    Q'.add_sub_cancel_eqv left (-right)
  have hinner : left + -(-right) ≈ left + right :=
    Q'.add_eqv_congr_left left _ _ (Q'.neg_neg_eqv right)
  have hmiddle : (-right) + (left + -(-right)) ≈
      (-right) + (left + right) :=
    Q'.add_eqv_congr_left (-right) _ _ hinner
  have hend : (-right) + (left + right) ≈ -right := by
    refine Q'.eqv_trans _ ((-right) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (-right) _ _ hsum
    · exact Q'.eqv_of_eq (Q'.add_zero' (-right))
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hmiddle hend)

/-- Under global centering, the negative product of the two block means is a
positive square of the old-block mean. -/
theorem cutoffTwoNegOldMeanMulNewMean_centered_eqv_square
    (later : Nat) (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    -(cutoffTwoOldMean later coefficient *
        cutoffTwoNewMean later coefficient) ≈
      cutoffTwoOldMean later coefficient *
        cutoffTwoOldMean later coefficient := by
  have hsum := cutoffTwoOldMean_add_newMean_eqv_zero
    later coefficient hcenter
  have hnew : cutoffTwoNewMean later coefficient ≈
      -(cutoffTwoOldMean later coefficient) :=
    left_eqv_neg_of_add_eqv_zero
      (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv
          (cutoffTwoNewMean later coefficient)
          (cutoffTwoOldMean later coefficient)) hsum)
  refine Q'.eqv_trans _
    (-(cutoffTwoOldMean later coefficient *
      -(cutoffTwoOldMean later coefficient))) _ ?_ ?_
  · exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left
        (cutoffTwoOldMean later coefficient) _ _ hnew)
  q_ring

/-- The full directed cross pairwise variance consists of two copies of the
opposite-mass-scaled internal squares plus two positive copies of the
old-block mean square in each orientation. -/
theorem cutoffTwoCrossBlockPairwiseVariance_centered_eqv
    (later : Nat) (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    cutoffTwoCrossBlockPairwiseVariance later coefficient ≈
      ((cutoffTwoOldSquare later coefficient * cutoffTwoNewMass later +
          cutoffTwoOldMass later * cutoffTwoNewSquare later coefficient) +
        (cutoffTwoOldMean later coefficient *
            cutoffTwoOldMean later coefficient +
          cutoffTwoOldMean later coefficient *
            cutoffTwoOldMean later coefficient)) +
      ((cutoffTwoOldSquare later coefficient * cutoffTwoNewMass later +
          cutoffTwoOldMass later * cutoffTwoNewSquare later coefficient) +
        (cutoffTwoOldMean later coefficient *
            cutoffTwoOldMean later coefficient +
          cutoffTwoOldMean later coefficient *
            cutoffTwoOldMean later coefficient)) := by
  let oldMean := cutoffTwoOldMean later coefficient
  let newMean := cutoffTwoNewMean later coefficient
  let base :=
    cutoffTwoOldSquare later coefficient * cutoffTwoNewMass later +
      cutoffTwoOldMass later * cutoffTwoNewSquare later coefficient
  let meanSquare := oldMean * oldMean
  have hnegOldNew : -(oldMean * newMean) ≈ meanSquare := by
    unfold oldMean newMean meanSquare
    exact cutoffTwoNegOldMeanMulNewMean_centered_eqv_square
      later coefficient hcenter
  have hnegNewOld : -(newMean * oldMean) ≈ meanSquare := by
    refine Q'.eqv_trans _ (-(oldMean * newMean)) _ ?_ hnegOldNew
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv newMean oldMean)
  have holdNew : cutoffTwoOldNewPairwiseVariance later coefficient ≈
      base + (meanSquare + meanSquare) := by
    refine Q'.eqv_trans _ _ _
      (cutoffTwoOldNewPairwiseVariance_eqv_mass_square_mean
        later coefficient) ?_
    unfold base meanSquare
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr' hnegOldNew hnegOldNew)
  have hnewOld : cutoffTwoNewOldPairwiseVariance later coefficient ≈
      base + (meanSquare + meanSquare) := by
    refine Q'.eqv_trans _ _ _
      (cutoffTwoNewOldPairwiseVariance_eqv_mass_square_mean
        later coefficient) ?_
    unfold base meanSquare
    refine Q'.add_eqv_congr' ?_
      (Q'.add_eqv_congr' hnegNewOld hnegNewOld)
    q_ring
  unfold cutoffTwoCrossBlockPairwiseVariance
  exact Q'.add_eqv_congr' holdNew hnewOld

/-! ## 3. Pointwise kernel minorization supplies cross coercivity -/

/-- Scaling one rectangular stationary-product block is monotone under a
pointwise joint-kernel minorization. -/
theorem scale_mul_finiteWeightedDirichletBlock_le
    {State : Type}
    (leftStates rightStates : List State)
    (weight coefficient : State → Q')
    (joint : State → State → Q') (scale : Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        scale * finiteStationaryProductJoint weight left right ≤
          joint left right) :
    scale * finiteJointDirichletBlock
        leftStates rightStates coefficient
        (finiteStationaryProductJoint weight) ≤
      finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  let square : State → State → Q' := fun left right =>
    (coefficient left + -coefficient right) *
      (coefficient left + -coefficient right)
  have hsum :
      finiteRectDoubleSum leftStates rightStates
          (fun left right =>
            (scale * finiteStationaryProductJoint weight left right) *
              square left right) ≤
        finiteRectDoubleSum leftStates rightStates
          (fun left right => joint left right * square left right) := by
    unfold finiteRectDoubleSum
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (hjoint left hleft right hright)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        (coefficient left + -coefficient right))
  have hleft :
      scale * finiteJointDirichletBlock
          leftStates rightStates coefficient
          (finiteStationaryProductJoint weight) ≈
        finiteRectDoubleSum leftStates rightStates
          (fun left right =>
            (scale * finiteStationaryProductJoint weight left right) *
              square left right) := by
    unfold finiteJointDirichletBlock finiteRectDoubleSum square
    refine Q'.eqv_trans _
      (listQSum
        (fun left => scale *
          listQSum
            (fun right =>
              finiteStationaryProductJoint weight left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
            rightStates)
        leftStates) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_mul_left scale _ leftStates)
    apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right => scale *
          (finiteStationaryProductJoint weight left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_mul_left scale _ rightStates)
    apply listQSum_congr
    intro right
    q_ring
  have hright :
      finiteRectDoubleSum leftStates rightStates
          (fun left right => joint left right * square left right) =
        finiteJointDirichletBlock
          leftStates rightStates coefficient joint := rfl
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (hright ▸ hsum)

/-- A local directed minorization on both old/new orientations. -/
structure CutoffTwoCrossKernelMinorizationAt
    (later : Nat) (floor : Q') : Type 1 where
  old_new : ∀ old,
    old ∈ centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0 →
    ∀ new,
    new ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0 →
      floor * finiteStationaryProductJoint
          (centralPhysicalFiniteWeight
            cutoffTwoHalfCoupling (by decide) later 0)
          old new ≤
        centralPhysicalFiniteKernel
          cutoffTwoHalfCoupling (by decide) later 0 old new
  new_old : ∀ new,
    new ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0 →
    ∀ old,
    old ∈ centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0 →
      floor * finiteStationaryProductJoint
          (centralPhysicalFiniteWeight
            cutoffTwoHalfCoupling (by decide) later 0)
          new old ≤
        centralPhysicalFiniteKernel
          cutoffTwoHalfCoupling (by decide) later 0 new old

namespace CutoffTwoCrossKernelMinorizationAt

/-- Pointwise old/new minorization is sufficient for the cross-energy field
of the two-block gluing certificate. -/
theorem cross_coercivity
    {later : Nat} {floor : Q'}
    (certificate : CutoffTwoCrossKernelMinorizationAt later floor)
    (coefficient : Nat → Q') :
    floor * cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
      cutoffTwoCrossBlockDirichlet later coefficient := by
  have holdNew :
      floor * cutoffTwoOldNewPairwiseVariance later coefficient ≤
        cutoffTwoOldNewDirichlet later coefficient := by
    unfold cutoffTwoOldNewPairwiseVariance cutoffTwoOldNewDirichlet
    exact scale_mul_finiteWeightedDirichletBlock_le _ _ _ _ _ floor
      certificate.old_new
  have hnewOld :
      floor * cutoffTwoNewOldPairwiseVariance later coefficient ≤
        cutoffTwoNewOldDirichlet later coefficient := by
    unfold cutoffTwoNewOldPairwiseVariance cutoffTwoNewOldDirichlet
    exact scale_mul_finiteWeightedDirichletBlock_le _ _ _ _ _ floor
      certificate.new_old
  refine Q'.le_trans' _
    (floor * cutoffTwoOldNewPairwiseVariance later coefficient +
      floor * cutoffTwoNewOldPairwiseVariance later coefficient) _ ?_ ?_
  · unfold cutoffTwoCrossBlockPairwiseVariance
    exact Q'.le_of_eqv (Q'.mul_add_eqv floor _ _)
  · unfold cutoffTwoCrossBlockDirichlet
    exact Q'.add_le_add holdNew hnewOld

end CutoffTwoCrossKernelMinorizationAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.finiteWeightedDirichletBlock_eqv_mass_square_mean
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.cutoffTwoOldNewPairwiseVariance_eqv_mass_square_mean
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.cutoffTwoNewOldPairwiseVariance_eqv_mass_square_mean
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.cutoffTwoOldMean_add_newMean_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.cutoffTwoNegOldMeanMulNewMean_centered_eqv_square
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.cutoffTwoCrossBlockPairwiseVariance_centered_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.scale_mul_finiteWeightedDirichletBlock_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.CutoffTwoCrossKernelMinorizationAt.cross_coercivity
