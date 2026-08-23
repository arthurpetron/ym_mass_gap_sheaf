/-
# Two-block Dirichlet gluing for the growing physical sector

The full old/new Dirichlet partition is useful only once the stationary
variance is split along the same cut.  This module performs that split and
isolates a genuinely recursive Poincare input: one common positive floor
must dominate the within-block stationary pairwise variance by the physical
within-block energy and the cross-block stationary pairwise variance by the
physical cross-block energy.

Those two estimates glue exactly.  Together with a positive lower bound on
the total sector mass they imply a uniform centered Poincare inequality, an
explicit strict transfer rate, and, for a constructively cofinal family, the
existing completed vacuum-sector contraction.

No within/cross coercivity floor or cofinal family is constructed here.  The
module is a compiler for the next analytic frontier, not a completed gap,
thermodynamic/continuum limit, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

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

/-! ## 1. Stationary pairwise variance under the same old/new cut -/

def cutoffTwoFullSectorPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorPairwiseVariance
    cutoffTwoHalfCoupling (by decide) later 0 coefficient

def cutoffTwoOldOldPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0))

def cutoffTwoOldNewPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0))

def cutoffTwoNewOldPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0))

def cutoffTwoNewNewPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (finiteStationaryProductJoint
      (centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0))

def cutoffTwoWithinBlockPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoOldOldPairwiseVariance later coefficient +
    cutoffTwoNewNewPairwiseVariance later coefficient

def cutoffTwoCrossBlockPairwiseVariance
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoOldNewPairwiseVariance later coefficient +
    cutoffTwoNewOldPairwiseVariance later coefficient

private theorem four_term_within_cross_reshuffle
    (oldOld oldNew newOld newNew : Q') :
    (oldOld + oldNew) + (newOld + newNew) ≈
      (oldOld + newNew) + (oldNew + newOld) := by
  q_ring

/-- Exact partition of stationary pairwise variance into within-block and
cross-block fluctuations.  The cross term contains the separation of the two
block means, while the within term is invariant under separate blockwise
constant shifts. -/
theorem cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorPairwiseVariance later coefficient ≈
      cutoffTwoWithinBlockPairwiseVariance later coefficient +
        cutoffTwoCrossBlockPairwiseVariance later coefficient := by
  unfold cutoffTwoFullSectorPairwiseVariance
    centralPhysicalFiniteVacuumSectorPairwiseVariance
    finiteWeightedPairwiseVariance
  refine Q'.eqv_trans _ _ _
    (finiteJointDirichletEnergy_filter_four_blocks
      (centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0)
      (centralPhysicalFiniteEmbeddedVacuumSectorB
        cutoffTwoHalfCoupling (by decide) 2 later 0)
      coefficient
      (finiteStationaryProductJoint
        (centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) later 0))) ?_
  unfold cutoffTwoWithinBlockPairwiseVariance
    cutoffTwoCrossBlockPairwiseVariance
    cutoffTwoOldOldPairwiseVariance cutoffTwoOldNewPairwiseVariance
    cutoffTwoNewOldPairwiseVariance cutoffTwoNewNewPairwiseVariance
    centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact four_term_within_cross_reshuffle _ _ _ _

private theorem cutoffTwoPairwiseBlock_nonnegative
    (leftStates rightStates : List Nat)
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteJointDirichletBlock
      leftStates rightStates coefficient
      (finiteStationaryProductJoint
        (centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) later 0)) := by
  exact finiteJointDirichletBlock_nonnegative
    leftStates rightStates coefficient _
    (fun left right => by
      unfold finiteStationaryProductJoint
      exact Q'.mul_nonneg _ _
        (centralPhysicalRowMarginal_nonnegative (by decide) later 0
          (centralPhysicalFiniteStateAt
            cutoffTwoHalfCoupling (by decide) later 0 left))
        (centralPhysicalRowMarginal_nonnegative (by decide) later 0
          (centralPhysicalFiniteStateAt
            cutoffTwoHalfCoupling (by decide) later 0 right)))

theorem cutoffTwoWithinBlockPairwiseVariance_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoWithinBlockPairwiseVariance later coefficient := by
  unfold cutoffTwoWithinBlockPairwiseVariance
    cutoffTwoOldOldPairwiseVariance cutoffTwoNewNewPairwiseVariance
  exact Q'.zero_le_add _ _
    (cutoffTwoPairwiseBlock_nonnegative _ _ later coefficient)
    (cutoffTwoPairwiseBlock_nonnegative _ _ later coefficient)

theorem cutoffTwoCrossBlockPairwiseVariance_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoCrossBlockPairwiseVariance later coefficient := by
  unfold cutoffTwoCrossBlockPairwiseVariance
    cutoffTwoOldNewPairwiseVariance cutoffTwoNewOldPairwiseVariance
  exact Q'.zero_le_add _ _
    (cutoffTwoPairwiseBlock_nonnegative _ _ later coefficient)
    (cutoffTwoPairwiseBlock_nonnegative _ _ later coefficient)

/-! ## 2. One two-block gluing certificate -/

/-- The exact analytic data needed to glue old and new fluctuations at one
later cutoff.  A single floor is used on both pieces so their exact sums can
be recombined without losing a rate. -/
structure CutoffTwoFullSectorDirichletGluingAt
    (later : Nat) (floor massFloor : Q') : Type 1 where
  later_ge : 2 ≤ later
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  within_coercivity : ∀ coefficient,
    floor * cutoffTwoWithinBlockPairwiseVariance later coefficient ≤
      cutoffTwoWithinBlockDirichlet later coefficient
  cross_coercivity : ∀ coefficient,
    floor * cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
      cutoffTwoCrossBlockDirichlet later coefficient

namespace CutoffTwoFullSectorDirichletGluingAt

/-- The two blockwise estimates glue to the full stationary-product versus
physical-kernel Dirichlet comparison. -/
theorem floor_mul_pairwiseVariance_le_fullDirichlet
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletGluingAt
      later floor massFloor)
    (coefficient : Nat → Q') :
    floor * cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoFullSectorDirichlet later coefficient := by
  have hblocks := Q'.add_le_add
    (certificate.within_coercivity coefficient)
    (certificate.cross_coercivity coefficient)
  refine Q'.le_trans' _
    (floor * cutoffTwoWithinBlockPairwiseVariance later coefficient +
      floor * cutoffTwoCrossBlockPairwiseVariance later coefficient) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (floor *
          (cutoffTwoWithinBlockPairwiseVariance later coefficient +
            cutoffTwoCrossBlockPairwiseVariance later coefficient)) _
        (Q'.mul_eqv_congr_left floor _ _
          (cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
            later coefficient))
        (Q'.mul_add_eqv floor _ _))
  · exact Q'.le_trans' _ _ _ hblocks
      (Q'.ge_of_eqv
        (cutoffTwoFullSectorDirichlet_eqv_within_add_cross
          later coefficient))

private theorem ofNat_two_mul_eqv_local (value : Q') :
    Q'.ofNat 2 * value ≈ value + value := by
  show (Q'.ofNat 2 * value).num * ((value + value).den : Int) =
      (value + value).num * ((Q'.ofNat 2 * value).den : Int)
  have hn : (Q'.ofNat 2 * value).num = (2 : Int) * value.num := rfl
  have hd2 : ((Q'.ofNat 2 * value).den : Int) =
      (value.den : Int) := by
    show (((Q'.ofNat 2).den * value.den - 1 + 1 : Nat) : Int) =
      (value.den : Int)
    rw [show (Q'.ofNat 2).den = 1 from rfl, Nat.one_mul,
      Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (Q'.den_pos value)))]
  have hxxn : (value + value).num =
      value.num * (value.den : Int) +
        value.num * (value.den : Int) := rfl
  have hxxd : ((value + value).den : Int) =
      (value.den : Int) * (value.den : Int) := by
    show (((value.den * value.den - 1) + 1 : Nat) : Int) =
      (value.den : Int) * (value.den : Int)
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp
          (Nat.mul_pos (Q'.den_pos value) (Q'.den_pos value)))),
      Int.natCast_mul]
  rw [hn, hd2, hxxn, hxxd]
  rw [Int.add_mul, Int.two_mul, Int.add_mul]
  rw [Int.mul_assoc value.num (value.den : Int) (value.den : Int)]

private theorem twice_floor_mass_diagonal_eqv
    (floor mass diagonal : Q') :
    Q'.ofNat 2 * ((floor * mass) * diagonal) ≈
      floor * (mass * diagonal + mass * diagonal) := by
  refine Q'.eqv_trans _
    (((floor * mass) * diagonal) +
      ((floor * mass) * diagonal)) _
    (ofNat_two_mul_eqv_local ((floor * mass) * diagonal)) ?_
  q_ring

private theorem twice_deficit_eqv
    (diagonal matrix : Q') :
    (diagonal + diagonal) + -(matrix + matrix) ≈
      Q'.ofNat 2 * (diagonal + -matrix) := by
  refine Q'.eqv_trans _
    ((diagonal + -matrix) + (diagonal + -matrix)) _ ?_ ?_
  · q_ring
  · exact Q'.eqv_symm
      (ofNat_two_mul_eqv_local (diagonal + -matrix))

/-- Exact centering converts the glued pairwise estimate and a total-mass
floor into a Poincare inequality for the full later sector. -/
theorem strength_mul_diagonal_le_deficit
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletGluingAt
      later floor massFloor)
    (hfloor : (0 : Q') ≤ floor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    (floor * massFloor) * cutoffTwoFullSectorDiagonal later coefficient ≤
      cutoffTwoFullSectorDiagonal later coefficient +
        -cutoffTwoFullSectorMatrix later coefficient := by
  let mass := centralPhysicalFiniteVacuumSectorMass
    cutoffTwoHalfCoupling (by decide) later 0
  let diagonal := cutoffTwoFullSectorDiagonal later coefficient
  let matrix := cutoffTwoFullSectorMatrix later coefficient
  let pairwise := cutoffTwoFullSectorPairwiseVariance later coefficient
  let energy := cutoffTwoFullSectorDirichlet later coefficient
  have hdiagonal : (0 : Q') ≤ diagonal := by
    unfold diagonal cutoffTwoFullSectorDiagonal
    exact centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
      cutoffTwoHalfCoupling (by decide) later 0 coefficient
  have hmassTerm : massFloor * diagonal ≤ mass * diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ diagonal
      certificate.mass_floor_le hdiagonal
  have hmassTwice :
      massFloor * diagonal + massFloor * diagonal ≤
        mass * diagonal + mass * diagonal :=
    Q'.add_le_add hmassTerm hmassTerm
  have hfloorMass :
      floor * (massFloor * diagonal + massFloor * diagonal) ≤
        floor * (mass * diagonal + mass * diagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ floor hmassTwice hfloor
  have hpairwise : pairwise ≈
      mass * diagonal + mass * diagonal := by
    have hcenterPhysical :
        centralPhysicalFiniteVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) later 0 coefficient ≈ 0 := by
      exact hcenter
    unfold pairwise mass diagonal
      cutoffTwoFullSectorPairwiseVariance cutoffTwoFullSectorDiagonal
    exact centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
      cutoffTwoHalfCoupling (by decide) later 0 coefficient hcenterPhysical
  have hfloorPairwise :
      floor * (mass * diagonal + mass * diagonal) ≤ floor * pairwise :=
    Q'.le_of_eqv
      (Q'.mul_eqv_congr_left floor _ _ (Q'.eqv_symm hpairwise))
  have hglued :
      floor * (massFloor * diagonal + massFloor * diagonal) ≤ energy :=
    Q'.le_trans' _ _ _ hfloorMass
      (Q'.le_trans' _ _ _ hfloorPairwise
        (certificate.floor_mul_pairwiseVariance_le_fullDirichlet coefficient))
  have henergy : energy ≈
      (diagonal + diagonal) + -(matrix + matrix) := by
    unfold energy diagonal matrix
    exact cutoffTwoFullSectorDirichlet_eqv_twice_deficit later coefficient
  have htwice :
      Q'.ofNat 2 * ((floor * massFloor) * diagonal) ≤
        Q'.ofNat 2 * (diagonal + -matrix) :=
    Q'.le_trans' _
      (floor * (massFloor * diagonal + massFloor * diagonal)) _
      (Q'.le_of_eqv
        (twice_floor_mass_diagonal_eqv floor massFloor diagonal))
      (Q'.le_trans' _ energy _ hglued
        (Q'.le_trans' _
          ((diagonal + diagonal) + -(matrix + matrix)) _
          (Q'.le_of_eqv henergy)
          (Q'.le_of_eqv (twice_deficit_eqv diagonal matrix))))
  exact Q'.le_of_mul_le_mul_left htwice (Q'.ofNat_succ_pos 1)

end CutoffTwoFullSectorDirichletGluingAt

/-! ## 3. Explicit strict rate -/

def cutoffTwoDirichletGluingStrength
    (floor massFloor : Q') : Q' :=
  floor * massFloor

def cutoffTwoDirichletGluingDenominator
    (floor massFloor : Q') : Q' :=
  1 + cutoffTwoDirichletGluingStrength floor massFloor

theorem cutoffTwoDirichletGluingStrength_pos
    {floor massFloor : Q'}
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor) :
    (0 : Q') < cutoffTwoDirichletGluingStrength floor massFloor := by
  unfold cutoffTwoDirichletGluingStrength
  exact Q'.mul_pos hfloor hmass

theorem cutoffTwoDirichletGluingDenominator_pos
    {floor massFloor : Q'}
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor) :
    (0 : Q') < cutoffTwoDirichletGluingDenominator floor massFloor := by
  unfold cutoffTwoDirichletGluingDenominator
  exact Q'.pos_add_nonneg (by decide)
    (Q'.le_of_lt
      (cutoffTwoDirichletGluingStrength_pos hfloor hmass))

def cutoffTwoDirichletGluingRate
    (floor massFloor : Q')
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor) : Q' :=
  Q'.divPos 1
    (cutoffTwoDirichletGluingDenominator floor massFloor)
    (cutoffTwoDirichletGluingDenominator_pos hfloor hmass)

private theorem lt_add_of_pos_right (a b : Q')
    (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key : (0 : Int) <
      b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

private theorem divPos_lt_one_of_lt
    (numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator)
    (hnumerator : numerator < denominator) :
    Q'.divPos numerator denominator hdenominator < (1 : Q') := by
  unfold Q'.divPos
  have hreciprocal : (0 : Q') <
      Q'.recipPos denominator hdenominator :=
    Q'.recipPos_pos denominator hdenominator
  have hscaled :
      Q'.recipPos denominator hdenominator * numerator <
        Q'.recipPos denominator hdenominator * denominator :=
    Q'.mul_lt_mul_of_pos_left hreciprocal hnumerator
  have hleft :
      numerator * Q'.recipPos denominator hdenominator ≈
        Q'.recipPos denominator hdenominator * numerator :=
    Q'.mul_comm_eqv _ _
  have hright :
      Q'.recipPos denominator hdenominator * denominator ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator hdenominator)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

theorem cutoffTwoDirichletGluingRate_nonnegative
    {floor massFloor : Q'}
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor) :
    (0 : Q') ≤ cutoffTwoDirichletGluingRate
      floor massFloor hfloor hmass := by
  exact Q'.le_of_lt
    (Q'.divPos_pos _ _
      (cutoffTwoDirichletGluingDenominator_pos hfloor hmass)
      (by decide))

theorem cutoffTwoDirichletGluingRate_lt_one
    {floor massFloor : Q'}
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor) :
    cutoffTwoDirichletGluingRate floor massFloor hfloor hmass <
      (1 : Q') := by
  apply divPos_lt_one_of_lt
  unfold cutoffTwoDirichletGluingDenominator
  exact lt_add_of_pos_right _ _
    (cutoffTwoDirichletGluingStrength_pos hfloor hmass)

private theorem strength_deficit_cancel
    (strength diagonal matrix : Q') :
    strength * (diagonal + -matrix) + strength * matrix ≈
      strength * diagonal := by
  refine Q'.eqv_trans _
    ((strength * diagonal + strength * (-matrix)) +
      strength * matrix) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_add_eqv strength diagonal (-matrix))
  refine Q'.eqv_trans _
    (strength * diagonal +
      (strength * (-matrix) + strength * matrix)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (strength * diagonal +
      (-(strength * matrix) + strength * matrix)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_neg_eqv strength matrix))
  refine Q'.eqv_trans _ (strength * diagonal + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv (strength * matrix))
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem sub_add_cancel_eqv (diagonal matrix : Q') :
    (diagonal + -matrix) + matrix ≈ diagonal := by
  refine Q'.eqv_trans _
    (diagonal + (-matrix + matrix)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (diagonal + 0) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv matrix)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem denominator_mul_matrix_eqv
    (strength matrix : Q') :
    (1 + strength) * matrix ≈ strength * matrix + matrix := by
  q_ring

private theorem divPos_one_mul_right_eqv
    (diagonal denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos diagonal denominator hdenominator ≈
      Q'.divPos 1 denominator hdenominator * diagonal := by
  unfold Q'.divPos
  q_ring

namespace CutoffTwoFullSectorDirichletGluingAt

/-- Positive gluing strength gives an explicit one-sided strict rate. -/
theorem matrix_le_rate_mul_diagonal
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletGluingAt
      later floor massFloor)
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    cutoffTwoFullSectorMatrix later coefficient ≤
      cutoffTwoDirichletGluingRate floor massFloor hfloor hmass *
        cutoffTwoFullSectorDiagonal later coefficient := by
  let strength := cutoffTwoDirichletGluingStrength floor massFloor
  let denominator := cutoffTwoDirichletGluingDenominator floor massFloor
  let diagonal := cutoffTwoFullSectorDiagonal later coefficient
  let matrix := cutoffTwoFullSectorMatrix later coefficient
  have hstrength0 : (0 : Q') ≤ strength :=
    Q'.le_of_lt (cutoffTwoDirichletGluingStrength_pos hfloor hmass)
  have hpoincare : strength * diagonal ≤ diagonal + -matrix := by
    unfold strength cutoffTwoDirichletGluingStrength diagonal matrix
    exact certificate.strength_mul_diagonal_le_deficit
      (Q'.le_of_lt hfloor) coefficient hcenter
  have hmatrixDiagonal : matrix ≤ diagonal := by
    unfold matrix diagonal cutoffTwoFullSectorMatrix
      cutoffTwoFullSectorDiagonal
    exact centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
      cutoffTwoHalfCoupling (by decide) later 0 coefficient
  have hstrengthMatrix : strength * matrix ≤ strength * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ strength
      hmatrixDiagonal hstrength0
  have hfirst : strength * matrix + matrix ≤
      strength * diagonal + matrix :=
    Q'.add_le_add_right _ _ matrix hstrengthMatrix
  have hsecond : strength * diagonal + matrix ≤ diagonal := by
    have hadd := Q'.add_le_add_right
      (strength * diagonal) (diagonal + -matrix) matrix hpoincare
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (sub_add_cancel_eqv diagonal matrix))
  have hdenominatorMatrix : denominator * matrix ≤ diagonal := by
    unfold denominator cutoffTwoDirichletGluingDenominator
    exact Q'.le_trans' _ (strength * matrix + matrix) _
      (Q'.le_of_eqv (denominator_mul_matrix_eqv strength matrix))
      (Q'.le_trans' _ _ _ hfirst hsecond)
  have hcommuted : matrix * denominator ≤ diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv matrix denominator))
      hdenominatorMatrix
  have hdivision := Q'.le_divPos_of_mul_le diagonal denominator
    (cutoffTwoDirichletGluingDenominator_pos hfloor hmass) hcommuted
  exact Q'.le_trans' _ _ _ hdivision
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        (Q'.divPos 1 denominator
          (cutoffTwoDirichletGluingDenominator_pos hfloor hmass) *
            diagonal) _
        (divPos_one_mul_right_eqv diagonal denominator
          (cutoffTwoDirichletGluingDenominator_pos hfloor hmass))
        (Q'.eqv_refl _)))

/-- Gram positivity upgrades the one-sided rate to the absolute form required
by the cofinal completion interface. -/
theorem abs_matrix_le_rate_mul_diagonal
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletGluingAt
      later floor massFloor)
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    Q'.abs (cutoffTwoFullSectorMatrix later coefficient) ≤
      cutoffTwoDirichletGluingRate floor massFloor hfloor hmass *
        cutoffTwoFullSectorDiagonal later coefficient := by
  rw [abs_of_nonneg]
  · exact certificate.matrix_le_rate_mul_diagonal
      hfloor hmass coefficient hcenter
  · unfold cutoffTwoFullSectorMatrix
    exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      cutoffTwoHalfCoupling (by decide) later 0 coefficient

end CutoffTwoFullSectorDirichletGluingAt

/-! ## 4. Cofinal gluing reaches the completed transfer -/

/-- Fixed positive gluing and mass floors on a constructively cofinal cutoff
schedule.  These two analytic numbers determine one uniform strict rate. -/
structure CutoffTwoCofinalFullSectorDirichletGluing
    (floor massFloor : Q') : Type 1 where
  floor_pos : (0 : Q') < floor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  gluing : ∀ request,
    CutoffTwoFullSectorDirichletGluingAt
      (anchor request) floor massFloor

namespace CutoffTwoCofinalFullSectorDirichletGluing

def toFiniteStrictGap
    {floor massFloor : Q'}
    (family : CutoffTwoCofinalFullSectorDirichletGluing
      floor massFloor) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      cutoffTwoHalfCoupling (by decide) 0
      (cutoffTwoDirichletGluingRate
        floor massFloor family.floor_pos family.mass_floor_pos) where
  rate_nonnegative := cutoffTwoDirichletGluingRate_nonnegative
    family.floor_pos family.mass_floor_pos
  rate_lt_one := cutoffTwoDirichletGluingRate_lt_one
    family.floor_pos family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := by
    intro request
    exact Nat.le_trans (Nat.le_max_right 2 request)
      (family.anchor_ge request)
  sectorGap := by
    intro request coefficient hcenter
    exact (family.gluing request).abs_matrix_le_rate_mul_diagonal
      family.floor_pos family.mass_floor_pos coefficient hcenter

def toCompletedStrictContractionData
    {floor massFloor : Q'}
    (family : CutoffTwoCofinalFullSectorDirichletGluing
      floor massFloor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalFullSectorDirichletGluing

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.cutoffTwoWithinBlockPairwiseVariance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.cutoffTwoCrossBlockPairwiseVariance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.CutoffTwoFullSectorDirichletGluingAt.floor_mul_pairwiseVariance_le_fullDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.CutoffTwoFullSectorDirichletGluingAt.strength_mul_diagonal_le_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.cutoffTwoDirichletGluingRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.cutoffTwoDirichletGluingRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.CutoffTwoFullSectorDirichletGluingAt.abs_matrix_le_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.CutoffTwoCofinalFullSectorDirichletGluing.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.CutoffTwoCofinalFullSectorDirichletGluing.toCompletedStrictContractionData
