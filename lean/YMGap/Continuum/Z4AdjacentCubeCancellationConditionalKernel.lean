/-
# Post-gluing conditional law for two adjacent cutoff-one cubes

The adjacent-cube cancellation theorem gives the four physical carriers
obtained by independently occupying the left and right elementary cubes:

* vacuum;
* the left six-face boundary;
* the right six-face boundary; and
* the ten-face symmetric-difference boundary when both are occupied.

This module normalizes those *joint, already glued* physical activities.  For
each fixed left occupation it defines the conditional law of the right
occupation.  The denominator is formed only after the shared face has been
cancelled, so the doubly occupied state uses the exact tenth-power activity,
not the product of two independently normalized sixth-power rows.

The resulting two-state kernel is nonnegative, row-normalized, and reversible
with respect to its exact source partition.  It is a cutoff-one overlap
kernel, not an arbitrary-spin slab block: the missing all-cutoff recoupling
fiber remains a separate gate.
-/

import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.Z4AdjacentCubeCancellationActivity

namespace YMGap.Continuum.Z4AdjacentCubeCancellationConditionalKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4AdjacentCubeCancellationActivity
open YMGap.Continuum.Z4AdjacentCubeCancellationCarrier
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The four already-glued physical carriers -/

def adjacentCubeOccupationRoot : Bool → Bool → List Nat
  | false, false => []
  | true, false => axisCoarseRoot zeroAxisOffset
  | false, true => axisCoarseRoot xAxisOffset
  | true, true => zeroXAxisCancelledRoot

def adjacentCubeRightStateSpace : List Bool := [false, true]

theorem adjacentCubeRightStateSpace_nodup :
    adjacentCubeRightStateSpace.Nodup := by
  decide

theorem adjacentCubeRightStateSpace_complete (right : Bool) :
    right ∈ adjacentCubeRightStateSpace := by
  cases right <;> simp [adjacentCubeRightStateSpace]

def adjacentCubeJointRawWeight
    (coupling : Q') (left right : Bool) : Q' :=
  canonicalSurfaceActivity coupling 6
    (adjacentCubeOccupationRoot left right)

theorem adjacentCubeJointRawWeight_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (left right : Bool) :
    (0 : Q') ≤ adjacentCubeJointRawWeight coupling left right := by
  unfold adjacentCubeJointRawWeight
  exact canonicalSurfaceActivity_nonnegative hcoupling 6 _

theorem adjacentCubeJointRawWeight_false_false_eqv_one
    (coupling : Q') :
    adjacentCubeJointRawWeight coupling false false ≈ 1 := by
  have hlabel : componentLabel ([] : List Nat) =
      zeroEdgeLabelling := by
    funext edge
    rfl
  unfold adjacentCubeJointRawWeight adjacentCubeOccupationRoot
    canonicalSurfaceActivity
  rw [hlabel]
  exact parametricLocalizedSpinFoamWeight_zero_eqv_one coupling 6

theorem adjacentCubeJointRawWeight_true_false_eqv_pow_six
    (coupling : Q') :
    adjacentCubeJointRawWeight coupling true false ≈
      (coeffW coupling 1) ^ 6 := by
  exact axisCoarseRoot_canonicalSurfaceActivity_eqv_pow_six coupling
    zeroAxisOffset (Or.inl rfl)

theorem adjacentCubeJointRawWeight_false_true_eqv_pow_six
    (coupling : Q') :
    adjacentCubeJointRawWeight coupling false true ≈
      (coeffW coupling 1) ^ 6 := by
  exact axisCoarseRoot_canonicalSurfaceActivity_eqv_pow_six coupling
    xAxisOffset (Or.inr (Or.inl rfl))

theorem adjacentCubeJointRawWeight_true_true_eqv_pow_ten
    (coupling : Q') :
    adjacentCubeJointRawWeight coupling true true ≈
      (coeffW coupling 1) ^ 10 := by
  exact
    zeroXAxisCancelledRoot_canonicalSurfaceActivity_eqv_pow_ten coupling

theorem adjacentCubeJointRawWeight_swap
    (coupling : Q') (left right : Bool) :
    adjacentCubeJointRawWeight coupling left right ≈
      adjacentCubeJointRawWeight coupling right left := by
  cases left <;> cases right
  · exact Q'.eqv_refl _
  · exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 6) _
      (adjacentCubeJointRawWeight_false_true_eqv_pow_six coupling)
      (Q'.eqv_symm
        (adjacentCubeJointRawWeight_true_false_eqv_pow_six coupling))
  · exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 6) _
      (adjacentCubeJointRawWeight_true_false_eqv_pow_six coupling)
      (Q'.eqv_symm
        (adjacentCubeJointRawWeight_false_true_eqv_pow_six coupling))
  · exact Q'.eqv_refl _

/-! ## 2. One post-gluing normalization -/

def adjacentCubeConditionalPartition
    (coupling : Q') (left : Bool) : Q' :=
  listQSum (adjacentCubeJointRawWeight coupling left)
    adjacentCubeRightStateSpace

theorem adjacentCubeConditionalPartition_false_eqv
    (coupling : Q') :
    adjacentCubeConditionalPartition coupling false ≈
      1 + (coeffW coupling 1) ^ 6 := by
  change
    (adjacentCubeJointRawWeight coupling false false +
      (adjacentCubeJointRawWeight coupling false true + 0)) ≈
      1 + (coeffW coupling 1) ^ 6
  exact Q'.eqv_trans _
    (adjacentCubeJointRawWeight coupling false false +
      adjacentCubeJointRawWeight coupling false true) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.eqv_of_eq
        (Q'.add_zero'
          (adjacentCubeJointRawWeight coupling false true))))
    (Q'.add_eqv_congr'
      (adjacentCubeJointRawWeight_false_false_eqv_one coupling)
      (adjacentCubeJointRawWeight_false_true_eqv_pow_six coupling))

theorem adjacentCubeConditionalPartition_true_eqv
    (coupling : Q') :
    adjacentCubeConditionalPartition coupling true ≈
      (coeffW coupling 1) ^ 6 + (coeffW coupling 1) ^ 10 := by
  change
    (adjacentCubeJointRawWeight coupling true false +
      (adjacentCubeJointRawWeight coupling true true + 0)) ≈
      (coeffW coupling 1) ^ 6 + (coeffW coupling 1) ^ 10
  exact Q'.eqv_trans _
    (adjacentCubeJointRawWeight coupling true false +
      adjacentCubeJointRawWeight coupling true true) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.eqv_of_eq
        (Q'.add_zero'
          (adjacentCubeJointRawWeight coupling true true))))
    (Q'.add_eqv_congr'
      (adjacentCubeJointRawWeight_true_false_eqv_pow_six coupling)
      (adjacentCubeJointRawWeight_true_true_eqv_pow_ten coupling))

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

theorem adjacentCubeJointRawWeight_right_true_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (left : Bool) :
    (0 : Q') < adjacentCubeJointRawWeight coupling left true := by
  have hcoefficient :
      (0 : Q') < coeffW coupling 1 :=
    coeffW_pos hcoupling 1
  cases left
  · have hpow : (0 : Q') < (coeffW coupling 1) ^ 6 :=
      YMGap.Continuum.HKPos.pow_pos hcoefficient 6
    exact Q'.pos_of_lt_of_le hpow
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (adjacentCubeJointRawWeight_false_true_eqv_pow_six coupling)))
  · exact zeroXAxisCancelledRoot_activity_pos hcoupling

theorem adjacentCubeConditionalPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (left : Bool) :
    (0 : Q') < adjacentCubeConditionalPartition coupling left := by
  have hle := listQSum_member_le_local
    (adjacentCubeJointRawWeight coupling left)
    (adjacentCubeJointRawWeight_nonnegative
      (Q'.le_of_lt hcoupling) left)
    adjacentCubeRightStateSpace
    (adjacentCubeRightStateSpace_complete true)
  exact Q'.pos_of_lt_of_le
    (adjacentCubeJointRawWeight_right_true_pos hcoupling left) hle

def adjacentCubeConditionalKernel
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (left right : Bool) : Q' :=
  Q'.divPos
    (adjacentCubeJointRawWeight coupling left right)
    (adjacentCubeConditionalPartition coupling left)
    (adjacentCubeConditionalPartition_pos hcoupling left)

theorem adjacentCubeConditionalKernel_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (left right : Bool) :
    (0 : Q') ≤
      adjacentCubeConditionalKernel coupling hcoupling left right := by
  unfold adjacentCubeConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (adjacentCubeJointRawWeight_nonnegative
      (Q'.le_of_lt hcoupling) left right)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem adjacentCubeConditionalKernel_row_normalized
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (left : Bool) :
    listQSum
        (adjacentCubeConditionalKernel coupling hcoupling left)
        adjacentCubeRightStateSpace ≈ 1 := by
  unfold adjacentCubeConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (adjacentCubeConditionalPartition coupling left *
      Q'.recipPos (adjacentCubeConditionalPartition coupling left)
        (adjacentCubeConditionalPartition_pos hcoupling left)) _
    (listQSum_mul_right
      (adjacentCubeJointRawWeight coupling left)
      (Q'.recipPos (adjacentCubeConditionalPartition coupling left)
        (adjacentCubeConditionalPartition_pos hcoupling left))
      adjacentCubeRightStateSpace)
    (Q'.mul_recipPos_eqv _
      (adjacentCubeConditionalPartition_pos hcoupling left))

/-! ## 3. Exact reversibility of the normalized overlap law -/

theorem adjacentCubePartition_mul_kernel_eqv_raw
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (left right : Bool) :
    adjacentCubeConditionalPartition coupling left *
      adjacentCubeConditionalKernel coupling hcoupling left right ≈
      adjacentCubeJointRawWeight coupling left right := by
  unfold adjacentCubeConditionalKernel
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (adjacentCubeConditionalPartition coupling left)
      (Q'.divPos
        (adjacentCubeJointRawWeight coupling left right)
        (adjacentCubeConditionalPartition coupling left)
        (adjacentCubeConditionalPartition_pos hcoupling left)))
    (Q'.divPos_mul_eqv
      (adjacentCubeJointRawWeight coupling left right)
      (adjacentCubeConditionalPartition coupling left)
      (adjacentCubeConditionalPartition_pos hcoupling left))

/-- Detailed balance for the post-gluing two-state conditional law.  The
unnormalized source marginal is the exact conditional partition. -/
theorem adjacentCubeConditionalKernel_detailed_balance
    (coupling : Q') (hcoupling : (0 : Q') < coupling)
    (left right : Bool) :
    adjacentCubeConditionalPartition coupling left *
        adjacentCubeConditionalKernel coupling hcoupling left right ≈
      adjacentCubeConditionalPartition coupling right *
        adjacentCubeConditionalKernel coupling hcoupling right left := by
  exact Q'.eqv_trans _ _ _
    (adjacentCubePartition_mul_kernel_eqv_raw
      coupling hcoupling left right)
    (Q'.eqv_trans _ _ _
      (adjacentCubeJointRawWeight_swap coupling left right)
      (Q'.eqv_symm
        (adjacentCubePartition_mul_kernel_eqv_raw
          coupling hcoupling right left)))

/-! ## 4. The normalized row is genuinely source dependent -/

private theorem pow_eqv_congr_local {a b : Q'} (hab : a ≈ b) :
    ∀ exponent : Nat, a ^ exponent ≈ b ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      change a * a ^ exponent ≈ b * b ^ exponent
      exact Q'.eqv_trans _ (b * a ^ exponent) _
        (Q'.mul_eqv_congr_right _ _ _ hab)
        (Q'.mul_eqv_congr_left _ _ _
          (pow_eqv_congr_local hab exponent))

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

def anchorLeftVacantRightOccupiedProbability : Q' :=
  Q'.divPos
    (anchorFaceCoefficient ^ 6)
    (1 + anchorFaceCoefficient ^ 6)
    (by decide)

def anchorLeftOccupiedRightOccupiedProbability : Q' :=
  Q'.divPos
    (anchorFaceCoefficient ^ 10)
    (anchorFaceCoefficient ^ 6 + anchorFaceCoefficient ^ 10)
    (by decide)

theorem anchorRightOccupiedProbabilities_ne :
    ¬ anchorLeftVacantRightOccupiedProbability ≈
      anchorLeftOccupiedRightOccupiedProbability := by
  decide

theorem adjacentCubeConditionalKernel_anchor_false_true_eqv :
    adjacentCubeConditionalKernel anchorCoupling (by decide) false true ≈
      anchorLeftVacantRightOccupiedProbability := by
  have hpowSix := pow_eqv_congr_local anchorFundamentalCoefficient 6
  have hden :
      adjacentCubeConditionalPartition anchorCoupling false ≈
        1 + anchorFaceCoefficient ^ 6 :=
    Q'.eqv_trans _ (1 + (coeffW anchorCoupling 1) ^ 6) _
      (adjacentCubeConditionalPartition_false_eqv anchorCoupling)
      (Q'.add_eqv_congr' (Q'.eqv_refl 1) hpowSix)
  unfold adjacentCubeConditionalKernel
    anchorLeftVacantRightOccupiedProbability
  exact divPos_eqv_congr_local
    (adjacentCubeConditionalPartition_pos (by decide) false)
    (by decide)
    (Q'.eqv_trans _ ((coeffW anchorCoupling 1) ^ 6) _
      (adjacentCubeJointRawWeight_false_true_eqv_pow_six
        anchorCoupling)
      hpowSix)
    hden

theorem adjacentCubeConditionalKernel_anchor_true_true_eqv :
    adjacentCubeConditionalKernel anchorCoupling (by decide) true true ≈
      anchorLeftOccupiedRightOccupiedProbability := by
  have hpowSix := pow_eqv_congr_local anchorFundamentalCoefficient 6
  have hpowTen := pow_eqv_congr_local anchorFundamentalCoefficient 10
  have hden :
      adjacentCubeConditionalPartition anchorCoupling true ≈
        anchorFaceCoefficient ^ 6 + anchorFaceCoefficient ^ 10 :=
    Q'.eqv_trans _
      ((coeffW anchorCoupling 1) ^ 6 +
        (coeffW anchorCoupling 1) ^ 10) _
      (adjacentCubeConditionalPartition_true_eqv anchorCoupling)
      (Q'.add_eqv_congr' hpowSix hpowTen)
  unfold adjacentCubeConditionalKernel
    anchorLeftOccupiedRightOccupiedProbability
  exact divPos_eqv_congr_local
    (adjacentCubeConditionalPartition_pos (by decide) true)
    (by decide)
    (Q'.eqv_trans _ ((coeffW anchorCoupling 1) ^ 10) _
      (adjacentCubeJointRawWeight_true_true_eqv_pow_ten
        anchorCoupling)
      hpowTen)
    hden

theorem adjacentCubeConditionalKernel_anchor_source_dependent :
    ¬ adjacentCubeConditionalKernel anchorCoupling (by decide) false true ≈
      adjacentCubeConditionalKernel anchorCoupling (by decide) true true := by
  intro hequal
  apply anchorRightOccupiedProbabilities_ne
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      adjacentCubeConditionalKernel_anchor_false_true_eqv)
    (Q'.eqv_trans _ _ _ hequal
      adjacentCubeConditionalKernel_anchor_true_true_eqv)

#print axioms adjacentCubeJointRawWeight_false_false_eqv_one
#print axioms adjacentCubeJointRawWeight_true_false_eqv_pow_six
#print axioms adjacentCubeJointRawWeight_false_true_eqv_pow_six
#print axioms adjacentCubeJointRawWeight_true_true_eqv_pow_ten
#print axioms adjacentCubeJointRawWeight_swap
#print axioms adjacentCubeConditionalPartition_pos
#print axioms adjacentCubeConditionalKernel_nonnegative
#print axioms adjacentCubeConditionalKernel_row_normalized
#print axioms adjacentCubePartition_mul_kernel_eqv_raw
#print axioms adjacentCubeConditionalKernel_detailed_balance
#print axioms anchorRightOccupiedProbabilities_ne
#print axioms adjacentCubeConditionalKernel_anchor_false_true_eqv
#print axioms adjacentCubeConditionalKernel_anchor_true_true_eqv
#print axioms adjacentCubeConditionalKernel_anchor_source_dependent

end YMGap.Continuum.Z4AdjacentCubeCancellationConditionalKernel
