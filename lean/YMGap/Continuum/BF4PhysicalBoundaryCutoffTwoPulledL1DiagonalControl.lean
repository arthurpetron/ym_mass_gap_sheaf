/-
# L1-to-diagonal coercivity on the pulled cutoff-two vacuum carrier

Entrywise cutoff errors naturally carry the square of a finite coefficient
`l1` envelope.  A relative form perturbation instead needs that envelope to
be controlled by the physical diagonal.  This module proves the missing
finite-dimensional bridge constructively.

First, a list-level Cauchy--Schwarz argument gives

    ||x||_1^2 <= |S| * sum_{s in S} x_s^2.

Second, the already verified uniform positive physical row floor is placed
below every pulled weight of the canonical cutoff-two vacuum component at
all sufficiently late representation cutoffs.  Combining the two results
gives

    floor * ||x||_1^2 <= |S| * D_later(x).

This is a genuine quantitative ingredient for converting entrywise kernel
errors into relative diagonal errors.  It does not bound the total kernel
perturbation from cutoff two, and hence does not by itself prove persistence
of the `49/50` gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_const_eqv_length_mul
    {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_eqv_length_mul constant tail)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * constant) constant)

private theorem listQSum_pair_double_eqv
    {A : Type} (value : A → A → Q') (items : List A) :
    listQSum
        (fun left => listQSum
          (fun right => value left right + value left right) items)
        items ≈
      listQSum (fun left => listQSum (value left) items) items +
        listQSum (fun left => listQSum (value left) items) items := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (value left) items + listQSum (value left) items)
      items) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact listQSum_add (value left) (value left) items
  · exact listQSum_add
      (fun left => listQSum (value left) items)
      (fun left => listQSum (value left) items) items

/-- Finite-list Cauchy--Schwarz in the exact `coefficientL1` normalization. -/
theorem coefficientL1_square_le_length_mul_squareSum
    {State : Type} (states : List State) (coefficient : State → Q') :
    coefficientL1 states coefficient * coefficientL1 states coefficient ≤
      Q'.ofNat states.length *
        listQSum
          (fun state => coefficient state * coefficient state) states := by
  let absolute : State → Q' := fun state => Q'.abs (coefficient state)
  let square : State → Q' := fun state => coefficient state * coefficient state
  let pair : State → State → Q' := fun left right => absolute left * absolute right
  let l1 := listQSum absolute states
  let squareSum := listQSum square states
  let count := Q'.ofNat states.length
  have hpair : ∀ left right,
      pair left right + pair left right ≤ square left + square right := by
    intro left right
    refine Q'.le_trans' _ _ _
      (amgm_two (absolute left) (absolute right)) ?_
    exact Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (Q'.abs_mul_self_eqv (coefficient left))
        (Q'.abs_mul_self_eqv (coefficient right)))
  have hdouble :
      listQSum
          (fun left => listQSum
            (fun right => pair left right + pair left right) states)
          states ≤
        listQSum
          (fun left => listQSum
            (fun right => square left + square right) states)
          states := by
    apply listQSum_mono
    intro left _hleft
    apply listQSum_mono
    intro right _hright
    exact hpair left right
  have hleft :
      listQSum
          (fun left => listQSum
            (fun right => pair left right + pair left right) states)
          states ≈
        (l1 * l1) + (l1 * l1) := by
    refine Q'.eqv_trans _
      (listQSum (fun left => listQSum (pair left) states) states +
        listQSum (fun left => listQSum (pair left) states) states) _
      (listQSum_pair_double_eqv pair states) ?_
    exact Q'.add_eqv_congr'
      (listQSum_product absolute absolute states states)
      (listQSum_product absolute absolute states states)
  have hrightInner : ∀ left,
      listQSum (fun right => square left + square right) states ≈
        count * square left + squareSum := by
    intro left
    refine Q'.eqv_trans _
      (listQSum (fun _right => square left) states +
        listQSum square states) _
      (listQSum_add (fun _right => square left) square states) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (listQSum_const_eqv_length_mul (square left) states)
  have hright :
      listQSum
          (fun left => listQSum
            (fun right => square left + square right) states)
          states ≈
        (count * squareSum) + (count * squareSum) := by
    refine Q'.eqv_trans _
      (listQSum (fun left => count * square left + squareSum) states) _ ?_ ?_
    · exact listQSum_congr hrightInner states
    refine Q'.eqv_trans _
      (listQSum (fun left => count * square left) states +
        listQSum (fun _left => squareSum) states) _
      (listQSum_add
        (fun left => count * square left)
        (fun _left => squareSum) states) ?_
    exact Q'.add_eqv_congr'
      (listQSum_mul_left count square states)
      (listQSum_const_eqv_length_mul squareSum states)
  have htwice : (l1 * l1) + (l1 * l1) ≤
      (count * squareSum) + (count * squareSum) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (Q'.le_trans' _ _ _ hdouble (Q'.le_of_eqv hright))
  have htwoMul :
      Q'.ofNat 2 * (l1 * l1) ≤
        Q'.ofNat 2 * (count * squareSum) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.CubeRatioBounds.ofNat_two_mul_eqv (l1 * l1)))
      (Q'.le_trans' _ _ _ htwice
        (Q'.ge_of_eqv
          (YMGap.Continuum.CubeRatioBounds.ofNat_two_mul_eqv
            (count * squareSum))))
  exact le_of_mul_le_mul_left_pos (Q'.ofNat_succ_pos 1) htwoMul

/-- A pointwise positive weight floor converts the finite `l1` square into
the corresponding weighted diagonal form. -/
theorem floor_mul_coefficientL1_square_le_length_mul_diagonal
    {State : Type} (states : List State)
    (weight : State → Q') (coefficient : State → Q') (floor : Q')
    (hfloor0 : (0 : Q') ≤ floor)
    (hfloor : ∀ state, state ∈ states → floor ≤ weight state) :
    floor *
        (coefficientL1 states coefficient * coefficientL1 states coefficient) ≤
      Q'.ofNat states.length *
        listQSum
          (fun state =>
            (coefficient state * coefficient state) * weight state)
          states := by
  let square : State → Q' := fun state => coefficient state * coefficient state
  let squareSum := listQSum square states
  let diagonal := listQSum (fun state => square state * weight state) states
  let count := Q'.ofNat states.length
  have hsquare0 : ∀ state, (0 : Q') ≤ square state :=
    fun state => SumOfSquares.q_mul_self_nonneg (coefficient state)
  have hweighted : floor * squareSum ≤ diagonal := by
    refine Q'.le_trans' _
      (listQSum (fun state => floor * square state) states) _ ?_ ?_
    · exact Q'.le_of_eqv
        (Q'.eqv_symm (listQSum_mul_left floor square states))
    · apply listQSum_mono
      intro state hstate
      exact Q'.le_trans' _ (square state * floor) _
        (Q'.le_of_eqv (Q'.mul_comm_eqv floor (square state)))
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (hfloor state hstate) (hsquare0 state))
  have hcs := coefficientL1_square_le_length_mul_squareSum states coefficient
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ _ hcs hfloor0
  have hreorder :
      floor * (count * squareSum) ≈ count * (floor * squareSum) := by
    refine Q'.eqv_trans _ ((floor * count) * squareSum) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv floor count squareSum)) ?_
    refine Q'.eqv_trans _ ((count * floor) * squareSum) _
      (Q'.mul_eqv_congr_right _ _ squareSum
        (Q'.mul_comm_eqv floor count)) ?_
    exact Q'.mul_assoc_eqv count floor squareSum
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hweighted
        (ExpNeg.ofNat_nonneg' states.length)))

/-! ## Physical specialization -/

def cutoffTwoPulledRowFloorAnchor : Nat :=
  max 2 (centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0)

def cutoffTwoPulledUniformPositiveRowFloor : Q' :=
  centralPhysicalMovingPositiveRowFloor
    cutoffTwoHalfCoupling (by decide) cutoffTwoPulledRowFloorAnchor 0

theorem cutoffTwoPulledUniformPositiveRowFloor_pos :
    (0 : Q') < cutoffTwoPulledUniformPositiveRowFloor :=
  centralPhysicalMovingPositiveRowFloor_pos
    cutoffTwoHalfCoupling (by decide) cutoffTwoPulledRowFloorAnchor 0

/-- Every canonical cutoff-two vacuum state has the fixed positive physical
row floor at every cutoff beyond the explicit row-floor schedule. -/
theorem cutoffTwoPulledUniformPositiveRowFloor_le_weight
    {later index : Nat}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0) :
    cutoffTwoPulledUniformPositiveRowFloor ≤
      centralPhysicalFinitePulledWeight
        cutoffTwoHalfCoupling (by decide) 2 later 0 index := by
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hindex
  have hbaseAnchor : 2 ≤ cutoffTwoPulledRowFloorAnchor := by
    unfold cutoffTwoPulledRowFloorAnchor
    exact Nat.le_max_left _ _
  have hretained :
      centralPhysicalUniformRowFloorCutoff cutoffTwoHalfCoupling 0 ≤
        cutoffTwoPulledRowFloorAnchor := by
    unfold cutoffTwoPulledRowFloorAnchor
    exact Nat.le_max_right _ _
  have hbaseLater : 2 ≤ later := Nat.le_trans hbaseAnchor hlater
  have hsourceBase := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) 2 0 hindexLt
  have hsourceAnchor := mem_centralPositiveHalfStates_of_le
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
    hbaseAnchor hsourceBase
  have hfloor := centralPhysicalMovingPositiveRowFloor_le
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    hretained hlater hsourceAnchor
  unfold cutoffTwoPulledUniformPositiveRowFloor
  rw [centralPhysicalFinitePulledWeight_eq_rowMarginal hbaseLater hindexLt]
  exact hfloor

/-- The exact physical norm conversion needed by pulled entrywise kernel
stability on the fixed cutoff-two vacuum carrier. -/
theorem cutoffTwoPulled_coefficientL1_square_control
    {later : Nat}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (coefficient : Nat → Q') :
    cutoffTwoPulledUniformPositiveRowFloor *
        (coefficientL1
            (centralPhysicalFiniteVacuumSectorIndices
              cutoffTwoHalfCoupling (by decide) 2 0)
            coefficient *
          coefficientL1
            (centralPhysicalFiniteVacuumSectorIndices
              cutoffTwoHalfCoupling (by decide) 2 0)
            coefficient) ≤
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorIndices
            cutoffTwoHalfCoupling (by decide) 2 0).length *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient := by
  exact floor_mul_coefficientL1_square_le_length_mul_diagonal
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) 2 0)
    (centralPhysicalFinitePulledWeight
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient cutoffTwoPulledUniformPositiveRowFloor
    (Q'.le_of_lt cutoffTwoPulledUniformPositiveRowFloor_pos)
    (fun index hindex =>
      cutoffTwoPulledUniformPositiveRowFloor_le_weight hlater hindex)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl.coefficientL1_square_le_length_mul_squareSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl.floor_mul_coefficientL1_square_le_length_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl.cutoffTwoPulledUniformPositiveRowFloor_le_weight
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl.cutoffTwoPulled_coefficientL1_square_control
