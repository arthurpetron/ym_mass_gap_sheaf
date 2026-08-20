/-
# A strict cutoff-two vacuum-centered physical excitation

The vacuum and lower-cube states are embedded through a two-element Boolean
index.  Giving the cube coefficient one and the vacuum coefficient the
negative vacuum/cube Gram entry produces a vector whose physical Gram pairing
with the vacuum is exactly zero.  Its physical quadratic form is the strict
vacuum/cube determinant and, independently, the generic finite Gram theorem
identifies it with a literal weighted sum of squared channel residuals.

This is a finite `K = 2`, half-extent-zero excitation.  It is not an invariant
transfer eigenstate, a cutoff-uniform spectral gap, or a continuum mass-gap
theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation

set_option maxRecDepth 300000
set_option maxHeartbeats 200000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDeterminant
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramDiagonal
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

/-! ## 1. The explicit vacuum/cube coefficient vector -/

/-- `false` is the vacuum and `true` is the lower-cube state. -/
def cutoffTwoVacuumCubeState : Bool → EdgeLabelling
  | false => zeroEdgeLabelling
  | true => centralLowerCubeState

/-- Coefficients of `cube - (1/4096) vacuum`. -/
def cutoffTwoVacuumCenteredCubeCoefficient : Bool → Q'
  | false => -cutoffTwoCubeLowerFaceScalar
  | true => 1

def cutoffTwoVacuumCubeIndex : List Bool := [false, true]

theorem cutoffTwoVacuumCubeState_mem (side : Bool) :
    cutoffTwoVacuumCubeState side ∈ centralHalfStates 2 0 := by
  cases side
  · exact zeroEdgeLabelling_mem_centralHalfStates 2 0
  · exact centralLowerCubeState_mem_centralHalfStates (by decide)

/-! ## 2. Exact vacuum orthogonality -/

/-- Physical Gram pairing of the explicit two-state vector with the vacuum. -/
def cutoffTwoVacuumCenteredCubeVacuumPairing : Q' :=
  (-cutoffTwoCubeLowerFaceScalar) *
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling zeroEdgeLabelling +
    (1 : Q') *
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        centralLowerCubeState zeroEdgeLabelling

theorem cutoffTwoVacuumCenteredCubeVacuumPairing_eqv_zero :
    cutoffTwoVacuumCenteredCubeVacuumPairing ≈ 0 := by
  unfold cutoffTwoVacuumCenteredCubeVacuumPairing
  refine Q'.eqv_trans _
    ((-cutoffTwoCubeLowerFaceScalar) * 1 +
      (1 : Q') * cutoffTwoCubeLowerFaceScalar) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (-cutoffTwoCubeLowerFaceScalar) _ _
        centralPhysicalReflectedKernel_cutoffTwo_vacuum_diagonal_eqv_one)
      (Q'.mul_eqv_congr_left 1 _ _
        centralPhysicalReflectedKernel_cutoffTwo_cube_vacuum_eqv)
  · ac_qeqv

/-! ## 3. Physical quadratic and its literal channel SOS -/

/-- The genuine physical quadratic form restricted to the displayed
two-state coefficient vector. -/
def cutoffTwoVacuumCenteredCubePhysicalQuadratic : Q' :=
  listQSum
    (fun left =>
      listQSum
        (fun right =>
          (cutoffTwoVacuumCenteredCubeCoefficient left *
              cutoffTwoVacuumCenteredCubeCoefficient right) *
            centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
              (cutoffTwoVacuumCubeState left)
              (cutoffTwoVacuumCubeState right))
        cutoffTwoVacuumCubeIndex)
    cutoffTwoVacuumCubeIndex

/-- The same excitation as a manifest finite sum of boundary weights times
squared channel residual amplitudes. -/
def cutoffTwoVacuumCenteredCubeChannelSOS : Q' :=
  weightedGramSOS
    cutoffTwoVacuumCubeIndex
    (centralBoundaryChannels 2 0)
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
    (fun side boundary =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0
        (cutoffTwoVacuumCubeState side) boundary)
    cutoffTwoVacuumCenteredCubeCoefficient

private theorem cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_weighted :
    cutoffTwoVacuumCenteredCubePhysicalQuadratic ≈
      weightedGramQuadratic
        cutoffTwoVacuumCubeIndex
        (centralBoundaryChannels 2 0)
        (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
        (fun side boundary =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            (cutoffTwoVacuumCubeState side) boundary)
        cutoffTwoVacuumCenteredCubeCoefficient := by
  unfold cutoffTwoVacuumCenteredCubePhysicalQuadratic weightedGramQuadratic
  apply listQSum_congr
  intro left
  apply listQSum_congr
  intro right
  exact Q'.mul_eqv_congr_left _ _ _
    (centralPhysicalReflectedKernel_eq_weightedGram
      cutoffTwoHalfCoupling
      (cutoffTwoVacuumCubeState_mem left)
      (cutoffTwoVacuumCubeState_mem right))

theorem cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_channelSOS :
    cutoffTwoVacuumCenteredCubePhysicalQuadratic ≈
      cutoffTwoVacuumCenteredCubeChannelSOS := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_weighted
    (weightedGramQuadratic_eq_sos
      cutoffTwoVacuumCubeIndex
      (centralBoundaryChannels 2 0)
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
      (fun side boundary =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          (cutoffTwoVacuumCubeState side) boundary)
      cutoffTwoVacuumCenteredCubeCoefficient)

/-! ## 4. Exact identification with the strict determinant -/

private def cutoffTwoVacuumCubeExpectedKernel : Bool → Bool → Q'
  | false, false => 1
  | false, true => cutoffTwoCubeLowerFaceScalar
  | true, false => cutoffTwoCubeLowerFaceScalar
  | true, true => cutoffTwoCubeExpectedPhysicalGramDiagonal

private theorem cutoffTwoVacuumCubeKernel_eqv_expected
    (left right : Bool) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoVacuumCubeState left)
        (cutoffTwoVacuumCubeState right) ≈
      cutoffTwoVacuumCubeExpectedKernel left right := by
  cases left <;> cases right
  · exact centralPhysicalReflectedKernel_cutoffTwo_vacuum_diagonal_eqv_one
  · exact centralPhysicalReflectedKernel_cutoffTwo_vacuum_cube_eqv
  · exact centralPhysicalReflectedKernel_cutoffTwo_cube_vacuum_eqv
  · exact centralPhysicalReflectedKernel_cutoffTwo_cube_diagonal_eqv

private theorem listQSum_pair_eqv
    {A : Type} (value : A → Q') (first second : A) :
    listQSum value [first, second] ≈ value first + value second := by
  unfold listQSum
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl (value first))
    (Q'.eqv_of_eq (Q'.add_zero' (value second)))

private theorem listQSum_bool_square_eqv
    (value : Bool → Bool → Q') :
    listQSum
        (fun left => listQSum (value left) [false, true])
        [false, true] ≈
      (value false false + value false true) +
        (value true false + value true true) := by
  refine Q'.eqv_trans _
    (listQSum (value false) [false, true] +
      listQSum (value true) [false, true]) _ ?_ ?_
  · exact listQSum_pair_eqv
      (fun left => listQSum (value left) [false, true]) false true
  · exact Q'.add_eqv_congr'
      (listQSum_pair_eqv (value false) false true)
      (listQSum_pair_eqv (value true) false true)

private theorem centeredTwoStateFourTermReduction
    (cross diagonal : Q') :
    (((-cross * -cross) * 1 +
        (-cross * 1) * cross) +
      ((1 * -cross) * cross +
        (1 * 1) * diagonal)) ≈
      diagonal + -(cross * cross) := by
  have hnegNeg : (-cross) * (-cross) ≈ cross * cross := by
    refine Q'.eqv_trans _ (-(cross * (-cross))) _
      (Q'.neg_mul_eqv cross (-cross)) ?_
    refine Q'.eqv_trans _ (-(-(cross * cross))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv cross cross)
    · exact Q'.neg_neg_eqv (cross * cross)
  have hfirst : ((-cross * -cross) * 1) ≈ cross * cross := by
    exact Q'.eqv_trans _ ((cross * cross) * 1) _
      (Q'.mul_eqv_congr_right _ _ 1 hnegNeg)
      (Q'.mul_one_eqv (cross * cross))
  have hsecond : ((-cross * 1) * cross) ≈ -(cross * cross) := by
    exact Q'.eqv_trans _ ((-cross) * cross) _
      (Q'.mul_eqv_congr_right _ _ cross (Q'.mul_one_eqv (-cross)))
      (Q'.neg_mul_eqv cross cross)
  have hthird : ((1 * -cross) * cross) ≈ -(cross * cross) := by
    exact Q'.eqv_trans _ ((-cross) * cross) _
      (Q'.mul_eqv_congr_right _ _ cross (Q'.one_mul_eqv (-cross)))
      (Q'.neg_mul_eqv cross cross)
  have hfourth : ((1 * 1) * diagonal) ≈ diagonal := by
    refine Q'.eqv_trans _ (1 * diagonal) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ diagonal (Q'.one_mul_eqv 1)
    · exact Q'.one_mul_eqv diagonal
  refine Q'.eqv_trans _
    ((cross * cross + -(cross * cross)) +
      (-(cross * cross) + diagonal)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hfirst hsecond)
      (Q'.add_eqv_congr' hthird hfourth)
  refine Q'.eqv_trans _
    (0 + (diagonal + -(cross * cross))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_neg_self_eqv (cross * cross))
      (Q'.add_comm_eqv (-(cross * cross)) diagonal)
  · exact Q'.eqv_of_eq (Q'.zero_add' _)

private theorem centeredDiagonalFactorization
    (cross interface : Q') :
    (cross * cross) * interface + -(cross * cross) ≈
      (cross * cross) * (interface + -(1 : Q')) := by
  have hneg : (cross * cross) * (-(1 : Q')) ≈
      -(cross * cross) := by
    exact Q'.eqv_trans _ (-(cross * cross * 1)) _
      (Q'.mul_neg_eqv (cross * cross) 1)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (cross * cross)))
  refine Q'.eqv_trans _
    ((cross * cross) * interface +
      (cross * cross) * (-(1 : Q'))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm hneg)
  · exact Q'.eqv_symm
      (Q'.mul_add_eqv (cross * cross) interface (-(1 : Q')))

theorem cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_expected :
    cutoffTwoVacuumCenteredCubePhysicalQuadratic ≈
      cutoffTwoVacuumCubeExpectedGramDeterminant := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            (cutoffTwoVacuumCenteredCubeCoefficient left *
                cutoffTwoVacuumCenteredCubeCoefficient right) *
              cutoffTwoVacuumCubeExpectedKernel left right)
          cutoffTwoVacuumCubeIndex)
      cutoffTwoVacuumCubeIndex) _ ?_ ?_
  · unfold cutoffTwoVacuumCenteredCubePhysicalQuadratic
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.mul_eqv_congr_left _ _ _
      (cutoffTwoVacuumCubeKernel_eqv_expected left right)
  · unfold cutoffTwoVacuumCubeIndex
    refine Q'.eqv_trans _
      (((-cutoffTwoCubeLowerFaceScalar *
            -cutoffTwoCubeLowerFaceScalar) * 1 +
          (-cutoffTwoCubeLowerFaceScalar * 1) *
            cutoffTwoCubeLowerFaceScalar) +
        ((1 * -cutoffTwoCubeLowerFaceScalar) *
            cutoffTwoCubeLowerFaceScalar +
          (1 * 1) * cutoffTwoCubeExpectedPhysicalGramDiagonal)) _ ?_ ?_
    · simpa only [cutoffTwoVacuumCenteredCubeCoefficient,
        cutoffTwoVacuumCubeExpectedKernel] using
        (listQSum_bool_square_eqv
          (fun left right =>
            (cutoffTwoVacuumCenteredCubeCoefficient left *
                cutoffTwoVacuumCenteredCubeCoefficient right) *
              cutoffTwoVacuumCubeExpectedKernel left right))
    refine Q'.eqv_trans _
      (cutoffTwoCubeExpectedPhysicalGramDiagonal +
        -(cutoffTwoCubeLowerFaceScalar *
          cutoffTwoCubeLowerFaceScalar)) _ ?_ ?_
    · exact centeredTwoStateFourTermReduction
        cutoffTwoCubeLowerFaceScalar
        cutoffTwoCubeExpectedPhysicalGramDiagonal
    unfold cutoffTwoCubeExpectedPhysicalGramDiagonal
      cutoffTwoCubeGramScalar
      cutoffTwoVacuumCubeExpectedGramDeterminant
    exact centeredDiagonalFactorization
      cutoffTwoCubeLowerFaceScalar cutoffTwoCubeExpectedInterfaceSum

theorem cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_determinant :
    cutoffTwoVacuumCenteredCubePhysicalQuadratic ≈
      cutoffTwoVacuumCubePhysicalGramDeterminant := by
  exact Q'.eqv_trans _ cutoffTwoVacuumCubeExpectedGramDeterminant _
    cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_expected
    (Q'.eqv_symm cutoffTwoVacuumCubePhysicalGramDeterminant_eqv)

theorem cutoffTwoVacuumCenteredCubePhysicalQuadratic_pos :
    (0 : Q') < cutoffTwoVacuumCenteredCubePhysicalQuadratic := by
  exact Q'.pos_of_lt_of_le
    cutoffTwoVacuumCubeExpectedGramDeterminant_pos
    (Q'.ge_of_eqv
      cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_expected)

theorem cutoffTwoVacuumCenteredCubeChannelSOS_pos :
    (0 : Q') < cutoffTwoVacuumCenteredCubeChannelSOS := by
  exact Q'.pos_of_lt_of_le
    cutoffTwoVacuumCenteredCubePhysicalQuadratic_pos
    (Q'.le_of_eqv
      cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_channelSOS)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation.cutoffTwoVacuumCenteredCubeVacuumPairing_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation.cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_channelSOS
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation.cutoffTwoVacuumCenteredCubePhysicalQuadratic_eqv_determinant
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation.cutoffTwoVacuumCenteredCubePhysicalQuadratic_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitation.cutoffTwoVacuumCenteredCubeChannelSOS_pos
