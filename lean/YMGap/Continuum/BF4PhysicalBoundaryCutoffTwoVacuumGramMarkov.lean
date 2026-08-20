/-
# The cutoff-two vacuum row of the genuine reflected physical Gram

The ternary delta certificate for the vacuum half-amplitude collapses the
genuine reflected BF4 Gram row at the vacuum source to the opposite
source-to-vacuum half-amplitude, multiplied by the positive vacuum interface
weight.  Its retained row mass is therefore the already certified cutoff-two
column denominator.  After row normalization, the physical Gram vacuum row is
exactly the posterior-refresh row and annihilates the explicit centered
excitation mode.

This is one finite physical row at `K = 2`, half extent zero, and coupling
`1/2`.  It does not show that the refresh sector is invariant under all
physical rows and is not a cutoff-uniform, volume-uniform, or continuum gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumDeltaRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

private theorem eqv_divPos_of_mul_local
    {a numerator denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hmul : a * denominator ≈ numerator) :
    a ≈ Q'.divPos numerator denominator hdenominator := by
  apply Q'.mul_left_cancel_of_pos hdenominator
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv denominator a) ?_
  refine Q'.eqv_trans _ _ _ hmul ?_
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv denominator
        (Q'.divPos numerator denominator hdenominator))
      (Q'.divPos_mul_eqv numerator denominator hdenominator))

/-! ## 1. Exact ternary-delta contraction against any row -/

private theorem eliminateHead_ternaryVacuum_mul
    (value : List Nat → Q') (tail : List Nat) :
    eliminateHead 3
        (fun word => binaryVacuumWordWeight word * value word) tail ≈
      binaryVacuumWordWeight tail * value (0 :: tail) := by
  unfold eliminateHead
  change
    binaryVacuumWordWeight (0 :: tail) * value (0 :: tail) +
      (binaryVacuumWordWeight (1 :: tail) * value (1 :: tail) +
        (binaryVacuumWordWeight (2 :: tail) * value (2 :: tail) + 0)) ≈
      binaryVacuumWordWeight tail * value (0 :: tail)
  cases htail : binaryVacuumWordB tail with
  | false =>
      simp only [binaryVacuumWordWeight, binaryVacuumWordB, htail,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact Q'.eqv_trans _ (0 + (0 + (0 + 0))) _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv _)
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv _)
            (Q'.add_eqv_congr'
              (Q'.zero_mul_eqv _) (Q'.eqv_refl 0))))
        (by
          rw [Q'.zero_add', Q'.zero_add', Q'.zero_add']
          exact Q'.eqv_symm (Q'.zero_mul_eqv _))
  | true =>
      simp only [binaryVacuumWordWeight, binaryVacuumWordB, htail,
        decide_true, Bool.true_and, ↓reduceIte]
      exact Q'.eqv_trans _
        (value (0 :: tail) + (0 + (0 + 0))) _
        (Q'.add_eqv_congr'
          (Q'.one_mul_eqv _)
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv _)
            (Q'.add_eqv_congr'
              (Q'.zero_mul_eqv _) (Q'.eqv_refl 0))))
        (Q'.eqv_trans _ (value (0 :: tail)) _
          (by
            rw [Q'.zero_add', Q'.zero_add', Q'.add_zero']
            exact Q'.eqv_refl _)
          (Q'.eqv_symm (Q'.one_mul_eqv _)))

private theorem finiteAssignmentSum_ternaryVacuumWordWeight_mul
    (value : List Nat → Q') : ∀ variables : Nat,
    finiteAssignmentSum 3 variables
        (fun word => binaryVacuumWordWeight word * value word) ≈
      value (List.replicate variables 0)
  | 0 => by
      unfold finiteAssignmentSum allSeqs listQSum
      change 1 * value [] + 0 ≈ value []
      exact Q'.eqv_trans _ (value [] + 0) _
        (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl 0))
        (Q'.eqv_of_eq (Q'.add_zero' _))
  | variables + 1 => by
      refine Q'.eqv_trans _
        (finiteAssignmentSum 3 variables
          (eliminateHead 3
            (fun word => binaryVacuumWordWeight word * value word))) _
        (finiteAssignmentSum_succ_eqv_eliminateHead 3 variables _) ?_
      refine Q'.eqv_trans _
        (finiteAssignmentSum 3 variables
          (fun tail =>
            binaryVacuumWordWeight tail * value (0 :: tail))) _ ?_ ?_
      · unfold finiteAssignmentSum
        apply listQSum_congr_on
        intro tail _
        exact eliminateHead_ternaryVacuum_mul value tail
      · simpa [List.replicate_succ] using
          (finiteAssignmentSum_ternaryVacuumWordWeight_mul
            (fun tail => value (0 :: tail)) variables)

private theorem rotate_vacuum_delta
    (weight delta target : Q') :
    weight * (delta * target) ≈ delta * (weight * target) := by
  refine Q'.eqv_trans _ ((weight * delta) * target) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv weight delta target)) ?_
  refine Q'.eqv_trans _ ((delta * weight) * target) _
    (Q'.mul_eqv_congr_right _ _ target
      (Q'.mul_comm_eqv weight delta)) ?_
  exact Q'.mul_assoc_eqv delta weight target

/-! ## 2. Genuine reflected physical vacuum row -/

theorem centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffTwoVacuumColumnCarrier) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling
        2 0 zeroEdgeLabelling target ≈
      centralBoundaryWeight cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling *
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          target zeroEdgeLabelling := by
  let edges := centralFixedFaceIds 0
  let decode := wordToEdgeLabelling edges
  let value : List Nat → Q' := fun word =>
    centralBoundaryWeight cutoffTwoHalfCoupling 2 0 (decode word) *
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 target (decode word)
  refine Q'.eqv_trans _
    (weightedGram (centralBoundaryChannels 2 0)
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 0)
      (centralHalfAmplitude cutoffTwoHalfCoupling 2 0)
      zeroEdgeLabelling target) _ ?_ ?_
  · exact centralPhysicalReflectedKernel_eq_weightedGram
      cutoffTwoHalfCoupling
      (zeroEdgeLabelling_mem_centralHalfStates 2 0)
      ((mem_centralPositiveHalfStates_iff.mp htarget).1)
  unfold weightedGram
  rw [centralBoundaryChannels_eq_map_allSeqs]
  refine Q'.eqv_trans _
    (finiteAssignmentSum 3 edges.length
      (fun word => binaryVacuumWordWeight word * value word)) _ ?_ ?_
  · unfold finiteAssignmentSum
    refine Q'.eqv_trans _
      (listQSum
        (fun word =>
          centralBoundaryWeight cutoffTwoHalfCoupling 2 0 (decode word) *
            (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
                zeroEdgeLabelling (decode word) *
              centralHalfAmplitude cutoffTwoHalfCoupling 2 0
                target (decode word)))
        (allSeqs 3 edges.length)) _ ?_ ?_
    · exact Q'.eqv_of_eq
        (listQSum_map
          (fun boundary =>
            centralBoundaryWeight cutoffTwoHalfCoupling 2 0 boundary *
              (centralHalfAmplitude cutoffTwoHalfCoupling 2 0
                  zeroEdgeLabelling boundary *
                centralHalfAmplitude cutoffTwoHalfCoupling 2 0
                  target boundary))
          decode (allSeqs 3 edges.length))
    refine Q'.eqv_trans _
      (listQSum
        (fun word =>
          centralBoundaryWeight cutoffTwoHalfCoupling 2 0 (decode word) *
            (binaryVacuumWordWeight word *
              centralHalfAmplitude cutoffTwoHalfCoupling 2 0
                target (decode word)))
        (allSeqs 3 edges.length)) _ ?_ ?_
    · apply listQSum_congr_on
      intro word hword
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (centralHalfAmplitude_cutoffTwo_vacuum_word_eqv_delta
            word hword))
    apply listQSum_congr_on
    intro word _
    exact rotate_vacuum_delta _ _ _
  refine Q'.eqv_trans _
    (value (List.replicate edges.length 0)) _
    (finiteAssignmentSum_ternaryVacuumWordWeight_mul
      value edges.length) ?_
  have hdecoded :
      decode (List.replicate edges.length 0) = zeroEdgeLabelling := by
    exact wordToEdgeLabelling_eq_zero_of_binaryVacuum
      edges (List.replicate edges.length 0) (by decide)
  dsimp only [value]
  rw [hdecoded]
  exact Q'.eqv_refl _

/-! ## 3. Row normalization and posterior identification -/

def cutoffTwoVacuumPhysicalGramRowMass : Q' :=
  listQSum
    (centralPhysicalReflectedKernel cutoffTwoHalfCoupling
      2 0 zeroEdgeLabelling)
    cutoffTwoVacuumColumnCarrier

theorem cutoffTwoVacuumPhysicalGramRowMass_eqv :
    cutoffTwoVacuumPhysicalGramRowMass ≈
      centralBoundaryWeight cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling *
        cutoffTwoVacuumColumnDenominator := by
  unfold cutoffTwoVacuumPhysicalGramRowMass
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        centralBoundaryWeight cutoffTwoHalfCoupling 2 0
            zeroEdgeLabelling *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            target zeroEdgeLabelling)
      cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
      target htarget
  refine Q'.eqv_trans _
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 0 zeroEdgeLabelling *
      listQSum
        (fun target =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            target zeroEdgeLabelling)
        cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · exact listQSum_mul_left
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling)
      (fun target =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          target zeroEdgeLabelling)
      cutoffTwoVacuumColumnCarrier
  exact Q'.mul_eqv_congr_left _ _ _
    (by
      simpa [cutoffTwoVacuumColumnCarrier,
        centralBoundaryColumnMass] using
        centralPositiveBoundaryTotalHalfAmplitude_cutoffTwo_vacuum_eqv)

theorem centralBoundaryWeight_cutoffTwo_vacuum_pos :
    (0 : Q') <
      centralBoundaryWeight cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling := by
  let amplitude := centralHalfAmplitude cutoffTwoHalfCoupling
    2 0 zeroEdgeLabelling zeroEdgeLabelling
  apply q_left_pos_of_mul_pos_local
    (Q'.mul_nonneg amplitude amplitude
      (centralHalfAmplitude_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling zeroEdgeLabelling)
      (centralHalfAmplitude_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling zeroEdgeLabelling))
  exact centralVacuumBoundaryGramIntegrand_pos 2 0

theorem cutoffTwoVacuumPhysicalGramRowMass_pos :
    (0 : Q') < cutoffTwoVacuumPhysicalGramRowMass := by
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos centralBoundaryWeight_cutoffTwo_vacuum_pos
      cutoffTwoVacuumColumnDenominator_pos)
    (Q'.ge_of_eqv cutoffTwoVacuumPhysicalGramRowMass_eqv)

def cutoffTwoVacuumPhysicalGramMarkov
    (target : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralPhysicalReflectedKernel cutoffTwoHalfCoupling
      2 0 zeroEdgeLabelling target)
    cutoffTwoVacuumPhysicalGramRowMass
    cutoffTwoVacuumPhysicalGramRowMass_pos

theorem cutoffTwoVacuumPhysicalGramMarkov_total_one :
    listQSum cutoffTwoVacuumPhysicalGramMarkov
        cutoffTwoVacuumColumnCarrier ≈ 1 := by
  unfold cutoffTwoVacuumPhysicalGramMarkov Q'.divPos
  refine Q'.eqv_trans _
    (cutoffTwoVacuumPhysicalGramRowMass *
      Q'.recipPos cutoffTwoVacuumPhysicalGramRowMass
        cutoffTwoVacuumPhysicalGramRowMass_pos) _ ?_ ?_
  · exact listQSum_mul_right
      (centralPhysicalReflectedKernel cutoffTwoHalfCoupling
        2 0 zeroEdgeLabelling)
      (Q'.recipPos cutoffTwoVacuumPhysicalGramRowMass
        cutoffTwoVacuumPhysicalGramRowMass_pos)
      cutoffTwoVacuumColumnCarrier
  exact Q'.mul_recipPos_eqv _ _

theorem cutoffTwoVacuumPhysicalGramMarkov_eqv_refresh
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffTwoVacuumColumnCarrier) :
    cutoffTwoVacuumPhysicalGramMarkov target ≈
      cutoffTwoVacuumColumnRefreshKernel zeroEdgeLabelling target := by
  let amplitude := centralHalfAmplitude cutoffTwoHalfCoupling
    2 0 target zeroEdgeLabelling
  let weight := centralBoundaryWeight cutoffTwoHalfCoupling
    2 0 zeroEdgeLabelling
  let denominator := cutoffTwoVacuumColumnDenominator
  let rowMass := cutoffTwoVacuumPhysicalGramRowMass
  let posterior := cutoffTwoVacuumColumnPosterior target
  have hrow :=
    centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
      target htarget
  have hposteriorMul :
      posterior * rowMass ≈
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling
          2 0 zeroEdgeLabelling target := by
    refine Q'.eqv_trans _ (posterior * (weight * denominator)) _
      (Q'.mul_eqv_congr_left posterior _ _
        cutoffTwoVacuumPhysicalGramRowMass_eqv) ?_
    refine Q'.eqv_trans _ ((posterior * weight) * denominator) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv posterior weight denominator)) ?_
    refine Q'.eqv_trans _ ((weight * posterior) * denominator) _
      (Q'.mul_eqv_congr_right _ _ denominator
        (Q'.mul_comm_eqv posterior weight)) ?_
    refine Q'.eqv_trans _ (weight * (posterior * denominator)) _
      (Q'.mul_assoc_eqv weight posterior denominator) ?_
    refine Q'.eqv_trans _ (weight * amplitude) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left weight _ _
        (by
          unfold posterior amplitude cutoffTwoVacuumColumnPosterior
          exact Q'.divPos_mul_eqv _ _ _)
    exact Q'.eqv_symm hrow
  have hposteriorPhysical :
      posterior ≈ cutoffTwoVacuumPhysicalGramMarkov target := by
    unfold cutoffTwoVacuumPhysicalGramMarkov
    exact eqv_divPos_of_mul_local
      cutoffTwoVacuumPhysicalGramRowMass_pos hposteriorMul
  exact Q'.eqv_trans _ posterior _
    (Q'.eqv_symm hposteriorPhysical) (Q'.eqv_refl _)

def cutoffTwoVacuumPhysicalGramAction
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun target =>
      cutoffTwoVacuumPhysicalGramMarkov target * observable target)
    cutoffTwoVacuumColumnCarrier

theorem cutoffTwoVacuumPhysicalGramAction_eqv_refresh
    (observable : EdgeLabelling → Q') :
    cutoffTwoVacuumPhysicalGramAction observable ≈
      cutoffTwoVacuumColumnRefreshAction observable
        zeroEdgeLabelling := by
  unfold cutoffTwoVacuumPhysicalGramAction
    cutoffTwoVacuumColumnRefreshAction
  apply listQSum_congr_on
  intro target htarget
  exact Q'.mul_eqv_congr_right _ _ (observable target)
    (cutoffTwoVacuumPhysicalGramMarkov_eqv_refresh target htarget)

theorem cutoffTwoVacuumPhysicalGramAction_centeredExcitationMode_zero :
    cutoffTwoVacuumPhysicalGramAction
        cutoffTwoVacuumColumnCenteredExcitationMode ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (cutoffTwoVacuumPhysicalGramAction_eqv_refresh _)
    (cutoffTwoVacuumColumnRefreshAction_centeredExcitationMode_zero
      zeroEdgeLabelling)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov.centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov.cutoffTwoVacuumPhysicalGramRowMass_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov.cutoffTwoVacuumPhysicalGramMarkov_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov.cutoffTwoVacuumPhysicalGramMarkov_eqv_refresh
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov.cutoffTwoVacuumPhysicalGramAction_centeredExcitationMode_zero
