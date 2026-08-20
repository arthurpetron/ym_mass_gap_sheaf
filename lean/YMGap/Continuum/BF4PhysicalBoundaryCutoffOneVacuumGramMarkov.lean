/-
# The cutoff-one vacuum row of the genuine physical Gram

This file upgrades the exact vacuum-column posterior from a statistical
refresh construction to the row normalization of the genuine reflected BF4
Gram.  The cutoff-one vacuum half-amplitude is a checked Boolean delta on the
fixed-interface carrier, so contracting one physical Gram row evaluates the
other half-amplitude at the vacuum interface.  The full retained target sum
is therefore the already computed two-term vacuum-column denominator.

This is still a finite `K = 1`, half-extent-zero row theorem.  It neither
proves invariance of a cutoff-uniform transfer sector nor supplies a
continuum spectral gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum
import YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate
import YMGap.Continuum.BF4PhysicalBoundaryVariableElimination

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnAnnihilation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum
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
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
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

/-! ## 1. A generic exact Boolean-delta contraction -/

private theorem eliminateHead_binaryVacuum_mul
    (value : List Nat → Q') (tail : List Nat) :
    eliminateHead 2
        (fun word => binaryVacuumWordWeight word * value word) tail ≈
      binaryVacuumWordWeight tail * value (0 :: tail) := by
  unfold eliminateHead
  change
    binaryVacuumWordWeight (0 :: tail) * value (0 :: tail) +
        (binaryVacuumWordWeight (1 :: tail) * value (1 :: tail) + 0) ≈
      binaryVacuumWordWeight tail * value (0 :: tail)
  cases htail : binaryVacuumWordB tail with
  | false =>
      simp only [binaryVacuumWordWeight, binaryVacuumWordB, htail,
        Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv _)
          (Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) (Q'.eqv_refl 0))
            (Q'.eqv_of_eq (Q'.zero_add' 0))))
        (Q'.eqv_trans _ 0 _
          (Q'.eqv_of_eq (Q'.zero_add' 0))
          (Q'.eqv_symm (Q'.zero_mul_eqv _)))
  | true =>
      simp only [binaryVacuumWordWeight, binaryVacuumWordB, htail,
        decide_true, Bool.true_and, ↓reduceIte]
      exact Q'.eqv_trans _
        (value (0 :: tail) + 0) _
        (Q'.add_eqv_congr'
          (Q'.one_mul_eqv _)
          (Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) (Q'.eqv_refl 0))
            (Q'.eqv_of_eq (Q'.zero_add' 0))))
        (Q'.eqv_trans _ (value (0 :: tail)) _
          (Q'.eqv_of_eq (Q'.add_zero' _))
          (Q'.eqv_symm (Q'.one_mul_eqv _)))

/-- Multiplying an arbitrary finite word function by the Boolean vacuum
delta and summing evaluates that function at the all-zero word. -/
theorem finiteAssignmentSum_binaryVacuumWordWeight_mul
    (value : List Nat → Q') : ∀ variables : Nat,
    finiteAssignmentSum 2 variables
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
        (finiteAssignmentSum 2 variables
          (eliminateHead 2
            (fun word => binaryVacuumWordWeight word * value word))) _
        (finiteAssignmentSum_succ_eqv_eliminateHead 2 variables _) ?_
      refine Q'.eqv_trans _
        (finiteAssignmentSum 2 variables
          (fun tail =>
            binaryVacuumWordWeight tail * value (0 :: tail))) _ ?_ ?_
      · unfold finiteAssignmentSum
        apply listQSum_congr_on
        intro tail _
        exact eliminateHead_binaryVacuum_mul value tail
      · simpa [List.replicate_succ] using
          (finiteAssignmentSum_binaryVacuumWordWeight_mul
            (fun tail => value (0 :: tail)) variables)

/-! ## 2. Exact genuine physical vacuum Gram row -/

private theorem rotate_vacuum_delta
    (weight delta target : Q') :
    weight * (delta * target) ≈ delta * (weight * target) := by
  refine Q'.eqv_trans _ ((weight * delta) * target) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv weight delta target)) ?_
  refine Q'.eqv_trans _ ((delta * weight) * target) _
    (Q'.mul_eqv_congr_right _ _ target
      (Q'.mul_comm_eqv weight delta)) ?_
  exact Q'.mul_assoc_eqv delta weight target

/-- The genuine reflected Gram row at the vacuum source evaluates the other
half-amplitude at the vacuum interface, multiplied by the physical vacuum
interface weight. -/
theorem centralPhysicalReflectedKernel_cutoffOne_vacuum_row_eqv
    {w : Q'} (hw : (0 : Q') < w)
    (target : EdgeLabelling)
    (htarget : target ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalReflectedKernel
        w 1 0 zeroEdgeLabelling target ≈
      centralBoundaryWeight w 1 0 zeroEdgeLabelling *
        centralHalfAmplitude w 1 0 target zeroEdgeLabelling := by
  let edges := centralFixedFaceIds 0
  let decode := wordToEdgeLabelling edges
  let value : List Nat → Q' := fun word =>
    centralBoundaryWeight w 1 0 (decode word) *
      centralHalfAmplitude w 1 0 target (decode word)
  refine Q'.eqv_trans _
    (weightedGram (centralBoundaryChannels 1 0)
      (centralBoundaryWeight w 1 0)
      (centralHalfAmplitude w 1 0)
      zeroEdgeLabelling target) _ ?_ ?_
  · exact centralPhysicalReflectedKernel_eq_weightedGram w
      (zeroEdgeLabelling_mem_centralHalfStates 1 0)
      ((mem_centralPositiveHalfStates_iff.mp htarget).1)
  unfold weightedGram
  rw [centralBoundaryChannels_eq_map_allSeqs]
  refine Q'.eqv_trans _
    (finiteAssignmentSum 2 edges.length
      (fun word => binaryVacuumWordWeight word * value word)) _ ?_ ?_
  · unfold finiteAssignmentSum
    refine Q'.eqv_trans _
      (listQSum
        (fun word =>
          centralBoundaryWeight w 1 0 (decode word) *
            (centralHalfAmplitude w 1 0 zeroEdgeLabelling (decode word) *
              centralHalfAmplitude w 1 0 target (decode word)))
        (allSeqs 2 edges.length)) _ ?_ ?_
    · exact Q'.eqv_of_eq
        (listQSum_map
          (fun boundary =>
            centralBoundaryWeight w 1 0 boundary *
              (centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary *
                centralHalfAmplitude w 1 0 target boundary))
          decode (allSeqs 2 edges.length))
    · refine Q'.eqv_trans _
        (listQSum
          (fun word =>
            centralBoundaryWeight w 1 0 (decode word) *
              (binaryVacuumWordWeight word *
                centralHalfAmplitude w 1 0 target (decode word)))
          (allSeqs 2 edges.length)) _ ?_ ?_
      · apply listQSum_congr_on
        intro word hword
        exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
              w word hword))
      apply listQSum_congr_on
      intro word hword
      exact rotate_vacuum_delta _ _ _
  refine Q'.eqv_trans _
    (value (List.replicate edges.length 0)) _
    (finiteAssignmentSum_binaryVacuumWordWeight_mul value edges.length) ?_
  have hdecoded :
      decode (List.replicate edges.length 0) = zeroEdgeLabelling := by
    exact wordToEdgeLabelling_eq_zero_of_binaryVacuum
      edges (List.replicate edges.length 0) (by decide)
  dsimp only [value]
  rw [hdecoded]
  exact Q'.eqv_refl _

/-- The genuine physical Gram row at the central lower cube is the vacuum
Gram profile multiplied by the exact six-face activity. -/
theorem centralPhysicalReflectedKernel_cutoffOne_cube_row_eqv
    {w : Q'} (hw : (0 : Q') < w)
    (target : EdgeLabelling)
    (htarget : target ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalReflectedKernel
        w 1 0 centralLowerCubeState target ≈
      centralBoundaryWeight w 1 0 zeroEdgeLabelling *
        ((coeffW w 1) ^ 6 *
          centralHalfAmplitude w 1 0 target zeroEdgeLabelling) := by
  let edges := centralFixedFaceIds 0
  let decode := wordToEdgeLabelling edges
  let activity := (coeffW w 1) ^ 6
  let value : List Nat → Q' := fun word =>
    centralBoundaryWeight w 1 0 (decode word) *
      (activity *
        centralHalfAmplitude w 1 0 target (decode word))
  refine Q'.eqv_trans _
    (weightedGram (centralBoundaryChannels 1 0)
      (centralBoundaryWeight w 1 0)
      (centralHalfAmplitude w 1 0)
      centralLowerCubeState target) _ ?_ ?_
  · exact centralPhysicalReflectedKernel_eq_weightedGram w
      ((mem_centralPositiveHalfStates_iff.mp
        (centralLowerCubeState_mem_centralPositiveHalfStates
          hw (by decide : 1 ≤ 1))).1)
      ((mem_centralPositiveHalfStates_iff.mp htarget).1)
  unfold weightedGram
  rw [centralBoundaryChannels_eq_map_allSeqs]
  refine Q'.eqv_trans _
    (finiteAssignmentSum 2 edges.length
      (fun word => binaryVacuumWordWeight word * value word)) _ ?_ ?_
  · unfold finiteAssignmentSum
    refine Q'.eqv_trans _
      (listQSum
        (fun word =>
          centralBoundaryWeight w 1 0 (decode word) *
            (centralHalfAmplitude w 1 0 centralLowerCubeState (decode word) *
              centralHalfAmplitude w 1 0 target (decode word)))
        (allSeqs 2 edges.length)) _ ?_ ?_
    · exact Q'.eqv_of_eq
        (listQSum_map
          (fun boundary =>
            centralBoundaryWeight w 1 0 boundary *
              (centralHalfAmplitude w 1 0 centralLowerCubeState boundary *
                centralHalfAmplitude w 1 0 target boundary))
          decode (allSeqs 2 edges.length))
    refine Q'.eqv_trans _
      (listQSum
        (fun word =>
          centralBoundaryWeight w 1 0 (decode word) *
            ((binaryVacuumWordWeight word * activity) *
              centralHalfAmplitude w 1 0 target (decode word)))
        (allSeqs 2 edges.length)) _ ?_ ?_
    · apply listQSum_congr_on
      intro word hword
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (centralHalfAmplitude_cutoffOne_cube_word_eqv_delta
            w word hword))
    apply listQSum_congr_on
    intro word _hword
    refine Q'.eqv_trans _
      (centralBoundaryWeight w 1 0 (decode word) *
        (binaryVacuumWordWeight word *
          (activity *
            centralHalfAmplitude w 1 0 target (decode word)))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_assoc_eqv _ _ _)
    exact rotate_vacuum_delta _ _ _
  refine Q'.eqv_trans _
    (value (List.replicate edges.length 0)) _
    (finiteAssignmentSum_binaryVacuumWordWeight_mul value edges.length) ?_
  have hdecoded :
      decode (List.replicate edges.length 0) = zeroEdgeLabelling := by
    exact wordToEdgeLabelling_eq_zero_of_binaryVacuum
      edges (List.replicate edges.length 0) (by decide)
  dsimp only [value, activity]
  rw [hdecoded]
  exact Q'.eqv_refl _

/-! ## 3. Exact row normalization -/

/-- Full retained-target mass of the genuine physical vacuum Gram row. -/
def cutoffOneVacuumPhysicalGramRowMass
    (w : Q') (hw : (0 : Q') < w) : Q' :=
  listQSum
    (centralPhysicalReflectedKernel w 1 0 zeroEdgeLabelling)
    (cutoffOneVacuumColumnCarrier w hw)

/-- The physical vacuum Gram-row mass is the interface weight times the
checked two-term vacuum-column denominator. -/
theorem cutoffOneVacuumPhysicalGramRowMass_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumPhysicalGramRowMass w hw ≈
      centralBoundaryWeight w 1 0 zeroEdgeLabelling *
        cutoffOneVacuumColumnDenominator w := by
  unfold cutoffOneVacuumPhysicalGramRowMass
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        centralBoundaryWeight w 1 0 zeroEdgeLabelling *
          centralHalfAmplitude w 1 0 target zeroEdgeLabelling)
      (cutoffOneVacuumColumnCarrier w hw)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact centralPhysicalReflectedKernel_cutoffOne_vacuum_row_eqv
      hw target htarget
  refine Q'.eqv_trans _
    (centralBoundaryWeight w 1 0 zeroEdgeLabelling *
      listQSum
        (fun target =>
          centralHalfAmplitude w 1 0 target zeroEdgeLabelling)
        (cutoffOneVacuumColumnCarrier w hw)) _ ?_ ?_
  · exact listQSum_mul_left
      (centralBoundaryWeight w 1 0 zeroEdgeLabelling)
      (fun target =>
        centralHalfAmplitude w 1 0 target zeroEdgeLabelling)
      (cutoffOneVacuumColumnCarrier w hw)
  exact Q'.mul_eqv_congr_left _ _ _
    (by
      simpa [cutoffOneVacuumColumnCarrier,
        centralBoundaryColumnMass,
        cutoffOneVacuumColumnDenominator] using
        (centralBoundaryColumnMass_cutoffOne_vacuum_eqv hw))

theorem centralBoundaryWeight_cutoffOne_vacuum_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < centralBoundaryWeight w 1 0 zeroEdgeLabelling := by
  let amplitude :=
    centralHalfAmplitude w 1 0 zeroEdgeLabelling zeroEdgeLabelling
  apply q_left_pos_of_mul_pos_local
    (Q'.mul_nonneg amplitude amplitude
      (centralHalfAmplitude_nonnegative
        (Q'.le_of_lt hw) 1 0 zeroEdgeLabelling zeroEdgeLabelling)
      (centralHalfAmplitude_nonnegative
        (Q'.le_of_lt hw) 1 0 zeroEdgeLabelling zeroEdgeLabelling))
  exact centralVacuumBoundaryGramIntegrand_pos 1 0

theorem cutoffOneVacuumPhysicalGramRowMass_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < cutoffOneVacuumPhysicalGramRowMass w hw := by
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos
      (centralBoundaryWeight_cutoffOne_vacuum_pos hw)
      (cutoffOneVacuumColumnDenominator_pos hw))
    (Q'.ge_of_eqv
      (cutoffOneVacuumPhysicalGramRowMass_eqv hw))

/-- Row-normalized genuine physical reflected Gram at the vacuum source. -/
def cutoffOneVacuumPhysicalGramMarkov
    (w : Q') (hw : (0 : Q') < w)
    (target : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralPhysicalReflectedKernel w 1 0 zeroEdgeLabelling target)
    (cutoffOneVacuumPhysicalGramRowMass w hw)
    (cutoffOneVacuumPhysicalGramRowMass_pos hw)

theorem cutoffOneVacuumPhysicalGramMarkov_total_one
    {w : Q'} (hw : (0 : Q') < w) :
    listQSum
        (cutoffOneVacuumPhysicalGramMarkov w hw)
        (cutoffOneVacuumColumnCarrier w hw) ≈
      1 := by
  unfold cutoffOneVacuumPhysicalGramMarkov Q'.divPos
  refine Q'.eqv_trans _
    (cutoffOneVacuumPhysicalGramRowMass w hw *
      Q'.recipPos
        (cutoffOneVacuumPhysicalGramRowMass w hw)
        (cutoffOneVacuumPhysicalGramRowMass_pos hw)) _ ?_ ?_
  · exact listQSum_mul_right
      (centralPhysicalReflectedKernel w 1 0 zeroEdgeLabelling)
      (Q'.recipPos
        (cutoffOneVacuumPhysicalGramRowMass w hw)
        (cutoffOneVacuumPhysicalGramRowMass_pos hw))
      (cutoffOneVacuumColumnCarrier w hw)
  exact Q'.mul_recipPos_eqv _ _

/-- On every retained target, the row-normalized genuine physical Gram at
the vacuum source is exactly the posterior-refresh row. -/
theorem cutoffOneVacuumPhysicalGramMarkov_eqv_refresh
    {w : Q'} (hw : (0 : Q') < w)
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw) :
    cutoffOneVacuumPhysicalGramMarkov w hw target ≈
      cutoffOneVacuumColumnRefreshKernel
        w hw zeroEdgeLabelling target := by
  let amplitude :=
    centralHalfAmplitude w 1 0 target zeroEdgeLabelling
  let weight := centralBoundaryWeight w 1 0 zeroEdgeLabelling
  let denominator := cutoffOneVacuumColumnDenominator w
  let rowMass := cutoffOneVacuumPhysicalGramRowMass w hw
  let posterior := cutoffOneVacuumColumnPosterior w hw target
  have hrow :=
    centralPhysicalReflectedKernel_cutoffOne_vacuum_row_eqv
      hw target htarget
  have hmass := cutoffOneVacuumPhysicalGramRowMass_eqv hw
  have hposteriorMul :
      posterior * rowMass ≈
        centralPhysicalReflectedKernel
          w 1 0 zeroEdgeLabelling target := by
    refine Q'.eqv_trans _ (posterior * (weight * denominator)) _
      (Q'.mul_eqv_congr_left posterior _ _ hmass) ?_
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
          unfold posterior amplitude
            cutoffOneVacuumColumnPosterior
          exact Q'.divPos_mul_eqv _ _ _)
    exact Q'.eqv_symm hrow
  have hposteriorPhysical :
      posterior ≈ cutoffOneVacuumPhysicalGramMarkov w hw target := by
    unfold cutoffOneVacuumPhysicalGramMarkov
    exact eqv_divPos_of_mul_local
      (cutoffOneVacuumPhysicalGramRowMass_pos hw)
      hposteriorMul
  exact Q'.eqv_trans _ posterior _
    (Q'.eqv_symm hposteriorPhysical)
    (Q'.eqv_refl _)

/-- Genuine normalized physical Gram action from the vacuum source. -/
def cutoffOneVacuumPhysicalGramAction
    (w : Q') (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun target =>
      cutoffOneVacuumPhysicalGramMarkov w hw target * observable target)
    (cutoffOneVacuumColumnCarrier w hw)

/-- The complete finite action of the genuine normalized physical Gram
vacuum row equals the posterior-refresh action. -/
theorem cutoffOneVacuumPhysicalGramAction_eqv_refresh
    {w : Q'} (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q') :
    cutoffOneVacuumPhysicalGramAction w hw observable ≈
      cutoffOneVacuumColumnRefreshAction
        w hw observable zeroEdgeLabelling := by
  unfold cutoffOneVacuumPhysicalGramAction
    cutoffOneVacuumColumnRefreshAction
  apply listQSum_congr_on
  intro target htarget
  exact Q'.mul_eqv_congr_right _ _ (observable target)
    (cutoffOneVacuumPhysicalGramMarkov_eqv_refresh
      hw target htarget)

/-- In particular, the genuine normalized physical Gram vacuum row kills
the explicit nonzero cube-centered mode. -/
theorem cutoffOneVacuumPhysicalGramAction_centeredCubeMode_zero
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumPhysicalGramAction w hw
        (cutoffOneVacuumColumnCenteredCubeMode w hw) ≈
      0 := by
  exact Q'.eqv_trans _ _ _
    (cutoffOneVacuumPhysicalGramAction_eqv_refresh hw _)
    (cutoffOneVacuumColumnRefreshAction_centeredCubeMode_zero
      hw zeroEdgeLabelling)

/-! ## 4. The companion central-cube physical Gram row -/

def cutoffOneCubePhysicalGramRowMass
    (w : Q') (hw : (0 : Q') < w) : Q' :=
  listQSum
    (centralPhysicalReflectedKernel w 1 0 centralLowerCubeState)
    (cutoffOneVacuumColumnCarrier w hw)

theorem cutoffOneCubePhysicalGramRowMass_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneCubePhysicalGramRowMass w hw ≈
      centralBoundaryWeight w 1 0 zeroEdgeLabelling *
        ((coeffW w 1) ^ 6 *
          cutoffOneVacuumColumnDenominator w) := by
  let weight := centralBoundaryWeight w 1 0 zeroEdgeLabelling
  let activity := (coeffW w 1) ^ 6
  let states := cutoffOneVacuumColumnCarrier w hw
  let amplitude := fun target =>
    centralHalfAmplitude w 1 0 target zeroEdgeLabelling
  unfold cutoffOneCubePhysicalGramRowMass
  refine Q'.eqv_trans _
    (listQSum (fun target => weight * (activity * amplitude target))
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact centralPhysicalReflectedKernel_cutoffOne_cube_row_eqv
      hw target htarget
  refine Q'.eqv_trans _
    (weight * listQSum (fun target => activity * amplitude target) states) _
    (listQSum_mul_left weight _ states) ?_
  refine Q'.eqv_trans _
    (weight * (activity * listQSum amplitude states)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left weight _ _
      (listQSum_mul_left activity amplitude states)
  exact Q'.mul_eqv_congr_left weight _ _
    (Q'.mul_eqv_congr_left activity _ _
      (by
        simpa [states, amplitude, cutoffOneVacuumColumnCarrier,
          centralBoundaryColumnMass,
          cutoffOneVacuumColumnDenominator] using
          (centralBoundaryColumnMass_cutoffOne_vacuum_eqv hw)))

theorem cutoffOneCubePhysicalGramRowMass_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < cutoffOneCubePhysicalGramRowMass w hw := by
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos
      (centralBoundaryWeight_cutoffOne_vacuum_pos hw)
      (Q'.mul_pos
        (cutoffOneVacuumColumnActivity_pos hw)
        (cutoffOneVacuumColumnDenominator_pos hw)))
    (Q'.ge_of_eqv (cutoffOneCubePhysicalGramRowMass_eqv hw))

def cutoffOneCubePhysicalGramMarkov
    (w : Q') (hw : (0 : Q') < w)
    (target : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralPhysicalReflectedKernel w 1 0 centralLowerCubeState target)
    (cutoffOneCubePhysicalGramRowMass w hw)
    (cutoffOneCubePhysicalGramRowMass_pos hw)

theorem cutoffOneCubePhysicalGramMarkov_total_one
    {w : Q'} (hw : (0 : Q') < w) :
    listQSum
        (cutoffOneCubePhysicalGramMarkov w hw)
        (cutoffOneVacuumColumnCarrier w hw) ≈
      1 := by
  unfold cutoffOneCubePhysicalGramMarkov Q'.divPos
  refine Q'.eqv_trans _
    (cutoffOneCubePhysicalGramRowMass w hw *
      Q'.recipPos
        (cutoffOneCubePhysicalGramRowMass w hw)
        (cutoffOneCubePhysicalGramRowMass_pos hw)) _ ?_ ?_
  · exact listQSum_mul_right
      (centralPhysicalReflectedKernel w 1 0 centralLowerCubeState)
      (Q'.recipPos
        (cutoffOneCubePhysicalGramRowMass w hw)
        (cutoffOneCubePhysicalGramRowMass_pos hw))
      (cutoffOneVacuumColumnCarrier w hw)
  exact Q'.mul_recipPos_eqv _ _

theorem cutoffOneCubePhysicalGramMarkov_eqv_refresh
    {w : Q'} (hw : (0 : Q') < w)
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw) :
    cutoffOneCubePhysicalGramMarkov w hw target ≈
      cutoffOneVacuumColumnRefreshKernel
        w hw centralLowerCubeState target := by
  let amplitude :=
    centralHalfAmplitude w 1 0 target zeroEdgeLabelling
  let weight := centralBoundaryWeight w 1 0 zeroEdgeLabelling
  let activity := (coeffW w 1) ^ 6
  let denominator := cutoffOneVacuumColumnDenominator w
  let rowMass := cutoffOneCubePhysicalGramRowMass w hw
  let posterior := cutoffOneVacuumColumnPosterior w hw target
  have hrow := centralPhysicalReflectedKernel_cutoffOne_cube_row_eqv
    hw target htarget
  have hmass := cutoffOneCubePhysicalGramRowMass_eqv hw
  have hposteriorMul :
      posterior * rowMass ≈
        centralPhysicalReflectedKernel
          w 1 0 centralLowerCubeState target := by
    refine Q'.eqv_trans _
      (posterior * (weight * (activity * denominator))) _
      (Q'.mul_eqv_congr_left posterior _ _ hmass) ?_
    refine Q'.eqv_trans _
      ((posterior * weight) * (activity * denominator)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv posterior weight
          (activity * denominator))) ?_
    refine Q'.eqv_trans _
      ((weight * posterior) * (activity * denominator)) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv posterior weight)) ?_
    refine Q'.eqv_trans _
      (weight * (posterior * (activity * denominator))) _
      (Q'.mul_assoc_eqv weight posterior
        (activity * denominator)) ?_
    refine Q'.eqv_trans _
      (weight * ((posterior * activity) * denominator)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left weight _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv posterior activity denominator))
    refine Q'.eqv_trans _
      (weight * ((activity * posterior) * denominator)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left weight _ _
        (Q'.mul_eqv_congr_right _ _ denominator
          (Q'.mul_comm_eqv posterior activity))
    refine Q'.eqv_trans _
      (weight * (activity * (posterior * denominator))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left weight _ _
        (Q'.mul_assoc_eqv activity posterior denominator)
    refine Q'.eqv_trans _ (weight * (activity * amplitude)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left weight _ _
        (Q'.mul_eqv_congr_left activity _ _
          (by
            unfold posterior amplitude
              cutoffOneVacuumColumnPosterior
            exact Q'.divPos_mul_eqv _ _ _))
    exact Q'.eqv_symm hrow
  have hposteriorPhysical :
      posterior ≈ cutoffOneCubePhysicalGramMarkov w hw target := by
    unfold cutoffOneCubePhysicalGramMarkov
    exact eqv_divPos_of_mul_local
      (cutoffOneCubePhysicalGramRowMass_pos hw)
      hposteriorMul
  exact Q'.eqv_trans _ posterior _
    (Q'.eqv_symm hposteriorPhysical)
    (Q'.eqv_refl _)

/-! ## 5. The genuine two-source physical Markov block -/

def cutoffOneVacuumCubePhysicalSources : List EdgeLabelling :=
  [zeroEdgeLabelling, centralLowerCubeState]

theorem cutoffOneVacuumCubePhysicalSources_subset_carrier
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources) :
    source ∈ cutoffOneVacuumColumnCarrier w hw := by
  simp only [cutoffOneVacuumCubePhysicalSources,
    List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with hsource | hsource
  · subst source
    exact zeroEdgeLabelling_mem_centralPositiveHalfStates
      (Q'.le_of_lt hw) 1 0
  · subst source
    exact centralLowerCubeState_mem_centralPositiveHalfStates
      hw (by decide : 1 ≤ 1)

/-- Select the appropriate row normalization of the genuine physical Gram
on the displayed vacuum/cube source sector. -/
def cutoffOneVacuumCubePhysicalGramMarkov
    (w : Q') (hw : (0 : Q') < w)
    (source target : EdgeLabelling) : Q' :=
  if bf4StateCode 1 0 source =
      bf4StateCode 1 0 centralLowerCubeState then
    cutoffOneCubePhysicalGramMarkov w hw target
  else
    cutoffOneVacuumPhysicalGramMarkov w hw target

/-- Each selected row is the row-normalization of its genuine physical Gram
row, and both coincide with the posterior refresh. -/
theorem cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources)
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw) :
    cutoffOneVacuumCubePhysicalGramMarkov w hw source target ≈
      cutoffOneVacuumColumnRefreshKernel w hw source target := by
  simp only [cutoffOneVacuumCubePhysicalSources,
    List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with hsource | hsource
  · subst source
    unfold cutoffOneVacuumCubePhysicalGramMarkov
    rw [if_neg cutoffOne_vacuum_cube_code_ne]
    exact cutoffOneVacuumPhysicalGramMarkov_eqv_refresh
      hw target htarget
  · subst source
    unfold cutoffOneVacuumCubePhysicalGramMarkov
    rw [if_pos rfl]
    exact cutoffOneCubePhysicalGramMarkov_eqv_refresh
      hw target htarget

theorem cutoffOneVacuumCubePhysicalGramMarkov_row_normalized
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources) :
    listQSum
        (cutoffOneVacuumCubePhysicalGramMarkov w hw source)
        (cutoffOneVacuumColumnCarrier w hw) ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (cutoffOneVacuumColumnRefreshKernel w hw source)
      (cutoffOneVacuumColumnCarrier w hw)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
      hw source hsource target htarget
  exact cutoffOneVacuumColumnRefreshKernel_row_normalized hw source

theorem cutoffOneVacuumCubePhysicalGramMarkov_detailedBalance
    {w : Q'} (hw : (0 : Q') < w)
    (source target : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources)
    (htarget : target ∈ cutoffOneVacuumCubePhysicalSources) :
    cutoffOneVacuumColumnPosterior w hw source *
        cutoffOneVacuumCubePhysicalGramMarkov w hw source target ≈
      cutoffOneVacuumColumnPosterior w hw target *
        cutoffOneVacuumCubePhysicalGramMarkov w hw target source := by
  have hsourceCarrier :=
    cutoffOneVacuumCubePhysicalSources_subset_carrier hw source hsource
  have htargetCarrier :=
    cutoffOneVacuumCubePhysicalSources_subset_carrier hw target htarget
  refine Q'.eqv_trans _
    (cutoffOneVacuumColumnPosterior w hw source *
      cutoffOneVacuumColumnRefreshKernel w hw source target) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
        hw source hsource target htargetCarrier)
  refine Q'.eqv_trans _
    (cutoffOneVacuumColumnPosterior w hw target *
      cutoffOneVacuumColumnRefreshKernel w hw target source) _
    (cutoffOneVacuumColumnRefreshKernel_detailedBalance
      hw source target) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
        hw target htarget source hsourceCarrier))

/-- Markov action of the genuine normalized two-source physical Gram block. -/
def cutoffOneVacuumCubePhysicalGramAction
    (w : Q') (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      cutoffOneVacuumCubePhysicalGramMarkov w hw source target *
        observable target)
    (cutoffOneVacuumColumnCarrier w hw)

theorem cutoffOneVacuumCubePhysicalGramAction_eqv_refresh
    {w : Q'} (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources) :
    cutoffOneVacuumCubePhysicalGramAction
        w hw observable source ≈
      cutoffOneVacuumColumnRefreshAction
        w hw observable source := by
  unfold cutoffOneVacuumCubePhysicalGramAction
    cutoffOneVacuumColumnRefreshAction
  apply listQSum_congr_on
  intro target htarget
  exact Q'.mul_eqv_congr_right _ _ (observable target)
    (cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
      hw source hsource target htarget)

theorem cutoffOneVacuumCubePhysicalGramAction_one
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources) :
    cutoffOneVacuumCubePhysicalGramAction w hw (fun _ => 1) source ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (cutoffOneVacuumCubePhysicalGramMarkov w hw source)
      (cutoffOneVacuumColumnCarrier w hw)) _ ?_ ?_
  · unfold cutoffOneVacuumCubePhysicalGramAction
    apply listQSum_congr
    intro target
    exact Q'.mul_one_eqv _
  exact cutoffOneVacuumCubePhysicalGramMarkov_row_normalized
    hw source hsource

theorem cutoffOneVacuumCubePhysicalGramAction_centeredCubeMode_zero
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources) :
    cutoffOneVacuumCubePhysicalGramAction w hw
        (cutoffOneVacuumColumnCenteredCubeMode w hw) source ≈
      0 := by
  exact Q'.eqv_trans _ _ _
    (cutoffOneVacuumCubePhysicalGramAction_eqv_refresh
      hw _ source hsource)
    (cutoffOneVacuumColumnRefreshAction_centeredCubeMode_zero hw source)

/-- Outside the vacuum/cube sector, the normalized target posterior is
exactly zero on the retained carrier. -/
theorem cutoffOneVacuumColumnPosterior_eqv_zero_of_outside_block
    {w : Q'} (hw : (0 : Q') < w)
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw)
    (hneVacuum : target ≠ zeroEdgeLabelling)
    (hneCube : target ≠ centralLowerCubeState) :
    cutoffOneVacuumColumnPosterior w hw target ≈ 0 := by
  unfold cutoffOneVacuumColumnPosterior Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (cutoffOneVacuumColumnDenominator w)
      (cutoffOneVacuumColumnDenominator_pos hw)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralHalfAmplitude_cutoffOne_vacuumColumn_eqv_zero_of_ne
        w target
        ((mem_centralPositiveHalfStates_iff.mp htarget).1)
        hneVacuum hneCube)
  exact Q'.zero_mul_eqv _

/-- Hence every row of the genuine two-source physical block has no mass
outside that same sector. -/
theorem cutoffOneVacuumCubePhysicalGramMarkov_eqv_zero_of_outside_block
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ cutoffOneVacuumCubePhysicalSources)
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw)
    (hneVacuum : target ≠ zeroEdgeLabelling)
    (hneCube : target ≠ centralLowerCubeState) :
    cutoffOneVacuumCubePhysicalGramMarkov w hw source target ≈ 0 := by
  exact Q'.eqv_trans _
    (cutoffOneVacuumColumnRefreshKernel w hw source target) _
    (cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
      hw source hsource target htarget)
    (cutoffOneVacuumColumnPosterior_eqv_zero_of_outside_block
      hw target htarget hneVacuum hneCube)

/-- Exact finite physical spectral certificate on the invariant vacuum/cube
sector: constants have eigenvalue one, while the explicit nonzero centered
cube mode has eigenvalue zero. -/
theorem cutoffOneVacuumCubePhysicalGram_exact_modes
    {w : Q'} (hw : (0 : Q') < w) :
    (∀ source,
      source ∈ cutoffOneVacuumCubePhysicalSources →
        cutoffOneVacuumCubePhysicalGramAction
          w hw (fun _ => 1) source ≈ 1) ∧
    (0 : Q') <
      cutoffOneVacuumColumnCenteredCubeMode
        w hw centralLowerCubeState ∧
    (∀ source,
      source ∈ cutoffOneVacuumCubePhysicalSources →
        cutoffOneVacuumCubePhysicalGramAction w hw
          (cutoffOneVacuumColumnCenteredCubeMode w hw) source ≈ 0) := by
  exact ⟨
    fun source hsource =>
      cutoffOneVacuumCubePhysicalGramAction_one hw source hsource,
    cutoffOneVacuumColumnCenteredCubeMode_at_cube_pos hw,
    fun source hsource =>
      cutoffOneVacuumCubePhysicalGramAction_centeredCubeMode_zero
        hw source hsource⟩

def cutoffOneVacuumCubePhysicalGramAlgebraicGap : Q' := 1

theorem cutoffOneVacuumCubePhysicalGramAlgebraicGap_pos :
    (0 : Q') < cutoffOneVacuumCubePhysicalGramAlgebraicGap := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.finiteAssignmentSum_binaryVacuumWordWeight_mul
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.centralPhysicalReflectedKernel_cutoffOne_vacuum_row_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumPhysicalGramRowMass_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumPhysicalGramMarkov_total_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumPhysicalGramMarkov_eqv_refresh
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumPhysicalGramAction_centeredCubeMode_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.centralPhysicalReflectedKernel_cutoffOne_cube_row_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneCubePhysicalGramRowMass_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneCubePhysicalGramMarkov_eqv_refresh
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumCubePhysicalGramMarkov_row_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumCubePhysicalGramMarkov_detailedBalance
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumCubePhysicalGramAction_centeredCubeMode_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumCubePhysicalGramMarkov_eqv_zero_of_outside_block
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumCubePhysicalGram_exact_modes
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov.cutoffOneVacuumCubePhysicalGramAlgebraicGap_pos
