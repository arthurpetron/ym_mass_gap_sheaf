/-
# Qualitative existence of the finite cutoff-two prefix increments

The finite-prefix gap compiler asks for a relative matrix and diagonal error
at every consecutive cutoff.  This module proves that those relative errors
are not an additional qualitative analytic hypothesis for any coefficient
with a non-root component.

Such a component is unchanged by moving root centering.  Its cutoff-two
physical state has positive row mass, that positivity persists at every
larger cutoff, and hence its square-weight summand makes every later moving
diagonal strictly positive.  We may therefore divide the sum of the two
absolute consecutive form differences by the later diagonal.  The resulting
explicit rational is a common relative error for both differences.

The construction does not claim that the finite sum of these explicit errors
is small.  That quantitative sum budget, rather than existence of the
individual increments, is the remaining analytic obstruction.  A small named
recode structure records the exact equality between the compact Bishop-real
approximant aliases and their displayed physical forms.  This is a
proof-engineering seam, not a new estimate: the definitions make the two
sides pointwise identical, but asking Lean to unfold that identity here has
already proved prohibitively expensive.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge
import YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A},
      item ∈ items → value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          exact Q'.le_trans' _ (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head) (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem neg_mul_neg_eqv_local (a b : Q') :
    (-a) * (-b) ≈ a * b := by
  refine Q'.eqv_trans _ (-(a * (-b))) _
    (Q'.neg_mul_eqv a (-b)) ?_
  refine Q'.eqv_trans _ (-(-(a * b))) _
    (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b))
    (Q'.neg_neg_eqv (a * b))

private theorem square_pos_of_abs_pos
    {value : Q'} (hvalue : (0 : Q') < Q'.abs value) :
    (0 : Q') < value * value := by
  unfold Q'.abs at hvalue
  by_cases hnonnegative : (0 : Q') ≤ value
  · rw [if_pos hnonnegative] at hvalue
    exact Q'.mul_pos hvalue hvalue
  · rw [if_neg hnonnegative] at hvalue
    exact Q'.pos_of_lt_of_le
      (Q'.mul_pos hvalue hvalue)
      (Q'.le_of_eqv (neg_mul_neg_eqv_local value value))

private theorem abs_pos_of_not_eqv_zero_local
    {value : Q'} (hvalue : ¬ value ≈ 0) :
    (0 : Q') < Q'.abs value := by
  have hnum : value.num ≠ 0 := by
    intro hzero
    apply hvalue
    change value.num * (1 : Int) = (0 : Int) * (value.den : Int)
    simp only [hzero, Int.zero_mul, Int.mul_one]
  unfold Q'.abs
  by_cases hnonnegative : (0 : Q') ≤ value
  · rw [if_pos hnonnegative]
    rw [Q'.zero_le_iff_num_nonneg] at hnonnegative
    change (0 : Int) * (value.den : Int) < value.num * (1 : Int)
    simp only [Int.zero_mul, Int.mul_one]
    omega
  · rw [if_neg hnonnegative]
    rw [Q'.zero_le_iff_num_nonneg] at hnonnegative
    change (0 : Int) * ((-value).den : Int) <
      (-value).num * (1 : Int)
    simpa only [Int.zero_mul, Int.mul_one] using
      Int.neg_pos.mpr (Int.not_le.mp hnonnegative)

/-! A data-bearing finite dichotomy.  The older `Or` theorem is sufficient
for propositions, but constructing a prefix certificate in `Type` requires
the selected non-root coordinate itself, not `Nonempty` erasure. -/

private structure RootSupportOn
    (coefficient : Nat → Q') (states : List Nat) : Type where
  supported : ∀ index, index ∈ states → index ≠ 0 →
    coefficient index ≈ 0

private structure NonRootWitnessOn
    (coefficient : Nat → Q') (states : List Nat) : Type where
  index : Nat
  index_mem : index ∈ states
  index_ne_root : index ≠ 0
  magnitude_pos : (0 : Q') < Q'.abs (coefficient index)

private def coefficientOnListRootOrNonRootData
    (coefficient : Nat → Q') :
    ∀ states : List Nat,
      Sum (RootSupportOn coefficient states)
        (NonRootWitnessOn coefficient states)
  | [] => by
      exact Sum.inl
        { supported := by
            intro index hmem _hne
            exact False.elim (List.not_mem_nil hmem) }
  | head :: tail => by
      by_cases hroot : head = 0
      · cases coefficientOnListRootOrNonRootData coefficient tail with
        | inl htail =>
            exact Sum.inl
              { supported := by
                  intro index hmem hne
                  rcases List.mem_cons.mp hmem with hhead | htailMem
                  · subst index
                    exact False.elim (hne hroot)
                  · exact htail.supported index htailMem hne }
        | inr witness =>
            exact Sum.inr
              { index := witness.index
                index_mem := List.mem_cons_of_mem head witness.index_mem
                index_ne_root := witness.index_ne_root
                magnitude_pos := witness.magnitude_pos }
      · by_cases hzero : coefficient head ≈ 0
        · cases coefficientOnListRootOrNonRootData coefficient tail with
          | inl htail =>
              exact Sum.inl
                { supported := by
                    intro index hmem hne
                    rcases List.mem_cons.mp hmem with hhead | htailMem
                    · subst index
                      exact hzero
                    · exact htail.supported index htailMem hne }
          | inr witness =>
              exact Sum.inr
                { index := witness.index
                  index_mem := List.mem_cons_of_mem head witness.index_mem
                  index_ne_root := witness.index_ne_root
                  magnitude_pos := witness.magnitude_pos }
        · exact Sum.inr
            { index := head
              index_mem := List.mem_cons_self
              index_ne_root := hroot
              magnitude_pos := abs_pos_of_not_eqv_zero_local hzero }

/-- Type-level wrapper for the root-supported branch. -/
structure CutoffTwoRootSupportedWitness
    (coefficient : Nat → Q') : Type where
  supported : CutoffTwoRootSupportedCoefficient coefficient

/-- Constructive finite data selecting the zero root mode or an explicit
positive non-root coordinate. -/
def cutoffTwoRootSupported_orNonRootData
    (coefficient : Nat → Q') :
    Sum (CutoffTwoRootSupportedWitness coefficient)
      (CutoffTwoNonRootCoefficientWitness coefficient) := by
  cases coefficientOnListRootOrNonRootData
      coefficient cutoffTwoPulledStates with
  | inl hsupported =>
      exact Sum.inl
        { supported := hsupported.supported }
  | inr witness =>
      exact Sum.inr
        { index := witness.index
          index_mem := witness.index_mem
          index_ne_root := witness.index_ne_root
          magnitude_pos := witness.magnitude_pos }

/-! ## 1. A non-root witness forces every later moving diagonal positive -/

theorem CutoffTwoNonRootCoefficientWitness.pulledWeight_pos
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    {later : Nat} (hlater : 2 ≤ later) :
    (0 : Q') < cutoffTwoPulledWeightAt later witness.index := by
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 witness.index_mem
  have hsource := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) 2 0 hindexLt
  have hsourceParts := mem_centralPositiveHalfStates_iff.mp hsource
  unfold cutoffTwoPulledWeightAt
  rw [centralPhysicalFinitePulledWeight_eq_rowMarginal hlater hindexLt]
  exact centralPhysicalRowMarginal_pos_of_le
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
    hlater hsourceParts.1 hsourceParts.2

theorem CutoffTwoNonRootCoefficientWitness.movingDiagonalAt_pos
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    {later : Nat} (hlater : 2 ≤ later) :
    (0 : Q') <
      cutoffTwoPulledDiagonalAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let centered :=
    cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let summand := fun index =>
    (centered index * centered index) *
      cutoffTwoPulledWeightAt later index
  have hcentered : centered witness.index ≈ coefficient witness.index :=
    cutoffTwoPulledMovingCenteredCoefficient_eqv_raw_of_nonroot
      later witness.index coefficient witness.index_ne_root
  have hsquareEqv :
      centered witness.index * centered witness.index ≈
        coefficient witness.index * coefficient witness.index := by
    exact Q'.eqv_trans _
      (coefficient witness.index * centered witness.index) _
      (Q'.mul_eqv_congr_right _ _ _ hcentered)
      (Q'.mul_eqv_congr_left _ _ _ hcentered)
  have hsquare :
      (0 : Q') < centered witness.index * centered witness.index := by
    exact Q'.pos_of_lt_of_le
      (square_pos_of_abs_pos witness.magnitude_pos)
      (Q'.ge_of_eqv hsquareEqv)
  have hsummand : (0 : Q') < summand witness.index :=
    Q'.mul_pos hsquare (CutoffTwoNonRootCoefficientWitness.pulledWeight_pos
      witness hlater)
  have hsummandLe :
      summand witness.index ≤ listQSum summand cutoffTwoPulledStates := by
    exact listQSum_member_le_nonnegative_local summand
      (fun index =>
        Q'.mul_nonneg _ _
          (SumOfSquares.q_mul_self_nonneg (centered index))
          (centralPhysicalFinitePulledWeight_nonnegative
            cutoffTwoHalfCoupling (by decide) 2 later 0 index))
      cutoffTwoPulledStates witness.index_mem
  unfold cutoffTwoPulledDiagonalAt
  exact Q'.pos_of_lt_of_le hsummand hsummandLe

def cutoffTwoPhysicalMovingMatrixAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoPulledMatrixAt cutoff
    (cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient)

def cutoffTwoPhysicalMovingDiagonalAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoPulledDiagonalAt cutoff
    (cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient)

/-- Exact recoding seam between compact CReal-approximant aliases and the
displayed finite physical forms.  Both fields are definitional identities in
the imported construction; keeping them named prevents a giant reduction in
every downstream theorem. -/
structure CutoffTwoActualMovingFormRecode
    (coefficient : Nat → Q') : Type 1 where
  matrix_eqv : ∀ cutoff,
    cutoffTwoActualMovingMatrixAt cutoff coefficient ≈
      cutoffTwoPhysicalMovingMatrixAt cutoff coefficient
  diagonal_eqv : ∀ cutoff,
    cutoffTwoActualMovingDiagonalAt cutoff coefficient ≈
      cutoffTwoPhysicalMovingDiagonalAt cutoff coefficient

namespace CutoffTwoActualMovingFormRecode

theorem actualMovingDiagonalAt_pos
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    {later : Nat} (hlater : 2 ≤ later) :
    (0 : Q') < cutoffTwoActualMovingDiagonalAt later coefficient := by
  exact Q'.pos_of_lt_of_le
    (CutoffTwoNonRootCoefficientWitness.movingDiagonalAt_pos witness hlater)
    (Q'.ge_of_eqv (recode.diagonal_eqv later))

/-- The exact physical cutoff-two theorem, transported only across the named
compact recoding seam. -/
theorem anchor_gap
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient) :
    Q'.abs
        (cutoffTwoActualMovingMatrixAt
          (cutoffTwoPrefixCutoff 0) coefficient) ≤
      cutoffTwoAnchorRate *
        cutoffTwoActualMovingDiagonalAt
          (cutoffTwoPrefixCutoff 0) coefficient := by
  have hphysical :
      Q'.abs (cutoffTwoPhysicalMovingMatrixAt 2 coefficient) ≤
        cutoffTwoAnchorRate *
          cutoffTwoPhysicalMovingDiagonalAt 2 coefficient := by
    simpa only [cutoffTwoPhysicalMovingMatrixAt,
      cutoffTwoPhysicalMovingDiagonalAt,
      cutoffTwoPulledMatrixAt, cutoffTwoPulledDiagonalAt,
      cutoffTwoPulledMovingCenteredCoefficientAt,
      cutoffTwoAnchorRate] using
        (cutoffTwoPulledHeadCentered_abs_gap coefficient)
  have hmatrix :
      Q'.abs (cutoffTwoActualMovingMatrixAt 2 coefficient) ≈
        Q'.abs (cutoffTwoPhysicalMovingMatrixAt 2 coefficient) :=
    Q'.abs_eqv_congr (recode.matrix_eqv 2)
  have hdiagonal :
      cutoffTwoAnchorRate * cutoffTwoPhysicalMovingDiagonalAt 2 coefficient ≈
        cutoffTwoAnchorRate * cutoffTwoActualMovingDiagonalAt 2 coefficient :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (recode.diagonal_eqv 2))
  unfold cutoffTwoPrefixCutoff
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hmatrix)
    (Q'.le_trans' _ _ _ hphysical (Q'.le_of_eqv hdiagonal))

theorem rootActualMovingMatrixAt_eqv_zero
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (cutoff : Nat) :
    cutoffTwoActualMovingMatrixAt cutoff coefficient ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (recode.matrix_eqv cutoff) ?_
  unfold cutoffTwoPhysicalMovingMatrixAt
  exact cutoffTwoRootSupported_movingMatrix_eqv_zero
    hsupported cutoff cutoff

theorem rootActualMovingDiagonalAt_eqv_zero
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (cutoff : Nat) :
    cutoffTwoActualMovingDiagonalAt cutoff coefficient ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (recode.diagonal_eqv cutoff) ?_
  unfold cutoffTwoPhysicalMovingDiagonalAt
  exact cutoffTwoRootSupported_movingDiagonal_eqv_zero
    hsupported cutoff cutoff

end CutoffTwoActualMovingFormRecode

/-! ## 2. Canonical quotient increments -/

def cutoffTwoCanonicalPrefixIncrementNumerator
    (coefficient : Nat → Q') (stage : Nat) : Q' :=
  Q'.abs
      (cutoffTwoActualMovingMatrixAt
          (cutoffTwoPrefixCutoff stage) coefficient +
        (-cutoffTwoActualMovingMatrixAt
          (cutoffTwoPrefixCutoff (stage + 1)) coefficient)) +
    Q'.abs
      (cutoffTwoActualMovingDiagonalAt
          (cutoffTwoPrefixCutoff stage) coefficient +
        (-cutoffTwoActualMovingDiagonalAt
          (cutoffTwoPrefixCutoff (stage + 1)) coefficient))

def cutoffTwoCanonicalPrefixIncrement
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (stage : Nat) : Q' :=
  Q'.divPos
    (cutoffTwoCanonicalPrefixIncrementNumerator coefficient stage)
    (cutoffTwoActualMovingDiagonalAt
      (cutoffTwoPrefixCutoff (stage + 1)) coefficient)
    (recode.actualMovingDiagonalAt_pos witness (by
      unfold cutoffTwoPrefixCutoff
      omega))

theorem cutoffTwoCanonicalPrefixIncrement_nonnegative
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (stage : Nat) :
    (0 : Q') ≤ cutoffTwoCanonicalPrefixIncrement recode witness stage := by
  unfold cutoffTwoCanonicalPrefixIncrement Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (Q'.abs_nonneg _) (Q'.abs_nonneg _))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

private theorem canonicalPrefixIncrement_mul_diagonal_eqv_numerator
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (stage : Nat) :
    cutoffTwoCanonicalPrefixIncrement recode witness stage *
        cutoffTwoActualMovingDiagonalAt
          (cutoffTwoPrefixCutoff (stage + 1)) coefficient ≈
      cutoffTwoCanonicalPrefixIncrementNumerator coefficient stage := by
  unfold cutoffTwoCanonicalPrefixIncrement
  exact Q'.divPos_mul_eqv _ _ _

theorem cutoffTwoCanonicalPrefixIncrement_moving_error
    {coefficient : Nat → Q'}
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (stage : Nat) :
    Q'.abs
        (cutoffTwoActualMovingMatrixAt
            (cutoffTwoPrefixCutoff stage) coefficient +
          (-cutoffTwoActualMovingMatrixAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient)) ≤
        cutoffTwoCanonicalPrefixIncrement recode witness stage *
          cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient ∧
      Q'.abs
        (cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff stage) coefficient +
          (-cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient)) ≤
        cutoffTwoCanonicalPrefixIncrement recode witness stage *
          cutoffTwoActualMovingDiagonalAt
            (cutoffTwoPrefixCutoff (stage + 1)) coefficient := by
  let matrixDifference := Q'.abs
    (cutoffTwoActualMovingMatrixAt
        (cutoffTwoPrefixCutoff stage) coefficient +
      (-cutoffTwoActualMovingMatrixAt
        (cutoffTwoPrefixCutoff (stage + 1)) coefficient))
  let diagonalDifference := Q'.abs
    (cutoffTwoActualMovingDiagonalAt
        (cutoffTwoPrefixCutoff stage) coefficient +
      (-cutoffTwoActualMovingDiagonalAt
        (cutoffTwoPrefixCutoff (stage + 1)) coefficient))
  have hmatrix : matrixDifference ≤ matrixDifference + diagonalDifference :=
    Q'.add_le_self_of_nonneg matrixDifference diagonalDifference
      (Q'.abs_nonneg _)
  have hdiagonal : diagonalDifference ≤ matrixDifference + diagonalDifference := by
    exact Q'.le_trans' _ (diagonalDifference + matrixDifference) _
      (Q'.add_le_self_of_nonneg diagonalDifference matrixDifference
        (Q'.abs_nonneg _))
      (Q'.le_of_eqv
        (Q'.add_comm_eqv diagonalDifference matrixDifference))
  have heqv := canonicalPrefixIncrement_mul_diagonal_eqv_numerator
    recode witness stage
  constructor
  · exact Q'.le_trans' _ _ _ hmatrix (Q'.ge_of_eqv heqv)
  · exact Q'.le_trans' _ _ _ hdiagonal (Q'.ge_of_eqv heqv)

/-! ## 3. The finite increment certificate -/

private theorem abs_add_neg_le_zero_mul_of_eqv_zero
    {first later diagonal : Q'}
    (hfirst : first ≈ 0) (hlater : later ≈ 0) :
    Q'.abs (first + (-later)) ≤ (0 : Q') * diagonal := by
  have hdifference : first + (-later) ≈ 0 := by
    refine Q'.eqv_trans _ (0 + (-0)) _
      (Q'.add_eqv_congr'
        hfirst (Q'.neg_eqv_congr _ _ hlater)) ?_
    exact Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq rfl))
      (Q'.eqv_of_eq (Q'.zero_add' 0))
  have habs : Q'.abs (first + (-later)) ≈ 0 :=
    Q'.eqv_trans _ (Q'.abs 0) _
      (Q'.abs_eqv_congr hdifference)
      (Q'.eqv_of_eq rfl)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ 0 _ habs
      (Q'.eqv_symm (Q'.zero_mul_eqv diagonal)))

def rootSupportedFinitePrefixIncrementControl
    {coefficient : Nat → Q'}
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (length : Nat) :
    CutoffTwoPulledFinitePrefixIncrementControl coefficient length where
  error := fun _stage => 0
  anchor_gap := recode.anchor_gap
  error_nonnegative := by
    intro stage _hstage
    exact Q'.le_refl' 0
  moving_error := by
    intro stage _hstage
    let first := cutoffTwoPrefixCutoff stage
    let later := cutoffTwoPrefixCutoff (stage + 1)
    let diagonal := cutoffTwoActualMovingDiagonalAt later coefficient
    exact
      ⟨abs_add_neg_le_zero_mul_of_eqv_zero
          (recode.rootActualMovingMatrixAt_eqv_zero hsupported first)
          (recode.rootActualMovingMatrixAt_eqv_zero hsupported later),
        abs_add_neg_le_zero_mul_of_eqv_zero
          (recode.rootActualMovingDiagonalAt_eqv_zero hsupported first)
          (recode.rootActualMovingDiagonalAt_eqv_zero hsupported later)⟩

def CutoffTwoNonRootCoefficientWitness.finitePrefixIncrementControl
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (length : Nat) :
    CutoffTwoPulledFinitePrefixIncrementControl coefficient length where
  error := cutoffTwoCanonicalPrefixIncrement recode witness
  anchor_gap := recode.anchor_gap
  error_nonnegative := by
    intro stage _hstage
    exact cutoffTwoCanonicalPrefixIncrement_nonnegative recode witness stage
  moving_error := by
    intro stage _hstage
    exact cutoffTwoCanonicalPrefixIncrement_moving_error recode witness stage

/-- Every coefficient now has explicit finite relative-increment controls,
given only the exact compact-form recoding seam.  Root modes use zero error;
non-root modes use the canonical positive-diagonal quotient. -/
def finitePrefixIncrementControlForEveryCoefficient
    (coefficient : Nat → Q')
    (recode : CutoffTwoActualMovingFormRecode coefficient)
    (length : Nat) :
    CutoffTwoPulledFinitePrefixIncrementControl coefficient length :=
  match cutoffTwoRootSupported_orNonRootData coefficient with
  | Sum.inl hsupported =>
      rootSupportedFinitePrefixIncrementControl
        hsupported.supported recode length
  | Sum.inr witness =>
      CutoffTwoNonRootCoefficientWitness.finitePrefixIncrementControl
        witness recode length

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.CutoffTwoNonRootCoefficientWitness.pulledWeight_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.CutoffTwoNonRootCoefficientWitness.movingDiagonalAt_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.cutoffTwoCanonicalPrefixIncrement_moving_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.CutoffTwoNonRootCoefficientWitness.finitePrefixIncrementControl
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.rootSupportedFinitePrefixIncrementControl
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.cutoffTwoRootSupported_orNonRootData
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.finitePrefixIncrementControlForEveryCoefficient
