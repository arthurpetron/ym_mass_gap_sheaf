/-
# Outer centered transfer-matrix convergence for completed BF4 sector vectors

The raw moving pulled matrices of the constructed cofinal presentation now
converge to the actual completed transfer form.  Head centering adds two
correction-cross terms and one correction-square root term.  This file first
packages each finite pulled kernel as a constructive rational GNS form, so its
bilinear cross terms obey sharp Cauchy--Schwarz.  The correction-cross squares
are therefore bounded by a null correction square times the convergent raw
and root quadratics, avoiding any choice of square root or any coefficient-l1
bound on a moving completion representative.

No common strict rate, thermodynamic or continuum limit, or Clay conclusion
is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal
import YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Sharp Cauchy--Schwarz for every pulled finite-sector kernel -/

/-- The fixed-base pulled positive kernel, regarded as a rational GNS form on
coefficient functions.  Only coefficients on the finite sector list are read.
-/
def centralPhysicalFinitePulledVacuumSectorMatrixGNSData
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later) : GNSData where
  V := Nat → Q'
  veq := fun left right => ∀ index, left index ≈ right index
  veq_refl := fun coefficient index => Q'.eqv_refl (coefficient index)
  veq_symm := fun h index => Q'.eqv_symm (h index)
  veq_trans := fun hleft hright index =>
    Q'.eqv_trans _ _ _ (hleft index) (hright index)
  zero := fun _ => 0
  add := fun left right index => left index + right index
  neg := fun coefficient index => -coefficient index
  smul := fun scalar coefficient index => scalar * coefficient index
  add_congr := by
    intro left left' right right' hleft hright index
    exact Q'.add_eqv_congr' (hleft index) (hright index)
  neg_congr := by
    intro left right h index
    exact Q'.neg_eqv_congr _ _ (h index)
  smul_congr := by
    intro scalar left right h index
    exact Q'.mul_eqv_congr_left scalar _ _ (h index)
  add_assoc := fun left middle right index =>
    Q'.add_assoc_eqv (left index) (middle index) (right index)
  add_comm := fun left right index => Q'.add_comm_eqv (left index) (right index)
  zero_add := fun coefficient index =>
    Q'.eqv_of_eq (Q'.zero_add' (coefficient index))
  neg_add := fun coefficient index => Q'.neg_add_self_eqv (coefficient index)
  B := fun left right =>
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear
      w (Q'.le_of_lt hw0) base later half left right
  B_congr_left := by
    intro left left' right hleft
    unfold centralPhysicalFinitePulledVacuumSectorMatrixBilinear
    exact finiteJointBilinear_coefficient_eqv_on
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)
      left left' right right
      (centralPhysicalFinitePulledKernel
        w (Q'.le_of_lt hw0) base later half)
      (fun index _ => hleft index)
      (fun index _ => Q'.eqv_refl (right index))
  B_add_left := by
    intro left right test
    unfold centralPhysicalFinitePulledVacuumSectorMatrixBilinear
    exact finiteJointBilinear_add_left
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)
      left right test
      (centralPhysicalFinitePulledKernel
        w (Q'.le_of_lt hw0) base later half)
  B_smul_left := by
    intro scalar left right
    unfold centralPhysicalFinitePulledVacuumSectorMatrixBilinear
    exact finiteJointBilinear_scale_left
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)
      scalar left right
      (centralPhysicalFinitePulledKernel
        w (Q'.le_of_lt hw0) base later half)
  B_symm := by
    intro left right
    unfold centralPhysicalFinitePulledVacuumSectorMatrixBilinear
    apply finiteJointBilinear_swap_of_symmetric
    intro row column hrow hcolumn
    unfold centralPhysicalFinitePulledKernel
    exact centralNormalizedPhysicalReflectedKernel_symm
      ((mem_centralPositiveHalfStates_iff.mp
        (centralPhysicalFiniteStateAt_mem_positive
          w (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w (Q'.le_of_lt hw0) later half
            (centralPhysicalFiniteVacuumSectorIndexMap_mem
              hbase hrow)))).1)
      ((mem_centralPositiveHalfStates_iff.mp
        (centralPhysicalFiniteStateAt_mem_positive
          w (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w (Q'.le_of_lt hw0) later half
            (centralPhysicalFiniteVacuumSectorIndexMap_mem
              hbase hcolumn)))).1)
  self_nonneg := by
    intro coefficient
    let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
      w (Q'.le_of_lt hw0) base later half coefficient
    have hpositive :=
      centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
        w (Q'.le_of_lt hw0) later half extension
    have hpulled :=
      centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
        (w := w) (hw := Q'.le_of_lt hw0) (base := base)
        (later := later) (half := half) hbase coefficient
    change (0 : Q') ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half coefficient
    exact Q'.le_trans' _ _ _ hpositive (Q'.le_of_eqv hpulled)

/-- Sharp rational Cauchy--Schwarz for the finite pulled bilinear form. -/
theorem centralPhysicalFinitePulledVacuumSectorMatrixBilinear_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later)
    (left right : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half left right *
        centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half left right ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half left *
        centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half right := by
  exact
    (centralPhysicalFinitePulledVacuumSectorMatrixGNSData
      hw0 base later half hbase).cauchy_schwarz left right

theorem centralPhysicalFinitePulledVacuumSectorMatrixBilinear_symm
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later)
    (left right : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) base later half left right ≈
      centralPhysicalFinitePulledVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) base later half right left :=
  (centralPhysicalFinitePulledVacuumSectorMatrixGNSData
    hw0 base later half hbase).B_symm left right

/-- Cauchy--Schwarz after packaging the three fixed-presentation cutoff
limits as constructive reals. -/
theorem centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (left right : Nat → Q') :
    CReal.leEv
      (CReal.mul
        (centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
          hw0 hw1 base half left right)
        (centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
          hw0 hw1 base half left right))
      (CReal.mul
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
          hw0 hw1 base half left)
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
          hw0 hw1 base half right)) := by
  intro epsilon hepsilon
  refine ⟨base, fun later hlater => ?_⟩
  exact Q'.le_trans' _ _ _
    (centralPhysicalFinitePulledVacuumSectorMatrixBilinear_cauchy_schwarz
      hw0 base later half hlater left right)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-! ## 2. The moving pulled root quadratic is one canonical real -/

private theorem listQSum_value_mul_rootIndicator
    (value : Nat → Q') :
    ∀ states : List Nat, states.Nodup → 0 ∈ states →
      listQSum
          (fun index => value index * finiteRootIndicator index)
          states ≈ value 0
  | [], _hnodup, hroot => False.elim (List.not_mem_nil hroot)
  | head :: tail, hnodup, hroot => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hroot with hhead | htail
      · subst head
        simp only [listQSum]
        have hzero :
            listQSum
                (fun index => value index * finiteRootIndicator index)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _ => (0 : Q')) tail) _ ?_ (listQSum_zero tail)
          apply listQSum_congr_on
          intro index hindex
          have hne : index ≠ 0 := by
            intro heq
            subst index
            exact hparts.1 hindex
          unfold finiteRootIndicator
          rw [if_neg hne]
          exact Q'.mul_zero_eqv _
        unfold finiteRootIndicator
        rw [if_pos rfl]
        exact Q'.eqv_trans _ (value 0 + 0) _
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv (value 0)) hzero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : head ≠ 0 := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum]
        unfold finiteRootIndicator
        rw [if_neg hne]
        exact Q'.eqv_trans _ (0 + value 0) _
          (Q'.add_eqv_congr'
            (Q'.mul_zero_eqv (value head))
            (listQSum_value_mul_rootIndicator value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

theorem centralPhysicalFinitePulledVacuumSectorMatrix_le_diagonal
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half coefficient ≤
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half coefficient := by
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w (Q'.le_of_lt hw0) base later half coefficient
  have hfull := centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
    w (Q'.le_of_lt hw0) later half extension
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
      (w := w) (hw := Q'.le_of_lt hw0) (base := base)
      (later := later) (half := half) hbase coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
      (w := w) (hw := Q'.le_of_lt hw0) (base := base)
      (later := later) (half := half) hbase coefficient
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
    (Q'.le_trans' _ _ _ hfull (Q'.le_of_eqv hdiagonal))

theorem centralPhysicalFinitePulledVacuumSector_rootDiagonal_eqv_weight
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) :
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half finiteRootIndicator ≈
      centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base later half 0 := by
  unfold centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base later half index *
            finiteRootIndicator index)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    by_cases hzero : index = 0
    · simp only [finiteRootIndicator, if_pos hzero]
      refine Q'.eqv_trans _
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base later half index) _ ?_ ?_
      · exact Q'.eqv_trans _
          (1 * centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) base later half index) _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1))
          (Q'.one_mul_eqv _)
      · exact Q'.eqv_symm (Q'.mul_one_eqv _)
    · simp only [finiteRootIndicator, if_neg hzero]
      refine Q'.eqv_trans _ 0 _ ?_ ?_
      · exact Q'.eqv_trans _
          (0 * centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) base later half index) _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv 0))
          (Q'.zero_mul_eqv _)
      · exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  · exact listQSum_value_mul_rootIndicator
      (centralPhysicalFinitePulledWeight
        w (Q'.le_of_lt hw0) base later half)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        w (Q'.le_of_lt hw0) base half)
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half)

/-- Each finite pulled cross square is bounded by the raw pulled quadratic
times the distinguished pulled root weight. -/
theorem centralPhysicalFinitePulledVacuumSectorMatrixCross_sq_le_raw_mul_rootWeight
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half
          coefficient finiteRootIndicator *
        centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half
          coefficient finiteRootIndicator ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half coefficient *
        centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base later half 0 := by
  have hcs :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear_cauchy_schwarz
      hw0 base later half hbase coefficient finiteRootIndicator
  have hroot := centralPhysicalFinitePulledVacuumSectorMatrix_le_diagonal
    hw0 base later half hbase finiteRootIndicator
  have hrootWeight :=
    centralPhysicalFinitePulledVacuumSector_rootDiagonal_eqv_weight
      hw0 base later half
  have hrawNonnegative :=
    (centralPhysicalFinitePulledVacuumSectorMatrixGNSData
      hw0 base later half hbase).self_nonneg coefficient
  have hrootFinal :
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half finiteRootIndicator ≤
        centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base later half 0 :=
    Q'.le_trans' _ _ _ hroot (Q'.le_of_eqv hrootWeight)
  exact Q'.le_trans' _ _ _ hcs
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hrootFinal hrawNonnegative)

/-! ## 3. The two correction-cross terms vanish -/

private theorem q_mul_mul_mul_comm (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

private theorem q_neg_zero_eqv : (-(0 : Q')) ≈ 0 := by decide

private theorem q_sub_zero_mul_square_rearrange (scalar cross : Q') :
    ((scalar * cross + -(0 : Q')) *
        (scalar * cross + -(0 : Q'))) ≈
      (scalar * scalar) * (cross * cross) := by
  have hdrop : scalar * cross + -(0 : Q') ≈ scalar * cross :=
    Q'.eqv_trans _ (scalar * cross + 0) _
      (Q'.add_eqv_congr_left _ _ _ q_neg_zero_eqv)
      (QPoly.q_add_zero_eqv _)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _
      ((scalar * cross) * (scalar * cross + -(0 : Q'))) _
      (Q'.mul_eqv_congr_right _ _ _ hdrop)
      (Q'.mul_eqv_congr_left _ _ _ hdrop))
    (q_mul_mul_mul_comm scalar cross scalar cross)

private theorem creal_neg_czero :
    CReal.Equiv (CReal.neg CReal.czero) CReal.czero :=
  Equiv_of_approx_eqv (fun _ => q_neg_zero_eqv)

private theorem creal_zero_mul (value : CReal) :
    CReal.Equiv (CReal.mul CReal.czero value) CReal.czero :=
  Equiv_of_approx_eqv (fun stage => Q'.zero_mul_eqv (value.approx stage))

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  Equiv_of_approx_eqv (fun stage =>
    Q'.eqv_of_eq (Q'.add_zero' (value.approx stage)))

def centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  CReal.neg
    (centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq
      (centralPhysicalVacuumSectorOuterMatrixInputCauchy
        hw0 hw1 half X) stage)

def centralPhysicalVacuumSectorCylinderOuterMatrixRightCrossSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
    hw0 hw1 presentation.base half
    presentation.coefficient finiteRootIndicator

def centralPhysicalVacuumSectorCylinderOuterMatrixLeftCrossSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
    hw0 hw1 presentation.base half
    finiteRootIndicator presentation.coefficient

def centralPhysicalVacuumSectorCylinderOuterMatrixRightCorrectionSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  CReal.mul
    (centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
      hw0 hw1 half X stage)
    (centralPhysicalVacuumSectorCylinderOuterMatrixRightCrossSeq
      hw0 hw1 half X stage)

theorem centralPhysicalVacuumSectorCylinder_outerMatrixRightCorrection_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterMatrixRightCorrectionSeq
        hw0 hw1 half X)
      CReal.czero := by
  let Z := centralPhysicalVacuumSectorOuterMatrixInputCauchy
    hw0 hw1 half X
  let shiftSeq := centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
    hw0 hw1 half X
  let crossSeq := centralPhysicalVacuumSectorCylinderOuterMatrixRightCrossSeq
    hw0 hw1 half X
  let rawSeq := centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X
  let weightSeq := centralPhysicalVacuumSectorCylinderOuterRootWeightSeq Z
  let errorSeq := fun stage =>
    CReal.mul
      (CReal.mul (shiftSeq stage) (shiftSeq stage))
      (CReal.mul (rawSeq stage) (weightSeq stage))
  let rawLimit := centralPhysicalVacuumSectorOuterMatrixPairingLimit
    hw0 hw1 half X
  let weightLimit :=
    centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
      hw0 hw1 half
  have horthogonalZ :
      CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
        hw0 hw1 half
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid Z) := by
    rw [← centralPhysicalVacuumSectorOuterMatrixInput_class_eq
      hw0 hw1 half X]
    exact horthogonal
  have hcorrection : CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq Z)
      CReal.czero :=
    centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero
      hw0 hw1 half Z horthogonalZ
  have hshiftRaw := CReal.convergesTo_neg hcorrection
  have hshift : CReal.ConvergesTo shiftSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr hshiftRaw
    exact creal_neg_czero
  have hshiftSquareRaw := CReal.convergesTo_mul_general hshift hshift
  have hshiftSquare : CReal.ConvergesTo
      (fun stage => CReal.mul (shiftSeq stage) (shiftSeq stage))
      CReal.czero := by
    apply CReal.convergesTo_limit_congr hshiftSquareRaw
    exact creal_zero_mul CReal.czero
  have hraw : CReal.ConvergesTo rawSeq rawLimit := by
    simpa only [rawSeq] using
      (centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
        hw0 hw1 half X)
  have hweight : CReal.ConvergesTo weightSeq weightLimit := by
    simpa only [weightSeq, weightLimit] using
      (centralPhysicalVacuumSectorCylinder_outerRootWeight_converges
        hw0 hw1 half Z)
  have hrawWeight := CReal.convergesTo_mul_general hraw hweight
  have herrorRaw := CReal.convergesTo_mul_general hshiftSquare hrawWeight
  have herror : CReal.ConvergesTo errorSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr herrorRaw
    exact creal_zero_mul (CReal.mul rawLimit weightLimit)
  apply CReal.convergesTo_of_sqDiff_le_null (e := errorSeq)
  · intro stage
    let presentation := Z.seq stage
    intro epsilon hepsilon
    refine ⟨presentation.base, fun later hlater => ?_⟩
    have hcross :=
      centralPhysicalFinitePulledVacuumSectorMatrixCross_sq_le_raw_mul_rootWeight
        hw0 presentation.base later half hlater presentation.coefficient
    let scalar := (shiftSeq stage).approx later
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hcross
      (q_mul_self_nonneg scalar)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (q_sub_zero_mul_square_rearrange scalar
          ((crossSeq stage).approx later)))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))
  · exact herror

theorem centralPhysicalFinitePulledVacuumSectorMatrixRootCross_sq_le_raw_mul_rootWeight
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half
          finiteRootIndicator coefficient *
        centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half
          finiteRootIndicator coefficient ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half coefficient *
        centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base later half 0 := by
  have hsymm := centralPhysicalFinitePulledVacuumSectorMatrixBilinear_symm
    hw0 base later half hbase finiteRootIndicator coefficient
  have hsquare :
      centralPhysicalFinitePulledVacuumSectorMatrixBilinear
            w (Q'.le_of_lt hw0) base later half
            finiteRootIndicator coefficient *
          centralPhysicalFinitePulledVacuumSectorMatrixBilinear
            w (Q'.le_of_lt hw0) base later half
            finiteRootIndicator coefficient ≈
        centralPhysicalFinitePulledVacuumSectorMatrixBilinear
            w (Q'.le_of_lt hw0) base later half
            coefficient finiteRootIndicator *
          centralPhysicalFinitePulledVacuumSectorMatrixBilinear
            w (Q'.le_of_lt hw0) base later half
            coefficient finiteRootIndicator :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hsymm)
      (Q'.mul_eqv_congr_left _ _ _ hsymm)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare)
    (centralPhysicalFinitePulledVacuumSectorMatrixCross_sq_le_raw_mul_rootWeight
      hw0 base later half hbase coefficient)

def centralPhysicalVacuumSectorCylinderOuterMatrixLeftCorrectionSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  CReal.mul
    (centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
      hw0 hw1 half X stage)
    (centralPhysicalVacuumSectorCylinderOuterMatrixLeftCrossSeq
      hw0 hw1 half X stage)

theorem centralPhysicalVacuumSectorCylinder_outerMatrixLeftCorrection_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterMatrixLeftCorrectionSeq
        hw0 hw1 half X)
      CReal.czero := by
  let Z := centralPhysicalVacuumSectorOuterMatrixInputCauchy
    hw0 hw1 half X
  let shiftSeq := centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
    hw0 hw1 half X
  let crossSeq := centralPhysicalVacuumSectorCylinderOuterMatrixLeftCrossSeq
    hw0 hw1 half X
  let rawSeq := centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X
  let weightSeq := centralPhysicalVacuumSectorCylinderOuterRootWeightSeq Z
  let errorSeq := fun stage =>
    CReal.mul
      (CReal.mul (shiftSeq stage) (shiftSeq stage))
      (CReal.mul (rawSeq stage) (weightSeq stage))
  let rawLimit := centralPhysicalVacuumSectorOuterMatrixPairingLimit
    hw0 hw1 half X
  let weightLimit :=
    centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
      hw0 hw1 half
  have horthogonalZ :
      CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
        hw0 hw1 half
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid Z) := by
    rw [← centralPhysicalVacuumSectorOuterMatrixInput_class_eq
      hw0 hw1 half X]
    exact horthogonal
  have hcorrection : CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq Z)
      CReal.czero :=
    centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero
      hw0 hw1 half Z horthogonalZ
  have hshiftRaw := CReal.convergesTo_neg hcorrection
  have hshift : CReal.ConvergesTo shiftSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr hshiftRaw
    exact creal_neg_czero
  have hshiftSquareRaw := CReal.convergesTo_mul_general hshift hshift
  have hshiftSquare : CReal.ConvergesTo
      (fun stage => CReal.mul (shiftSeq stage) (shiftSeq stage))
      CReal.czero := by
    apply CReal.convergesTo_limit_congr hshiftSquareRaw
    exact creal_zero_mul CReal.czero
  have hraw : CReal.ConvergesTo rawSeq rawLimit := by
    simpa only [rawSeq] using
      (centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
        hw0 hw1 half X)
  have hweight : CReal.ConvergesTo weightSeq weightLimit := by
    simpa only [weightSeq, weightLimit] using
      (centralPhysicalVacuumSectorCylinder_outerRootWeight_converges
        hw0 hw1 half Z)
  have hrawWeight := CReal.convergesTo_mul_general hraw hweight
  have herrorRaw := CReal.convergesTo_mul_general hshiftSquare hrawWeight
  have herror : CReal.ConvergesTo errorSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr herrorRaw
    exact creal_zero_mul (CReal.mul rawLimit weightLimit)
  apply CReal.convergesTo_of_sqDiff_le_null (e := errorSeq)
  · intro stage
    let presentation := Z.seq stage
    intro epsilon hepsilon
    refine ⟨presentation.base, fun later hlater => ?_⟩
    have hcross :=
      centralPhysicalFinitePulledVacuumSectorMatrixRootCross_sq_le_raw_mul_rootWeight
        hw0 presentation.base later half hlater presentation.coefficient
    let scalar := (shiftSeq stage).approx later
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hcross
      (q_mul_self_nonneg scalar)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (q_sub_zero_mul_square_rearrange scalar
          ((crossSeq stage).approx later)))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))
  · exact herror

/-! ## 4. The correction-square root term vanishes -/

theorem centralPhysicalFinitePulledVacuumSectorRootMatrix_nonnegative_le_weight
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (hbase : base ≤ later) :
    (0 : Q') ≤
        centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half
          finiteRootIndicator finiteRootIndicator ∧
      centralPhysicalFinitePulledVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) base later half
          finiteRootIndicator finiteRootIndicator ≤
        centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base later half 0 := by
  have hnonnegative :=
    (centralPhysicalFinitePulledVacuumSectorMatrixGNSData
      hw0 base later half hbase).self_nonneg finiteRootIndicator
  have hmatrix := centralPhysicalFinitePulledVacuumSectorMatrix_le_diagonal
    hw0 base later half hbase finiteRootIndicator
  have hweight :=
    centralPhysicalFinitePulledVacuumSector_rootDiagonal_eqv_weight
      hw0 base later half
  exact ⟨hnonnegative,
    Q'.le_trans' _ _ _ hmatrix (Q'.le_of_eqv hweight)⟩

def centralPhysicalVacuumSectorCylinderOuterMatrixRootRootSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
    hw0 hw1 presentation.base half
    finiteRootIndicator finiteRootIndicator

def centralPhysicalVacuumSectorCylinderOuterMatrixRootCorrectionSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  let shift := centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
    hw0 hw1 half X stage
  CReal.mul (CReal.mul shift shift)
    (centralPhysicalVacuumSectorCylinderOuterMatrixRootRootSeq
      hw0 hw1 half X stage)

theorem centralPhysicalVacuumSectorCylinder_outerMatrixRootCorrection_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterMatrixRootCorrectionSeq
        hw0 hw1 half X)
      CReal.czero := by
  let Z := centralPhysicalVacuumSectorOuterMatrixInputCauchy
    hw0 hw1 half X
  let shiftSeq := centralPhysicalVacuumSectorCylinderOuterMatrixShiftSeq
    hw0 hw1 half X
  let rootSeq := centralPhysicalVacuumSectorCylinderOuterMatrixRootRootSeq
    hw0 hw1 half X
  let weightSeq := centralPhysicalVacuumSectorCylinderOuterRootWeightSeq Z
  let boundSeq := fun stage =>
    CReal.mul
      (CReal.mul (shiftSeq stage) (shiftSeq stage))
      (weightSeq stage)
  let errorSeq := fun stage => CReal.mul (boundSeq stage) (boundSeq stage)
  let weightLimit :=
    centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
      hw0 hw1 half
  have horthogonalZ :
      CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
        hw0 hw1 half
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid Z) := by
    rw [← centralPhysicalVacuumSectorOuterMatrixInput_class_eq
      hw0 hw1 half X]
    exact horthogonal
  have hcorrection : CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq Z)
      CReal.czero :=
    centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero
      hw0 hw1 half Z horthogonalZ
  have hshiftRaw := CReal.convergesTo_neg hcorrection
  have hshift : CReal.ConvergesTo shiftSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr hshiftRaw
    exact creal_neg_czero
  have hshiftSquareRaw := CReal.convergesTo_mul_general hshift hshift
  have hshiftSquare : CReal.ConvergesTo
      (fun stage => CReal.mul (shiftSeq stage) (shiftSeq stage))
      CReal.czero := by
    apply CReal.convergesTo_limit_congr hshiftSquareRaw
    exact creal_zero_mul CReal.czero
  have hweight : CReal.ConvergesTo weightSeq weightLimit := by
    simpa only [weightSeq, weightLimit] using
      (centralPhysicalVacuumSectorCylinder_outerRootWeight_converges
        hw0 hw1 half Z)
  have hboundRaw := CReal.convergesTo_mul_general hshiftSquare hweight
  have hbound : CReal.ConvergesTo boundSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr hboundRaw
    exact creal_zero_mul weightLimit
  have herrorRaw := CReal.convergesTo_mul_general hbound hbound
  have herror : CReal.ConvergesTo errorSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr herrorRaw
    exact creal_zero_mul CReal.czero
  apply CReal.convergesTo_of_sqDiff_le_null (e := errorSeq)
  · intro stage
    let presentation := Z.seq stage
    intro epsilon hepsilon
    refine ⟨presentation.base, fun later hlater => ?_⟩
    obtain ⟨hrootNonnegative, hrootWeight⟩ :=
      centralPhysicalFinitePulledVacuumSectorRootMatrix_nonnegative_le_weight
        hw0 presentation.base later half hlater
    let scalar := (shiftSeq stage).approx later
    let root := (rootSeq stage).approx later
    let weight := (weightSeq stage).approx later
    have hweightNonnegative : (0 : Q') ≤ weight :=
      Q'.le_trans' _ _ _ hrootNonnegative hrootWeight
    have hrootSquare : root * root ≤ weight * weight :=
      Q'.mul_le_mul_of_nonneg hrootWeight hrootWeight
        hweightNonnegative hrootNonnegative
    have hscalarFourth : (0 : Q') ≤
        (scalar * scalar) * (scalar * scalar) :=
      q_mul_self_nonneg (scalar * scalar)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hrootSquare
      hscalarFourth
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (q_sub_zero_mul_square_rearrange
          (scalar * scalar) root))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (q_mul_mul_mul_comm
                (scalar * scalar) weight
                (scalar * scalar) weight)))
          (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))))
  · exact herror

/-! ## 5. Outer centered-matrix convergence and endpoint identification -/

def centralPhysicalVacuumSectorCylinderOuterHeadCenteredMatrixSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
    hw0 hw1 presentation.base half presentation.coefficient

def centralPhysicalVacuumSectorCylinderOuterMatrixExpansionSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  CReal.add
    (centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X stage)
    (CReal.add
      (centralPhysicalVacuumSectorCylinderOuterMatrixRightCorrectionSeq
        hw0 hw1 half X stage)
      (CReal.add
        (centralPhysicalVacuumSectorCylinderOuterMatrixLeftCorrectionSeq
          hw0 hw1 half X stage)
        (centralPhysicalVacuumSectorCylinderOuterMatrixRootCorrectionSeq
          hw0 hw1 half X stage)))

theorem centralPhysicalVacuumSectorCylinder_outerHeadCenteredMatrix_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterHeadCenteredMatrixSeq
        hw0 hw1 half X)
      (centralPhysicalVacuumSectorOuterMatrixPairingLimit
        hw0 hw1 half X) := by
  let rawSeq := centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X
  let rightSeq :=
    centralPhysicalVacuumSectorCylinderOuterMatrixRightCorrectionSeq
      hw0 hw1 half X
  let leftSeq :=
    centralPhysicalVacuumSectorCylinderOuterMatrixLeftCorrectionSeq
      hw0 hw1 half X
  let rootSeq :=
    centralPhysicalVacuumSectorCylinderOuterMatrixRootCorrectionSeq
      hw0 hw1 half X
  let rawLimit := centralPhysicalVacuumSectorOuterMatrixPairingLimit
    hw0 hw1 half X
  have hraw : CReal.ConvergesTo rawSeq rawLimit := by
    simpa only [rawSeq] using
      (centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
        hw0 hw1 half X)
  have hright : CReal.ConvergesTo rightSeq CReal.czero := by
    simpa only [rightSeq] using
      (centralPhysicalVacuumSectorCylinder_outerMatrixRightCorrection_converges_zero
        hw0 hw1 half X horthogonal)
  have hleft : CReal.ConvergesTo leftSeq CReal.czero := by
    simpa only [leftSeq] using
      (centralPhysicalVacuumSectorCylinder_outerMatrixLeftCorrection_converges_zero
        hw0 hw1 half X horthogonal)
  have hroot : CReal.ConvergesTo rootSeq CReal.czero := by
    simpa only [rootSeq] using
      (centralPhysicalVacuumSectorCylinder_outerMatrixRootCorrection_converges_zero
        hw0 hw1 half X horthogonal)
  have hleftRootRaw := CReal.convergesTo_add hleft hroot
  have hleftRoot : CReal.ConvergesTo
      (fun stage => CReal.add (leftSeq stage) (rootSeq stage))
      CReal.czero := by
    apply CReal.convergesTo_limit_congr hleftRootRaw
    exact creal_add_czero CReal.czero
  have htailRaw := CReal.convergesTo_add hright hleftRoot
  have htail : CReal.ConvergesTo
      (fun stage =>
        CReal.add (rightSeq stage)
          (CReal.add (leftSeq stage) (rootSeq stage)))
      CReal.czero := by
    apply CReal.convergesTo_limit_congr htailRaw
    exact creal_add_czero CReal.czero
  have hexpansionRaw := CReal.convergesTo_add hraw htail
  have hexpansion : CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterMatrixExpansionSeq
        hw0 hw1 half X)
      rawLimit := by
    apply CReal.convergesTo_limit_congr hexpansionRaw
    exact creal_add_czero rawLimit
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := centralPhysicalVacuumSectorCylinderOuterMatrixExpansionSeq
      hw0 hw1 half X)
  · intro stage
    let presentation :=
      (centralPhysicalVacuumSectorOuterMatrixInputCauchy
        hw0 hw1 half X).seq stage
    exact CReal.Equiv.symm
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_expansion
        hw0 hw1 presentation.base half presentation.coefficient)
  · exact hexpansion

/-- The centered-matrix convergence target is the actual completed transfer
pairing of the original quotient vector. -/
theorem centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerCenteredMatrixLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          (Quotient.mk
            (centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).completionSetoid X))
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid X) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalVacuumSectorOuterMatrixPairingLimit
          hw0 hw1 half X) :=
  centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerRawMatrixLimit
    hw0 hw1 half X

/-! ## 6. Choice-free all-vector closure of a fixed strict certificate -/

/-- The outer matrix presentation simultaneously represents the centered
diagonal and centered transfer form of one arbitrary quotient representative.
The diagonal uses the recoded representative itself, while the transfer
endpoint is transported back to the original quotient class. -/
def centralPhysicalVacuumSectorCylinder_centeredFormLimitData_mk
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CentralPhysicalVacuumSectorCylinderCenteredFormLimitData
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X) := by
  let Z := centralPhysicalVacuumSectorOuterMatrixInputCauchy
    hw0 hw1 half X
  let normLimit := physicalCauchyPairingLimit hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal Z)
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal Z)
  let formLimit := centralPhysicalVacuumSectorOuterMatrixPairingLimit
    hw0 hw1 half X
  have horthogonalZ :
      CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
        hw0 hw1 half
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid Z) := by
    rw [<- centralPhysicalVacuumSectorOuterMatrixInput_class_eq
      hw0 hw1 half X]
    exact horthogonal
  refine {
    presentation := Z.seq
    normLimit := normLimit
    formLimit := formLimit
    diagonal_converges := ?_
    matrix_converges := ?_
    norm_identifies := ?_
    form_identifies := ?_
  }
  · exact centralPhysicalVacuumSectorCylinder_outerHeadCenteredDiagonal_converges
      hw0 hw1 half Z horthogonalZ
  · exact centralPhysicalVacuumSectorCylinder_outerHeadCenteredMatrix_converges
      hw0 hw1 half X horthogonal
  · rw [centralPhysicalVacuumSectorOuterMatrixInput_class_eq
      hw0 hw1 half X]
    exact
      centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerCenteredDiagonalLimit
        hw0 hw1 half Z
  · exact
      centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerCenteredMatrixLimit
        hw0 hw1 half X

/-- One finite-sector strict certificate gives the actual completed strict
form bound on every vector in the root-sector vacuum complement.  The proof
eliminates the completion quotient only into this proposition and constructs
the moving centered limits locally for each representative; it therefore does
not require a choice of representatives or the stronger Type-valued global
cofinality structure. -/
theorem centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_constructed
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1 vector.1)
      (CReal.RCscale q
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half vector.1 vector.1)) := by
  rcases vector with ⟨vector, horthogonal⟩
  change CReal.RCle
    (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedTransfer
        hw0 hw1 half vector) vector)
    (CReal.RCscale q
      (centralPhysicalVacuumSectorCylinderCompletedInner
        hw0 hw1 half vector vector))
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  let data :=
    centralPhysicalVacuumSectorCylinder_centeredFormLimitData_mk
      hw0 hw1 half X horthogonal
  rw [data.form_identifies, data.norm_identifies,
    CReal.RCscale_mk, CReal.RCle_mk]
  apply CReal.leEv_of_convergesTo_le
    data.matrix_converges
    (CReal.convergesTo_constMul q data.diagonal_converges)
  intro stage
  exact certificate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half
    (data.presentation stage).base
    (data.presentation stage).coefficient

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalFinitePulledVacuumSectorMatrixGNSData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalFinitePulledVacuumSectorMatrixBilinear_cauchy_schwarz
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit_cauchy_schwarz
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalFinitePulledVacuumSectorMatrixCross_sq_le_raw_mul_rootWeight
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_outerMatrixRightCorrection_converges_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_outerMatrixLeftCorrection_converges_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_outerMatrixRootCorrection_converges_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_outerHeadCenteredMatrix_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerCenteredMatrixLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_centeredFormLimitData_mk
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_constructed
