/-
# Cauchy limit of the root-centered vacuum-sector diagonal form

The moving head correction is already a Bishop real.  Since head centering
changes only coefficient zero, its pulled diagonal form is the fixed-
coefficient diagonal plus one explicit polynomial in the moving correction
and the pulled root weight.  Pointwise constructive-real addition and
multiplication therefore give a Cauchy reference sequence.

This file proves the exact finite root-replacement identity, recodes the
reference sequence so that its approximants are literally the physical
root-centered diagonal forms, and packages those forms as a Bishop real.
The reflected matrix form and a cutoff-uniform strict contraction remain
separate frontiers.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.CRealAdd
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic exact root replacement -/

private theorem listQSum_ite_single_local
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if item = selected then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if item = selected then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            · exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : head ≠ selected := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single_local selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem root_square_replacement_eqv
    (oldRoot newRoot rootWeight : Q') :
    (newRoot * newRoot) * rootWeight ≈
      (oldRoot * oldRoot) * rootWeight +
        (((newRoot * newRoot) + -(oldRoot * oldRoot)) * rootWeight) := by
  let newTerm := (newRoot * newRoot) * rootWeight
  let oldTerm := (oldRoot * oldRoot) * rootWeight
  have hdifference :
      ((newRoot * newRoot) + -(oldRoot * oldRoot)) * rootWeight ≈
        newTerm + -oldTerm := by
    exact Q'.eqv_trans _
      ((newRoot * newRoot) * rootWeight +
        (-(oldRoot * oldRoot)) * rootWeight) _
      (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (Q'.neg_mul_eqv (oldRoot * oldRoot) rootWeight))
  have hcancel : oldTerm + (newTerm + -oldTerm) ≈ newTerm := by
    refine Q'.eqv_trans _ ((oldTerm + newTerm) + -oldTerm) _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ ((newTerm + oldTerm) + -oldTerm) _
      (Q'.add_eqv_congr'
        (Q'.add_comm_eqv oldTerm newTerm) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ (newTerm + (oldTerm + -oldTerm)) _
      (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ (newTerm + 0) _
      (Q'.add_eqv_congr'
        (Q'.eqv_refl _) (Q'.add_neg_self_eqv oldTerm)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' newTerm)
  exact Q'.eqv_symm
    (Q'.eqv_trans _ (oldTerm + (newTerm + -oldTerm)) _
      (Q'.add_eqv_congr'
        (Q'.eqv_refl oldTerm) hdifference)
      hcancel)

/-- Replacing only coefficient zero changes a finite weighted square by the
corresponding difference of its two root contributions. -/
theorem finiteListRootCenteredCoefficient_diagonalExpansion
    (states : List Nat) (weight : Nat → Q')
    (hrootWeight : (0 : Q') < weight 0)
    (hnodup : states.Nodup) (hroot : 0 ∈ states)
    (coefficient : Nat → Q') :
    listQSum
        (fun index =>
          (finiteListRootCenteredCoefficient
              states weight hrootWeight coefficient index *
            finiteListRootCenteredCoefficient
              states weight hrootWeight coefficient index) *
            weight index)
        states ≈
      listQSum
          (fun index =>
            (coefficient index * coefficient index) * weight index)
          states +
        (((coefficient 0 +
              -(Q'.divPos
                (listQSum
                  (fun item => coefficient item * weight item) states)
                (weight 0) hrootWeight)) *
              (coefficient 0 +
                -(Q'.divPos
                  (listQSum
                    (fun item => coefficient item * weight item) states)
                  (weight 0) hrootWeight)) +
            -(coefficient 0 * coefficient 0)) * weight 0) := by
  let mean := listQSum
    (fun item => coefficient item * weight item) states
  let correction := -(Q'.divPos mean (weight 0) hrootWeight)
  let rootDifference :=
    (((coefficient 0 + correction) * (coefficient 0 + correction) +
      -(coefficient 0 * coefficient 0)) * weight 0)
  have hpointwise : ∀ index, index ∈ states →
      (finiteListRootCenteredCoefficient
          states weight hrootWeight coefficient index *
        finiteListRootCenteredCoefficient
          states weight hrootWeight coefficient index) * weight index ≈
        (coefficient index * coefficient index) * weight index +
          (if index = 0 then rootDifference else 0) := by
    intro index _hindex
    by_cases hzero : index = 0
    · subst index
      unfold finiteListRootCenteredCoefficient
      simp only [ite_true]
      dsimp [correction, mean, rootDifference]
      exact root_square_replacement_eqv
        (coefficient 0)
        (coefficient 0 +
          -(Q'.divPos
            (listQSum (fun item => coefficient item * weight item) states)
            (weight 0) hrootWeight))
        (weight 0)
    · simp only [if_neg hzero]
      unfold finiteListRootCenteredCoefficient
      simp only [if_neg hzero]
      have hcoefficient : coefficient index + 0 ≈ coefficient index :=
        Q'.eqv_of_eq (Q'.add_zero' _)
      have hsquare :
          (coefficient index + 0) * (coefficient index + 0) ≈
            coefficient index * coefficient index :=
        Q'.eqv_trans _ (coefficient index * (coefficient index + 0)) _
          (Q'.mul_eqv_congr_right _ _ _ hcoefficient)
          (Q'.mul_eqv_congr_left _ _ _ hcoefficient)
      exact Q'.eqv_trans _
        ((coefficient index * coefficient index) * weight index) _
        (Q'.mul_eqv_congr_right _ _ _ hsquare)
        (Q'.eqv_symm
          (Q'.eqv_of_eq
            (Q'.add_zero'
              ((coefficient index * coefficient index) * weight index))))
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        (coefficient index * coefficient index) * weight index +
          (if index = 0 then rootDifference else 0))
      states) _ ?_ ?_
  · apply listQSum_congr_on
    exact hpointwise
  refine Q'.eqv_trans _
    (listQSum
        (fun index =>
          (coefficient index * coefficient index) * weight index)
        states +
      listQSum
        (fun index => if index = 0 then rootDifference else 0)
        states) _ (listQSum_add _ _ states) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  exact Q'.eqv_trans _ rootDifference _
    (listQSum_ite_single_local 0 (fun _ => rootDifference)
      states hnodup hroot)
    (Q'.eqv_of_eq rfl)

/-! ## 2. Exact physical diagonal expansion -/

/-- At every cutoff, the moving centered diagonal is the raw fixed-vector
diagonal plus one root polynomial. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_expansion
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half coefficient +
        (((coefficient 0 +
              -centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient later) *
              (coefficient 0 +
                -centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                  hw0 base half coefficient later) +
            -(coefficient 0 * coefficient 0)) *
          centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) base later half 0) := by
  unfold centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
    centralPhysicalFinitePulledVacuumSectorWeightedMean
  exact finiteListRootCenteredCoefficient_diagonalExpansion
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (centralPhysicalFinitePulledWeight
      w (Q'.le_of_lt hw0) base later half)
    (centralPhysicalFinitePulledWeight_zero_pos
      w (Q'.le_of_lt hw0) base later half)
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      w (Q'.le_of_lt hw0) base half)
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    coefficient

/-! ## 3. Pointwise polynomial CReal and exact physical recoding -/

/-- Pointwise `Q'.eqv` recoding of a Bishop real preserves its Cauchy
modulus while allowing the displayed approximants to be the physical forms. -/
def cRealRecodePointwiseEqv
    (reference : CReal) (approximation : Nat → Q')
    (heqv : ∀ stage, approximation stage ≈ reference.approx stage) : CReal where
  approx := approximation
  cauchy := by
    intro epsilon hepsilon
    obtain ⟨cutoff, hreference⟩ := reference.cauchy epsilon hepsilon
    refine ⟨cutoff, ?_⟩
    intro first second hfirst hsecond
    have htwo := hreference first second hfirst hsecond
    constructor
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (heqv first))
        (Q'.le_trans' _ _ _ htwo.1
          (Q'.add_le_add_right _ _ epsilon
            (Q'.ge_of_eqv (heqv second))))
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (heqv second))
        (Q'.le_trans' _ _ _ htwo.2
          (Q'.add_le_add_right _ _ epsilon
            (Q'.ge_of_eqv (heqv first))))

/-- The moving root coefficient itself as a Bishop real. -/
def centralPhysicalFinitePulledVacuumSectorHeadCenteredRootCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal :=
  CReal.add
    (CReal.ofQ' (coefficient 0))
    (CReal.neg
      (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
        hw0 hw1 base half coefficient))

/-- A pointwise polynomial reference for the moving centered diagonal. -/
def centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalExpansionCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal :=
  let raw :=
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
      hw0 hw1 base half coefficient
  let centeredRoot :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredRootCutoffLimit
      hw0 hw1 base half coefficient
  let oldRootSquare := CReal.ofQ' (coefficient 0 * coefficient 0)
  let rootWeight :=
    centralPhysicalFinitePulledWeightCutoffLimit
      hw0 hw1 base half 0
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w (Q'.le_of_lt hw0) base half
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw0) base half))
  CReal.add raw
    (CReal.mul
      (CReal.add
        (CReal.mul centeredRoot centeredRoot)
        (CReal.neg oldRootSquare))
      rootWeight)

theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_eqv_expansionApprox
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') (later : Nat) :
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) ≈
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalExpansionCutoffLimit
        hw0 hw1 base half coefficient).approx later := by
  change
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) base later half coefficient +
        (((coefficient 0 +
              -centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient later) *
              (coefficient 0 +
                -centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                  hw0 base half coefficient later) +
            -(coefficient 0 * coefficient 0)) *
          centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) base later half 0)
  exact
    centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_expansion
      hw0 base later half coefficient

/-- The actual moving root-centered diagonal sequence is a Bishop real. -/
def centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal :=
  cRealRecodePointwiseEqv
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalExpansionCutoffLimit
      hw0 hw1 base half coefficient)
    (fun later =>
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient))
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_eqv_expansionApprox
      hw0 hw1 base half coefficient)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy.finiteListRootCenteredCoefficient_diagonalExpansion
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy.centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_expansion
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy.cRealRecodePointwiseEqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy.centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
