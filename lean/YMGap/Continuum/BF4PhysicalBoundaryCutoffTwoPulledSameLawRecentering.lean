/-
# Same-law form stability for moving cutoff-two recentering

The previous module proves that changing the representation cutoff changes a
moving centered coefficient only at the distinguished root.  Here that exact
coefficient motion is passed through one fixed later pulled law.

First, a generic finite quadratic perturbation theorem bounds the form change
caused by adding a scalar multiple of one basis vector.  Second, normalized
physical pulled-kernel entries on the cutoff-two carrier are proved to have
absolute value at most one: nonnegativity puts an entry below its full row
sum, and the retained physical row marginal is at most one.  The final theorem
therefore gives an explicit same-law matrix error whose small parameter is
exactly the head-correction change.

This does not yet compare two different cutoff laws or provide a strict total
cutoff-two-to-limit rate budget.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RcQuadResidualClose
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite same-law coefficient stability -/

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

private theorem finiteJointBilinear_zeroLaw_eqv
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q') :
    finiteJointBilinear states leftCoefficient rightCoefficient
        (fun _ _ => (0 : Q')) ≈ 0 := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum (fun _ : State => (0 : Q')) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _hleft
    refine Q'.eqv_trans _
      (listQSum (fun _ : State => (0 : Q')) states) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _hright
      exact Q'.mul_zero_eqv
        (leftCoefficient left * rightCoefficient right)
    · exact listQSum_zero states
  · exact listQSum_zero states

private theorem add_neg_zero_eqv_local (value : Q') :
    value + (-(0 : Q')) ≈ value := by
  refine Q'.eqv_trans _ (value + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (by decide : (-(0 : Q')) ≈ 0)
  · exact Q'.eqv_of_eq (Q'.add_zero' value)

/-- A finite bilinear form under a law whose entries have absolute value at
most one is bounded by the product of the two coefficient `l1` norms. -/
theorem finiteJointBilinear_abs_le_productL1_of_entry_abs_le_one
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q')
    (hentry : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (joint left right) ≤ 1) :
    Q'.abs
        (finiteJointBilinear
          states leftCoefficient rightCoefficient joint) ≤
      coefficientL1 states leftCoefficient *
        coefficientL1 states rightCoefficient := by
  let zeroLaw : State → State → Q' := fun _ _ => 0
  have hfinite := finiteJointBilinear_abs_sub_le_productL1
    states leftCoefficient rightCoefficient joint zeroLaw 1
    (by decide : (0 : Q') ≤ 1)
    (fun left right hleft hright => by
      have hdifference :
          joint left right + (-zeroLaw left right) ≈
            joint left right := add_neg_zero_eqv_local (joint left right)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
        (hentry left right hleft hright))
  have hzero :
      finiteJointBilinear
          states leftCoefficient rightCoefficient zeroLaw ≈ 0 :=
    finiteJointBilinear_zeroLaw_eqv
      states leftCoefficient rightCoefficient
  have hdifference :
      finiteJointBilinear states leftCoefficient rightCoefficient joint +
          (-finiteJointBilinear
            states leftCoefficient rightCoefficient zeroLaw) ≈
        finiteJointBilinear
          states leftCoefficient rightCoefficient joint := by
    refine Q'.eqv_trans _
      (finiteJointBilinear states leftCoefficient rightCoefficient joint +
        (-(0 : Q'))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ hzero)
    · exact add_neg_zero_eqv_local _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hdifference)))
    (Q'.le_trans' _ _ _ hfinite
      (Q'.le_of_eqv
        (Q'.mul_one_eqv
          (coefficientL1 states leftCoefficient *
            coefficientL1 states rightCoefficient))))

/-- Adding a scalar multiple of one finite coefficient vector changes a
quadratic under one fixed entry-bounded law by the three exact bilinear
terms, each controlled by the corresponding `l1` product. -/
theorem finiteJointQuadratic_add_scaled_abs_sub_le
    {State : Type} (states : List State)
    (coefficient basis : State → Q') (scalar : Q')
    (joint : State → State → Q')
    (hentry : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (joint left right) ≤ 1) :
    Q'.abs
        (finiteJointQuadratic states
            (fun state => coefficient state + scalar * basis state) joint +
          (-finiteJointQuadratic states coefficient joint)) ≤
      Q'.abs scalar *
          (coefficientL1 states coefficient * coefficientL1 states basis) +
        (Q'.abs scalar *
            (coefficientL1 states basis * coefficientL1 states coefficient) +
          (Q'.abs scalar * Q'.abs scalar) *
            (coefficientL1 states basis * coefficientL1 states basis)) := by
  change Q'.abs
      (finiteJointBilinear states
          (fun state => coefficient state + scalar * basis state)
          (fun state => coefficient state + scalar * basis state) joint +
        (-finiteJointBilinear
          states coefficient coefficient joint)) ≤ _
  let baseForm :=
    finiteJointBilinear states coefficient coefficient joint
  let rightCross :=
    finiteJointBilinear states coefficient basis joint
  let leftCross :=
    finiteJointBilinear states basis coefficient joint
  let basisForm :=
    finiteJointBilinear states basis basis joint
  let firstTerm := scalar * rightCross
  let secondTerm := scalar * leftCross
  let thirdTerm := (scalar * scalar) * basisForm
  let remainder := firstTerm + (secondTerm + thirdTerm)
  have hexpansion := finiteJointBilinear_add_scaled_self
    states coefficient basis scalar joint
  have hdifference :
      finiteJointBilinear states
          (fun state => coefficient state + scalar * basis state)
          (fun state => coefficient state + scalar * basis state) joint +
        (-finiteJointBilinear states coefficient coefficient joint) ≈
      remainder := by
    refine Q'.eqv_trans _ ((baseForm + remainder) + (-baseForm)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ hexpansion
    · refine Q'.eqv_trans _ ((remainder + baseForm) + (-baseForm)) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv baseForm remainder)) ?_
      refine Q'.eqv_trans _ (remainder + (baseForm + (-baseForm))) _
        (Q'.add_assoc_eqv remainder baseForm (-baseForm)) ?_
      refine Q'.eqv_trans _ (remainder + 0) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_neg_self_eqv baseForm)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' remainder)
  have hright := finiteJointBilinear_abs_le_productL1_of_entry_abs_le_one
    states coefficient basis joint hentry
  have hleft := finiteJointBilinear_abs_le_productL1_of_entry_abs_le_one
    states basis coefficient joint hentry
  have hbasis := finiteJointBilinear_abs_le_productL1_of_entry_abs_le_one
    states basis basis joint hentry
  have hfirst : Q'.abs firstTerm ≤
      Q'.abs scalar *
        (coefficientL1 states coefficient * coefficientL1 states basis) := by
    refine Q'.le_trans' _
      (Q'.abs scalar * Q'.abs rightCross) _
      (Q'.le_of_eqv (q_abs_mul_eqv scalar rightCross)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hright
      (Q'.abs_nonneg scalar)
  have hsecond : Q'.abs secondTerm ≤
      Q'.abs scalar *
        (coefficientL1 states basis * coefficientL1 states coefficient) := by
    refine Q'.le_trans' _
      (Q'.abs scalar * Q'.abs leftCross) _
      (Q'.le_of_eqv (q_abs_mul_eqv scalar leftCross)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hleft
      (Q'.abs_nonneg scalar)
  have hthird : Q'.abs thirdTerm ≤
      (Q'.abs scalar * Q'.abs scalar) *
        (coefficientL1 states basis * coefficientL1 states basis) := by
    refine Q'.le_trans' _
      (Q'.abs (scalar * scalar) * Q'.abs basisForm) _
      (Q'.le_of_eqv (q_abs_mul_eqv (scalar * scalar) basisForm)) ?_
    refine Q'.le_trans' _
      ((Q'.abs scalar * Q'.abs scalar) * Q'.abs basisForm) _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _ _
          (q_abs_mul_eqv scalar scalar))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hbasis
      (Q'.mul_nonneg _ _ (Q'.abs_nonneg scalar) (Q'.abs_nonneg scalar))
  have htriangleFirst := Q'.abs_add_le' firstTerm (secondTerm + thirdTerm)
  have htriangleRest := Q'.abs_add_le' secondTerm thirdTerm
  refine Q'.le_trans' _ (Q'.abs remainder) _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) ?_
  refine Q'.le_trans' _
    (Q'.abs firstTerm + Q'.abs (secondTerm + thirdTerm)) _
    htriangleFirst ?_
  exact Q'.add_le_add hfirst
    (Q'.le_trans' _ _ _ htriangleRest
      (Q'.add_le_add hsecond hthird))

/-! ## 2. Finite diagonal forms on the same quadratic interface -/

def finiteDiagonalJoint {State : Type} [DecidableEq State]
    (weight : State → Q') (left right : State) : Q' :=
  if left = right then weight left else 0

theorem finiteJointQuadratic_diagonalJoint_eqv
    {State : Type} [DecidableEq State]
    (states : List State) (hnodup : states.Nodup)
    (weight : State → Q') (coefficient : State → Q') :
    finiteJointQuadratic states coefficient (finiteDiagonalJoint weight) ≈
      listQSum
        (fun state =>
          (coefficient state * coefficient state) * weight state)
        states := by
  unfold finiteJointQuadratic
  apply listQSum_congr_on
  intro left hleft
  refine Q'.eqv_trans _
    (listQSum
      (fun right =>
        if right = left then
          (coefficient left * coefficient right) * weight left
        else 0)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro right _hright
    by_cases heq : right = left
    · subst right
      unfold finiteDiagonalJoint
      simp only [if_pos]
      exact Q'.eqv_refl _
    · have hne : left ≠ right := by
        intro hreverse
        exact heq hreverse.symm
      unfold finiteDiagonalJoint
      simp only [if_neg hne, if_neg heq]
      exact Q'.mul_zero_eqv
        (coefficient left * coefficient right)
  · exact listQSum_ite_single_local left
      (fun right =>
        (coefficient left * coefficient right) * weight left)
      states hnodup hleft

/-! ## 3. Physical normalized entry caps on the pulled carrier -/

theorem cutoffTwoPulledKernelAt_abs_le_one
    {later row column : Nat} (hlater : 2 ≤ later)
    (hrow : row ∈ cutoffTwoPulledStates)
    (hcolumn : column ∈ cutoffTwoPulledStates) :
    Q'.abs (cutoffTwoPulledKernelAt later row column) ≤ 1 := by
  have hrowLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hrow
  have hcolumnLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hcolumn
  let source := centralPhysicalFiniteStateAt
    cutoffTwoHalfCoupling (by decide) 2 0 row
  let target := centralPhysicalFiniteStateAt
    cutoffTwoHalfCoupling (by decide) 2 0 column
  have hsourceBase : source ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling (by decide) 2 0 :=
    centralPhysicalFiniteStateAt_mem_positive
      cutoffTwoHalfCoupling (by decide) 2 0 hrowLt
  have htargetBase : target ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling (by decide) 2 0 :=
    centralPhysicalFiniteStateAt_mem_positive
      cutoffTwoHalfCoupling (by decide) 2 0 hcolumnLt
  have hsourceLater : source ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling (by decide) later 0 :=
    mem_centralPositiveHalfStates_of_le (by decide) hlater hsourceBase
  have htargetLater : target ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling (by decide) later 0 :=
    mem_centralPositiveHalfStates_of_le (by decide) hlater htargetBase
  have htargetHalf : target ∈ centralHalfStates later 0 :=
    (mem_centralPositiveHalfStates_iff.mp htargetLater).1
  have hentry0 : (0 : Q') ≤
      centralNormalizedPhysicalReflectedKernel
        cutoffTwoHalfCoupling (by decide) later 0 source target :=
    centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) later 0 source target
  have hentryRow :
      centralNormalizedPhysicalReflectedKernel
          cutoffTwoHalfCoupling (by decide) later 0 source target ≤
        centralPhysicalRowMarginal
          cutoffTwoHalfCoupling (by decide) later 0 source := by
    unfold centralPhysicalRowMarginal
    exact listQSum_member_le_nonnegative_local
      (centralNormalizedPhysicalReflectedKernel
        cutoffTwoHalfCoupling (by decide) later 0 source)
      (fun item =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          (by decide) later 0 source item)
      (centralHalfStates later 0) htargetHalf
  have hrowOne := centralPhysicalRowMarginal_le_one_on_carrier hsourceLater
  unfold cutoffTwoPulledKernelAt
  rw [centralPhysicalFinitePulledKernel_eq_normalizedKernel
    hlater hrowLt hcolumnLt]
  rw [ExpNeg.abs_of_nonneg hentry0]
  exact Q'.le_trans' _ _ _ hentryRow hrowOne

theorem cutoffTwoPulledDiagonalJointAt_abs_le_one
    {later left right : Nat} (hlater : 2 ≤ later)
    (hleft : left ∈ cutoffTwoPulledStates)
    (_hright : right ∈ cutoffTwoPulledStates) :
    Q'.abs
        (finiteDiagonalJoint
          (cutoffTwoPulledWeightAt later) left right) ≤ 1 := by
  by_cases heq : left = right
  · subst right
    unfold finiteDiagonalJoint
    simp only [if_pos]
    have hweight0 : (0 : Q') ≤ cutoffTwoPulledWeightAt later left := by
      unfold cutoffTwoPulledWeightAt
      exact centralPhysicalFinitePulledWeight_nonnegative
        cutoffTwoHalfCoupling (by decide) 2 later 0 left
    rw [ExpNeg.abs_of_nonneg hweight0]
    exact centralPhysicalFinitePulledWeight_le_one hlater hleft
  · unfold finiteDiagonalJoint
    simp only [if_neg heq]
    exact (by decide : Q'.abs (0 : Q') ≤ 1)

/-! ## 4. The moving recentering under one fixed later law -/

def cutoffTwoPulledRootL1 : Q' :=
  coefficientL1 cutoffTwoPulledStates finiteRootIndicator

def cutoffTwoPulledMovingCenteredL1At
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  coefficientL1 cutoffTwoPulledStates
    (cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient)

def cutoffTwoPulledRecenteringSize
    (first later : Nat) (coefficient : Nat → Q') : Q' :=
  Q'.abs
    (cutoffTwoPulledHeadCorrectionAt later coefficient +
      (-cutoffTwoPulledHeadCorrectionAt first coefficient))

/-- The first moving-centered coefficient is the later one plus exactly the
head-correction difference at the root. -/
theorem cutoffTwoPulledMovingCenteredCoefficient_eqv_later_add_rootCorrection
    (first later index : Nat) (coefficient : Nat → Q') :
    cutoffTwoPulledMovingCenteredCoefficientAt first coefficient index ≈
      cutoffTwoPulledMovingCenteredCoefficientAt later coefficient index +
        (cutoffTwoPulledHeadCorrectionAt later coefficient +
          (-cutoffTwoPulledHeadCorrectionAt first coefficient)) *
            finiteRootIndicator index := by
  let firstValue :=
    cutoffTwoPulledMovingCenteredCoefficientAt first coefficient index
  let laterValue :=
    cutoffTwoPulledMovingCenteredCoefficientAt later coefficient index
  let delta := cutoffTwoPulledHeadCorrectionAt later coefficient +
    (-cutoffTwoPulledHeadCorrectionAt first coefficient)
  have hmotion :=
    cutoffTwoPulledMovingCenteredCoefficient_sub_eqv_rootCorrection
      first later index coefficient
  exact Q'.eqv_trans _ (laterValue + (firstValue + (-laterValue))) _
    (Q'.add_sub_cancel_eqv firstValue laterValue)
    (Q'.add_eqv_congr_left laterValue _ _ hmotion)

/-- Explicit same-law matrix error caused only by changing the moving root
centering.  The law on both sides is the later pulled normalized kernel. -/
theorem cutoffTwoPulledMovingCenteredSameLaw_matrix_error
    {first later : Nat} (hlater : 2 ≤ later)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
          (-cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
      cutoffTwoPulledRecenteringSize first later coefficient *
          (cutoffTwoPulledMovingCenteredL1At later coefficient *
            cutoffTwoPulledRootL1) +
        (cutoffTwoPulledRecenteringSize first later coefficient *
            (cutoffTwoPulledRootL1 *
              cutoffTwoPulledMovingCenteredL1At later coefficient) +
          (cutoffTwoPulledRecenteringSize first later coefficient *
              cutoffTwoPulledRecenteringSize first later coefficient) *
            (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)) := by
  let laterCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let delta := cutoffTwoPulledHeadCorrectionAt later coefficient +
    (-cutoffTwoPulledHeadCorrectionAt first coefficient)
  let shifted := fun index =>
    laterCoefficient index + delta * finiteRootIndicator index
  have hcoefficient : ∀ index, index ∈ cutoffTwoPulledStates →
      cutoffTwoPulledMovingCenteredCoefficientAt first coefficient index ≈
        shifted index := by
    intro index _hindex
    exact
      cutoffTwoPulledMovingCenteredCoefficient_eqv_later_add_rootCorrection
        first later index coefficient
  have hmatrix :
      cutoffTwoPulledMatrixAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) ≈
        cutoffTwoPulledMatrixAt later shifted := by
    unfold cutoffTwoPulledMatrixAt
    rw [finiteJointQuadratic_eq_bilinear,
      finiteJointQuadratic_eq_bilinear]
    exact finiteJointBilinear_coefficient_eqv_on
      cutoffTwoPulledStates
      (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient)
      shifted
      (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient)
      shifted
      (cutoffTwoPulledKernelAt later)
      hcoefficient hcoefficient
  have hgeneric := finiteJointQuadratic_add_scaled_abs_sub_le
    cutoffTwoPulledStates laterCoefficient finiteRootIndicator delta
    (cutoffTwoPulledKernelAt later)
    (fun left right hleft hright =>
      cutoffTwoPulledKernelAt_abs_le_one hlater hleft hright)
  have habsRecode :
      Q'.abs
          (cutoffTwoPulledMatrixAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
            (-cutoffTwoPulledMatrixAt later laterCoefficient)) ≈
        Q'.abs
          (cutoffTwoPulledMatrixAt later shifted +
            (-cutoffTwoPulledMatrixAt later laterCoefficient)) := by
    exact Q'.abs_eqv_congr
      (Q'.add_eqv_congr_right _ _ _ hmatrix)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv habsRecode) hgeneric

/-- Explicit same-law diagonal error caused only by changing the moving root
centering.  Both sides use the later pulled weight. -/
theorem cutoffTwoPulledMovingCenteredSameLaw_diagonal_error
    {first later : Nat} (hlater : 2 ≤ later)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
          (-cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
      cutoffTwoPulledRecenteringSize first later coefficient *
          (cutoffTwoPulledMovingCenteredL1At later coefficient *
            cutoffTwoPulledRootL1) +
        (cutoffTwoPulledRecenteringSize first later coefficient *
            (cutoffTwoPulledRootL1 *
              cutoffTwoPulledMovingCenteredL1At later coefficient) +
          (cutoffTwoPulledRecenteringSize first later coefficient *
              cutoffTwoPulledRecenteringSize first later coefficient) *
            (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)) := by
  let firstCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt first coefficient
  let laterCoefficient :=
    cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let delta := cutoffTwoPulledHeadCorrectionAt later coefficient +
    (-cutoffTwoPulledHeadCorrectionAt first coefficient)
  let shifted := fun index =>
    laterCoefficient index + delta * finiteRootIndicator index
  let diagonalLaw :=
    finiteDiagonalJoint (cutoffTwoPulledWeightAt later)
  have hnodup : cutoffTwoPulledStates.Nodup := by
    exact centralPhysicalFiniteVacuumSectorIndices_nodup
      cutoffTwoHalfCoupling (by decide) 2 0
  have hcoefficient : ∀ index, index ∈ cutoffTwoPulledStates →
      firstCoefficient index ≈ shifted index := by
    intro index _hindex
    exact
      cutoffTwoPulledMovingCenteredCoefficient_eqv_later_add_rootCorrection
        first later index coefficient
  have hquadratic :
      finiteJointQuadratic cutoffTwoPulledStates firstCoefficient diagonalLaw ≈
        finiteJointQuadratic cutoffTwoPulledStates shifted diagonalLaw := by
    change finiteJointBilinear cutoffTwoPulledStates
        firstCoefficient firstCoefficient diagonalLaw ≈
      finiteJointBilinear cutoffTwoPulledStates shifted shifted diagonalLaw
    exact finiteJointBilinear_coefficient_eqv_on
      cutoffTwoPulledStates firstCoefficient shifted
      firstCoefficient shifted diagonalLaw hcoefficient hcoefficient
  have hfirstDiagonal :
      finiteJointQuadratic cutoffTwoPulledStates firstCoefficient diagonalLaw ≈
        cutoffTwoPulledDiagonalAt later firstCoefficient := by
    exact finiteJointQuadratic_diagonalJoint_eqv
      cutoffTwoPulledStates hnodup
      (cutoffTwoPulledWeightAt later) firstCoefficient
  have hlaterDiagonal :
      finiteJointQuadratic cutoffTwoPulledStates laterCoefficient diagonalLaw ≈
        cutoffTwoPulledDiagonalAt later laterCoefficient := by
    exact finiteJointQuadratic_diagonalJoint_eqv
      cutoffTwoPulledStates hnodup
      (cutoffTwoPulledWeightAt later) laterCoefficient
  have hfirstRecode :
      cutoffTwoPulledDiagonalAt later firstCoefficient ≈
        finiteJointQuadratic cutoffTwoPulledStates shifted diagonalLaw :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hfirstDiagonal) hquadratic
  have hsumRecode :
      cutoffTwoPulledDiagonalAt later firstCoefficient +
          (-cutoffTwoPulledDiagonalAt later laterCoefficient) ≈
        finiteJointQuadratic cutoffTwoPulledStates shifted diagonalLaw +
          (-finiteJointQuadratic
            cutoffTwoPulledStates laterCoefficient diagonalLaw) := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic cutoffTwoPulledStates shifted diagonalLaw +
        (-cutoffTwoPulledDiagonalAt later laterCoefficient)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ hfirstRecode
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hlaterDiagonal))
  have hgeneric := finiteJointQuadratic_add_scaled_abs_sub_le
    cutoffTwoPulledStates laterCoefficient finiteRootIndicator delta
    diagonalLaw
    (fun left right hleft hright =>
      cutoffTwoPulledDiagonalJointAt_abs_le_one
        hlater hleft hright)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsumRecode)) hgeneric

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.finiteJointBilinear_abs_le_productL1_of_entry_abs_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.finiteJointQuadratic_add_scaled_abs_sub_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.cutoffTwoPulledKernelAt_abs_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.cutoffTwoPulledMovingCenteredSameLaw_matrix_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.cutoffTwoPulledDiagonalJointAt_abs_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.cutoffTwoPulledMovingCenteredSameLaw_diagonal_error
