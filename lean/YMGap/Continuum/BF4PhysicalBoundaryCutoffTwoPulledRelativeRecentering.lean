/-
# Relative tail recentering on the cutoff-two physical carrier

The moving-centering correction is cutoff-Cauchy, but this controls two
sufficiently late cutoffs rather than the total change from cutoff two.  This
module makes the useful tail statement precise.

For a coefficient with one non-root coordinate of positive absolute value,
that coordinate is unchanged by root centering and gives a fixed lower bound
for every later centered `l1` norm.  The head-correction Cauchy modulus can
therefore make the root shift an arbitrarily small multiple of that later
norm.  The same-law form estimates then become relative to the later physical
diagonal after the verified positive-floor coercivity.

This is a tail gap-openness ingredient.  It does not bound the finite change
from the cutoff-two gap anchor to the first cutoff in the tail.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
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

private theorem mul_four_mid_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a * ((c * b) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right _ _ d
        (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

private theorem mul_four_last_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * d) * (b * c) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a * (d * (b * c))) _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_comm_eqv (b * c) d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a d (b * c))

private theorem mul_square_product_reorder_local (a b c : Q') :
    ((a * b) * (a * b)) * (c * c) ≈
      ((a * a) * (c * c)) * (b * b) := by
  refine Q'.eqv_trans _ (((a * a) * (b * b)) * (c * c)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ (c * c)
      (mul_four_mid_local a b a b)
  refine Q'.eqv_trans _ ((a * a) * ((b * b) * (c * c))) _
    (Q'.mul_assoc_eqv (a * a) (b * b) (c * c)) ?_
  refine Q'.eqv_trans _ ((a * a) * ((c * c) * (b * b))) _
    (Q'.mul_eqv_congr_left (a * a) _ _
      (Q'.mul_comm_eqv (b * b) (c * c))) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (a * a) (c * c) (b * b))

/-! ## 1. A non-root coordinate survives every moving centering -/

def CutoffTwoRootSupportedCoefficient
    (coefficient : Nat → Q') : Prop :=
  ∀ index, index ∈ cutoffTwoPulledStates → index ≠ 0 →
    coefficient index ≈ 0

private theorem coefficient_on_list_root_zero_or_positive
    (coefficient : Nat → Q') :
    ∀ states : List Nat,
      (∀ index, index ∈ states → index ≠ 0 → coefficient index ≈ 0) ∨
      ∃ index,
        index ∈ states ∧ index ≠ 0 ∧
          (0 : Q') < Q'.abs (coefficient index)
  | [] => by
      left
      intro index hmem _hne
      exact False.elim (List.not_mem_nil hmem)
  | head :: tail => by
      by_cases hroot : head = 0
      · rcases coefficient_on_list_root_zero_or_positive coefficient tail with
          htail | ⟨index, hmem, hne, hpos⟩
        · left
          intro index hmem hne
          rcases List.mem_cons.mp hmem with hhead | htailMem
          · subst index
            exact False.elim (hne hroot)
          · exact htail index htailMem hne
        · right
          exact ⟨index, List.mem_cons_of_mem head hmem, hne, hpos⟩
      · by_cases hzero : coefficient head ≈ 0
        · rcases coefficient_on_list_root_zero_or_positive coefficient tail with
            htail | ⟨index, hmem, hne, hpos⟩
          · left
            intro index hmem hne
            rcases List.mem_cons.mp hmem with hhead | htailMem
            · subst index
              exact hzero
            · exact htail index htailMem hne
          · right
            exact ⟨index, List.mem_cons_of_mem head hmem, hne, hpos⟩
        · right
          exact ⟨head, List.mem_cons_self, hroot,
            abs_pos_of_not_eqv_zero_local hzero⟩

/-- Concrete coefficientwise witness that the raw finite vector has a
non-root coordinate of positive magnitude. -/
structure CutoffTwoNonRootCoefficientWitness
    (coefficient : Nat → Q') : Type where
  index : Nat
  index_mem : index ∈ cutoffTwoPulledStates
  index_ne_root : index ≠ 0
  magnitude_pos : (0 : Q') < Q'.abs (coefficient index)

theorem cutoffTwoRootSupported_or_nonRootWitness
    (coefficient : Nat → Q') :
    CutoffTwoRootSupportedCoefficient coefficient ∨
      Nonempty (CutoffTwoNonRootCoefficientWitness coefficient) := by
  rcases coefficient_on_list_root_zero_or_positive
      coefficient cutoffTwoPulledStates with
    hroot | ⟨index, hmem, hne, hpos⟩
  · exact Or.inl hroot
  · exact Or.inr ⟨⟨index, hmem, hne, hpos⟩⟩

theorem cutoffTwoPulledMovingCenteredCoefficient_eqv_raw_of_nonroot
    (cutoff index : Nat) (coefficient : Nat → Q')
    (hindex : index ≠ 0) :
    cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient index ≈
      coefficient index := by
  unfold cutoffTwoPulledMovingCenteredCoefficientAt
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    finiteListRootCenteredCoefficient
  simp only [if_neg hindex]
  exact Q'.eqv_of_eq (Q'.add_zero' _)

theorem cutoffTwoRootSupported_movingCentered_eqv_zero_on
    {coefficient : Nat → Q'}
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (cutoff : Nat) {index : Nat}
    (hindex : index ∈ cutoffTwoPulledStates) :
    cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient index ≈
      0 := by
  by_cases hroot : index = 0
  · subst index
    let centered :=
      cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient
    let weight := cutoffTwoPulledWeightAt cutoff
    have hmean :
        listQSum
            (fun item => centered item * weight item)
            cutoffTwoPulledStates ≈ 0 := by
      have hmeanRaw :=
        centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
          cutoffTwoHalfCoupling (by decide) 2 cutoff 0 coefficient
      unfold centralPhysicalFinitePulledVacuumSectorWeightedMean at hmeanRaw
      simpa only [centered, weight, cutoffTwoPulledStates,
        cutoffTwoPulledMovingCenteredCoefficientAt,
        cutoffTwoPulledWeightAt] using hmeanRaw
    have hsum :
        listQSum
            (fun item => centered item * weight item)
            cutoffTwoPulledStates ≈
          centered 0 * weight 0 := by
      refine Q'.eqv_trans _
        (listQSum
          (fun item =>
            if item = 0 then centered item * weight item else 0)
          cutoffTwoPulledStates) _ ?_ ?_
      · apply listQSum_congr_on
        intro item hitem
        by_cases hitemRoot : item = 0
        · simp only [if_pos hitemRoot]
          exact Q'.eqv_refl _
        · simp only [if_neg hitemRoot]
          have hraw :=
            cutoffTwoPulledMovingCenteredCoefficient_eqv_raw_of_nonroot
              cutoff item coefficient hitemRoot
          have hzero : centered item ≈ 0 :=
            Q'.eqv_trans _ _ _ hraw
              (hsupported item hitem hitemRoot)
          exact Q'.eqv_trans _ (0 * weight item) _
            (Q'.mul_eqv_congr_right _ _ _ hzero)
            (Q'.zero_mul_eqv _)
      · exact listQSum_ite_single_local 0
          (fun item => centered item * weight item)
          cutoffTwoPulledStates
          (centralPhysicalFiniteVacuumSectorIndices_nodup
            cutoffTwoHalfCoupling (by decide) 2 0)
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            cutoffTwoHalfCoupling (by decide) 2 0)
    have hrootTerm : centered 0 * weight 0 ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hsum) hmean
    have hweight : (0 : Q') < weight 0 :=
      centralPhysicalFinitePulledWeight_zero_pos
        cutoffTwoHalfCoupling (by decide) 2 cutoff 0
    have hcommuted : weight 0 * centered 0 ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (weight 0) (centered 0)) hrootTerm
    change centered 0 ≈ 0
    exact Q'.mul_eqv_zero_of_pos hweight hcommuted
  · exact Q'.eqv_trans _ _ _
      (cutoffTwoPulledMovingCenteredCoefficient_eqv_raw_of_nonroot
        cutoff index coefficient hroot)
      (hsupported index hindex hroot)

private theorem finiteJointQuadratic_eqv_zero_of_coefficient_zero_on
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q')
    (hzero : ∀ state, state ∈ states → coefficient state ≈ 0) :
    finiteJointQuadratic states coefficient joint ≈ 0 := by
  unfold finiteJointQuadratic
  refine Q'.eqv_trans _
    (listQSum (fun _state => (0 : Q')) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left hleft
    refine Q'.eqv_trans _
      (listQSum (fun _state => (0 : Q')) states) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _hright
      have hpair : coefficient left * coefficient right ≈ 0 :=
        Q'.eqv_trans _ (0 * coefficient right) _
          (Q'.mul_eqv_congr_right _ _ _ (hzero left hleft))
          (Q'.zero_mul_eqv _)
      exact Q'.eqv_trans _ (0 * joint left right) _
        (Q'.mul_eqv_congr_right _ _ _ hpair)
        (Q'.zero_mul_eqv _)
    · exact listQSum_zero states
  · exact listQSum_zero states

theorem cutoffTwoRootSupported_movingMatrix_eqv_zero
    {coefficient : Nat → Q'}
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (lawCutoff centeringCutoff : Nat) :
    cutoffTwoPulledMatrixAt lawCutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt
          centeringCutoff coefficient) ≈ 0 := by
  unfold cutoffTwoPulledMatrixAt
  exact finiteJointQuadratic_eqv_zero_of_coefficient_zero_on
    cutoffTwoPulledStates
    (cutoffTwoPulledMovingCenteredCoefficientAt
      centeringCutoff coefficient)
    (cutoffTwoPulledKernelAt lawCutoff)
    (fun index hindex =>
      cutoffTwoRootSupported_movingCentered_eqv_zero_on
        hsupported centeringCutoff hindex)

theorem cutoffTwoRootSupported_movingDiagonal_eqv_zero
    {coefficient : Nat → Q'}
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (lawCutoff centeringCutoff : Nat) :
    cutoffTwoPulledDiagonalAt lawCutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt
          centeringCutoff coefficient) ≈ 0 := by
  unfold cutoffTwoPulledDiagonalAt
  refine Q'.eqv_trans _
    (listQSum (fun _index => (0 : Q')) cutoffTwoPulledStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro index hindex
    let value :=
      cutoffTwoPulledMovingCenteredCoefficientAt
        centeringCutoff coefficient index
    have hvalue : value ≈ 0 :=
      cutoffTwoRootSupported_movingCentered_eqv_zero_on
        hsupported centeringCutoff hindex
    have hsquare : value * value ≈ 0 :=
      Q'.eqv_trans _ (0 * value) _
        (Q'.mul_eqv_congr_right _ _ _ hvalue)
        (Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _
      (0 * cutoffTwoPulledWeightAt lawCutoff index) _
      (Q'.mul_eqv_congr_right _ _ _ hsquare)
      (Q'.zero_mul_eqv _)
  · exact listQSum_zero cutoffTwoPulledStates

theorem CutoffTwoNonRootCoefficientWitness.magnitude_le_moving_l1
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (cutoff : Nat) :
    Q'.abs (coefficient witness.index) ≤
      cutoffTwoPulledMovingCenteredL1At cutoff coefficient := by
  have hraw :=
    cutoffTwoPulledMovingCenteredCoefficient_eqv_raw_of_nonroot
      cutoff witness.index coefficient witness.index_ne_root
  have habs :
      Q'.abs (coefficient witness.index) ≤
        Q'.abs
          (cutoffTwoPulledMovingCenteredCoefficientAt
            cutoff coefficient witness.index) :=
    Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hraw))
  exact Q'.le_trans' _ _ _ habs
    (listQSum_member_le_nonnegative_local
      (fun index => Q'.abs
        (cutoffTwoPulledMovingCenteredCoefficientAt
          cutoff coefficient index))
      (fun index => Q'.abs_nonneg _)
      cutoffTwoPulledStates witness.index_mem)

/-- For every positive requested fraction, sufficiently late pairs have
root-recentering size at most that fraction of the later centered `l1` norm. -/
theorem CutoffTwoNonRootCoefficientWitness.recenteringSize_le_scaled_l1_cofinally
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (alpha : Q') (halpha : (0 : Q') < alpha) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        cutoffTwoPulledRecenteringSize first later coefficient ≤
          alpha * cutoffTwoPulledMovingCenteredL1At later coefficient := by
  let magnitude := Q'.abs (coefficient witness.index)
  have hmagnitude : (0 : Q') < magnitude := witness.magnitude_pos
  have hepsilon : (0 : Q') < alpha * magnitude :=
    Q'.mul_pos halpha hmagnitude
  obtain ⟨cauchyCutoff, hcauchy⟩ :=
    cutoffTwoPulledMovingCenteredCoefficient_l1_cauchy
      coefficient (alpha * magnitude) hepsilon
  refine ⟨max cutoffTwoPulledRowFloorAnchor cauchyCutoff,
    Nat.le_max_left _ _, ?_⟩
  intro first later hfirst hlater
  have hcauchyFirst : cauchyCutoff ≤ first :=
    Nat.le_trans (Nat.le_max_right _ _) hfirst
  have hcauchyLater : cauchyCutoff ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  have hdistance := hcauchy first later hcauchyFirst hcauchyLater
  have hsize :
      cutoffTwoPulledRecenteringSize first later coefficient ≤
        alpha * magnitude := by
    exact Q'.le_trans' _
      (coefficientL1 cutoffTwoPulledStates
        (fun index =>
          cutoffTwoPulledMovingCenteredCoefficientAt first coefficient index +
            (-cutoffTwoPulledMovingCenteredCoefficientAt
              later coefficient index))) _
      (Q'.ge_of_eqv
        (cutoffTwoPulledMovingCenteredCoefficient_sub_l1_eqv_headCorrection
          first later coefficient))
      hdistance
  have hmagnitudeL1 := witness.magnitude_le_moving_l1 later
  exact Q'.le_trans' _ _ _ hsize
    (Q'.mul_le_mul_of_nonneg_left _ _ alpha hmagnitudeL1
      (Q'.le_of_lt halpha))

/-! ## 2. Turning a scaled root shift into a relative form error -/

def cutoffTwoPulledRecenteringAmplification (alpha : Q') : Q' :=
  (alpha * cutoffTwoPulledRootL1) +
    ((alpha * cutoffTwoPulledRootL1) +
      (alpha * alpha) *
        (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1))

theorem cutoffTwoPulledRecenteringAmplification_nonnegative
    {alpha : Q'} (halpha : (0 : Q') ≤ alpha) :
    (0 : Q') ≤ cutoffTwoPulledRecenteringAmplification alpha := by
  unfold cutoffTwoPulledRecenteringAmplification
  have hroot : (0 : Q') ≤ cutoffTwoPulledRootL1 :=
    coefficientL1_nonnegative_local _ _
  have hlinear : (0 : Q') ≤ alpha * cutoffTwoPulledRootL1 :=
    Q'.mul_nonneg _ _ halpha hroot
  have hquadratic : (0 : Q') ≤
      (alpha * alpha) *
        (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ halpha halpha)
      (Q'.mul_nonneg _ _ hroot hroot)
  exact Q'.zero_le_add _ _ hlinear
    (Q'.zero_le_add _ _ hlinear hquadratic)

private theorem cutoffTwoPulledRecenteringAmplification_linear_bound
    {alpha : Q'} (halpha0 : (0 : Q') ≤ alpha)
    (halpha1 : alpha ≤ 1) :
    cutoffTwoPulledRecenteringAmplification alpha ≤
      alpha *
        (cutoffTwoPulledRootL1 +
          (cutoffTwoPulledRootL1 +
            cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)) := by
  have hroot0 : (0 : Q') ≤ cutoffTwoPulledRootL1 :=
    coefficientL1_nonnegative_local _ _
  have hrootSquare0 : (0 : Q') ≤
      cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1 :=
    Q'.mul_nonneg _ _ hroot0 hroot0
  have halphaSquare : alpha * alpha ≤ alpha := by
    refine Q'.le_trans' _ ((1 : Q') * alpha) _
      (Q'.mul_le_mul_of_nonneg_right _ _ alpha halpha1 halpha0) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv alpha)
  have hquadratic :
      (alpha * alpha) *
          (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1) ≤
        alpha *
          (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ halphaSquare hrootSquare0
  have hsum := Q'.add_le_add
    (Q'.le_refl' (alpha * cutoffTwoPulledRootL1))
    (Q'.add_le_add
      (Q'.le_refl' (alpha * cutoffTwoPulledRootL1)) hquadratic)
  refine Q'.le_trans' _
    (alpha * cutoffTwoPulledRootL1 +
      (alpha * cutoffTwoPulledRootL1 +
        alpha *
          (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1))) _
    hsum ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.eqv_trans _
        (alpha * cutoffTwoPulledRootL1 +
          alpha *
            (cutoffTwoPulledRootL1 +
              cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)) _
        (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_add_eqv _ _ _))))

/-- Positivity of the physical floor lets every requested positive relative
error choose a smaller positive root-shift fraction whose explicit
amplification budget closes. -/
theorem exists_positive_recentering_fraction_for_relative_error
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    ∃ alpha : Q',
      (0 : Q') < alpha ∧
      Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha ≤
        relativeError * cutoffTwoPulledUniformPositiveRowFloor := by
  let coefficientScale :=
    cutoffTwoPulledRootL1 +
      (cutoffTwoPulledRootL1 +
        cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)
  let baseScale :=
    Q'.ofNat cutoffTwoPulledStates.length * coefficientScale
  let target := relativeError * cutoffTwoPulledUniformPositiveRowFloor
  have hroot0 : (0 : Q') ≤ cutoffTwoPulledRootL1 :=
    coefficientL1_nonnegative_local _ _
  have hcoefficientScale0 : (0 : Q') ≤ coefficientScale := by
    dsimp only [coefficientScale]
    exact Q'.zero_le_add _ _ hroot0
      (Q'.zero_le_add _ _ hroot0
        (Q'.mul_nonneg _ _ hroot0 hroot0))
  have hcount0 : (0 : Q') ≤ Q'.ofNat cutoffTwoPulledStates.length :=
    ExpNeg.ofNat_nonneg' _
  have hbaseScale0 : (0 : Q') ≤ baseScale :=
    Q'.mul_nonneg _ _ hcount0 hcoefficientScale0
  have htarget : (0 : Q') < target :=
    Q'.mul_pos hrelative cutoffTwoPulledUniformPositiveRowFloor_pos
  have htarget0 : (0 : Q') ≤ target := Q'.le_of_lt htarget
  let scale := (baseScale + target) + 1
  have hbaseTarget0 : (0 : Q') ≤ baseScale + target :=
    Q'.zero_le_add _ _ hbaseScale0 htarget0
  have hscale : (0 : Q') < scale := positive_scale hbaseTarget0
  let alpha := Q'.divPos target scale hscale
  have halpha : (0 : Q') < alpha :=
    Q'.divPos_pos target scale hscale htarget
  have htargetScale : target ≤ scale := by
    have hbaseTargetLe : target ≤ baseScale + target := by
      refine Q'.le_trans' _ (target + baseScale) _
        (Q'.add_le_self_of_nonneg target baseScale hbaseScale0) ?_
      exact Q'.le_of_eqv (Q'.add_comm_eqv target baseScale)
    exact Q'.le_trans' _ _ _ hbaseTargetLe
      (Q'.add_le_self_of_nonneg (baseScale + target) 1
        (by decide : (0 : Q') ≤ 1))
  have halphaOne : alpha ≤ 1 := by
    apply Q'.divPos_le_of_le_mul target scale hscale
    exact Q'.le_trans' _ scale _ htargetScale
      (Q'.ge_of_eqv (Q'.one_mul_eqv scale))
  have hbaseScaleLe : baseScale ≤ scale := by
    have hbaseTargetLe : baseScale ≤ baseScale + target :=
      Q'.add_le_self_of_nonneg baseScale target htarget0
    exact Q'.le_trans' _ _ _ hbaseTargetLe
      (Q'.add_le_self_of_nonneg (baseScale + target) 1
        (by decide : (0 : Q') ≤ 1))
  have hbaseAlpha : baseScale * alpha ≤ target := by
    have hmono : baseScale * alpha ≤ scale * alpha :=
      Q'.mul_le_mul_of_nonneg_right _ _ alpha hbaseScaleLe
        (Q'.le_of_lt halpha)
    exact Q'.le_trans' _ _ _ hmono
      (Q'.le_of_eqv
        (Q'.eqv_trans _ (alpha * scale) _
          (Q'.mul_comm_eqv scale alpha)
          (Q'.divPos_mul_eqv target scale hscale)))
  refine ⟨alpha, halpha, ?_⟩
  have hamp := cutoffTwoPulledRecenteringAmplification_linear_bound
    (Q'.le_of_lt halpha) halphaOne
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hamp hcount0
  refine Q'.le_trans' _
    (Q'.ofNat cutoffTwoPulledStates.length *
      (alpha * coefficientScale)) _ hscaled ?_
  refine Q'.le_trans' _ (baseScale * alpha) _
    (Q'.le_of_eqv (by
      dsimp only [baseScale]
      refine Q'.eqv_trans _
        ((Q'.ofNat cutoffTwoPulledStates.length * alpha) *
          coefficientScale) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat cutoffTwoPulledStates.length)
            alpha coefficientScale)) ?_
      refine Q'.eqv_trans _
        ((alpha * Q'.ofNat cutoffTwoPulledStates.length) *
          coefficientScale) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv
            (Q'.ofNat cutoffTwoPulledStates.length) alpha)) ?_
      refine Q'.eqv_trans _
        (alpha *
          (Q'.ofNat cutoffTwoPulledStates.length * coefficientScale)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_comm_eqv alpha
        (Q'.ofNat cutoffTwoPulledStates.length * coefficientScale)))
    hbaseAlpha

private theorem scalar_recentering_rhs_le_amplification_mul_square
    {delta l1 rootL1 alpha : Q'}
    (halpha : (0 : Q') ≤ alpha)
    (hl10 : (0 : Q') ≤ l1)
    (hroot0 : (0 : Q') ≤ rootL1)
    (hdelta : delta ≤ alpha * l1)
    (hdelta0 : (0 : Q') ≤ delta) :
    delta * (l1 * rootL1) +
        (delta * (rootL1 * l1) +
          (delta * delta) * (rootL1 * rootL1)) ≤
      ((alpha * rootL1) +
          ((alpha * rootL1) +
            (alpha * alpha) * (rootL1 * rootL1))) *
        (l1 * l1) := by
  let linear : Q' := alpha * rootL1
  let quadratic : Q' := (alpha * alpha) * (rootL1 * rootL1)
  have halphaL10 : (0 : Q') ≤ alpha * l1 :=
    Q'.mul_nonneg _ _ halpha hl10
  have hl1root0 : (0 : Q') ≤ l1 * rootL1 :=
    Q'.mul_nonneg _ _ hl10 hroot0
  have hrootl10 : (0 : Q') ≤ rootL1 * l1 :=
    Q'.mul_nonneg _ _ hroot0 hl10
  have hfirst : delta * (l1 * rootL1) ≤ linear * (l1 * l1) := by
    refine Q'.le_trans' _ ((alpha * l1) * (l1 * rootL1)) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hdelta hl1root0) ?_
    change (alpha * l1) * (l1 * rootL1) ≤
      (alpha * rootL1) * (l1 * l1)
    exact Q'.le_of_eqv (mul_four_last_local alpha l1 l1 rootL1)
  have hsecond : delta * (rootL1 * l1) ≤ linear * (l1 * l1) := by
    refine Q'.le_trans' _ ((alpha * l1) * (rootL1 * l1)) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hdelta hrootl10) ?_
    change (alpha * l1) * (rootL1 * l1) ≤
      (alpha * rootL1) * (l1 * l1)
    exact Q'.le_of_eqv (mul_four_mid_local alpha l1 rootL1 l1)
  have hdeltaSquare : delta * delta ≤ (alpha * l1) * (alpha * l1) := by
    refine Q'.le_trans' _ ((alpha * l1) * delta) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_right _ _ delta hdelta hdelta0
    · exact Q'.mul_le_mul_of_nonneg_left _ _ (alpha * l1)
        hdelta halphaL10
  have hrootSquare0 : (0 : Q') ≤ rootL1 * rootL1 :=
    Q'.mul_nonneg _ _ hroot0 hroot0
  have hthird :
      (delta * delta) * (rootL1 * rootL1) ≤
        quadratic * (l1 * l1) := by
    refine Q'.le_trans' _
      (((alpha * l1) * (alpha * l1)) * (rootL1 * rootL1)) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hdeltaSquare hrootSquare0) ?_
    change
      ((alpha * l1) * (alpha * l1)) * (rootL1 * rootL1) ≤
        ((alpha * alpha) * (rootL1 * rootL1)) * (l1 * l1)
    exact Q'.le_of_eqv
      (mul_square_product_reorder_local alpha l1 rootL1)
  have hterms := Q'.add_le_add hfirst (Q'.add_le_add hsecond hthird)
  refine Q'.le_trans' _
    (linear * (l1 * l1) +
      (linear * (l1 * l1) + quadratic * (l1 * l1))) _
    hterms ?_
  dsimp only [linear, quadratic]
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (Q'.eqv_trans _
        ((alpha * rootL1) * (l1 * l1) +
          ((alpha * rootL1) +
              (alpha * alpha) * (rootL1 * rootL1)) * (l1 * l1)) _
        (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_mul_eqv _ _ _))))

private theorem recentering_rhs_le_amplification_mul_l1_square
    {first later : Nat} {alpha : Q'}
    (halpha : (0 : Q') ≤ alpha)
    (coefficient : Nat → Q')
    (hdelta :
      cutoffTwoPulledRecenteringSize first later coefficient ≤
        alpha * cutoffTwoPulledMovingCenteredL1At later coefficient) :
    cutoffTwoPulledRecenteringSize first later coefficient *
          (cutoffTwoPulledMovingCenteredL1At later coefficient *
            cutoffTwoPulledRootL1) +
        (cutoffTwoPulledRecenteringSize first later coefficient *
            (cutoffTwoPulledRootL1 *
              cutoffTwoPulledMovingCenteredL1At later coefficient) +
          (cutoffTwoPulledRecenteringSize first later coefficient *
              cutoffTwoPulledRecenteringSize first later coefficient) *
            (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)) ≤
      cutoffTwoPulledRecenteringAmplification alpha *
        (cutoffTwoPulledMovingCenteredL1At later coefficient *
          cutoffTwoPulledMovingCenteredL1At later coefficient) := by
  unfold cutoffTwoPulledRecenteringAmplification
  exact scalar_recentering_rhs_le_amplification_mul_square
    halpha
    (coefficientL1_nonnegative_local _ _)
    (coefficientL1_nonnegative_local _ _)
    hdelta (Q'.abs_nonneg _)

/-- Any form error bounded by the explicit same-law recentering polynomial
becomes relative after clearing by the physical positive row floor. -/
theorem cutoffTwoPulledRecenteringError_cleared_relative
    {first later : Nat} {alpha formError : Q'}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (halpha : (0 : Q') ≤ alpha)
    (coefficient : Nat → Q')
    (hdelta :
      cutoffTwoPulledRecenteringSize first later coefficient ≤
        alpha * cutoffTwoPulledMovingCenteredL1At later coefficient)
    (hform : Q'.abs formError ≤
      cutoffTwoPulledRecenteringSize first later coefficient *
          (cutoffTwoPulledMovingCenteredL1At later coefficient *
            cutoffTwoPulledRootL1) +
        (cutoffTwoPulledRecenteringSize first later coefficient *
            (cutoffTwoPulledRootL1 *
              cutoffTwoPulledMovingCenteredL1At later coefficient) +
          (cutoffTwoPulledRecenteringSize first later coefficient *
              cutoffTwoPulledRecenteringSize first later coefficient) *
            (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1))) :
    cutoffTwoPulledUniformPositiveRowFloor * Q'.abs formError ≤
      (Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha) *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let l1 := cutoffTwoPulledMovingCenteredL1At later coefficient
  let amplification := cutoffTwoPulledRecenteringAmplification alpha
  let diagonal := cutoffTwoPulledDiagonalAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have hshape := recentering_rhs_le_amplification_mul_l1_square
    halpha coefficient hdelta
  have habs : Q'.abs formError ≤ amplification * (l1 * l1) :=
    Q'.le_trans' _ _ _ hform hshape
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ habs
    (Q'.le_of_lt cutoffTwoPulledUniformPositiveRowFloor_pos)
  have hcoercive :
      cutoffTwoPulledUniformPositiveRowFloor * (l1 * l1) ≤
        Q'.ofNat cutoffTwoPulledStates.length * diagonal :=
    cutoffTwoPulled_coefficientL1_square_control hlater
      (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have hamp0 : (0 : Q') ≤ amplification :=
    cutoffTwoPulledRecenteringAmplification_nonnegative halpha
  have hcoerciveScaled :
      amplification *
          (cutoffTwoPulledUniformPositiveRowFloor * (l1 * l1)) ≤
        amplification *
          (Q'.ofNat cutoffTwoPulledStates.length * diagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ amplification hcoercive hamp0
  refine Q'.le_trans' _
    (cutoffTwoPulledUniformPositiveRowFloor *
      (amplification * (l1 * l1))) _ hscaled ?_
  refine Q'.le_trans' _
    (amplification *
      (cutoffTwoPulledUniformPositiveRowFloor * (l1 * l1))) _
    (Q'.le_of_eqv (by
      refine Q'.eqv_trans _
        ((cutoffTwoPulledUniformPositiveRowFloor * amplification) *
          (l1 * l1)) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            cutoffTwoPulledUniformPositiveRowFloor amplification (l1 * l1))) ?_
      refine Q'.eqv_trans _
        ((amplification * cutoffTwoPulledUniformPositiveRowFloor) *
          (l1 * l1)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv
            cutoffTwoPulledUniformPositiveRowFloor amplification)) ?_
      exact Q'.mul_assoc_eqv
        amplification cutoffTwoPulledUniformPositiveRowFloor (l1 * l1))) ?_
  refine Q'.le_trans' _ _ _ hcoerciveScaled ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      ((amplification * Q'.ofNat cutoffTwoPulledStates.length) * diagonal) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv amplification
          (Q'.ofNat cutoffTwoPulledStates.length) diagonal))
      (Q'.mul_eqv_congr_right _ _ diagonal
        (Q'.mul_comm_eqv amplification
          (Q'.ofNat cutoffTwoPulledStates.length))))

/-- A rational amplification budget removes the positive clearing factor. -/
theorem cutoffTwoPulledRecenteringError_relative
    {first later : Nat} {alpha formError relativeError : Q'}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (halpha : (0 : Q') ≤ alpha)
    (coefficient : Nat → Q')
    (hdelta :
      cutoffTwoPulledRecenteringSize first later coefficient ≤
        alpha * cutoffTwoPulledMovingCenteredL1At later coefficient)
    (hform : Q'.abs formError ≤
      cutoffTwoPulledRecenteringSize first later coefficient *
          (cutoffTwoPulledMovingCenteredL1At later coefficient *
            cutoffTwoPulledRootL1) +
        (cutoffTwoPulledRecenteringSize first later coefficient *
            (cutoffTwoPulledRootL1 *
              cutoffTwoPulledMovingCenteredL1At later coefficient) +
          (cutoffTwoPulledRecenteringSize first later coefficient *
              cutoffTwoPulledRecenteringSize first later coefficient) *
            (cutoffTwoPulledRootL1 * cutoffTwoPulledRootL1)))
    (hbudget :
      Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha ≤
        relativeError * cutoffTwoPulledUniformPositiveRowFloor) :
    Q'.abs formError ≤
      relativeError *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let diagonal := cutoffTwoPulledDiagonalAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have hdiagonal0 : (0 : Q') ≤ diagonal :=
    cutoffTwoPulledDiagonalAt_nonnegative later _
  have hcleared := cutoffTwoPulledRecenteringError_cleared_relative
    hlater halpha coefficient hdelta hform
  have hbudgetScaled :
      (Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha) * diagonal ≤
        (relativeError * cutoffTwoPulledUniformPositiveRowFloor) *
          diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbudget hdiagonal0
  have hreorder :
      (relativeError * cutoffTwoPulledUniformPositiveRowFloor) * diagonal ≈
        cutoffTwoPulledUniformPositiveRowFloor *
          (relativeError * diagonal) := by
    refine Q'.eqv_trans _
      (relativeError *
        (cutoffTwoPulledUniformPositiveRowFloor * diagonal)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (relativeError *
        (diagonal * cutoffTwoPulledUniformPositiveRowFloor)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv
          cutoffTwoPulledUniformPositiveRowFloor diagonal)) ?_
    refine Q'.eqv_trans _
      ((relativeError * diagonal) *
        cutoffTwoPulledUniformPositiveRowFloor) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_comm_eqv _ _
  have hfinal :
      cutoffTwoPulledUniformPositiveRowFloor * Q'.abs formError ≤
        cutoffTwoPulledUniformPositiveRowFloor *
          (relativeError * diagonal) :=
    Q'.le_trans' _ _ _ hcleared
      (Q'.le_trans' _ _ _ hbudgetScaled (Q'.le_of_eqv hreorder))
  exact le_of_mul_le_mul_left_pos
    cutoffTwoPulledUniformPositiveRowFloor_pos hfinal

/-- Relative same-law matrix error for a scaled moving-root shift. -/
theorem cutoffTwoPulledMovingCenteredSameLaw_relative_matrix_error
    {first later : Nat} {alpha relativeError : Q'}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (halpha : (0 : Q') ≤ alpha)
    (coefficient : Nat → Q')
    (hdelta :
      cutoffTwoPulledRecenteringSize first later coefficient ≤
        alpha * cutoffTwoPulledMovingCenteredL1At later coefficient)
    (hbudget :
      Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha ≤
        relativeError * cutoffTwoPulledUniformPositiveRowFloor) :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
          (-cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
      relativeError *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  have htwoAnchor : 2 ≤ cutoffTwoPulledRowFloorAnchor := by
    unfold cutoffTwoPulledRowFloorAnchor
    exact Nat.le_max_left _ _
  have htwoLater : 2 ≤ later := Nat.le_trans htwoAnchor hlater
  exact cutoffTwoPulledRecenteringError_relative
    hlater halpha coefficient hdelta
    (cutoffTwoPulledMovingCenteredSameLaw_matrix_error
      htwoLater coefficient)
    hbudget

/-- Relative same-law diagonal error for the same scaled moving-root shift. -/
theorem cutoffTwoPulledMovingCenteredSameLaw_relative_diagonal_error
    {first later : Nat} {alpha relativeError : Q'}
    (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (halpha : (0 : Q') ≤ alpha)
    (coefficient : Nat → Q')
    (hdelta :
      cutoffTwoPulledRecenteringSize first later coefficient ≤
        alpha * cutoffTwoPulledMovingCenteredL1At later coefficient)
    (hbudget :
      Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha ≤
        relativeError * cutoffTwoPulledUniformPositiveRowFloor) :
    Q'.abs
        (cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt first coefficient) +
          (-cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient))) ≤
      relativeError *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  have htwoAnchor : 2 ≤ cutoffTwoPulledRowFloorAnchor := by
    unfold cutoffTwoPulledRowFloorAnchor
    exact Nat.le_max_left _ _
  have htwoLater : 2 ≤ later := Nat.le_trans htwoAnchor hlater
  exact cutoffTwoPulledRecenteringError_relative
    hlater halpha coefficient hdelta
    (cutoffTwoPulledMovingCenteredSameLaw_diagonal_error
      htwoLater coefficient)
    hbudget

/-- For every coefficient with a positive non-root coordinate, sufficiently
late pairs have both same-law recentering errors bounded by one prescribed
relative error, provided the explicit rational amplification budget closes. -/
theorem CutoffTwoNonRootCoefficientWitness.sameLaw_relative_errors_cofinally
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (alpha : Q') (halpha : (0 : Q') < alpha)
    (relativeError : Q')
    (hbudget :
      Q'.ofNat cutoffTwoPulledStates.length *
          cutoffTwoPulledRecenteringAmplification alpha ≤
        relativeError * cutoffTwoPulledUniformPositiveRowFloor) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  obtain ⟨cutoff, hfloor, hdelta⟩ :=
    witness.recenteringSize_le_scaled_l1_cofinally alpha halpha
  refine ⟨cutoff, hfloor, ?_⟩
  intro first later hfirst hlater
  have hlaterFloor : cutoffTwoPulledRowFloorAnchor ≤ later :=
    Nat.le_trans hfloor hlater
  have hscaled := hdelta first later hfirst hlater
  exact
    ⟨cutoffTwoPulledMovingCenteredSameLaw_relative_matrix_error
        hlaterFloor (Q'.le_of_lt halpha) coefficient hscaled hbudget,
      cutoffTwoPulledMovingCenteredSameLaw_relative_diagonal_error
        hlaterFloor (Q'.le_of_lt halpha) coefficient hscaled hbudget⟩

/-- The explicit amplification budget is always satisfiable: every positive
relative error is attained for all sufficiently late pairs. -/
theorem CutoffTwoNonRootCoefficientWitness.sameLaw_relative_errors_for_every_positive
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  obtain ⟨alpha, halpha, hbudget⟩ :=
    exists_positive_recentering_fraction_for_relative_error
      relativeError hrelative
  exact witness.sameLaw_relative_errors_cofinally
    alpha halpha relativeError hbudget

private theorem abs_add_neg_le_relativeDiagonal_of_eqv_zero
    {left right relativeError diagonal : Q'}
    (hrelative : (0 : Q') ≤ relativeError)
    (hdiagonal : (0 : Q') ≤ diagonal)
    (hleft : left ≈ 0) (hright : right ≈ 0) :
    Q'.abs (left + (-right)) ≤ relativeError * diagonal := by
  have hdifference : left + (-right) ≈ 0 :=
    Q'.eqv_trans _ (0 + (-(0 : Q'))) _
      (Q'.add_eqv_congr' hleft
        (Q'.neg_eqv_congr _ _ hright))
      (by decide)
  have habs : Q'.abs (left + (-right)) ≈ 0 :=
    Q'.eqv_trans _ (Q'.abs (0 : Q')) _
      (Q'.abs_eqv_congr hdifference)
      (by decide)
  exact Q'.le_trans' _ 0 _
    (Q'.le_of_eqv habs)
    (Q'.mul_nonneg _ _ hrelative hdiagonal)

/-- In the complementary finite dichotomy branch, root support is annihilated
exactly by moving root centering, so both relative errors are identically
zero at every pair of cutoffs. -/
theorem cutoffTwoRootSupported_sameLaw_relative_errors_for_every_positive
    {coefficient : Nat → Q'}
    (hsupported : CutoffTwoRootSupportedCoefficient coefficient)
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  refine ⟨cutoffTwoPulledRowFloorAnchor, Nat.le_refl _, ?_⟩
  intro first later _hfirst _hlater
  let diagonal := cutoffTwoPulledDiagonalAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have hdiagonal : (0 : Q') ≤ diagonal :=
    cutoffTwoPulledDiagonalAt_nonnegative later _
  have hrelative0 : (0 : Q') ≤ relativeError := Q'.le_of_lt hrelative
  exact
    ⟨abs_add_neg_le_relativeDiagonal_of_eqv_zero
        hrelative0 hdiagonal
        (cutoffTwoRootSupported_movingMatrix_eqv_zero
          hsupported later first)
        (cutoffTwoRootSupported_movingMatrix_eqv_zero
          hsupported later later),
      abs_add_neg_le_relativeDiagonal_of_eqv_zero
        hrelative0 hdiagonal
        (cutoffTwoRootSupported_movingDiagonal_eqv_zero
          hsupported later first)
        (cutoffTwoRootSupported_movingDiagonal_eqv_zero
          hsupported later later)⟩

/-- Constructively, every finite coefficient is either annihilated as a
root-only mode or has a positive non-root witness.  Hence the relative
same-law recentering tail holds for every coefficient and every positive
requested error. -/
theorem sameLaw_relative_errors_for_every_coefficient
    (coefficient : Nat → Q')
    (relativeError : Q') (hrelative : (0 : Q') < relativeError) :
    ∃ cutoff : Nat,
      cutoffTwoPulledRowFloorAnchor ≤ cutoff ∧
      ∀ first later : Nat,
        cutoff ≤ first → cutoff ≤ later →
        Q'.abs
            (cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) ∧
          Q'.abs
            (cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  first coefficient) +
              (-cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient))) ≤
            relativeError *
              cutoffTwoPulledDiagonalAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient) := by
  rcases cutoffTwoRootSupported_or_nonRootWitness coefficient with
    hsupported | hwitness
  · exact cutoffTwoRootSupported_sameLaw_relative_errors_for_every_positive
      hsupported relativeError hrelative
  · rcases hwitness with ⟨witness⟩
    exact witness.sameLaw_relative_errors_for_every_positive
      relativeError hrelative

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.cutoffTwoPulledMovingCenteredCoefficient_eqv_raw_of_nonroot
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.cutoffTwoRootSupported_or_nonRootWitness
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.cutoffTwoRootSupported_movingCentered_eqv_zero_on
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.CutoffTwoNonRootCoefficientWitness.recenteringSize_le_scaled_l1_cofinally
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.cutoffTwoPulledRecenteringError_cleared_relative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.exists_positive_recentering_fraction_for_relative_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.cutoffTwoPulledMovingCenteredSameLaw_relative_matrix_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.cutoffTwoPulledMovingCenteredSameLaw_relative_diagonal_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.CutoffTwoNonRootCoefficientWitness.sameLaw_relative_errors_cofinally
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.CutoffTwoNonRootCoefficientWitness.sameLaw_relative_errors_for_every_positive
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.sameLaw_relative_errors_for_every_coefficient
