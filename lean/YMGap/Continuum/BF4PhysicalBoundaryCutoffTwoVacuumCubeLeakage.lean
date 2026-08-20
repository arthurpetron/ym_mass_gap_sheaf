/-
# A third-state leakage witness for the cutoff-two vacuum/cube sector

The exact non-vacuum mass in the cutoff-two vacuum column is larger than the
single lower-cube contribution.  This module separates the cube by its
faithful finite state code, proves the positive remainder exactly, and uses a
total recursive search to select a retained third state with a strictly
positive genuine physical vacuum-row entry.

Thus the displayed vacuum/cube coordinate span is not closed under the raw
physical Gram action.  The strict two-by-two minor is consequently not an
invariant two-state spectral block.  This remains a finite cutoff-two result
and makes no cutoff-uniform or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeCenteredExcitationWitness

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage

set_option maxRecDepth 300000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeGramCross
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem split_one_zero (value : Q') :
    value ≈ value * 1 + value * 0 := by
  exact Q'.eqv_symm
    (Q'.eqv_trans _ (value * 1 + 0) _
      (Q'.add_eqv_congr'
        (Q'.eqv_refl (value * 1))
        (Q'.mul_zero_eqv value))
      (Q'.eqv_trans _ (value * 1) _
        (Q'.eqv_of_eq (Q'.add_zero' (value * 1)))
        (Q'.mul_one_eqv value)))

private theorem split_zero_one (value : Q') :
    value ≈ value * 0 + value * 1 := by
  exact Q'.eqv_symm
    (Q'.eqv_trans _ (0 + value * 1) _
      (Q'.add_eqv_congr'
        (Q'.mul_zero_eqv value)
        (Q'.eqv_refl (value * 1)))
      (Q'.eqv_trans _ (value * 1) _
        (Q'.eqv_of_eq (Q'.zero_add' (value * 1)))
        (Q'.mul_one_eqv value)))

private theorem add_then_neg_left_cancel_eqv
    (base value : Q') :
    (base + value) + (-base) ≈ value := by
  exact Q'.eqv_trans _ ((value + base) + (-base)) _
    (Q'.add_eqv_congr'
      (Q'.add_comm_eqv base value)
      (Q'.eqv_refl (-base)))
    (Q'.eqv_trans _ (value + (base + (-base))) _
      (Q'.add_assoc_eqv value base (-base))
      (Q'.eqv_trans _ (value + ((-base) + base)) _
        (Q'.add_eqv_congr_left value _ _
          (Q'.add_comm_eqv base (-base)))
        (Q'.eqv_trans _ (value + 0) _
          (Q'.add_eqv_congr_left value _ _
            (Q'.neg_add_self_eqv base))
          (Q'.eqv_of_eq (Q'.add_zero' value)))))

private theorem add_left_cancel_eqv
    {base left right : Q'}
    (h : base + left ≈ base + right) :
    left ≈ right := by
  have hshift :
      (base + left) + (-base) ≈
        (base + right) + (-base) :=
    Q'.add_eqv_congr' h (Q'.eqv_refl (-base))
  exact Q'.eqv_trans _ ((base + left) + (-base)) _
    (Q'.eqv_symm (add_then_neg_left_cancel_eqv base left))
    (Q'.eqv_trans _ ((base + right) + (-base)) _
      hshift (add_then_neg_left_cancel_eqv base right))

/-! ## 1. Faithful cutoff-two code Dirac action -/

def cutoffTwoSourceCodeDelta
    (source selected : EdgeLabelling) : Q' :=
  if bf4StateCode 2 0 source = bf4StateCode 2 0 selected then 1 else 0

theorem cutoffTwo_vacuum_cube_code_ne :
    bf4StateCode 2 0 zeroEdgeLabelling ≠
      bf4StateCode 2 0 centralLowerCubeState := by
  decide

private theorem listQSum_sourceCodeDelta_zero_of_not_mem
    (selected : EdgeLabelling)
    (hselected : selected ∈ cutoffTwoVacuumColumnCarrier)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items → item ∈ cutoffTwoVacuumColumnCarrier) →
      selected ∉ items →
      listQSum
          (fun item => cutoffTwoSourceCodeDelta item selected * value item)
          items ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hcarrier, hnot => by
      have hhead := hcarrier head List.mem_cons_self
      have htail :
          ∀ item, item ∈ tail → item ∈ cutoffTwoVacuumColumnCarrier :=
        fun item hitem => hcarrier item (List.mem_cons_of_mem head hitem)
      have hselectedTail : selected ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hcode :
          bf4StateCode 2 0 head ≠ bf4StateCode 2 0 selected := by
        intro heq
        have hsame := bf4StateCode_injective_on_positive hhead hselected heq
        subst head
        exact hnot List.mem_cons_self
      simp only [listQSum, cutoffTwoSourceCodeDelta, if_neg hcode]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv (value head))
          (listQSum_sourceCodeDelta_zero_of_not_mem
            selected hselected value tail htail hselectedTail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_sourceCodeDelta_of_mem_nodup
    (selected : EdgeLabelling)
    (hselected : selected ∈ cutoffTwoVacuumColumnCarrier)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items → item ∈ cutoffTwoVacuumColumnCarrier) →
      items.Nodup →
      selected ∈ items →
      listQSum
          (fun item => cutoffTwoSourceCodeDelta item selected * value item)
          items ≈ value selected
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hcarrier, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, cutoffTwoSourceCodeDelta, if_true]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr'
            (Q'.one_mul_eqv (value selected))
            (listQSum_sourceCodeDelta_zero_of_not_mem
              selected hselected value tail
              (fun item hitem =>
                hcarrier item (List.mem_cons_of_mem selected hitem))
              hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' (value selected)))
      · have hheadCarrier := hcarrier head List.mem_cons_self
        have hcode :
            bf4StateCode 2 0 head ≠ bf4StateCode 2 0 selected := by
          intro heq
          have hsame := bf4StateCode_injective_on_positive
            hheadCarrier hselected heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, cutoffTwoSourceCodeDelta, if_neg hcode]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.zero_mul_eqv (value head))
            (listQSum_sourceCodeDelta_of_mem_nodup
              selected hselected value tail
              (fun item hitem =>
                hcarrier item (List.mem_cons_of_mem head hitem))
              hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' (value selected)))

theorem cutoffTwoSourceCodeDelta_action_eqv
    (selected : EdgeLabelling)
    (hselected : selected ∈ cutoffTwoVacuumColumnCarrier)
    (value : EdgeLabelling → Q') :
    listQSum
        (fun source => cutoffTwoSourceCodeDelta source selected * value source)
        cutoffTwoVacuumColumnCarrier ≈ value selected := by
  exact listQSum_sourceCodeDelta_of_mem_nodup
    selected hselected value cutoffTwoVacuumColumnCarrier
    (fun item hitem => hitem)
    (centralPositiveHalfStates_nodup
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
    hselected

/-! ## 2. Exact positive mass outside both displayed states -/

def cutoffTwoOutsideVacuumCubeMask (source : EdgeLabelling) : Q' :=
  if bf4StateCode 2 0 source =
      bf4StateCode 2 0 zeroEdgeLabelling then 0
  else if bf4StateCode 2 0 source =
      bf4StateCode 2 0 centralLowerCubeState then 0
  else 1

def cutoffTwoOutsideVacuumCubeMass : Q' :=
  listQSum
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling * cutoffTwoOutsideVacuumCubeMask source)
    cutoffTwoVacuumColumnCarrier

def cutoffTwoVacuumOutsideCubeExcess : Q' :=
  Q'.mkPos 729 281474976710656 (by decide)

theorem cutoffTwoVacuumExcitedExcess_eqv_cube_add_outside :
    cutoffTwoVacuumExcitedExcess ≈
      cutoffTwoCubeLowerFaceScalar + cutoffTwoVacuumOutsideCubeExcess := by
  unfold cutoffTwoVacuumExcitedExcess cutoffTwoCubeLowerFaceScalar
    cutoffTwoVacuumOutsideCubeExcess
  decide

private theorem amplitude_nonvacuum_split_cube_outside
    (source : EdgeLabelling) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling * cutoffTwoNonvacuumMask source ≈
      cutoffTwoSourceCodeDelta source centralLowerCubeState *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling +
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling * cutoffTwoOutsideVacuumCubeMask source := by
  let amplitude := centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
    zeroEdgeLabelling
  by_cases hvacuum :
      bf4StateCode 2 0 source = bf4StateCode 2 0 zeroEdgeLabelling
  · have hcube :
        bf4StateCode 2 0 source ≠
          bf4StateCode 2 0 centralLowerCubeState := by
      intro h
      exact cutoffTwo_vacuum_cube_code_ne (hvacuum.symm.trans h)
    unfold cutoffTwoNonvacuumMask cutoffTwoSourceCodeDelta
      cutoffTwoOutsideVacuumCubeMask
    rw [if_pos hvacuum, if_neg hcube, if_pos hvacuum]
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (Q'.zero_mul_eqv amplitude)
          (Q'.mul_zero_eqv amplitude))
        (Q'.eqv_trans _ 0 _
          (Q'.eqv_of_eq (Q'.zero_add' 0))
          (Q'.eqv_symm (Q'.mul_zero_eqv amplitude))))
  · by_cases hcube :
      bf4StateCode 2 0 source =
        bf4StateCode 2 0 centralLowerCubeState
    · unfold cutoffTwoNonvacuumMask cutoffTwoSourceCodeDelta
        cutoffTwoOutsideVacuumCubeMask
      rw [if_neg hvacuum, if_pos hcube, if_neg hvacuum, if_pos hcube]
      exact Q'.eqv_trans _ amplitude _
        (Q'.mul_one_eqv amplitude)
        (Q'.eqv_symm
          (Q'.eqv_trans _ (amplitude + 0) _
            (Q'.add_eqv_congr'
              (Q'.one_mul_eqv amplitude)
              (Q'.mul_zero_eqv amplitude))
            (Q'.eqv_of_eq (Q'.add_zero' amplitude))))
    · unfold cutoffTwoNonvacuumMask cutoffTwoSourceCodeDelta
        cutoffTwoOutsideVacuumCubeMask
      rw [if_neg hvacuum, if_neg hcube, if_neg hvacuum, if_neg hcube]
      exact Q'.eqv_trans _ amplitude _
        (Q'.mul_one_eqv amplitude)
        (Q'.eqv_symm
          (Q'.eqv_trans _ (0 + amplitude) _
            (Q'.add_eqv_congr'
              (Q'.zero_mul_eqv amplitude)
              (Q'.mul_one_eqv amplitude))
            (Q'.eqv_of_eq (Q'.zero_add' amplitude))))

theorem cutoffTwoNonvacuumMass_eqv_cube_add_outsideMass :
    cutoffTwoNonvacuumVacuumColumnMass ≈
      cutoffTwoCubeLowerFaceScalar + cutoffTwoOutsideVacuumCubeMass := by
  let amplitude : EdgeLabelling → Q' := fun source =>
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source zeroEdgeLabelling
  have hcube : centralLowerCubeState ∈ cutoffTwoVacuumColumnCarrier :=
    centralLowerCubeState_mem_centralPositiveHalfStates
      (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide)
  unfold cutoffTwoNonvacuumVacuumColumnMass cutoffTwoOutsideVacuumCubeMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        cutoffTwoSourceCodeDelta source centralLowerCubeState *
            amplitude source +
          amplitude source * cutoffTwoOutsideVacuumCubeMask source)
      cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    exact amplitude_nonvacuum_split_cube_outside source
  refine Q'.eqv_trans _
    (listQSum
        (fun source =>
          cutoffTwoSourceCodeDelta source centralLowerCubeState *
            amplitude source)
        cutoffTwoVacuumColumnCarrier +
      listQSum
        (fun source =>
          amplitude source * cutoffTwoOutsideVacuumCubeMask source)
        cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · exact listQSum_add _ _ _
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ (amplitude centralLowerCubeState) _
      (cutoffTwoSourceCodeDelta_action_eqv
        centralLowerCubeState hcube amplitude)
      centralHalfAmplitude_cutoffTwo_cube_vacuum_eqv_scalar)
    (Q'.eqv_refl _)

theorem cutoffTwoOutsideVacuumCubeMass_eqv_expected :
    cutoffTwoOutsideVacuumCubeMass ≈
      cutoffTwoVacuumOutsideCubeExcess := by
  apply add_left_cancel_eqv (base := cutoffTwoCubeLowerFaceScalar)
  exact Q'.eqv_trans _ cutoffTwoNonvacuumVacuumColumnMass _
    (Q'.eqv_symm cutoffTwoNonvacuumMass_eqv_cube_add_outsideMass)
    (Q'.eqv_trans _ cutoffTwoVacuumExcitedExcess _
      cutoffTwoNonvacuumVacuumColumnMass_eqv_excitedExcess
      cutoffTwoVacuumExcitedExcess_eqv_cube_add_outside)

theorem cutoffTwoOutsideVacuumCubeMass_pos :
    (0 : Q') < cutoffTwoOutsideVacuumCubeMass := by
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < cutoffTwoVacuumOutsideCubeExcess)
    (Q'.ge_of_eqv cutoffTwoOutsideVacuumCubeMass_eqv_expected)

/-! ## 3. Computable third-state witness and row leakage -/

def cutoffTwoOutsideVacuumCubeSources : List EdgeLabelling :=
  cutoffTwoVacuumColumnCarrier.filter
    (fun source => decide
      (bf4StateCode 2 0 source ≠
          bf4StateCode 2 0 zeroEdgeLabelling ∧
        bf4StateCode 2 0 source ≠
          bf4StateCode 2 0 centralLowerCubeState))

private theorem cutoffTwoOutsideVacuumCubeMask_value
    (source : EdgeLabelling) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling * cutoffTwoOutsideVacuumCubeMask source ≈
      if decide
          (bf4StateCode 2 0 source ≠
              bf4StateCode 2 0 zeroEdgeLabelling ∧
            bf4StateCode 2 0 source ≠
              bf4StateCode 2 0 centralLowerCubeState) then
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling
      else 0 := by
  by_cases hvacuum :
      bf4StateCode 2 0 source = bf4StateCode 2 0 zeroEdgeLabelling
  · simp only [hvacuum, ne_eq, not_true_eq_false, false_and,
      decide_false]
    unfold cutoffTwoOutsideVacuumCubeMask
    rw [if_pos hvacuum]
    exact Q'.mul_zero_eqv _
  · by_cases hcube :
      bf4StateCode 2 0 source =
        bf4StateCode 2 0 centralLowerCubeState
    · simp only [hcube, ne_eq, not_true_eq_false]
      unfold cutoffTwoOutsideVacuumCubeMask
      rw [if_neg hvacuum, if_pos hcube]
      exact Q'.mul_zero_eqv _
    · simp only [hvacuum, hcube, ne_eq, not_false_eq_true, and_self,
        decide_true, if_true]
      unfold cutoffTwoOutsideVacuumCubeMask
      rw [if_neg hvacuum, if_neg hcube]
      exact Q'.mul_one_eqv _

private theorem listQSum_filter_eq_mask
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
    listQSum value (items.filter predicate) ≈
      listQSum (fun item => if predicate item then value item else 0) items
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (listQSum_filter_eq_mask value predicate tail)
            (Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr'
                  (Q'.eqv_refl 0) (Q'.eqv_refl _))
                (Q'.eqv_of_eq (Q'.zero_add' _))))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_filter_eq_mask value predicate tail)

theorem cutoffTwoOutsideVacuumCubeSources_sum_eqv_expected :
    listQSum
        (fun source =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling)
        cutoffTwoOutsideVacuumCubeSources ≈
      cutoffTwoVacuumOutsideCubeExcess := by
  let amplitude : EdgeLabelling → Q' := fun source =>
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source zeroEdgeLabelling
  let predicate : EdgeLabelling → Bool := fun source => decide
    (bf4StateCode 2 0 source ≠ bf4StateCode 2 0 zeroEdgeLabelling ∧
      bf4StateCode 2 0 source ≠ bf4StateCode 2 0 centralLowerCubeState)
  refine Q'.eqv_trans _
    (listQSum
      (fun source => if predicate source then amplitude source else 0)
      cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · exact listQSum_filter_eq_mask amplitude predicate _
  refine Q'.eqv_trans _ cutoffTwoOutsideVacuumCubeMass _ ?_
    cutoffTwoOutsideVacuumCubeMass_eqv_expected
  unfold cutoffTwoOutsideVacuumCubeMass
  apply listQSum_congr_on
  intro source _
  exact Q'.eqv_symm (cutoffTwoOutsideVacuumCubeMask_value source)

def cutoffTwoVacuumCubeLeakageState : EdgeLabelling :=
  firstPositiveOr zeroEdgeLabelling
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling)
    cutoffTwoOutsideVacuumCubeSources

theorem cutoffTwoVacuumCubeLeakageState_spec :
    cutoffTwoVacuumCubeLeakageState ∈ cutoffTwoVacuumColumnCarrier ∧
      cutoffTwoVacuumCubeLeakageState ≠ zeroEdgeLabelling ∧
      cutoffTwoVacuumCubeLeakageState ≠ centralLowerCubeState ∧
      (0 : Q') <
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          cutoffTwoVacuumCubeLeakageState zeroEdgeLabelling := by
  have hsum :
      (0 : Q') <
        listQSum
          (fun source =>
            centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
              zeroEdgeLabelling)
          cutoffTwoOutsideVacuumCubeSources :=
    Q'.pos_of_lt_of_le
      (by decide : (0 : Q') < cutoffTwoVacuumOutsideCubeExcess)
      (Q'.ge_of_eqv cutoffTwoOutsideVacuumCubeSources_sum_eqv_expected)
  have hselected := firstPositiveOr_mem_and_pos_of_sum_pos
    zeroEdgeLabelling
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling)
    cutoffTwoOutsideVacuumCubeSources hsum
  have hparts := List.mem_filter.mp hselected.1
  have hcodes := of_decide_eq_true hparts.2
  exact ⟨hparts.1,
    (fun heq => hcodes.1 (congrArg (bf4StateCode 2 0) heq)),
    (fun heq => hcodes.2 (congrArg (bf4StateCode 2 0) heq)),
    hselected.2⟩

theorem centralPhysicalReflectedKernel_cutoffTwo_vacuum_leakage_pos :
    (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        zeroEdgeLabelling cutoffTwoVacuumCubeLeakageState := by
  have hrow := centralPhysicalReflectedKernel_cutoffTwo_vacuum_row_eqv
    cutoffTwoVacuumCubeLeakageState
    cutoffTwoVacuumCubeLeakageState_spec.1
  have hentry :
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          zeroEdgeLabelling cutoffTwoVacuumCubeLeakageState ≈
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          cutoffTwoVacuumCubeLeakageState zeroEdgeLabelling := by
    exact Q'.eqv_trans _ _ _ hrow
      (Q'.eqv_trans _
        ((1 : Q') *
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0
            cutoffTwoVacuumCubeLeakageState zeroEdgeLabelling) _
        (Q'.mul_eqv_congr_right _ _ _
          centralBoundaryWeight_cutoffTwo_vacuum_eqv_one)
        (Q'.one_mul_eqv _))
  exact Q'.pos_of_lt_of_le
    cutoffTwoVacuumCubeLeakageState_spec.2.2.2
    (Q'.ge_of_eqv hentry)

/-- Row closure is the exact coordinate condition required for the raw
physical Gram action to preserve the displayed vacuum/cube span. -/
def cutoffTwoVacuumCubePhysicalRowClosed : Prop :=
  ∀ target : EdgeLabelling,
    target ∈ cutoffTwoVacuumColumnCarrier →
    target ≠ zeroEdgeLabelling →
    target ≠ centralLowerCubeState →
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      zeroEdgeLabelling target ≈ 0

theorem not_cutoffTwoVacuumCubePhysicalRowClosed :
    ¬ cutoffTwoVacuumCubePhysicalRowClosed := by
  intro hclosed
  have hzero := hclosed cutoffTwoVacuumCubeLeakageState
    cutoffTwoVacuumCubeLeakageState_spec.1
    cutoffTwoVacuumCubeLeakageState_spec.2.1
    cutoffTwoVacuumCubeLeakageState_spec.2.2.1
  exact (Int.not_lt_of_ge (Q'.le_of_eqv hzero))
    centralPhysicalReflectedKernel_cutoffTwo_vacuum_leakage_pos

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage.cutoffTwoSourceCodeDelta_action_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage.cutoffTwoOutsideVacuumCubeMass_eqv_expected
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage.cutoffTwoVacuumCubeLeakageState_spec
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage.centralPhysicalReflectedKernel_cutoffTwo_vacuum_leakage_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage.not_cutoffTwoVacuumCubePhysicalRowClosed
