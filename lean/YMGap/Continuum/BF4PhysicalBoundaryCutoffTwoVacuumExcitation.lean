/-
# A constructive non-vacuum source in the cutoff-two BF4 vacuum column

The exact retained cutoff-two vacuum column is strictly larger than its
all-vacuum source term.  This file separates that vacuum term with the
faithful finite BF4 state code, evaluates the remaining non-vacuum mass
exactly, and uses total finite search to return a concrete retained
non-vacuum source with strictly positive source-to-vacuum amplitude.

The witness is data in `Type`: it is computed by `firstPositiveOr` from the
literal finite carrier.  No choice or propositional existence is used.

This is a finite `K = 2`, half-extent-zero result at coupling `1/2`.  It does
not give a spectral-gap, cutoff-uniform, volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction
import YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumColumnFullContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundarySelfSmoothingReduction
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
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

/-! ## 1. Exact non-vacuum mass -/

/-- Complement of the faithful vacuum code delta. -/
def cutoffTwoNonvacuumMask (source : EdgeLabelling) : Q' :=
  if bf4StateCode 2 0 source =
      bf4StateCode 2 0 zeroEdgeLabelling then 0 else 1

/-- Exact contribution of all retained non-vacuum sources to the vacuum
boundary column. -/
def cutoffTwoNonvacuumVacuumColumnMass : Q' :=
  listQSum
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling *
        cutoffTwoNonvacuumMask source)
    (centralPositiveHalfStates cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)

/-- Exact excess beyond the all-vacuum source term. -/
def cutoffTwoVacuumExcitedExcess : Q' :=
  Q'.mkPos 68719477465 281474976710656 (by decide)

theorem cutoffTwoVacuumExpectedScalar_eqv_one_add_excitedExcess :
    cutoffTwoVacuumExpectedScalar ≈
      1 + cutoffTwoVacuumExcitedExcess := by
  decide

private theorem amplitude_split_vacuum_nonvacuum
    (source : EdgeLabelling) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling ≈
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling * vacuumCodeDelta 2 source +
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling * cutoffTwoNonvacuumMask source := by
  by_cases hcode :
      bf4StateCode 2 0 source =
        bf4StateCode 2 0 zeroEdgeLabelling
  · unfold vacuumCodeDelta cutoffTwoNonvacuumMask
    rw [if_pos hcode, if_pos hcode]
    exact split_one_zero _
  · unfold vacuumCodeDelta cutoffTwoNonvacuumMask
    rw [if_neg hcode, if_neg hcode]
    exact split_zero_one _

/-- The retained column splits exactly into its faithful vacuum-code term
and the complementary non-vacuum mass. -/
theorem centralBoundaryColumnMass_cutoffTwo_vacuum_split :
    centralBoundaryColumnMass cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling ≈
      listQSum
          (fun source =>
            centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
                zeroEdgeLabelling *
              vacuumCodeDelta 2 source)
          (centralPositiveHalfStates cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0) +
        cutoffTwoNonvacuumVacuumColumnMass := by
  unfold centralBoundaryColumnMass cutoffTwoNonvacuumVacuumColumnMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
              zeroEdgeLabelling * vacuumCodeDelta 2 source +
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
              zeroEdgeLabelling * cutoffTwoNonvacuumMask source)
      (centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    exact amplitude_split_vacuum_nonvacuum source
  · exact listQSum_add _ _ _

/-- The complete retained non-vacuum contribution is the exact positive
rational excess beyond one. -/
theorem cutoffTwoNonvacuumVacuumColumnMass_eqv_excitedExcess :
    cutoffTwoNonvacuumVacuumColumnMass ≈
      cutoffTwoVacuumExcitedExcess := by
  let states := centralPositiveHalfStates cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
  let amplitude : EdgeLabelling → Q' := fun source =>
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
      zeroEdgeLabelling
  let vacuumPart := listQSum
    (fun source => amplitude source * vacuumCodeDelta 2 source) states
  have hvacuumPart : vacuumPart ≈ 1 := by
    exact Q'.eqv_trans _ (amplitude zeroEdgeLabelling) _
      (listQSum_value_mul_vacuumCodeDelta_positive
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 amplitude)
      (centralHalfAmplitude_vacuum_eqv_one
        cutoffTwoHalfCoupling 2 0)
  have htotal :
      vacuumPart + cutoffTwoNonvacuumVacuumColumnMass ≈
        1 + cutoffTwoVacuumExcitedExcess := by
    exact Q'.eqv_trans _
      (centralBoundaryColumnMass cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 zeroEdgeLabelling) _
      (Q'.eqv_symm centralBoundaryColumnMass_cutoffTwo_vacuum_split)
      (Q'.eqv_trans _ cutoffTwoVacuumExpectedScalar _
        centralBoundaryColumnMass_cutoffTwo_vacuum_eqv_expected
        cutoffTwoVacuumExpectedScalar_eqv_one_add_excitedExcess)
  apply add_left_cancel_eqv (base := (1 : Q'))
  exact Q'.eqv_trans _
    (vacuumPart + cutoffTwoNonvacuumVacuumColumnMass) _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm hvacuumPart)
      (Q'.eqv_refl cutoffTwoNonvacuumVacuumColumnMass))
    htotal

theorem cutoffTwoNonvacuumVacuumColumnMass_pos :
    (0 : Q') < cutoffTwoNonvacuumVacuumColumnMass := by
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < cutoffTwoVacuumExcitedExcess)
    (Q'.ge_of_eqv
      cutoffTwoNonvacuumVacuumColumnMass_eqv_excitedExcess)

/-! ## 2. A computable excited-source witness -/

/-- Retained sources other than the unique faithful vacuum code. -/
def cutoffTwoNonvacuumPositiveSources : List EdgeLabelling :=
  (centralPositiveHalfStates cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0).filter
      (fun source => decide
        (bf4StateCode 2 0 source ≠
          bf4StateCode 2 0 zeroEdgeLabelling))

private theorem cutoffTwoNonvacuumMask_value
    (source : EdgeLabelling) :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling * cutoffTwoNonvacuumMask source ≈
      if decide (bf4StateCode 2 0 source ≠
          bf4StateCode 2 0 zeroEdgeLabelling) then
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
          zeroEdgeLabelling
      else 0 := by
  by_cases hcode :
      bf4StateCode 2 0 source =
        bf4StateCode 2 0 zeroEdgeLabelling
  · simp only [hcode, ne_eq, not_true_eq_false]
    unfold cutoffTwoNonvacuumMask
    rw [if_pos hcode]
    exact Q'.mul_zero_eqv _
  · simp only [hcode, ne_eq, not_false_eq_true]
    unfold cutoffTwoNonvacuumMask
    rw [if_neg hcode]
    exact Q'.mul_one_eqv _

private theorem listQSum_filter_eq_mask
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
    listQSum value (items.filter predicate) ≈
      listQSum
        (fun item => if predicate item then value item else 0)
        items
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

theorem cutoffTwoNonvacuumPositiveSources_sum_eqv_excitedExcess :
    listQSum
        (fun source =>
          centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling)
        cutoffTwoNonvacuumPositiveSources ≈
      cutoffTwoVacuumExcitedExcess := by
  let amplitude : EdgeLabelling → Q' := fun source =>
    centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
      zeroEdgeLabelling
  let predicate : EdgeLabelling → Bool := fun source => decide
    (bf4StateCode 2 0 source ≠
      bf4StateCode 2 0 zeroEdgeLabelling)
  refine Q'.eqv_trans _
    (listQSum
      (fun source => if predicate source then amplitude source else 0)
      (centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)) _ ?_ ?_
  · exact listQSum_filter_eq_mask amplitude predicate _
  · refine Q'.eqv_trans _ cutoffTwoNonvacuumVacuumColumnMass _ ?_
      cutoffTwoNonvacuumVacuumColumnMass_eqv_excitedExcess
    unfold cutoffTwoNonvacuumVacuumColumnMass
    apply listQSum_congr_on
    intro source _
    exact Q'.eqv_symm (cutoffTwoNonvacuumMask_value source)

/-- A deterministic finite search returns an actual excited source. -/
def cutoffTwoExcitedVacuumSource : EdgeLabelling :=
  firstPositiveOr zeroEdgeLabelling
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling)
    cutoffTwoNonvacuumPositiveSources

/-- The selected datum is retained, is not the vacuum source, and has
strictly positive production amplitude into the vacuum boundary. -/
theorem cutoffTwoExcitedVacuumSource_spec :
    cutoffTwoExcitedVacuumSource ∈
        centralPositiveHalfStates cutoffTwoHalfCoupling
          (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 ∧
      cutoffTwoExcitedVacuumSource ≠ zeroEdgeLabelling ∧
      (0 : Q') <
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0
          cutoffTwoExcitedVacuumSource zeroEdgeLabelling := by
  have hsumPos :
      (0 : Q') <
        listQSum
          (fun source =>
            centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
              zeroEdgeLabelling)
          cutoffTwoNonvacuumPositiveSources :=
    Q'.pos_of_lt_of_le
      (by decide : (0 : Q') < cutoffTwoVacuumExcitedExcess)
      (Q'.ge_of_eqv
        cutoffTwoNonvacuumPositiveSources_sum_eqv_excitedExcess)
  have hselected := firstPositiveOr_mem_and_pos_of_sum_pos
    zeroEdgeLabelling
    (fun source =>
      centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
        zeroEdgeLabelling)
    cutoffTwoNonvacuumPositiveSources hsumPos
  have hparts := List.mem_filter.mp hselected.1
  have hcodeNe :
      bf4StateCode 2 0 cutoffTwoExcitedVacuumSource ≠
        bf4StateCode 2 0 zeroEdgeLabelling :=
    of_decide_eq_true hparts.2
  exact ⟨hparts.1, (fun heq => hcodeNe (congrArg
    (bf4StateCode 2 0) heq)), hselected.2⟩

/-- Faithfulness strengthens the selected source's non-vacuum statement to
literal inequality of the finite BF4 state codes. -/
theorem cutoffTwoExcitedVacuumSource_code_ne :
    bf4StateCode 2 0 cutoffTwoExcitedVacuumSource ≠
      bf4StateCode 2 0 zeroEdgeLabelling := by
  intro hcode
  exact cutoffTwoExcitedVacuumSource_spec.2.1
    (bf4StateCode_injective_on_positive
      cutoffTwoExcitedVacuumSource_spec.1
      (YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.zeroEdgeLabelling_mem_centralPositiveHalfStates
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
      hcode)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation.cutoffTwoNonvacuumVacuumColumnMass_eqv_excitedExcess
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation.cutoffTwoNonvacuumPositiveSources_sum_eqv_excitedExcess
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation.cutoffTwoExcitedVacuumSource_spec
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation.cutoffTwoExcitedVacuumSource_code_ne
