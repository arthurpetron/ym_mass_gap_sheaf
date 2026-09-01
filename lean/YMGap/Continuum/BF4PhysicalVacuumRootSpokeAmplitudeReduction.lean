/-
# Reduce arbitrary-cutoff BF4 vacuum-root spokes to one half-amplitude

The arbitrary-cutoff vacuum boundary delta leaves exactly one boundary
coordinate in the weighted-Gram representation of a raw vacuum-root kernel
entry.  This module performs that collapse constructively.

For every retained lower state, the raw reflected kernel into the vacuum is
equivalent to the positive all-vacuum boundary weight times the state's
half-amplitude against the all-vacuum boundary.  At nonnegative coupling,
strict positivity of the kernel entry is therefore equivalent to strict
positivity of that one half-amplitude.

This identifies the exact remaining root-spoke classifier.  It does not
classify the surviving lower states, bound their number, construct a routing,
or assert a gap, continuum, or Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCommonKernelAction
open YMGap.Continuum.BF4PhysicalBoundaryVacuumColumnSupport
open YMGap.Continuum.BF4PhysicalBoundaryVacuumDeltaRow
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_on
    {Item : Type} (value : Item → Q') :
    ∀ items : List Item,
      (∀ item, item ∈ items → value item ≈ 0) →
        listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_on value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_eqv_member_of_nodup
    {Item : Type} (value : Item → Q') :
    ∀ (items : List Item) (target : Item),
      items.Nodup → target ∈ items →
      (∀ item, item ∈ items → item ≠ target → value item ≈ 0) →
        listQSum value items ≈ value target
  | [], target, _, htarget, _ =>
      False.elim (List.not_mem_nil htarget)
  | head :: tail, target, hnodup, htarget, hzero => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp htarget with heq | htail
      · subst head
        have htailZero : listQSum value tail ≈ 0 :=
          listQSum_eqv_zero_on value tail (fun item hitem =>
            hzero item (List.mem_cons_of_mem target hitem) (fun heq =>
              hparts.1 (heq ▸ hitem)))
        exact Q'.eqv_trans _ (value target + 0) _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hheadNe : head ≠ target := by
          intro heq
          exact hparts.1 (heq ▸ htail)
        have hheadZero : value head ≈ 0 :=
          hzero head List.mem_cons_self hheadNe
        have htailSum : listQSum value tail ≈ value target :=
          listQSum_eqv_member_of_nodup value tail target
            hparts.2 htail
            (fun item hitem hne =>
              hzero item (List.mem_cons_of_mem head hitem) hne)
        exact Q'.eqv_trans _ (0 + value target) _
          (Q'.add_eqv_congr' hheadZero htailSum)
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem q_left_pos_of_mul_pos
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

private theorem q_right_pos_of_mul_pos
    {left right : Q'}
    (hleft : (0 : Q') ≤ left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) ≤ left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-! ## 1. Only the all-vacuum boundary Gram coordinate survives -/

theorem centralPhysicalReflectedKernel_source_vacuum_eqv_singleBoundary
    (w : Q') (K : Nat) (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    centralPhysicalReflectedKernel w K 0
        source zeroEdgeLabelling ≈
      centralBoundaryWeight w K 0 zeroEdgeLabelling *
        (centralHalfAmplitude w K 0 source zeroEdgeLabelling *
          centralHalfAmplitude w K 0
            zeroEdgeLabelling zeroEdgeLabelling) := by
  let value : EdgeLabelling → Q' := fun boundary =>
    centralBoundaryWeight w K 0 boundary *
      (centralHalfAmplitude w K 0 source boundary *
        centralHalfAmplitude w K 0 zeroEdgeLabelling boundary)
  have hgram := centralPhysicalReflectedKernel_eq_weightedGram
    w hsource (zeroEdgeLabelling_mem_centralHalfStates K 0)
  refine Q'.eqv_trans _
    (weightedGram (centralBoundaryChannels K 0)
      (centralBoundaryWeight w K 0)
      (centralHalfAmplitude w K 0)
      source zeroEdgeLabelling) _ hgram ?_
  unfold weightedGram
  change listQSum value (centralBoundaryChannels K 0) ≈
    value zeroEdgeLabelling
  apply listQSum_eqv_member_of_nodup value
    (centralBoundaryChannels K 0) zeroEdgeLabelling
    (centralBoundaryChannels_nodup K 0)
    (zeroEdgeLabelling_mem_centralBoundaryChannels K 0)
  intro boundary hboundary hne
  have htestFalse : centralFixedBoundaryAllZeroB boundary = false := by
    cases htest : centralFixedBoundaryAllZeroB boundary with
    | false => exact rfl
    | true =>
        exact False.elim
          (hne (centralFixedBoundaryAllZeroB_eq_true_implies_eq_zero
            K boundary hboundary htest))
  have hvacuumZero :
      centralHalfAmplitude w K 0 zeroEdgeLabelling boundary ≈ 0 :=
    centralHalfAmplitude_vacuum_eqv_zero_of_allZeroB_false
      w K boundary hboundary htestFalse
  unfold value
  exact Q'.eqv_trans _
    (centralBoundaryWeight w K 0 boundary *
      (centralHalfAmplitude w K 0 source boundary * 0)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hvacuumZero))
    (Q'.eqv_trans _
      (centralBoundaryWeight w K 0 boundary * 0) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_zero_eqv _))
      (Q'.mul_zero_eqv _))

/-! ## 2. Exact root-spoke amplitude reduction -/

theorem centralPhysicalReflectedKernel_source_vacuum_eqv_weight_mul_amplitude
    (w : Q') (K : Nat) (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    centralPhysicalReflectedKernel w K 0
        source zeroEdgeLabelling ≈
      centralBoundaryWeight w K 0 zeroEdgeLabelling *
        centralHalfAmplitude w K 0 source zeroEdgeLabelling := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_source_vacuum_eqv_singleBoundary
      w K source hsource) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _
      (centralHalfAmplitude w K 0 source zeroEdgeLabelling * 1) _
      (Q'.mul_eqv_congr_left _ _ _
        (centralHalfAmplitude_vacuum_eqv_one w K 0))
      (Q'.mul_one_eqv _))

theorem centralBoundaryWeight_vacuum_pos
    {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') < centralBoundaryWeight w K 0 zeroEdgeLabelling := by
  have hvacuumNonnegative :
      (0 : Q') ≤
        centralHalfAmplitude w K 0
          zeroEdgeLabelling zeroEdgeLabelling :=
    centralHalfAmplitude_nonnegative hw K 0
      zeroEdgeLabelling zeroEdgeLabelling
  exact q_left_pos_of_mul_pos
    (Q'.mul_nonneg _ _ hvacuumNonnegative hvacuumNonnegative)
    (centralVacuumBoundaryGramIntegrand_pos K 0)

/-- A retained lower state is a positive raw predecessor of the vacuum
exactly when its one surviving all-vacuum half-amplitude is positive. -/
theorem centralPhysicalReflectedKernel_source_vacuum_pos_iff_amplitude_pos
    {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat)
    (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates K 0) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0
        source zeroEdgeLabelling ↔
      (0 : Q') <
        centralHalfAmplitude w K 0 source zeroEdgeLabelling := by
  let weight := centralBoundaryWeight w K 0 zeroEdgeLabelling
  let amplitude := centralHalfAmplitude w K 0 source zeroEdgeLabelling
  have hfactor :
      centralPhysicalReflectedKernel w K 0 source zeroEdgeLabelling ≈
        weight * amplitude :=
    centralPhysicalReflectedKernel_source_vacuum_eqv_weight_mul_amplitude
      w K source hsource
  have hweight : (0 : Q') < weight :=
    centralBoundaryWeight_vacuum_pos hw K
  constructor
  · intro hkernel
    have hproduct : (0 : Q') < weight * amplitude :=
      Q'.pos_of_lt_of_le hkernel (Q'.le_of_eqv hfactor)
    exact q_right_pos_of_mul_pos (Q'.le_of_lt hweight) hproduct
  · intro hamplitude
    have hproduct : (0 : Q') < weight * amplitude :=
      Q'.mul_pos hweight hamplitude
    exact Q'.pos_of_lt_of_le hproduct (Q'.ge_of_eqv hfactor)

end YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction.centralPhysicalReflectedKernel_source_vacuum_eqv_singleBoundary
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction.centralPhysicalReflectedKernel_source_vacuum_eqv_weight_mul_amplitude
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction.centralBoundaryWeight_vacuum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction.centralPhysicalReflectedKernel_source_vacuum_pos_iff_amplitude_pos
