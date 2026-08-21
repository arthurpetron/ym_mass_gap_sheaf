/-
# Pointwise Cauchy control for the physical BF4 conditional core

The normalized joint-kernel estimate cannot be divided entry by entry without
controlling row marginals.  This file performs that conditioning honestly for
an arbitrary unit observable.  It rewrites the genuine finite Markov value as
one quotient whose numerator is the observable-weighted normalized joint row,
splits that numerator into an old target core and a new-target shell, and
contracts the old-core difference against the existing row `l1` error.

The moving positive-row floor and the two target-shell bounds then feed the
constructive quotient-stability theorem.  The resulting pointwise estimate is
the finite core input needed by the atomic Markov Cauchy compiler; stationary
source-shell tightness remains a separate obligation.

## Axiom gate

Only finite list sums and exact rational order/algebra are used.  There is no
classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor

namespace YMGap.Continuum.BF4PhysicalCutoffConditionalCoreCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One weighted joint numerator for the genuine Markov value -/

/-- The normalized joint row tested against a unit observable, before
conditioning by the source marginal. -/
def centralPhysicalObservableJointNumerator
    (w : Q') (hw : (0 : Q') <= w)
    (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target *
        observable.value target)
    (centralHalfStates cutoff half)

theorem centralPhysicalObservableJointNumerator_nonnegative
    {w : Q'} (hw : (0 : Q') <= w)
    (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    (0 : Q') <= centralPhysicalObservableJointNumerator
      w hw cutoff half observable source := by
  unfold centralPhysicalObservableJointNumerator
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.mul_nonneg _ _
    (centralNormalizedPhysicalReflectedKernel_nonnegative
      hw cutoff half source target)
    (observable.nonnegative target)

theorem centralPhysicalObservableJointNumerator_le_rowMarginal
    {w : Q'} (hw : (0 : Q') <= w)
    (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    centralPhysicalObservableJointNumerator
        w hw cutoff half observable source <=
      centralPhysicalRowMarginal w hw cutoff half source := by
  unfold centralPhysicalObservableJointNumerator
    centralPhysicalRowMarginal
  apply listQSum_mono
  intro target _
  refine Q'.le_trans' _
    (centralNormalizedPhysicalReflectedKernel
      w hw cutoff half source target * 1) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (observable.le_one target)
      (centralNormalizedPhysicalReflectedKernel_nonnegative
        hw cutoff half source target)
  · exact Q'.le_of_eqv
      (Q'.mul_one_eqv
        (centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target))

private theorem listQSum_filter_eq_full_of_zero_local
    {A : Type} (value : A -> Q') (predicate : A -> Bool) :
    forall items : List A,
      (forall item, item ∈ items -> predicate item = false ->
        value item ≈ 0) ->
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          have hhead := hzero head List.mem_cons_self hp
          have htail := listQSum_filter_eq_full_of_zero_local
            value predicate tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))
          exact Q'.eqv_trans _ _ _ htail
            (Q'.eqv_trans _ (0 + listQSum value tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr'
                (Q'.eqv_symm hhead) (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_full_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))

private theorem centralPhysicalObservableJointNumerator_positive_filter
    {w : Q'} {hw : (0 : Q') <= w}
    {cutoff half : Nat}
    (observable : CentralPhysicalUnitObservable)
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates cutoff half) :
    listQSum
        (fun target =>
          centralNormalizedPhysicalReflectedKernel
              w hw cutoff half source target *
            observable.value target)
        (centralPositiveHalfStates w hw cutoff half) ≈
      centralPhysicalObservableJointNumerator
        w hw cutoff half observable source := by
  unfold centralPositiveHalfStates
    centralPhysicalObservableJointNumerator
  apply listQSum_filter_eq_full_of_zero_local
  intro target htarget hfalse
  have hnotPositive :
      ¬ (0 : Q') <
        centralPhysicalRowMarginal w hw cutoff half target := by
    simpa only [decide_eq_false_iff_not] using hfalse
  have hjoint :=
    centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
      hsource htarget hnotPositive
  exact Q'.eqv_trans _
    (0 * observable.value target) _
    (Q'.mul_eqv_congr_right _ _ _ hjoint)
    (Q'.zero_mul_eqv _)

private theorem centralPhysicalMarkovApply_eq_positiveWeighted_mul_recip
    {w : Q'} {hw : (0 : Q') <= w}
    {cutoff half : Nat}
    (observable : CentralPhysicalUnitObservable)
    {source : EdgeLabelling}
    (hrow : (0 : Q') <
      centralPhysicalRowMarginal w hw cutoff half source) :
    centralPhysicalMarkovApply
        w hw cutoff half observable.value source ≈
      listQSum
          (fun target =>
            centralNormalizedPhysicalReflectedKernel
                w hw cutoff half source target *
              observable.value target)
          (centralPositiveHalfStates w hw cutoff half) *
        Q'.recipPos
          (centralPhysicalRowMarginal
            w hw cutoff half source) hrow := by
  have hterm : forall target : EdgeLabelling,
      centralPhysicalConditionalKernel w hw cutoff half source target *
          observable.value target ≈
        (centralNormalizedPhysicalReflectedKernel
            w hw cutoff half source target * observable.value target) *
          Q'.recipPos
            (centralPhysicalRowMarginal
              w hw cutoff half source) hrow := by
    intro target
    rw [centralPhysicalConditionalKernel_eq_divPos hrow]
    unfold Q'.divPos
    refine Q'.eqv_trans _
      (centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target *
        (Q'.recipPos
            (centralPhysicalRowMarginal
              w hw cutoff half source) hrow *
          observable.value target)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target *
        (observable.value target *
          Q'.recipPos
            (centralPhysicalRowMarginal
              w hw cutoff half source) hrow)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  unfold centralPhysicalMarkovApply
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (centralNormalizedPhysicalReflectedKernel
            w hw cutoff half source target * observable.value target) *
          Q'.recipPos
            (centralPhysicalRowMarginal
              w hw cutoff half source) hrow)
      (centralPositiveHalfStates w hw cutoff half)) _ ?_ ?_
  · exact listQSum_congr hterm _
  exact listQSum_mul_right
    (fun target =>
      centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target * observable.value target)
    (Q'.recipPos
      (centralPhysicalRowMarginal
        w hw cutoff half source) hrow)
    (centralPositiveHalfStates w hw cutoff half)

/-- On a positive retained source, the genuine finite Markov value is the
single quotient of the weighted normalized joint numerator by its row
marginal. -/
theorem centralPhysicalMarkovApply_eq_divPos_observableJointNumerator
    {w : Q'} {hw : (0 : Q') <= w}
    {cutoff half : Nat}
    (observable : CentralPhysicalUnitObservable)
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates cutoff half)
    (hrow : (0 : Q') <
      centralPhysicalRowMarginal w hw cutoff half source) :
    centralPhysicalMarkovApply
        w hw cutoff half observable.value source ≈
      Q'.divPos
        (centralPhysicalObservableJointNumerator
          w hw cutoff half observable source)
        (centralPhysicalRowMarginal w hw cutoff half source)
        hrow := by
  refine Q'.eqv_trans _
    (listQSum
        (fun target =>
          centralNormalizedPhysicalReflectedKernel
              w hw cutoff half source target * observable.value target)
        (centralPositiveHalfStates w hw cutoff half) *
      Q'.recipPos
        (centralPhysicalRowMarginal
          w hw cutoff half source) hrow) _
    (centralPhysicalMarkovApply_eq_positiveWeighted_mul_recip
      observable hrow) ?_
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (centralPhysicalObservableJointNumerator_positive_filter
      observable hsource)

/-! ## 2. Old weighted target core and target shell -/

def centralOldRowObservableNumerator
    (w : Q') (hw : (0 : Q') <= w)
    (base cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target *
        observable.value target)
    (centralHalfStates base half)

def centralOldRowObservableTargetShellMass
    (w : Q') (hw : (0 : Q') <= w)
    (base cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target *
        observable.value target)
    ((centralHalfStates cutoff half).filter
      (fun target =>
        !(labelWithinB base
          (centralLowerFaceIds half) target)))

theorem centralOldRowObservableTargetShellMass_nonnegative
    {w : Q'} (hw : (0 : Q') <= w)
    (base cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    (0 : Q') <= centralOldRowObservableTargetShellMass
      w hw base cutoff half observable source := by
  unfold centralOldRowObservableTargetShellMass
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.mul_nonneg _ _
    (centralNormalizedPhysicalReflectedKernel_nonnegative
      hw cutoff half source target)
    (observable.nonnegative target)

theorem centralOldRowObservableTargetShellMass_le_jointShell
    {w : Q'} (hw : (0 : Q') <= w)
    (base cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    centralOldRowObservableTargetShellMass
        w hw base cutoff half observable source <=
      centralOldRowJointTargetShellMass
        w hw base cutoff half source := by
  unfold centralOldRowObservableTargetShellMass
    centralOldRowJointTargetShellMass
  apply listQSum_mono
  intro target _
  refine Q'.le_trans' _
    (centralNormalizedPhysicalReflectedKernel
      w hw cutoff half source target * 1) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (observable.le_one target)
      (centralNormalizedPhysicalReflectedKernel_nonnegative
        hw cutoff half source target)
  · exact Q'.le_of_eqv
      (Q'.mul_one_eqv
        (centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source target))

private theorem rangeNodup_local (N : Nat) :
    (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightN : right = N := List.mem_singleton.mp hright
      rw [heq, hrightN] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl N)

private theorem centralLowerFaceIds_nodup_local (half : Nat) :
    (centralLowerFaceIds half).Nodup := by
  have hfull :
      (slabPhysicalFaceEdges (centralExtent half)).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodup_local _
  have hall :
      ((centralLowerFaceIds half ++ centralFixedFaceIds half) ++
        centralUpperFaceIds half).Nodup := by
    simpa [centralLowerFaceIds, centralFixedFaceIds,
      centralUpperFaceIds] using
      ((centralSlabFaceIdParts_perm half).symm.nodup hfull)
  exact (List.nodup_append.mp (List.nodup_append.mp hall).1).1

theorem centralPhysicalObservableJointNumerator_eq_old_add_targetShell
    {w : Q'} (hw : (0 : Q') <= w)
    {base cutoff half : Nat} (hbase : base <= cutoff)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    centralPhysicalObservableJointNumerator
        w hw cutoff half observable source ≈
      centralOldRowObservableNumerator
          w hw base cutoff half observable source +
        centralOldRowObservableTargetShellMass
          w hw base cutoff half observable source := by
  let value := fun target =>
    centralNormalizedPhysicalReflectedKernel
        w hw cutoff half source target * observable.value target
  let test := labelWithinB base (centralLowerFaceIds half)
  have hfilter :
      (centralHalfStates cutoff half).filter test =
        centralHalfStates base half := by
    unfold centralHalfStates
    exact boundedEdgeLabellings_filter_cutoff
      hbase _ (centralLowerFaceIds_nodup_local half)
  have hsplit := listQSum_filter_partition
    value test (centralHalfStates cutoff half)
  unfold centralPhysicalObservableJointNumerator
    centralOldRowObservableNumerator
    centralOldRowObservableTargetShellMass
  rw [hfilter] at hsplit
  simpa [value, test] using hsplit

/-! ## 3. Weighted old-row differences contract against joint `l1` -/

private theorem weighted_joint_difference_abs_le
    (left right weight : Q')
    (hweight0 : (0 : Q') <= weight)
    (hweight1 : weight <= (1 : Q')) :
    Q'.abs (left * weight + -(right * weight)) <=
      Q'.abs (left + -right) := by
  have hfactor :
      left * weight + -(right * weight) ≈
        (left + -right) * weight := by
    refine Q'.eqv_trans _
      (left * weight + (-right) * weight) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.neg_mul_eqv right weight))
    · exact Q'.eqv_symm (Q'.add_mul_eqv left (-right) weight)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hfactor)) ?_
  refine Q'.le_trans' _
    (Q'.abs (left + -right) * Q'.abs weight) _
    (ExpNeg.abs_mul_le (left + -right) weight) ?_
  refine Q'.le_trans' _
    (Q'.abs (left + -right) * weight) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg hweight0)))
  refine Q'.le_trans' _
    (Q'.abs (left + -right) * 1) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      hweight1 (Q'.abs_nonneg (left + -right))
  · exact Q'.le_of_eqv
      (Q'.mul_one_eqv (Q'.abs (left + -right)))

theorem centralOldRowObservableNumerator_abs_sub_le_l1
    {w : Q'} (hw : (0 : Q') <= w)
    (base first second half : Nat)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    Q'.abs
        (centralOldRowObservableNumerator
            w hw base first half observable source +
          -centralOldRowObservableNumerator
            w hw base second half observable source) <=
      centralOldRowCutoffDifferenceL1
        w hw base first second half source := by
  let firstValue := fun target =>
    centralNormalizedPhysicalReflectedKernel
        w hw first half source target * observable.value target
  let secondValue := fun target =>
    centralNormalizedPhysicalReflectedKernel
        w hw second half source target * observable.value target
  refine Q'.le_trans' _
    (listQSum
      (fun target => Q'.abs
        (firstValue target + -secondValue target))
      (centralHalfStates base half)) _ ?_ ?_
  · unfold centralOldRowObservableNumerator
    exact abs_listQSum_sub_le firstValue secondValue _
  unfold centralOldRowCutoffDifferenceL1
  apply listQSum_mono
  intro target _
  exact weighted_joint_difference_abs_le _ _ _
    (observable.nonnegative target) (observable.le_one target)

/-! ## 4. Conditioning the weighted row -/

theorem centralOldRowCutoffDifferenceL1_nonnegative
    {w : Q'} (hw : (0 : Q') <= w)
    (base first second half : Nat)
    (source : EdgeLabelling) :
    (0 : Q') <= centralOldRowCutoffDifferenceL1
      w hw base first second half source := by
  unfold centralOldRowCutoffDifferenceL1
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.abs_nonneg _

/-- The weighted numerator has the same asymmetric old-core plus target-shell
comparison as the unweighted row marginal. -/
theorem centralPhysicalObservableJointNumerator_twoSided_of_oldRowL1
    {w : Q'} (hw : (0 : Q') <= w)
    {base first second half : Nat}
    (hbaseFirst : base <= first)
    (hbaseSecond : base <= second)
    (observable : CentralPhysicalUnitObservable)
    (source : EdgeLabelling) :
    let oldL1 := centralOldRowCutoffDifferenceL1
      w hw base first second half source
    let firstShell := centralOldRowJointTargetShellMass
      w hw base first half source
    let secondShell := centralOldRowJointTargetShellMass
      w hw base second half source
    centralPhysicalObservableJointNumerator
          w hw first half observable source <=
        centralPhysicalObservableJointNumerator
            w hw second half observable source +
          (oldL1 + firstShell) ∧
      centralPhysicalObservableJointNumerator
          w hw second half observable source <=
        centralPhysicalObservableJointNumerator
            w hw first half observable source +
          (oldL1 + secondShell) := by
  dsimp only
  let firstCore := centralOldRowObservableNumerator
    w hw base first half observable source
  let secondCore := centralOldRowObservableNumerator
    w hw base second half observable source
  let firstWeightedShell := centralOldRowObservableTargetShellMass
    w hw base first half observable source
  let secondWeightedShell := centralOldRowObservableTargetShellMass
    w hw base second half observable source
  let oldL1 := centralOldRowCutoffDifferenceL1
    w hw base first second half source
  let firstShell := centralOldRowJointTargetShellMass
    w hw base first half source
  let secondShell := centralOldRowJointTargetShellMass
    w hw base second half source
  have hfirstDecomp :=
    centralPhysicalObservableJointNumerator_eq_old_add_targetShell
      (half := half) hw hbaseFirst observable source
  have hsecondDecomp :=
    centralPhysicalObservableJointNumerator_eq_old_add_targetShell
      (half := half) hw hbaseSecond observable source
  have hcoreAbs :
      Q'.abs (firstCore + -secondCore) <= oldL1 := by
    unfold firstCore secondCore oldL1
    exact centralOldRowObservableNumerator_abs_sub_le_l1
      hw base first second half observable source
  have hfirstWeighted0 : (0 : Q') <= firstWeightedShell := by
    unfold firstWeightedShell
    exact centralOldRowObservableTargetShellMass_nonnegative
      hw base first half observable source
  have hsecondWeighted0 : (0 : Q') <= secondWeightedShell := by
    unfold secondWeightedShell
    exact centralOldRowObservableTargetShellMass_nonnegative
      hw base second half observable source
  have hfirstWeightedLe : firstWeightedShell <= firstShell := by
    unfold firstWeightedShell firstShell
    exact centralOldRowObservableTargetShellMass_le_jointShell
      hw base first half observable source
  have hsecondWeightedLe : secondWeightedShell <= secondShell := by
    unfold secondWeightedShell secondShell
    exact centralOldRowObservableTargetShellMass_le_jointShell
      hw base second half observable source
  have hfirstCoreLeFull :
      firstCore <= centralPhysicalObservableJointNumerator
        w hw first half observable source := by
    refine Q'.le_trans' _ (firstCore + firstWeightedShell) _
      (Q'.add_le_self_of_nonneg _ _ hfirstWeighted0) ?_
    exact Q'.ge_of_eqv hfirstDecomp
  have hsecondCoreLeFull :
      secondCore <= centralPhysicalObservableJointNumerator
        w hw second half observable source := by
    refine Q'.le_trans' _ (secondCore + secondWeightedShell) _
      (Q'.add_le_self_of_nonneg _ _ hsecondWeighted0) ?_
    exact Q'.ge_of_eqv hsecondDecomp
  constructor
  · have hcore := ExpNeg.le_add_of_abs_sub_le hcoreAbs
    have hadd := Q'.add_le_add_right
      firstCore (secondCore + oldL1) firstWeightedShell hcore
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfirstDecomp) ?_
    refine Q'.le_trans' _ _ _ hadd ?_
    refine Q'.le_trans' _
      (secondCore + (oldL1 + firstWeightedShell)) _
      (Q'.le_of_eqv
        (Q'.add_assoc_eqv secondCore oldL1 firstWeightedShell)) ?_
    exact Q'.add_le_add
      hsecondCoreLeFull
      (Q'.add_le_add_left oldL1
        firstWeightedShell firstShell hfirstWeightedLe)
  · have hcoreComm :
        Q'.abs (secondCore + -firstCore) <= oldL1 :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (ExpNeg.abs_sub_comm secondCore firstCore))
        hcoreAbs
    have hcore := ExpNeg.le_add_of_abs_sub_le hcoreComm
    have hadd := Q'.add_le_add_right
      secondCore (firstCore + oldL1) secondWeightedShell hcore
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsecondDecomp) ?_
    refine Q'.le_trans' _ _ _ hadd ?_
    refine Q'.le_trans' _
      (firstCore + (oldL1 + secondWeightedShell)) _
      (Q'.le_of_eqv
        (Q'.add_assoc_eqv firstCore oldL1 secondWeightedShell)) ?_
    exact Q'.add_le_add
      hfirstCoreLeFull
      (Q'.add_le_add_left oldL1
        secondWeightedShell secondShell hsecondWeightedLe)

/-- One common error that dominates the old-row joint discrepancy and both
outgoing target shells. -/
def centralPhysicalConditioningCoreError
    (w : Q') (hw : (0 : Q') <= w)
    (base first second half : Nat)
    (source : EdgeLabelling) : Q' :=
  centralOldRowCutoffDifferenceL1
      w hw base first second half source +
    (centralOldRowJointTargetShellMass
        w hw base first half source +
      centralOldRowJointTargetShellMass
        w hw base second half source)

theorem centralPhysicalConditioningCoreError_nonnegative
    {w : Q'} (hw : (0 : Q') <= w)
    (base first second half : Nat)
    (source : EdgeLabelling) :
    (0 : Q') <= centralPhysicalConditioningCoreError
      w hw base first second half source := by
  unfold centralPhysicalConditioningCoreError
  exact Q'.zero_le_add _ _
    (centralOldRowCutoffDifferenceL1_nonnegative
      hw base first second half source)
    (Q'.zero_le_add _ _
      (centralOldRowJointTargetShellMass_nonnegative
        hw base first half source)
      (centralOldRowJointTargetShellMass_nonnegative
        hw base second half source))

private theorem asymmetric_error_le_common
    (old firstShell secondShell : Q')
    (hsecondShell0 : (0 : Q') <= secondShell) :
    old + firstShell <= old + (firstShell + secondShell) := by
  exact Q'.add_le_add_left old _ _
    (Q'.add_le_self_of_nonneg firstShell secondShell hsecondShell0)

/-- Fully inhabited pointwise conditioning estimate on an arbitrary moving
positive source core.  The right side contains only the proved old-row `l1`
error, the two proved target shells, and the explicit moving row floor. -/
theorem centralPhysicalMarkovApply_abs_sub_le_conditioningCoreError
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat)
    {sourceBase targetBase first second : Nat}
    (hretained :
      centralPhysicalUniformRowFloorCutoff w half <= sourceBase)
    (hsourceTarget : sourceBase <= targetBase)
    (htargetFirst : targetBase <= first)
    (htargetSecond : targetBase <= second)
    (observable : CentralPhysicalUnitObservable)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0) sourceBase half) :
    Q'.abs
        (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) first half observable.value source +
          -centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) second half observable.value source) <=
      Q'.divPos
        (centralPhysicalConditioningCoreError
              w (Q'.le_of_lt hw0) targetBase first second half source +
          centralPhysicalConditioningCoreError
              w (Q'.le_of_lt hw0) targetBase first second half source)
        (centralPhysicalMovingPositiveRowFloor
          w (Q'.le_of_lt hw0) sourceBase half)
        (centralPhysicalMovingPositiveRowFloor_pos
          w (Q'.le_of_lt hw0) sourceBase half) := by
  let hw := Q'.le_of_lt hw0
  let numeratorFirst := centralPhysicalObservableJointNumerator
    w hw first half observable source
  let numeratorSecond := centralPhysicalObservableJointNumerator
    w hw second half observable source
  let denominatorFirst := centralPhysicalRowMarginal
    w hw first half source
  let denominatorSecond := centralPhysicalRowMarginal
    w hw second half source
  let oldL1 := centralOldRowCutoffDifferenceL1
    w hw targetBase first second half source
  let firstShell := centralOldRowJointTargetShellMass
    w hw targetBase first half source
  let secondShell := centralOldRowJointTargetShellMass
    w hw targetBase second half source
  let commonError := centralPhysicalConditioningCoreError
    w hw targetBase first second half source
  let floor := centralPhysicalMovingPositiveRowFloor w hw sourceBase half
  have hsourceFirstCutoff : sourceBase <= first :=
    Nat.le_trans hsourceTarget htargetFirst
  have hsourceSecondCutoff : sourceBase <= second :=
    Nat.le_trans hsourceTarget htargetSecond
  have hsourceFirst := mem_centralPositiveHalfStates_of_le
    hw hsourceFirstCutoff hsource
  have hsourceSecond := mem_centralPositiveHalfStates_of_le
    hw hsourceSecondCutoff hsource
  have hfirstParts := mem_centralPositiveHalfStates_iff.mp hsourceFirst
  have hsecondParts := mem_centralPositiveHalfStates_iff.mp hsourceSecond
  have hfirstShell0 : (0 : Q') <= firstShell := by
    unfold firstShell
    exact centralOldRowJointTargetShellMass_nonnegative
      hw targetBase first half source
  have hsecondShell0 : (0 : Q') <= secondShell := by
    unfold secondShell
    exact centralOldRowJointTargetShellMass_nonnegative
      hw targetBase second half source
  have hnumeratorAsym :=
    centralPhysicalObservableJointNumerator_twoSided_of_oldRowL1
      (half := half) hw htargetFirst htargetSecond observable source
  have hdenominatorAsym :=
    centralPhysicalRowMarginal_twoSided_of_oldRowL1
      (half := half) hw htargetFirst htargetSecond source
  have hfirstAsymLe : oldL1 + firstShell <= commonError := by
    unfold commonError centralPhysicalConditioningCoreError
    exact asymmetric_error_le_common
      oldL1 firstShell secondShell hsecondShell0
  have hsecondAsymLe : oldL1 + secondShell <= commonError := by
    unfold commonError centralPhysicalConditioningCoreError
    refine Q'.le_trans' _ (oldL1 + (secondShell + firstShell)) _ ?_ ?_
    · exact asymmetric_error_le_common
        oldL1 secondShell firstShell hfirstShell0
    · exact Q'.le_of_eqv
        (Q'.add_eqv_congr_left oldL1 _ _
          (Q'.add_comm_eqv secondShell firstShell))
  have hnumeratorForward :
      numeratorFirst <= numeratorSecond + commonError :=
    Q'.le_trans' _ _ _ hnumeratorAsym.1
      (Q'.add_le_add_left numeratorSecond _ _ hfirstAsymLe)
  have hnumeratorBackward :
      numeratorSecond <= numeratorFirst + commonError :=
    Q'.le_trans' _ _ _ hnumeratorAsym.2
      (Q'.add_le_add_left numeratorFirst _ _ hsecondAsymLe)
  have hdenominatorForward :
      denominatorFirst <= denominatorSecond + commonError :=
    Q'.le_trans' _ _ _ hdenominatorAsym.1
      (Q'.add_le_add_left denominatorSecond _ _ hfirstAsymLe)
  have hdenominatorBackward :
      denominatorSecond <= denominatorFirst + commonError :=
    Q'.le_trans' _ _ _ hdenominatorAsym.2
      (Q'.add_le_add_left denominatorFirst _ _ hsecondAsymLe)
  have hfloorPos : (0 : Q') < floor := by
    unfold floor
    exact centralPhysicalMovingPositiveRowFloor_pos
      w hw sourceBase half
  have hfloorFirst : floor <= denominatorFirst := by
    unfold floor denominatorFirst hw
    exact centralPhysicalMovingPositiveRowFloor_le
      hw0 hw1 half hretained hsourceFirstCutoff hsource
  have hfloorSecond : floor <= denominatorSecond := by
    unfold floor denominatorSecond hw
    exact centralPhysicalMovingPositiveRowFloor_le
      hw0 hw1 half hretained hsourceSecondCutoff hsource
  have hratio := divPos_conditioning_abs_sub_le
    numeratorFirst numeratorSecond denominatorFirst denominatorSecond
    commonError commonError floor
    hfirstParts.2 hsecondParts.2 hfloorPos
    (centralPhysicalObservableJointNumerator_nonnegative
      hw first half observable source)
    (centralPhysicalObservableJointNumerator_nonnegative
      hw second half observable source)
    (centralPhysicalObservableJointNumerator_le_rowMarginal
      hw first half observable source)
    (centralPhysicalObservableJointNumerator_le_rowMarginal
      hw second half observable source)
    hnumeratorForward hnumeratorBackward
    hdenominatorForward hdenominatorBackward
    (centralPhysicalConditioningCoreError_nonnegative
      hw targetBase first second half source)
    (centralPhysicalConditioningCoreError_nonnegative
      hw targetBase first second half source)
    hfloorFirst hfloorSecond
  have hfirstMarkov :=
    centralPhysicalMarkovApply_eq_divPos_observableJointNumerator
      observable hfirstParts.1 hfirstParts.2
  have hsecondMarkov :=
    centralPhysicalMarkovApply_eq_divPos_observableJointNumerator
      observable hsecondParts.1 hsecondParts.2
  have hinside :
      centralPhysicalMarkovApply
            w hw first half observable.value source +
          -centralPhysicalMarkovApply
            w hw second half observable.value source ≈
        Q'.divPos numeratorFirst denominatorFirst hfirstParts.2 +
          -Q'.divPos numeratorSecond denominatorSecond hsecondParts.2 :=
    Q'.add_eqv_congr'
      hfirstMarkov
      (Q'.neg_eqv_congr _ _ hsecondMarkov)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hinside)) hratio

/-- A target shell may be based at any cutoff beyond the executable retained
cutoff.  Its complete new-label mass only decreases when the base is moved
outward, so the original tolerance remains valid. -/
theorem centralOldRowJointTargetShellMass_le_of_scheduled_base
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {base later : Nat}
    (hscheduled :
      centralPhysicalTargetShellCutoff w half epsilon <= base)
    (hbaseLater : base <= later)
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates base half) :
    centralOldRowJointTargetShellMass
        w (Q'.le_of_lt hw0) base later half source <= epsilon := by
  have hshell := centralOldRowJointTargetShellMass_le_increment
    (Q'.le_of_lt hw0) hbaseLater hsource
  have hincrementMono := slabParametricKCutoffIncrement_antitone_base
    (extent := centralExtent half)
    (Q'.le_of_lt hw0) hscheduled hbaseLater
  have hscheduledLater :
      centralPhysicalTargetShellCutoff w half epsilon <= later :=
    Nat.le_trans hscheduled hbaseLater
  have htolerance :
      slabParametricKCutoffIncrement
          w (centralPhysicalTargetShellCutoff w half epsilon)
          later (centralExtent half) <= epsilon := by
    unfold centralPhysicalTargetShellCutoff
    exact slabPhysicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 (centralExtent half) hepsilon hscheduledLater
  exact Q'.le_trans' _ _ _ hshell
    (Q'.le_trans' _ _ _ hincrementMono htolerance)

/-! ## Axiom audit -/

#print axioms centralPhysicalObservableJointNumerator
#print axioms centralPhysicalMarkovApply_eq_divPos_observableJointNumerator
#print axioms centralPhysicalObservableJointNumerator_eq_old_add_targetShell
#print axioms centralOldRowObservableTargetShellMass_le_jointShell
#print axioms centralOldRowObservableNumerator_abs_sub_le_l1
#print axioms centralPhysicalObservableJointNumerator_twoSided_of_oldRowL1
#print axioms centralPhysicalConditioningCoreError
#print axioms centralPhysicalMarkovApply_abs_sub_le_conditioningCoreError
#print axioms centralOldRowJointTargetShellMass_le_of_scheduled_base

end YMGap.Continuum.BF4PhysicalCutoffConditionalCoreCauchy
