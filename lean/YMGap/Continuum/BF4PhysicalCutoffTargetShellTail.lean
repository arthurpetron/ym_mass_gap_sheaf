/-
# Target-shell tail for one physical BF4 source row

The conditional-kernel reduction leaves the normalized joint mass in targets
that enter beyond a fixed old representation carrier.  This file identifies
that mass with one literal corrected-slab Boolean event: the lower restriction
equals the selected source while the reflected upper restriction lies outside
the old carrier.

At the old cutoff the event is empty.  At every later cutoff its expectation
is therefore bounded by the complete corrected-slab new-label increment.  The
existing arbitrary-nome degree-thirteen schedule then supplies an executable,
source-uniform target-shell modulus.

This controls the target shell only.  The stationary source-shell estimate and
the quantitative denominator floor needed by the completed Markov compiler
remain separate obligations.

## Axiom gate

Only finite-list recoding, exact rational algebra, and the proved corrected-
slab cutoff tail are used.  There is no classical choice, noncomputable
declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination

namespace YMGap.Continuum.BF4PhysicalCutoffTargetShellTail

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One aggregate source/target-shell cylinder -/

/-- The lower restriction is the selected source and the reflected upper
restriction lies outside representation carrier `base`. -/
def centralSourceTargetShellB
    (base half : Nat) (source physical : EdgeLabelling) : Bool :=
  labellingsAgreeOnB
      (centralLowerFaceIds half)
      (centralLowerRestriction half physical) source &&
    !(labelWithinB base
      (centralLowerFaceIds half)
      (centralReflectedUpperRestriction half physical))

def centralSourceTargetShellIndicator
    (base half : Nat) (source physical : EdgeLabelling) : Q' :=
  if centralSourceTargetShellB base half source physical then 1 else 0

/-- The aggregate shell event is a cutoff-stable unit observable. -/
def centralSourceTargetShellObservable
    (base half : Nat) (source : EdgeLabelling) :
    CutoffStableSlabUnitObservable (centralExtent half) where
  value := fun _cutoff physical =>
    centralSourceTargetShellIndicator base half source physical
  nonnegative := by
    intro _cutoff physical _
    unfold centralSourceTargetShellIndicator
    cases centralSourceTargetShellB base half source physical <;> decide
  le_one := by
    intro _cutoff physical _
    unfold centralSourceTargetShellIndicator
    cases centralSourceTargetShellB base half source physical <;> decide
  cutoff_stable := by
    intro _K _L _physical _ _
    exact Q'.eqv_refl _

private theorem centralSourceTargetShellIndicator_assembled
    {K base half : Nat}
    {source left right boundary : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralSourceTargetShellIndicator base half source
        (assembleReflectedSlabLabelling
          half left boundary right) =
      if labellingsAgreeOnB
            (centralLowerFaceIds half) left source &&
          !(labelWithinB base
            (centralLowerFaceIds half) right)
      then 1 else 0 := by
  unfold centralSourceTargetShellIndicator
    centralSourceTargetShellB
  rw [centralLowerRestriction_assemble hleft,
    centralReflectedUpperRestriction_assemble hright]

/-! ## 2. Finite selector and aggregate-cylinder identity -/

private theorem listQSum_unique_bool_local
    {A : Type} (predicate : A -> Bool)
    (value : A -> Q') (target : A) :
    forall items : List A,
      items.Nodup ->
      target ∈ items ->
      predicate target = true ->
      (forall item, item ∈ items ->
        predicate item = true -> item = target) ->
      listQSum
          (fun item => if predicate item then value item else 0)
          items ≈ value target
  | [], _, htarget, _, _ => absurd htarget List.not_mem_nil
  | head :: tail, hnodup, htarget, htargetTrue, hunique => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp htarget with htargetHead | htargetTail
      · subst target
        simp only [listQSum, htargetTrue, if_true]
        refine Q'.eqv_trans _ (value head + 0) _
          (Q'.add_eqv_congr_left _ _ _ ?_)
          (Q'.eqv_of_eq (Q'.add_zero' _))
        refine Q'.eqv_trans _
          (listQSum (fun _ => (0 : Q')) tail) _
          ?_ (listQSum_zero _)
        apply listQSum_congr_on
        intro item hitem
        have hfalse : predicate item = false := by
          cases hp : predicate item with
          | false => rfl
          | true =>
              have heq := hunique item
                (List.mem_cons_of_mem head hitem) hp
              subst item
              exact absurd hitem hparts.1
        simp only [hfalse]
        exact Q'.eqv_refl 0
      · have hheadFalse : predicate head = false := by
          cases hp : predicate head with
          | false => rfl
          | true =>
              have heq := hunique head List.mem_cons_self hp
              subst target
              exact absurd htargetTail hparts.1
        simp only [listQSum, hheadFalse]
        exact Q'.eqv_trans _ _ _
          (QPoly.q_zero_add_eqv _)
          (listQSum_unique_bool_local
            predicate value target tail
            hparts.2 htargetTail htargetTrue
            (fun item hitem hp =>
              hunique item
                (List.mem_cons_of_mem head hitem) hp))

theorem listQSum_left_selector_right_filter
    {A B C : Type}
    (leftItems : List A) (rightItems : List B)
    (channels : List C)
    (leftPredicate : A -> Bool)
    (rightPredicate : B -> Bool)
    (term : A -> B -> C -> Q')
    (selectedLeft : A)
    (leftNodup : leftItems.Nodup)
    (selectedLeftMem : selectedLeft ∈ leftItems)
    (selectedLeftTrue : leftPredicate selectedLeft = true)
    (leftUnique : forall item, item ∈ leftItems ->
      leftPredicate item = true -> item = selectedLeft) :
    listQSum
        (fun triple =>
          if leftPredicate triple.1 &&
              rightPredicate triple.2.1
          then term triple.1 triple.2.1 triple.2.2
          else 0)
        (leftItems.flatMap
          (fun left =>
            rightItems.flatMap
              (fun right =>
                channels.map
                  (fun channel =>
                    (left, (right, channel)))))) ≈
      listQSum
        (fun right =>
          listQSum (term selectedLeft right) channels)
        (rightItems.filter rightPredicate) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            if leftPredicate left && rightPredicate right
            then listQSum (term left right) channels
            else 0)
          rightItems)
      leftItems) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_flatMap _ _ _) ?_
    apply listQSum_congr
    intro left
    refine Q'.eqv_trans _ _ _
      (listQSum_flatMap _ _ _) ?_
    apply listQSum_congr
    intro right
    rw [listQSum_map]
    cases hselected :
        leftPredicate left && rightPredicate right
    · simp only [hselected, Bool.false_eq_true, if_false]
      exact listQSum_zero _
    · simp only [hselected, if_true]
      exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          if leftPredicate left then
            listQSum
              (finiteMaskedValue rightPredicate
                (fun right => listQSum (term left right) channels))
              rightItems
          else 0)
        leftItems) _ ?_ ?_
    · apply listQSum_congr
      intro left
      cases hleft : leftPredicate left
      · simp only [Bool.false_and,
          Bool.false_eq_true, if_false]
        exact listQSum_zero _
      · simp only [Bool.true_and, if_true]
        exact Q'.eqv_refl _
    · refine Q'.eqv_trans _
        (listQSum
          (finiteMaskedValue rightPredicate
            (fun right =>
              listQSum (term selectedLeft right) channels))
          rightItems) _ ?_ ?_
      · exact listQSum_unique_bool_local
          leftPredicate
          (fun left =>
            listQSum
              (finiteMaskedValue rightPredicate
                (fun right => listQSum (term left right) channels))
              rightItems)
          selectedLeft leftItems leftNodup
          selectedLeftMem selectedLeftTrue leftUnique
      · exact listQSum_finiteMaskedValue_eqv_filter
          rightPredicate
          (fun right =>
            listQSum (term selectedLeft right) channels)
          rightItems

private theorem assembledSourceTargetShellNumerator_eq_rawShell
    {w : Q'} {K base half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    listQSum
        (fun physical =>
          centralSourceTargetShellIndicator
              base half source physical *
            slabParametricKPhysicalTerm
              w K (centralExtent half) physical)
        (centralAssembledSlabLabellings K half) ≈
      listQSum
        (centralPhysicalReflectedKernel w K half source)
        ((centralHalfStates K half).filter
          (fun target =>
            !(labelWithinB base
              (centralLowerFaceIds half) target))) := by
  let leftPredicate : EdgeLabelling -> Bool :=
    fun left => labellingsAgreeOnB
      (centralLowerFaceIds half) left source
  let rightPredicate : EdgeLabelling -> Bool :=
    fun right => !(labelWithinB base
      (centralLowerFaceIds half) right)
  let term : EdgeLabelling -> EdgeLabelling ->
      EdgeLabelling -> Q' :=
    fun left right boundary =>
      slabParametricKPhysicalTerm
        w K (centralExtent half)
        (assembleReflectedSlabLabelling
          half left boundary right)
  unfold centralAssembledSlabLabellings
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun triple =>
        if leftPredicate triple.1 &&
            rightPredicate triple.2.1
        then term triple.1 triple.2.1 triple.2.2
        else 0)
      (centralReflectionTriples K half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro triple htriple
    have hparts := mem_centralReflectionTriples.mp htriple
    unfold assembleCentralReflectionTriple
    rw [centralSourceTargetShellIndicator_assembled
      hparts.1 hparts.2.1]
    dsimp only [leftPredicate, rightPredicate, term]
    cases hselected :
        labellingsAgreeOnB
            (centralLowerFaceIds half) triple.1 source &&
          !(labelWithinB base
            (centralLowerFaceIds half) triple.2.1)
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.zero_mul_eqv _
    · simp only [if_true]
      exact Q'.one_mul_eqv _
  · unfold centralReflectionTriples
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          listQSum (term source target)
            (centralBoundaryChannels K half))
        ((centralHalfStates K half).filter rightPredicate)) _ ?_ ?_
    · exact listQSum_left_selector_right_filter
        (centralHalfStates K half)
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        leftPredicate rightPredicate term source
        (centralHalfStates_nodup K half)
        hsource
        (labellingsAgreeOnB_self
          (centralLowerFaceIds half) source)
        (fun left hleft hagree =>
          eq_of_labellingsAgreeOnB_of_bounded
            hleft hsource hagree)
    · apply listQSum_congr
      intro target
      exact Q'.eqv_refl _

/-- The aggregate shell-event numerator is exactly the sum of unnormalized
reflected-kernel entries in the target shell. -/
theorem centralSourceTargetShellNumerator_eq_rawShell
    {w : Q'} {K base half : Nat}
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    slabBoundedObservableNumerator
        w K (centralExtent half)
        (centralSourceTargetShellObservable
          base half source) ≈
      listQSum
        (centralPhysicalReflectedKernel w K half source)
        ((centralHalfStates K half).filter
          (fun target =>
            !(labelWithinB base
              (centralLowerFaceIds half) target))) := by
  unfold slabBoundedObservableNumerator
    centralSourceTargetShellObservable
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_centralAssembledSlabLabellings
        (fun physical =>
          centralSourceTargetShellIndicator
              base half source physical *
            slabParametricKPhysicalTerm
              w K (centralExtent half) physical)
        K half))
    (assembledSourceTargetShellNumerator_eq_rawShell hsource)

/-- The normalized aggregate event is exactly the target-shell mass used by
the conditional-core reduction. -/
theorem centralOldRowJointTargetShellMass_eq_expectation
    {w : Q'} (hw : (0 : Q') <= w)
    {K base half : Nat} {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    centralOldRowJointTargetShellMass
        w hw base K half source ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw K (centralExtent half)
        (centralSourceTargetShellObservable
          base half source) := by
  have hpartition :
      (0 : Q') < slabParametricKPhysicalPartition
        w K (centralExtent half) :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  have hnumerator :=
    centralSourceTargetShellNumerator_eq_rawShell
      (w := w) (base := base) hsource
  unfold centralOldRowJointTargetShellMass
    centralNormalizedPhysicalReflectedKernel
    slabNomeCutoffBoundedObservableExpectation Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
        (centralPhysicalReflectedKernel w K half source)
        ((centralHalfStates K half).filter
          (fun target =>
            !(labelWithinB base
              (centralLowerFaceIds half) target))) *
      Q'.recipPos
        (slabParametricKPhysicalPartition
          w K (centralExtent half)) hpartition) _
    (listQSum_mul_right
      (centralPhysicalReflectedKernel w K half source)
      (Q'.recipPos
        (slabParametricKPhysicalPartition
          w K (centralExtent half)) hpartition)
      ((centralHalfStates K half).filter
        (fun target =>
          !(labelWithinB base
            (centralLowerFaceIds half) target)))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm hnumerator)

/-! ## 3. Empty anchor shell and the scheduled tail -/

private theorem filter_not_true_empty_local
    {A : Type} (test : A -> Bool) :
    forall items : List A,
      (forall item, item ∈ items -> test item = true) ->
      items.filter (fun item => !(test item)) = []
  | [], _ => rfl
  | head :: tail, htrue => by
      have hhead := htrue head List.mem_cons_self
      have htail : forall item, item ∈ tail -> test item = true :=
        fun item hitem =>
          htrue item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead, Bool.not_true,
        Bool.false_eq_true, if_false]
      exact filter_not_true_empty_local test tail htail

private theorem centralTargetShell_filter_self_empty
    (K half : Nat) :
    (centralHalfStates K half).filter
        (fun target =>
          !(labelWithinB K
            (centralLowerFaceIds half) target)) = [] := by
  apply filter_not_true_empty_local
  intro state hstate
  apply (labelWithinB_true_iff
    K (centralLowerFaceIds half) state).mpr
  unfold centralHalfStates at hstate
  exact (boundedEdgeLabellings_sound
    K (centralLowerFaceIds half) state hstate).1

theorem centralOldRowJointTargetShellMass_self_eqv_zero
    {w : Q'} (hw : (0 : Q') <= w)
    (K half : Nat) (source : EdgeLabelling) :
    centralOldRowJointTargetShellMass
        w hw K K half source ≈ 0 := by
  unfold centralOldRowJointTargetShellMass
  rw [centralTargetShell_filter_self_empty]
  exact Q'.eqv_refl 0

/-- At any later cutoff, the target shell of a fixed source is bounded by the
complete corrected-slab new-label increment beyond the old cutoff. -/
theorem centralOldRowJointTargetShellMass_le_increment
    {w : Q'} (hw : (0 : Q') <= w)
    {base later half : Nat} (hcutoff : base <= later)
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates base half) :
    centralOldRowJointTargetShellMass
        w hw base later half source <=
      slabParametricKCutoffIncrement
        w base later (centralExtent half) := by
  have hsourceLater :
      source ∈ centralHalfStates later half := by
    unfold centralHalfStates at hsource ⊢
    have hsound := boundedEdgeLabellings_sound
      base (centralLowerFaceIds half) source hsource
    apply boundedEdgeLabellings_complete
    · intro edge hedge
      have hbound := hsound.1 edge hedge
      omega
    · exact hsound.2
  let observable :=
    centralSourceTargetShellObservable base half source
  have habs :=
    slabNomeCutoffBoundedObservableExpectation_abs_le_increment
      hw hcutoff observable
  have hbaseEq :=
    centralOldRowJointTargetShellMass_eq_expectation
      (K := base) (base := base) (half := half)
      (source := source) hw hsource
  have hlaterEq :=
    centralOldRowJointTargetShellMass_eq_expectation
      (K := later) (base := base) (half := half)
      (source := source) hw hsourceLater
  have hzero :=
    centralOldRowJointTargetShellMass_self_eqv_zero
      hw base half source
  have hbaseExpectationZero :
      slabNomeCutoffBoundedObservableExpectation
          w hw base (centralExtent half) observable ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm hbaseEq) hzero
  have habsQ :
      Q'.abs
          (slabNomeCutoffBoundedObservableExpectation
              w hw base (centralExtent half) observable +
            -slabNomeCutoffBoundedObservableExpectation
              w hw later (centralExtent half) observable) <=
        slabParametricKCutoffIncrement
          w base later (centralExtent half) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs _)))
      habs
  have hlaterLe :
      slabNomeCutoffBoundedObservableExpectation
          w hw later (centralExtent half) observable <=
        slabNomeCutoffBoundedObservableExpectation
            w hw base (centralExtent half) observable +
          slabParametricKCutoffIncrement
            w base later (centralExtent half) := by
    apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm _ _))
      habsQ
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv hlaterEq) ?_
  refine Q'.le_trans' _ _ _ hlaterLe ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hbaseExpectationZero)
      (QPoly.q_zero_add_eqv _))

/-- The executable retained cutoff that pays target-shell tolerance
`epsilon` at fixed nome and half-extent. -/
def centralPhysicalTargetShellCutoff
    (w : Q') (half : Nat) (epsilon : Q') : Nat :=
  physicalNomeTensorToleranceRetainedCutoff
    w
    (plaquetteEdgeCount (centralExtent half + 1))
    epsilon

/-- Uniform scheduled target-shell bound for every source already carried by
the retained cutoff. -/
theorem centralOldRowJointTargetShellMass_le_of_cutoff
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon)
    {later : Nat}
    (hlater :
      centralPhysicalTargetShellCutoff
          w half epsilon <= later)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralHalfStates
        (centralPhysicalTargetShellCutoff
          w half epsilon) half) :
    centralOldRowJointTargetShellMass
        w (Q'.le_of_lt hw0)
        (centralPhysicalTargetShellCutoff w half epsilon)
        later half source <= epsilon := by
  refine Q'.le_trans' _ _ _
    (centralOldRowJointTargetShellMass_le_increment
      (Q'.le_of_lt hw0) hlater hsource) ?_
  exact slabPhysicalNomeCutoffIncrement_le_tolerance
    hw0 hw1 (centralExtent half) hepsilon hlater

/-! ## Axiom audit -/

#print axioms centralSourceTargetShellObservable
#print axioms centralSourceTargetShellNumerator_eq_rawShell
#print axioms centralOldRowJointTargetShellMass_eq_expectation
#print axioms centralOldRowJointTargetShellMass_le_increment
#print axioms centralPhysicalTargetShellCutoff
#print axioms centralOldRowJointTargetShellMass_le_of_cutoff

end YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
