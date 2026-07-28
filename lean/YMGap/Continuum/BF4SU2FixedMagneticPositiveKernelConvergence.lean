/-
# Positive-kernel convergence for the genuine BF4 reflected Choi carrier

The magnetically enlarged fixed-plane carrier gives an exact Choi
disintegration of the corrected-slab reflection kernel.  This module
connects each entry of that kernel to the already-completed arbitrary-nome
outer-cutoff theory.

For fixed lower labels `left` and `right`, the corresponding full-slab
cylinder event asks that the lower restriction equal `left` and the
reflected upper restriction equal `right`.  Its indicator is independent of
the representation cutoff and lies in `[0,1]`.  Exact lower/fixed/upper
reindexing proves

    cylinder numerator = centralPhysicalReflectedKernel left right.

Consequently the partition-normalized physical Choi entry is literally the
expectation of a cutoff-stable Yang--Mills cylinder event.  The existing
degree-thirteen incidence/Fubini envelope therefore supplies an executable
Cauchy modulus for every such entry at every rational nome `0 < w < 1`.
That degree already pays the complete link-intertwiner growth; the magnetic
fiber is the heat-kernel dimension factor which raises degree twelve to
degree thirteen.

Honest scope: this is positive-kernel convergence in the representation
cutoff at fixed finite slab extent and fixed nome.  It does not identify the
limit with a Gaussian Mehler operator, make the modulus uniform as `w → 1`,
or construct the continuum mean-zero Perron mode.

## Axiom gate

Finite list recursion and exact `Q'` order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
import YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail

namespace YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite equality tests for supported labellings -/

/-- Equality of two edge labellings on a displayed finite face list. -/
def labellingsAgreeOnB
    (ids : List Nat) (left right : EdgeLabelling) : Bool :=
  ids.all (fun id => decide (left id = right id))

theorem labellingsAgreeOnB_true_iff
    (ids : List Nat) (left right : EdgeLabelling) :
    labellingsAgreeOnB ids left right = true ↔
      ∀ id, id ∈ ids → left id = right id := by
  unfold labellingsAgreeOnB
  rw [List.all_eq_true]
  constructor
  · intro hagree id hid
    have hdecision := hagree id hid
    simpa only [decide_eq_true_eq] using hdecision
  · intro hagree id hid
    simpa only [decide_eq_true_eq] using hagree id hid

theorem labellingsAgreeOnB_self
    (ids : List Nat) (label : EdgeLabelling) :
    labellingsAgreeOnB ids label label = true := by
  apply (labellingsAgreeOnB_true_iff ids label label).2
  intro id _
  rfl

/-- On the zero-extended bounded carrier, finite coordinate agreement is
actual equality of edge-labelling functions. -/
theorem eq_of_labellingsAgreeOnB_of_bounded
    {K : Nat} {ids : List Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K ids)
    (hright : right ∈ boundedEdgeLabellings K ids)
    (hagree :
      labellingsAgreeOnB ids left right = true) :
    left = right := by
  have hleftSound :=
    (boundedEdgeLabellings_sound K ids left hleft).2
  have hrightSound :=
    (boundedEdgeLabellings_sound K ids right hright).2
  have hon :=
    (labellingsAgreeOnB_true_iff ids left right).1 hagree
  funext id
  by_cases hid : id ∈ ids
  · exact hon id hid
  · rw [hleftSound id hid, hrightSound id hid]

private theorem listQSum_unique_bool
    {A : Type} (predicate : A → Bool)
    (value : A → Q') (target : A) :
    ∀ items : List A,
      items.Nodup →
      target ∈ items →
      predicate target = true →
      (∀ item, item ∈ items →
        predicate item = true → item = target) →
      listQSum
          (fun item =>
            if predicate item then value item else 0)
          items ≈
        value target
  | [], _, htarget, _, _ =>
      absurd htarget List.not_mem_nil
  | head :: tail, hnodup, htarget, htargetTrue, hunique => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp htarget with htargetHead | htargetTail
      · subst target
        simp only [listQSum, htargetTrue, if_true]
        refine Q'.eqv_trans _
          (value head + 0) _
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
              have heq :=
                hunique item
                  (List.mem_cons_of_mem head
                    hitem) hp
              subst item
              exact absurd hitem hparts.1
        simp only [hfalse]
        exact Q'.eqv_refl 0
      · have hheadFalse : predicate head = false := by
          cases hp : predicate head with
          | false => rfl
          | true =>
              have heq :=
                hunique head List.mem_cons_self hp
              subst target
              exact absurd htargetTail hparts.1
        simp only [listQSum, hheadFalse]
        exact Q'.eqv_trans _ _ _
          (QPoly.q_zero_add_eqv _)
          (listQSum_unique_bool
            predicate value target tail
            hparts.2 htargetTail htargetTrue
            (fun item hitem hp =>
              hunique item
                (List.mem_cons_of_mem head hitem) hp))

/-! ## 2. The exact lower/reflected-upper cylinder observable -/

/-- Boolean cylinder selecting one lower state and one reflected upper
state.  Only finitely many physical face coordinates are inspected. -/
def centralPairCylinderB
    (half : Nat) (left right physical : EdgeLabelling) : Bool :=
  labellingsAgreeOnB
      (centralLowerFaceIds half)
      (centralLowerRestriction half physical) left &&
    labellingsAgreeOnB
      (centralLowerFaceIds half)
      (centralReflectedUpperRestriction half physical) right

/-- Rational indicator of the selected reflected cylinder. -/
def centralPairCylinderIndicator
    (half : Nat) (left right physical : EdgeLabelling) : Q' :=
  if centralPairCylinderB half left right physical then 1 else 0

/-- The cylinder indicator is a cutoff-stable `[0,1]` corrected-slab
observable. -/
def centralPairCylinderObservable
    (half : Nat) (left right : EdgeLabelling) :
    CutoffStableSlabUnitObservable (centralExtent half) where
  value := fun _cutoff physical =>
    centralPairCylinderIndicator half left right physical
  nonnegative := by
    intro _cutoff physical _
    unfold centralPairCylinderIndicator
    cases centralPairCylinderB half left right physical <;> decide
  le_one := by
    intro _cutoff physical _
    unfold centralPairCylinderIndicator
    cases centralPairCylinderB half left right physical <;> decide
  cutoff_stable := by
    intro _K _L _physical _ _
    exact Q'.eqv_refl _

private theorem centralPairCylinderIndicator_assembled
    {K half : Nat}
    {left right lower upper boundary : EdgeLabelling}
    (hlower :
      lower ∈ centralHalfStates K half)
    (hupper :
      upper ∈ centralHalfStates K half) :
    centralPairCylinderIndicator half left right
        (assembleReflectedSlabLabelling
          half lower boundary upper) =
      if labellingsAgreeOnB
            (centralLowerFaceIds half) lower left &&
          labellingsAgreeOnB
            (centralLowerFaceIds half) upper right
      then 1 else 0 := by
  unfold centralPairCylinderIndicator centralPairCylinderB
  rw [centralLowerRestriction_assemble hlower,
    centralReflectedUpperRestriction_assemble hupper]

private theorem listQSum_two_coordinate_selector
    {A B C : Type}
    (leftItems : List A) (rightItems : List B)
    (channels : List C)
    (leftPredicate : A → Bool)
    (rightPredicate : B → Bool)
    (term : A → B → C → Q')
    (selectedLeft : A) (selectedRight : B)
    (leftNodup : leftItems.Nodup)
    (rightNodup : rightItems.Nodup)
    (selectedLeftMem : selectedLeft ∈ leftItems)
    (selectedRightMem : selectedRight ∈ rightItems)
    (selectedLeftTrue :
      leftPredicate selectedLeft = true)
    (selectedRightTrue :
      rightPredicate selectedRight = true)
    (leftUnique :
      ∀ item, item ∈ leftItems →
        leftPredicate item = true →
        item = selectedLeft)
    (rightUnique :
      ∀ item, item ∈ rightItems →
        rightPredicate item = true →
        item = selectedRight) :
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
        (term selectedLeft selectedRight) channels := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            if leftPredicate left &&
                rightPredicate right
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
        leftPredicate left &&
          rightPredicate right
    · simp only [hselected, Bool.false_eq_true, if_false]
      exact listQSum_zero _
    · simp only [hselected, if_true]
      exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          if leftPredicate left then
            listQSum
              (term left selectedRight)
              channels
          else 0)
        leftItems) _ ?_ ?_
    · apply listQSum_congr
      intro left
      cases hleft : leftPredicate left
      · simp only [Bool.false_and]
        exact listQSum_zero _
      · simp only [Bool.true_and, if_true]
        exact listQSum_unique_bool
          rightPredicate
          (fun right =>
            listQSum (term left right) channels)
          selectedRight rightItems
          rightNodup selectedRightMem
          selectedRightTrue rightUnique
    · exact listQSum_unique_bool
        leftPredicate
        (fun left =>
          listQSum
            (term left selectedRight)
            channels)
        selectedLeft leftItems
        leftNodup selectedLeftMem
        selectedLeftTrue leftUnique

private theorem assembledCylinderNumerator_eq_kernel
    {w : Q'} {K half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    listQSum
        (fun physical =>
          centralPairCylinderIndicator
              half left right physical *
            slabParametricKPhysicalTerm
              w K (centralExtent half) physical)
        (centralAssembledSlabLabellings K half) ≈
      centralPhysicalReflectedKernel
        w K half left right := by
  let leftPredicate : EdgeLabelling → Bool :=
    fun lower =>
      labellingsAgreeOnB
        (centralLowerFaceIds half) lower left
  let rightPredicate : EdgeLabelling → Bool :=
    fun upper =>
      labellingsAgreeOnB
        (centralLowerFaceIds half) upper right
  let term :
      EdgeLabelling → EdgeLabelling →
        EdgeLabelling → Q' :=
    fun lower upper boundary =>
      slabParametricKPhysicalTerm
        w K (centralExtent half)
        (assembleReflectedSlabLabelling
          half lower boundary upper)
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
    have hparts :=
      mem_centralReflectionTriples.mp htriple
    unfold assembleCentralReflectionTriple
    rw [centralPairCylinderIndicator_assembled
      hparts.1 hparts.2.1]
    dsimp only [leftPredicate, rightPredicate, term,
      assembleCentralReflectionTriple]
    cases hselected :
        labellingsAgreeOnB
            (centralLowerFaceIds half) triple.1 left &&
          labellingsAgreeOnB
            (centralLowerFaceIds half) triple.2.1 right
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.zero_mul_eqv _
    · simp only [if_true]
      exact Q'.one_mul_eqv _
  · refine Q'.eqv_trans _
      (listQSum (term left right)
        (centralBoundaryChannels K half)) _ ?_ ?_
    · unfold centralReflectionTriples
      exact listQSum_two_coordinate_selector
        (centralHalfStates K half)
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        leftPredicate rightPredicate term
        left right
        (centralHalfStates_nodup K half)
        (centralHalfStates_nodup K half)
        hleft hright
        (labellingsAgreeOnB_self
          (centralLowerFaceIds half) left)
        (labellingsAgreeOnB_self
          (centralLowerFaceIds half) right)
        (fun lower hlower hmatch =>
          eq_of_labellingsAgreeOnB_of_bounded
            hlower hleft hmatch)
        (fun upper hupper hmatch =>
          eq_of_labellingsAgreeOnB_of_bounded
            hupper hright hmatch)
    · unfold centralPhysicalReflectedKernel term
      exact Q'.eqv_refl _

/-- **Exact Yang--Mills cylinder identification.**  The unnormalized
cutoff-stable lower/reflected-upper cylinder numerator is the genuine
grouped BF4 reflected-kernel entry, and hence also the magnetically enlarged
Choi entry. -/
theorem centralPairCylinderNumerator_eq_physicalKernel
    {w : Q'} {K half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    slabBoundedObservableNumerator
        w K (centralExtent half)
        (centralPairCylinderObservable half left right) ≈
      centralPhysicalReflectedKernel
        w K half left right := by
  unfold slabBoundedObservableNumerator
    centralPairCylinderObservable
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_centralAssembledSlabLabellings
        (fun physical =>
          centralPairCylinderIndicator half left right physical *
            slabParametricKPhysicalTerm
              w K (centralExtent half) physical)
        K half))
    (assembledCylinderNumerator_eq_kernel
      hleft hright)

/-! ## 3. Partition-normalized positive kernel and its cutoff modulus -/

/-- Partition-normalized entry of the genuine reflected physical kernel. -/
def centralNormalizedPhysicalReflectedKernel
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (left right : EdgeLabelling) : Q' :=
  Q'.divPos
    (centralPhysicalReflectedKernel
      w K half left right)
    (slabParametricKPhysicalPartition
      w K (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw K (centralExtent half))

/-- The normalized kernel entry is exactly the expectation of the
cutoff-stable cylinder observable. -/
theorem centralNormalizedPhysicalReflectedKernel_eq_expectation
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {left right : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half)
    (hright : right ∈ centralHalfStates K half) :
    centralNormalizedPhysicalReflectedKernel
        w hw K half left right ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw K (centralExtent half)
        (centralPairCylinderObservable
          half left right) := by
  unfold centralNormalizedPhysicalReflectedKernel
    slabNomeCutoffBoundedObservableExpectation
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (centralPairCylinderNumerator_eq_physicalKernel
        hleft hright))

/-- Every two representation cutoffs beyond the executable degree-thirteen
modulus give two-sided `ε`-close entries of the genuine normalized physical
kernel.  The fixed labels are supplied as members of both displayed
cutoff carriers. -/
theorem centralNormalizedPhysicalReflectedKernel_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : EdgeLabelling)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      slabNomeBoundedObservableModulus
          w (centralExtent half) ε ≤ first)
    (hsecond :
      slabNomeBoundedObservableModulus
          w (centralExtent half) ε ≤ second)
    (hleftFirst :
      left ∈ centralHalfStates first half)
    (hrightFirst :
      right ∈ centralHalfStates first half)
    (hleftSecond :
      left ∈ centralHalfStates second half)
    (hrightSecond :
      right ∈ centralHalfStates second half) :
    centralNormalizedPhysicalReflectedKernel
          w (Q'.le_of_lt hw0)
          first half left right ≤
        centralNormalizedPhysicalReflectedKernel
            w (Q'.le_of_lt hw0)
            second half left right + ε ∧
      centralNormalizedPhysicalReflectedKernel
          w (Q'.le_of_lt hw0)
          second half left right ≤
        centralNormalizedPhysicalReflectedKernel
            w (Q'.le_of_lt hw0)
            first half left right + ε := by
  have hconvergence :=
    slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
      hw0 hw1
      (centralExtent half)
      (centralPairCylinderObservable
        half left right)
      hε hfirst hsecond
  have hfirstEq :=
    centralNormalizedPhysicalReflectedKernel_eq_expectation
      (w := w) (hw := Q'.le_of_lt hw0)
      hleftFirst hrightFirst
  have hsecondEq :=
    centralNormalizedPhysicalReflectedKernel_eq_expectation
      (w := w) (hw := Q'.le_of_lt hw0)
      hleftSecond hrightSecond
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hfirstEq)
      (Q'.le_trans' _ _ _
        hconvergence.1
        (Q'.add_le_add_right _ _ ε
          (Q'.le_of_eqv
            (Q'.eqv_symm hsecondEq))))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hsecondEq)
      (Q'.le_trans' _ _ _
        hconvergence.2
        (Q'.add_le_add_right _ _ ε
          (Q'.le_of_eqv
            (Q'.eqv_symm hfirstEq))))

#print axioms labellingsAgreeOnB_true_iff
#print axioms eq_of_labellingsAgreeOnB_of_bounded
#print axioms centralPairCylinderObservable
#print axioms centralPairCylinderNumerator_eq_physicalKernel
#print axioms centralNormalizedPhysicalReflectedKernel_eq_expectation
#print axioms
  centralNormalizedPhysicalReflectedKernel_twoSided_of_modulus

end YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
