/-
# Positive-row persistence for the physical BF4 cutoff

The atomic Markov core is the finite carrier on which the source row has
positive normalized mass.  This file proves that membership in that positive
carrier persists whenever the Peter--Weyl representation cutoff is enlarged.

The proof is literal and constructive.  A positive finite row contains a
positive target entry.  Multiplication by the positive partition shows that
the corresponding unnormalized reflected-kernel entry is positive.  Its
cutoff-stable cylinder numerator is retained exactly at every larger cutoff
and receives only a nonnegative new-label increment.  The later positive
partition then gives a positive normalized entry and hence a positive later
row.

This is positivity, not a uniform quantitative lower bound.  It therefore
closes every later `divPos` guard on the old positive carrier, but does not by
itself control the inverse denominator uniformly in the cutoff.

## Axiom gate

Only finite-list induction, exact rational order/algebra, and the existing
corrected-slab numerator decomposition are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction

namespace YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) :
    q <= 0 := by
  show q.num * (1 : Int) <= (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- A positive finite rational sum contains a positive summand.  The witness
is obtained by structural recursion on the list; no choice principle is
used. -/
private theorem exists_mem_pos_of_listQSum_pos
    {A : Type} (value : A -> Q') :
    forall items : List A,
      (0 : Q') < listQSum value items ->
        Exists fun item =>
          item ∈ items ∧ (0 : Q') < value item
  | [], hsum => by
      have hnum := Q'.num_pos_of_pos hsum
      simp only [listQSum] at hnum
      exact False.elim (Int.lt_irrefl 0 hnum)
  | head :: tail, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact Exists.intro head
          ⟨List.mem_cons_self, hhead⟩
      · have hheadLe : value head <= 0 :=
          q_nonpos_of_not_pos_local hhead
        have hsumLe :
            value head + listQSum value tail <=
              listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (value head) 0 (listQSum value tail) hheadLe
          simpa only [Q'.zero_add'] using hadd
        have htail :
            (0 : Q') < listQSum value tail := by
          change (0 : Q') <
            value head + listQSum value tail at hsum
          exact Q'.pos_of_lt_of_le hsum hsumLe
        rcases exists_mem_pos_of_listQSum_pos
            value tail htail with
          ⟨item, hitem, hitemPos⟩
        exact Exists.intro item
          ⟨List.mem_cons_of_mem head hitem, hitemPos⟩

private theorem centralHalfStates_mem_of_le_local
    {base later half : Nat}
    (hcutoff : base <= later)
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates base half) :
    state ∈ centralHalfStates later half := by
  unfold centralHalfStates at hstate ⊢
  have hsound := boundedEdgeLabellings_sound
    base (centralLowerFaceIds half) state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    have hbound := hsound.1 id hid
    omega
  · exact hsound.2

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A -> Q')
    (hvalue : forall item, (0 : Q') <= value item) :
    forall (items : List A) {item : A},
      item ∈ items -> value item <= listQSum value items
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
        exact Q'.le_trans' _ _ _ ih
          (Q'.le_trans' _ _ _
            (Q'.add_le_self_of_nonneg
              (listQSum value tail) (value head)
              (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head))))

/-- Positivity of one physical row persists at every larger representation
cutoff.  No small-error or tail hypothesis is needed for this qualitative
statement. -/
theorem centralPhysicalRowMarginal_pos_of_le
    {w : Q'} (hw : (0 : Q') <= w)
    {base later half : Nat} (hcutoff : base <= later)
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates base half)
    (hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal w hw base half source) :
    (0 : Q') <
      centralPhysicalRowMarginal w hw later half source := by
  unfold centralPhysicalRowMarginal at hpositive
  rcases exists_mem_pos_of_listQSum_pos
      (centralNormalizedPhysicalReflectedKernel
        w hw base half source)
      (centralHalfStates base half) hpositive with
    ⟨target, htarget, htargetPositive⟩
  have hsourceLater :=
    centralHalfStates_mem_of_le_local hcutoff hsource
  have htargetLater :=
    centralHalfStates_mem_of_le_local hcutoff htarget
  have hpartitionBase :
      (0 : Q') < slabParametricKPhysicalPartition
        w base (centralExtent half) :=
    slabParametricKPhysicalPartition_pos
      hw base (centralExtent half)
  have hrawBase :
      (0 : Q') <
        centralPhysicalReflectedKernel
          w base half source target := by
    have hproduct :
        (0 : Q') <
          centralNormalizedPhysicalReflectedKernel
              w hw base half source target *
            slabParametricKPhysicalPartition
              w base (centralExtent half) :=
      Q'.mul_pos htargetPositive hpartitionBase
    refine Q'.pos_of_lt_of_le hproduct ?_
    unfold centralNormalizedPhysicalReflectedKernel
    exact Q'.le_of_eqv
      (Q'.divPos_mul_eqv _ _ hpartitionBase)
  let observable :=
    centralPairCylinderObservable half source target
  have hbaseNumeratorPositive :
      (0 : Q') <
        slabBoundedObservableNumerator
          w base (centralExtent half) observable := by
    have heq :=
      centralPairCylinderNumerator_eq_physicalKernel
        (w := w) hsource htarget
    exact Q'.pos_of_lt_of_le hrawBase
      (Q'.ge_of_eqv heq)
  have hincrementNonnegative :
      (0 : Q') <=
        slabBoundedObservableCutoffIncrement
          w base later (centralExtent half) observable :=
    slabBoundedObservableCutoffIncrement_nonnegative
      hw base later (centralExtent half) observable
  have hlaterNumeratorPositive :
      (0 : Q') <
        slabBoundedObservableNumerator
          w later (centralExtent half) observable := by
    have hdecomposition :=
      slabBoundedObservableNumerator_eq_base_add_increment
        (w := w) hcutoff observable
    refine Q'.pos_of_lt_of_le hbaseNumeratorPositive ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ hincrementNonnegative) ?_
    exact Q'.ge_of_eqv hdecomposition
  have hrawLater :
      (0 : Q') <
        centralPhysicalReflectedKernel
          w later half source target := by
    have heq :=
      centralPairCylinderNumerator_eq_physicalKernel
        (w := w) hsourceLater htargetLater
    exact Q'.pos_of_lt_of_le hlaterNumeratorPositive
      (Q'.le_of_eqv heq)
  have hentryLater :
      (0 : Q') <
        centralNormalizedPhysicalReflectedKernel
          w hw later half source target := by
    unfold centralNormalizedPhysicalReflectedKernel
    exact Q'.divPos_pos _ _
      (slabParametricKPhysicalPartition_pos
        hw later (centralExtent half))
      hrawLater
  refine Q'.pos_of_lt_of_le hentryLater ?_
  unfold centralPhysicalRowMarginal
  exact listQSum_member_le_nonnegative_local
    (centralNormalizedPhysicalReflectedKernel
      w hw later half source)
    (fun item =>
      centralNormalizedPhysicalReflectedKernel_nonnegative
        hw later half source item)
    (centralHalfStates later half) htargetLater

/-- The old positive carrier embeds into every later positive carrier. -/
theorem mem_centralPositiveHalfStates_of_le
    {w : Q'} (hw : (0 : Q') <= w)
    {base later half : Nat} (hcutoff : base <= later)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw base half) :
    source ∈ centralPositiveHalfStates w hw later half := by
  have hparts :=
    mem_centralPositiveHalfStates_iff.mp hsource
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨centralHalfStates_mem_of_le_local hcutoff hparts.1,
      centralPhysicalRowMarginal_pos_of_le
        hw hcutoff hparts.1 hparts.2⟩

/-! ## Axiom audit -/

#print axioms centralPhysicalRowMarginal_pos_of_le
#print axioms mem_centralPositiveHalfStates_of_le

end YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
