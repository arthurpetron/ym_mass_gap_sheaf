/-
# Corrected-slab SU(2) outer-cutoff event tail

`SlabPhysicalData` is built on the boundary-complete corrected reflection
slab, not on the full corner box.  This module proves the cutoff tail on that
literal carrier.

For every `K ≤ L`, the corrected-slab partition and every Boolean-event
numerator split exactly into the retained sector plus the new-label sector.
The normalized event difference is bounded sharply by the complete new slab
mass.  At `anchorCoupling`, zero extension sends every new slab state
injectively into the supported part of the ambient new-label sector and
preserves its physical weight.  Consequently the slab increment is bounded
by the ambient degree-thirteen finite-Fubini envelope.  No equality between
the corrected-slab partition and the full ambient-box partition is used or
claimed.

The final cutoff modulus is executable for every fixed corrected-slab extent
and positive rational tolerance.  It is uniform over Boolean events and all
later Peter--Weyl cutoffs, but it is fixed at `anchorCoupling` and at one
finite slab extent.

## Axiom gate

Finite `List`, `Nat`, `Bool`, and `Q'` algebra only.  No `Classical.*`,
`Real`, `native_decide`, `sorry`, custom axiom, functional extensionality, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
import YMGap.Continuum.SU2PhysicalOuterCutoffAnchorTotalTolerance
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage

namespace YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule
open YMGap.Continuum.SU2PhysicalOuterCutoffAnchorTotalTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup_local :
    ∀ N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨range_nodup_local N,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N)
        (List.mem_range.mp hleft)

private theorem slabPhysicalFaceEdges_nodup (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact range_nodup_local _

private theorem listQSum_nonnegative_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ source : List A,
      (0 : Q') ≤ listQSum weight source
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _
        (hweight head)
        (listQSum_nonnegative_local weight hweight tail)

private theorem listQSum_mono_local
    {A : Type} (lower upper : A → Q') :
    ∀ source : List A,
      (∀ item, item ∈ source →
        lower item ≤ upper item) →
      listQSum lower source ≤ listQSum upper source
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpointwise =>
      Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hpointwise item
              (List.mem_cons_of_mem head hitem)))

private theorem positive_of_one_le_local
    {q : Q'} (hq : (1 : Q') ≤ q) :
    (0 : Q') < q :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide) hq

private theorem one_le_add_nonnegative_local
    {d n : Q'} (hd : (1 : Q') ≤ d)
    (hn : (0 : Q') ≤ n) :
    (1 : Q') ≤ d + n :=
  Q'.le_trans' _ _ _ hd
    (Q'.add_le_self_of_nonneg d n hn)

private theorem map_filter_eq_filter_map_on
    {A B : Type} (encode : A → B)
    (targetTest : B → Bool)
    (sourceTest : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source →
        targetTest (encode item) = sourceTest item) →
      (source.filter sourceTest).map encode =
        (source.map encode).filter targetTest
  | [], _ => rfl
  | head :: tail, htest => by
      have hhead :=
        htest head List.mem_cons_self
      have htail :=
        map_filter_eq_filter_map_on
          encode targetTest sourceTest tail
          (fun item hitem =>
            htest item
              (List.mem_cons_of_mem head hitem))
      simp only [List.filter_cons, List.map_cons]
      rw [hhead]
      cases hsource : sourceTest head
      · simp only [Bool.false_eq_true,
          ↓reduceIte]
        exact htail
      · simp only [↓reduceIte]
        exact congrArg (List.cons (encode head)) htail

private theorem filter_filter_comm_local
    {A : Type} (first second : A → Bool) :
    ∀ source : List A,
      (source.filter first).filter second =
        (source.filter second).filter first
  | [] => rfl
  | head :: tail => by
      have ih :=
        filter_filter_comm_local first second tail
      cases hfirst : first head <;>
        cases hsecond : second head <;>
        simp only [List.filter_cons, hfirst, hsecond,
          Bool.false_eq_true, ↓reduceIte] <;>
        rw [ih]

private theorem listQSum_filter_le
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item)
    (test : A → Bool) (source : List A) :
    listQSum weight (source.filter test) ≤
      listQSum weight source := by
  have hcomplement :
      (0 : Q') ≤
        listQSum weight
          (source.filter (fun item => !(test item))) :=
    listQSum_nonnegative_local weight hweight _
  have hadd :
      listQSum weight (source.filter test) ≤
        listQSum weight (source.filter test) +
          listQSum weight
            (source.filter
              (fun item => !(test item))) :=
    Q'.add_le_self_of_nonneg _ _ hcomplement
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv
      (listQSum_filter_partition
        weight test source))

/-! ## 1. Literal corrected-slab event and new-sector masses -/

/-- One Boolean-masked corrected-slab physical summand. -/
def slabParametricKEventTerm
    (w : Q') (K extent : Nat)
    (event : EdgeLabelling → Bool)
    (physical : EdgeLabelling) : Q' :=
  if event physical then
    slabParametricKPhysicalTerm w K extent physical
  else 0

/-- Unnormalized Boolean-event mass on the literal corrected slab. -/
def slabParametricKEventNumerator
    (w : Q') (K extent : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (slabParametricKEventTerm w K extent event)
    (boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent))

/-- Complete corrected-slab mass carried by labels outside cutoff `K`, but
still inside the later cutoff `L`. -/
def slabParametricKCutoffIncrement
    (w : Q') (K L extent : Nat) : Q' :=
  listQSum
    (slabParametricKPhysicalTerm w L extent)
    ((boundedEdgeLabellings L
      (slabPhysicalFaceEdges extent)).filter
        (fun physical =>
          !(labelWithinB K
            (slabPhysicalFaceEdges extent) physical)))

/-- Boolean-event portion of the corrected-slab new-label sector. -/
def slabParametricKEventCutoffIncrement
    (w : Q') (K L extent : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (slabParametricKEventTerm w L extent event)
    ((boundedEdgeLabellings L
      (slabPhysicalFaceEdges extent)).filter
        (fun physical =>
          !(labelWithinB K
            (slabPhysicalFaceEdges extent) physical)))

theorem slabParametricKEventNumerator_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K extent : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      slabParametricKEventNumerator
        w K extent event := by
  unfold slabParametricKEventNumerator
  apply listQSum_nonnegative_local
  intro physical
  unfold slabParametricKEventTerm
  split
  · exact slabParametricKPhysicalTerm_nonnegative
      hw K extent physical
  · exact Q'.le_refl' 0

theorem slabParametricKEventNumerator_le_partition
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K extent : Nat)
    (event : EdgeLabelling → Bool) :
    slabParametricKEventNumerator
        w K extent event ≤
      slabParametricKPhysicalPartition
        w K extent := by
  unfold slabParametricKEventNumerator
    slabParametricKPhysicalPartition
  apply listQSum_mono_local
  intro physical _
  unfold slabParametricKEventTerm
  split
  · exact Q'.le_refl' _
  · exact slabParametricKPhysicalTerm_nonnegative
      hw K extent physical

theorem slabParametricKCutoffIncrement_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K L extent : Nat) :
    (0 : Q') ≤
      slabParametricKCutoffIncrement
        w K L extent := by
  unfold slabParametricKCutoffIncrement
  apply listQSum_nonnegative_local
  exact slabParametricKPhysicalTerm_nonnegative hw L extent

theorem slabParametricKEventCutoffIncrement_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K L extent : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      slabParametricKEventCutoffIncrement
        w K L extent event := by
  unfold slabParametricKEventCutoffIncrement
  apply listQSum_nonnegative_local
  intro physical
  unfold slabParametricKEventTerm
  split
  · exact slabParametricKPhysicalTerm_nonnegative
      hw L extent physical
  · exact Q'.le_refl' 0

theorem slabParametricKEventCutoffIncrement_le_total
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K L extent : Nat)
    (event : EdgeLabelling → Bool) :
    slabParametricKEventCutoffIncrement
        w K L extent event ≤
      slabParametricKCutoffIncrement
        w K L extent := by
  unfold slabParametricKEventCutoffIncrement
    slabParametricKCutoffIncrement
  apply listQSum_mono_local
  intro physical _
  unfold slabParametricKEventTerm
  split
  · exact Q'.le_refl' _
  · exact slabParametricKPhysicalTerm_nonnegative
      hw L extent physical

/-! ## 2. Exact cutoff stability and retained/new decomposition -/

private theorem slab_bounded_mem_of_le
    {K L extent : Nat} (hKL : K ≤ L)
    {physical : EdgeLabelling}
    (hphysical :
      physical ∈ boundedEdgeLabellings K
        (slabPhysicalFaceEdges extent)) :
    physical ∈ boundedEdgeLabellings L
      (slabPhysicalFaceEdges extent) := by
  let largeSupport :=
    boundedEdgeLabellings L
      (slabPhysicalFaceEdges extent)
  let smallSupport :=
    boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)
  have hfilter :
      largeSupport.filter
          (labelWithinB K
            (slabPhysicalFaceEdges extent)) =
        smallSupport := by
    dsimp only [largeSupport, smallSupport]
    exact boundedEdgeLabellings_filter_cutoff
      hKL _ (slabPhysicalFaceEdges_nodup extent)
  have hfiltered :
      physical ∈
        largeSupport.filter
          (labelWithinB K
            (slabPhysicalFaceEdges extent)) := by
    rw [hfilter]
    exact hphysical
  exact (List.mem_filter.mp hfiltered).1

/-- A supported corrected-slab summand is unchanged when only the
Peter--Weyl cutoff is enlarged.  The proof passes through zero extension to
the ambient term, without comparing either partition to the full box. -/
theorem slabParametricKPhysicalTerm_cutoff_stable
    {w : Q'} {K L extent : Nat}
    (hKL : K ≤ L) {physical : EdgeLabelling}
    (hphysical :
      physical ∈ boundedEdgeLabellings K
        (slabPhysicalFaceEdges extent)) :
    slabParametricKPhysicalTerm w L extent physical ≈
      slabParametricKPhysicalTerm w K extent physical := by
  have hphysicalL :=
    slab_bounded_mem_of_le hKL hphysical
  have hambientK :=
    slabToAmbientPhysical_mem_bounded hphysical
  exact Q'.eqv_trans _ _ _
    (slabParametricKPhysicalTerm_ambient w hphysicalL)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (parametricKPhysicalTerm_cutoff_stable
          hKL hambientK))
      (Q'.eqv_symm
        (slabParametricKPhysicalTerm_ambient
          w hphysical)))

theorem slabParametricKEventTerm_cutoff_stable
    {w : Q'} {K L extent : Nat}
    (hKL : K ≤ L)
    (event : EdgeLabelling → Bool)
    {physical : EdgeLabelling}
    (hphysical :
      physical ∈ boundedEdgeLabellings K
        (slabPhysicalFaceEdges extent)) :
    slabParametricKEventTerm w L extent event physical ≈
      slabParametricKEventTerm w K extent event physical := by
  unfold slabParametricKEventTerm
  split
  · exact slabParametricKPhysicalTerm_cutoff_stable
      hKL hphysical
  · exact Q'.eqv_refl 0

/-- Exact retained-plus-new decomposition of the corrected-slab partition. -/
theorem slabParametricKPhysicalPartition_eq_base_add_increment
    {w : Q'} {K L extent : Nat}
    (hKL : K ≤ L) :
    slabParametricKPhysicalPartition w L extent ≈
      slabParametricKPhysicalPartition w K extent +
        slabParametricKCutoffIncrement
          w K L extent := by
  let faces := slabPhysicalFaceEdges extent
  let oldTest := labelWithinB K faces
  let largeSupport := boundedEdgeLabellings L faces
  let smallSupport := boundedEdgeLabellings K faces
  have hfilter :
      largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, faces]
    exact boundedEdgeLabellings_filter_cutoff
      hKL _ (slabPhysicalFaceEdges_nodup extent)
  have hcommon :
      listQSum
          (slabParametricKPhysicalTerm w L extent)
          (largeSupport.filter oldTest) ≈
        listQSum
          (slabParametricKPhysicalTerm w K extent)
          smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro physical hphysical
    exact slabParametricKPhysicalTerm_cutoff_stable
      hKL hphysical
  have hsplit :
      listQSum
          (slabParametricKPhysicalTerm w L extent)
          largeSupport ≈
        listQSum
            (slabParametricKPhysicalTerm w L extent)
            (largeSupport.filter oldTest) +
          slabParametricKCutoffIncrement
            w K L extent := by
    have hpartition :=
      listQSum_filter_partition
        (slabParametricKPhysicalTerm w L extent)
        oldTest largeSupport
    simpa [slabParametricKCutoffIncrement,
      largeSupport, oldTest, faces] using hpartition
  unfold slabParametricKPhysicalPartition
  dsimp only [largeSupport, smallSupport, faces] at hcommon hsplit ⊢
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr' hcommon (Q'.eqv_refl _))

/-- Exact retained-plus-new decomposition of every corrected-slab Boolean
event numerator. -/
theorem slabParametricKEventNumerator_eq_base_add_increment
    {w : Q'} {K L extent : Nat}
    (hKL : K ≤ L)
    (event : EdgeLabelling → Bool) :
    slabParametricKEventNumerator
        w L extent event ≈
      slabParametricKEventNumerator
          w K extent event +
        slabParametricKEventCutoffIncrement
          w K L extent event := by
  let faces := slabPhysicalFaceEdges extent
  let oldTest := labelWithinB K faces
  let largeSupport := boundedEdgeLabellings L faces
  let smallSupport := boundedEdgeLabellings K faces
  have hfilter :
      largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, faces]
    exact boundedEdgeLabellings_filter_cutoff
      hKL _ (slabPhysicalFaceEdges_nodup extent)
  have hcommon :
      listQSum
          (slabParametricKEventTerm w L extent event)
          (largeSupport.filter oldTest) ≈
        listQSum
          (slabParametricKEventTerm w K extent event)
          smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro physical hphysical
    exact slabParametricKEventTerm_cutoff_stable
      hKL event hphysical
  have hsplit :
      listQSum
          (slabParametricKEventTerm w L extent event)
          largeSupport ≈
        listQSum
            (slabParametricKEventTerm w L extent event)
            (largeSupport.filter oldTest) +
          slabParametricKEventCutoffIncrement
            w K L extent event := by
    have hpartition :=
      listQSum_filter_partition
        (slabParametricKEventTerm w L extent event)
        oldTest largeSupport
    simpa [slabParametricKEventCutoffIncrement,
      largeSupport, oldTest, faces] using hpartition
  unfold slabParametricKEventNumerator
  dsimp only [largeSupport, smallSupport, faces] at hcommon hsplit ⊢
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr' hcommon (Q'.eqv_refl _))

/-! ## 3. Sharp normalized arbitrary-event tail -/

/-- Normalized corrected-slab probability of an arbitrary Boolean event at
the strong-coupling anchor. -/
def slabAnchorCutoffEventProbability
    (K extent : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  Q'.divPos
    (slabParametricKEventNumerator
      anchorCoupling K extent event)
    (slabParametricKPhysicalPartition
      anchorCoupling K extent)
    (slabParametricKPhysicalPartition_pos
      (by decide) K extent)

private theorem qeqv_of_le_of_ge_local
    {a b : Q'} (hab : a ≤ b) (hba : b ≤ a) :
    a ≈ b := by
  show a.num * (b.den : Int) =
    b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local
    {a a' b b' : Q'}
    (hb : (0 : Q') < b)
    (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈
      Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm ha)))

/-- Sharp normalized event tail on the actual corrected-slab carrier. -/
theorem slabAnchorCutoffEventProbability_abs_le_increment
    {K L extent : Nat} (hKL : K ≤ L)
    (event : EdgeLabelling → Bool) :
    absQ
        (slabAnchorCutoffEventProbability
            K extent event +
          -slabAnchorCutoffEventProbability
            L extent event) ≤
      slabParametricKCutoffIncrement
        anchorCoupling K L extent := by
  let a :=
    slabParametricKEventNumerator
      anchorCoupling K extent event
  let b :=
    slabParametricKEventCutoffIncrement
      anchorCoupling K L extent event
  let d :=
    slabParametricKPhysicalPartition
      anchorCoupling K extent
  let n :=
    slabParametricKCutoffIncrement
      anchorCoupling K L extent
  let A :=
    slabParametricKEventNumerator
      anchorCoupling L extent event
  let D :=
    slabParametricKPhysicalPartition
      anchorCoupling L extent
  have ha : (0 : Q') ≤ a := by
    dsimp only [a]
    exact slabParametricKEventNumerator_nonnegative
      (by decide) K extent event
  have hb : (0 : Q') ≤ b := by
    dsimp only [b]
    exact slabParametricKEventCutoffIncrement_nonnegative
      (by decide) K L extent event
  have hn : (0 : Q') ≤ n := by
    dsimp only [n]
    exact slabParametricKCutoffIncrement_nonnegative
      (by decide) K L extent
  have hd1 : (1 : Q') ≤ d := by
    dsimp only [d]
    exact slabParametricKPhysicalPartition_one_le
      (by decide) K extent
  have had : a ≤ d := by
    dsimp only [a, d]
    exact slabParametricKEventNumerator_le_partition
      (by decide) K extent event
  have hbn : b ≤ n := by
    dsimp only [b, n]
    exact slabParametricKEventCutoffIncrement_le_total
      (by decide) K L extent event
  have hbase :=
    nested_normalized_event_abs_le_newMass
      ha hb hn hd1 had hbn
  have hd : (0 : Q') < d :=
    positive_of_one_le_local hd1
  have hdn : (0 : Q') < d + n :=
    positive_of_one_le_local
      (one_le_add_nonnegative_local hd1 hn)
  have hA : A ≈ a + b := by
    dsimp only [A, a, b]
    exact
      slabParametricKEventNumerator_eq_base_add_increment
        hKL event
  have hD : D ≈ d + n := by
    dsimp only [D, d, n]
    exact
      slabParametricKPhysicalPartition_eq_base_add_increment
        hKL
  have hDactual : (0 : Q') < D := by
    dsimp only [D]
    exact slabParametricKPhysicalPartition_pos
      (by decide) L extent
  have hlarge :
      Q'.divPos A D hDactual ≈
        Q'.divPos (a + b) (d + n) hdn :=
    divPos_eqv_congr_local hDactual hdn hA hD
  unfold slabAnchorCutoffEventProbability
  dsimp only [a, b, d, n, A, D] at hbase hlarge ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr_left
          (Q'.divPos
            (slabParametricKEventNumerator
              anchorCoupling K extent event)
            (slabParametricKPhysicalPartition
              anchorCoupling K extent)
            (slabParametricKPhysicalPartition_pos
              (by decide) K extent))
          _
          (-(Q'.divPos
            (slabParametricKEventNumerator
                anchorCoupling K extent event +
              slabParametricKEventCutoffIncrement
                anchorCoupling K L extent event)
            (slabParametricKPhysicalPartition
                anchorCoupling K extent +
              slabParametricKCutoffIncrement
                anchorCoupling K L extent)
            hdn))
          (Q'.neg_eqv_congr _ _ hlarge))))
    hbase

/-! ## 4. Supported ambient injection and degree-thirteen domination -/

/-- Zero extension preserves the cutoff-window predicate exactly: slab
coordinates retain their labels and every omitted ambient coordinate is
vacuum-labelled. -/
theorem labelWithinB_slabToAmbientPhysical
    (K extent : Nat) (physical : EdgeLabelling) :
    labelWithinB K
        (List.range
          (plaquetteEdgeCount (extent + 1)))
        (slabToAmbientPhysical extent physical) =
      labelWithinB K
        (slabPhysicalFaceEdges extent) physical := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hambient
    apply (labelWithinB_true_iff K
      (slabPhysicalFaceEdges extent) physical).2
    intro sourceId hsourceId
    have hsourceIndexed :=
      slabPlaquetteAt_mem_enumerate hsourceId
    have hsourceSlab :=
      slabPlaquetteAt_mem hsourceId
    have hsourceBox :=
      (mem_boundaryCompleteSlabPlaquettes extent
        (slabPlaquetteAt extent sourceId)).mp
          hsourceSlab |>.1
    obtain ⟨targetId, htargetIndexed⟩ :=
      exists_mem_enumerate hsourceBox
    have htargetMem :
        targetId ∈
          List.range
            (plaquetteEdgeCount (extent + 1)) :=
      List.mem_range.mpr
        (enumerate_index_lt htargetIndexed)
    have hsmall :=
      (labelWithinB_true_iff K
        (List.range
          (plaquetteEdgeCount (extent + 1)))
        (slabToAmbientPhysical extent physical)).1
          hambient targetId htargetMem
    rw [slabToAmbientPhysical_eq_on_enumerate
      htargetIndexed,
      slabGeometricSpin_eq_of_enumerate
        hsourceIndexed] at hsmall
    exact hsmall
  · intro hslab
    apply (labelWithinB_true_iff K
      (List.range
        (plaquetteEdgeCount (extent + 1)))
      (slabToAmbientPhysical extent physical)).2
    intro targetId htargetId
    have htargetIndexed :
        (targetId,
          boxPlaquetteAt (extent + 1) targetId) ∈
            enumerate
              (boxPlaquettes (extent + 1)) :=
      boxPlaquetteAt_mem_enumerate
        (List.mem_range.mp htargetId)
    rw [slabToAmbientPhysical_eq_on_enumerate
      htargetIndexed]
    by_cases hsource :
        boxPlaquetteAt (extent + 1) targetId ∈
          boundaryCompleteSlabPlaquettes extent
    · obtain ⟨sourceId, hsourceIndexed⟩ :=
        exists_mem_enumerate hsource
      have hsourceMem :
          sourceId ∈
            slabPhysicalFaceEdges extent := by
        unfold slabPhysicalFaceEdges
        exact List.mem_range.mpr
          (enumerate_index_lt hsourceIndexed)
      rw [slabGeometricSpin_eq_of_enumerate
        hsourceIndexed]
      exact
        (labelWithinB_true_iff K
          (slabPhysicalFaceEdges extent)
          physical).1 hslab sourceId hsourceMem
    · rw [slabGeometricSpin_zero_of_not_mem
        extent physical hsource]
      omega

private theorem not_within_of_not_within_slab
    {K extent : Nat} {physical : EdgeLabelling}
    (hnew :
      (!(labelWithinB K
        (slabPhysicalFaceEdges extent) physical)) = true) :
    (!(labelWithinB K
      (List.range
        (plaquetteEdgeCount (extent + 1)))
      (slabToAmbientPhysical extent physical))) = true := by
  rw [labelWithinB_slabToAmbientPhysical]
  exact hnew

/-- Every new corrected-slab state lands both in the supported ambient
subensemble and in the full ambient new-label sector. -/
theorem slabNewState_embeds_supportedAmbientNewSector
    {K L extent : Nat} {physical : EdgeLabelling}
    (hphysical :
      physical ∈
        (boundedEdgeLabellings L
          (slabPhysicalFaceEdges extent)).filter
            (fun state =>
              !(labelWithinB K
                (slabPhysicalFaceEdges extent) state))) :
    slabToAmbientPhysical extent physical ∈
        ambientSlabSupportedLabellings L extent ∧
      slabToAmbientPhysical extent physical ∈
        (boundedEdgeLabellings L
          (List.range
            (plaquetteEdgeCount (extent + 1)))).filter
              (fun state =>
                !(labelWithinB K
                  (List.range
                    (plaquetteEdgeCount (extent + 1)))
                  state)) := by
  have hparts := List.mem_filter.mp hphysical
  constructor
  · unfold ambientSlabSupportedLabellings
    exact List.mem_filter.mpr
      ⟨slabToAmbientPhysical_mem_bounded hparts.1,
        slabToAmbientPhysical_supported extent physical⟩
  · exact List.mem_filter.mpr
      ⟨slabToAmbientPhysical_mem_bounded hparts.1,
        not_within_of_not_within_slab
          hparts.2⟩

/-- The corrected-slab new-sector mass is bounded by the full ambient-box
new-sector mass.  This is a weighted injection through the supported ambient
subset; it is not a partition identity. -/
theorem slabParametricKCutoffIncrement_le_ambient
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K L extent : Nat} :
    slabParametricKCutoffIncrement
        w K L extent ≤
      parametricKCutoffIncrement
        w K L (extent + 1) := by
  let slabFaces := slabPhysicalFaceEdges extent
  let ambientFaces :=
    List.range (plaquetteEdgeCount (extent + 1))
  let slabTest : EdgeLabelling → Bool := fun physical =>
    !(labelWithinB K slabFaces physical)
  let ambientTest : EdgeLabelling → Bool := fun physical =>
    !(labelWithinB K ambientFaces physical)
  let fullSource :=
    boundedEdgeLabellings L slabFaces
  let source :=
    fullSource.filter slabTest
  let embedded :=
    embeddedSlabLabellings L extent
  let supported :=
    ambientSlabSupportedLabellings L extent
  let ambientFull :=
    boundedEdgeLabellings L ambientFaces
  let ambientNew :=
    ambientFull.filter ambientTest
  let encode := slabToAmbientPhysical extent
  let sourceWeight :=
    slabParametricKPhysicalTerm w L extent
  let targetWeight :=
    parametricKPhysicalTerm w L (extent + 1)
  have htest :
      ∀ physical,
        physical ∈ fullSource →
          ambientTest (encode physical) =
            slabTest physical := by
    intro physical _
    dsimp only [ambientTest, slabTest, encode,
      ambientFaces, slabFaces]
    rw [labelWithinB_slabToAmbientPhysical]
  have hmap :
      source.map encode =
        embedded.filter ambientTest := by
    dsimp only [source, embedded, fullSource]
    exact map_filter_eq_filter_map_on
      encode ambientTest slabTest
      (boundedEdgeLabellings L slabFaces)
      htest
  have hweightMap :
      listQSum sourceWeight source ≈
        listQSum targetWeight
          (source.map encode) := by
    apply listQSum_map_eqv
    intro physical hphysical
    dsimp only [sourceWeight, targetWeight, encode]
    exact slabParametricKPhysicalTerm_ambient
      w
      (List.mem_filter.mp
        (by
          dsimp only [source, fullSource] at hphysical
          exact hphysical)).1
  have hperm :
      (embedded.filter ambientTest).Perm
        (supported.filter ambientTest) := by
    dsimp only [embedded, supported]
    exact
      (embeddedSlabLabellings_perm_supported
        L extent).filter ambientTest
  have hweightSupported :
      listQSum targetWeight
          (source.map encode) ≈
        listQSum targetWeight
          (supported.filter ambientTest) := by
    rw [hmap]
    exact listQSum_perm targetWeight hperm
  have hsupportedLe :
      listQSum targetWeight
          (supported.filter ambientTest) ≤
        listQSum targetWeight ambientNew := by
    dsimp only [supported, ambientNew, ambientFull,
      ambientSlabSupportedLabellings]
    rw [filter_filter_comm_local]
    exact listQSum_filter_le
      targetWeight
      (fun physical =>
        parametricKPhysicalTerm_nonnegative
          hw L (extent + 1) physical)
      (ambientSlabSupportedB extent)
      ((boundedEdgeLabellings L ambientFaces).filter
        ambientTest)
  unfold slabParametricKCutoffIncrement
    parametricKCutoffIncrement
  change
    listQSum sourceWeight source ≤
      listQSum targetWeight ambientNew
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        hweightMap hweightSupported))
    hsupportedLe

/-- Scheduled corrected-slab increment bound by the ambient degree-thirteen
finite-Fubini envelope. -/
theorem slabAnchorScheduledCutoffIncrement_le_tensorEnvelope
    (precision : Nat) {L extent : Nat}
    (hretained :
      anchorPhysicalRetainedCutoff precision ≤ L) :
    slabParametricKCutoffIncrement
        anchorCoupling
        (anchorPhysicalRetainedCutoff precision)
        L extent ≤
      su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        (anchorPhysicalRetainedCutoff precision)
        precision
        (plaquetteEdgeCount (extent + 1)) := by
  exact Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_le_ambient
      (w := anchorCoupling) (by decide))
    (anchorScheduledCutoffIncrement_le_tensorEnvelope
      precision hretained)

/-! ## 5. Executable total-tolerance modulus at fixed slab extent -/

/-- Retained cutoff making every later corrected-slab event probability
half of the requested tolerance close to the retained stage. -/
def slabAnchorEventProbabilityModulus
    (extent : Nat) (ε : Q') : Nat :=
  anchorPhysicalTensorToleranceRetainedCutoff
    (plaquetteEdgeCount (extent + 1))
    (HalfPow.half * ε)

private theorem slabAnchorEventProbability_from_modulus_abs_le_half
    (extent : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {L : Nat}
    (hL :
      slabAnchorEventProbabilityModulus extent ε ≤ L) :
    absQ
        (slabAnchorCutoffEventProbability
            (slabAnchorEventProbabilityModulus extent ε)
            extent event +
          -slabAnchorCutoffEventProbability
            L extent event) ≤
      HalfPow.half * ε := by
  let dimension := plaquetteEdgeCount (extent + 1)
  let halfTolerance := HalfPow.half * ε
  let precision :=
    anchorPhysicalTensorTolerancePrecision
      dimension halfTolerance
  have hhalf : (0 : Q') < halfTolerance :=
    YMGap.Constructive.ExpNeg.half_mul_pos ε hε
  have hsharp :=
    slabAnchorCutoffEventProbability_abs_le_increment
      (extent := extent) hL event
  have hincrement :=
    slabAnchorScheduledCutoffIncrement_le_tensorEnvelope
      precision (L := L) (extent := extent) hL
  have henvelope :=
    anchorPhysicalTensorTailEnvelope_le_tolerance
      dimension hhalf
  exact Q'.le_trans' _ _ _ hsharp
    (Q'.le_trans' _ _ _ hincrement henvelope)

private theorem twoSided_of_absQ_sub_le
    {a b ε : Q'} (h : absQ (a + (-b)) ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε := by
  have habs : Q'.abs (a + (-b)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
            (a + (-b)))))
      h
  constructor
  · exact YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
      habs
  · apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a))
      habs

private theorem add_two_halves_le
    (x ε : Q') :
    (x + HalfPow.half * ε) +
        HalfPow.half * ε ≤
      x + ε := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        x (HalfPow.half * ε)
        (HalfPow.half * ε))) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      x
      (HalfPow.half * ε +
        HalfPow.half * ε)
      ε
      (YMGap.Constructive.ExpNeg.two_halves ε))

/-- Executable Bishop-style total-tolerance theorem: every two corrected-slab
cutoffs beyond the modulus are two-sided `ε`-close, uniformly over Boolean
events. -/
theorem slabAnchorCutoffEventProbability_twoSided_of_modulus
    (extent : Nat) (event : EdgeLabelling → Bool)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      slabAnchorEventProbabilityModulus
        extent ε ≤ first)
    (hsecond :
      slabAnchorEventProbabilityModulus
        extent ε ≤ second) :
    slabAnchorCutoffEventProbability
          first extent event ≤
        slabAnchorCutoffEventProbability
            second extent event + ε ∧
      slabAnchorCutoffEventProbability
          second extent event ≤
        slabAnchorCutoffEventProbability
            first extent event + ε := by
  let halfTolerance := HalfPow.half * ε
  have hfirstHalf :=
    twoSided_of_absQ_sub_le
      (slabAnchorEventProbability_from_modulus_abs_le_half
        extent event hε hfirst)
  have hsecondHalf :=
    twoSided_of_absQ_sub_le
      (slabAnchorEventProbability_from_modulus_abs_le_half
        extent event hε hsecond)
  constructor
  · have hchain :
      slabAnchorCutoffEventProbability first extent event ≤
          (slabAnchorCutoffEventProbability
              second extent event + halfTolerance) +
            halfTolerance :=
        Q'.le_trans' _ _ _
          hfirstHalf.2
          (Q'.add_le_add_right _ _ halfTolerance
            hsecondHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (slabAnchorCutoffEventProbability
          second extent event) ε)
  · have hchain :
      slabAnchorCutoffEventProbability second extent event ≤
          (slabAnchorCutoffEventProbability
              first extent event + halfTolerance) +
            halfTolerance :=
        Q'.le_trans' _ _ _
          hsecondHalf.2
          (Q'.add_le_add_right _ _ halfTolerance
            hfirstHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (slabAnchorCutoffEventProbability
          first extent event) ε)

#print axioms slabParametricKPhysicalTerm_cutoff_stable
#print axioms slabParametricKPhysicalPartition_eq_base_add_increment
#print axioms slabParametricKEventNumerator_eq_base_add_increment
#print axioms slabAnchorCutoffEventProbability_abs_le_increment
#print axioms slabNewState_embeds_supportedAmbientNewSector
#print axioms slabParametricKCutoffIncrement_le_ambient
#print axioms slabAnchorScheduledCutoffIncrement_le_tensorEnvelope
#print axioms slabAnchorEventProbabilityModulus
#print axioms slabAnchorCutoffEventProbability_twoSided_of_modulus

end YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
