/-
# The second valence-five associator as a finite bistochastic block sum

The second associator is block diagonal in the physical intermediate
`m` produced by the `(b,c)` fusion.  Its written source list, however, is
the common middle list produced by the first associator and is organized by
the transient output `y`.  This module constructs the exact finite change of
index between those descriptions, then proves global row and column mass one.

Constructive contract: bounded proof-carrying lists and exact `Q'` algebra
only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernelComposition
import YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock

namespace YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical reconstruction of a middle state at fixed `m` -/

private theorem cgFusionStep_unique {a b c : Nat}
    (left right : CGFusionStep a b c) : left = right := by
  cases left with
  | mk leftOrder leftLe leftOutput =>
      cases right with
      | mk rightOrder rightLe rightOutput =>
          have hleft := Nat.le_min.mp leftLe
          have hright := Nat.le_min.mp rightLe
          have horder : leftOrder = rightOrder := by omega
          subst rightOrder
          rfl

/-- The inner `(b,c) -> m` step and a left channel for `(a,m,d;e)`
reconstruct the corresponding right channel `(a,(b,c));y`. -/
def middleFirstOfInnerLeft {a b c d e m : Nat}
    (inner : CGFusionStep b c m)
    (left : FixedLeftCGChannel a m d e) :
    FixedRightCGChannel a b c left.intermediate where
  p := inner.order
  p_le := inner.order_le
  r := left.k
  r_le := by
    have hk := Nat.le_min.mp left.k_le
    apply Nat.le_min.mpr
    constructor
    · exact hk.1
    · simpa only [inner.output_eq] using hk.2
  degree_eq := by
    simp only [inner.output_eq, FixedLeftCGChannel.intermediate]

/-- The outer step of a fixed left channel, retained as a trivalent suffix. -/
def suffixOfFixedLeft {a m d e : Nat}
    (left : FixedLeftCGChannel a m d e) :
    CGFusionStep left.intermediate d e where
  order := left.r
  order_le := left.r_le
  output_eq := left.degree_eq

/-- Canonical common-middle state reconstructed from one fixed-`m` left
channel. -/
def middleOfInnerLeft {a b c d e m : Nat}
    (inner : CGFusionStep b c m)
    (left : FixedLeftCGChannel a m d e) :
    ValenceFiveMiddleCarrier a b c d e where
  y := left.intermediate
  first := middleFirstOfInnerLeft inner left
  suffix := suffixOfFixedLeft left

theorem middleOfInnerLeft_first_intermediate {a b c d e m : Nat}
    (inner : CGFusionStep b c m)
    (left : FixedLeftCGChannel a m d e) :
    (middleOfInnerLeft inner left).first.intermediate = m := by
  change b + c - 2 * inner.order = m
  exact inner.output_eq

def middleSecondLeftAt {a b c d e m : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (h : middle.first.intermediate = m) :
    FixedLeftCGChannel a m d e :=
  h ▸ middle.secondLeft

theorem middleOfInnerLeft_secondLeftAt {a b c d e m : Nat}
    (inner : CGFusionStep b c m)
    (left : FixedLeftCGChannel a m d e) :
    middleSecondLeftAt (middleOfInnerLeft inner left)
      (middleOfInnerLeft_first_intermediate inner left) = left := by
  cases inner with
  | mk order orderLe output =>
      cases output
      unfold middleSecondLeftAt
      apply fixedLeftChannel_eq_of_k_eq
      simp only [ValenceFiveMiddleCarrier.secondLeft, middleOfInnerLeft,
        middleFirstOfInnerLeft, fixedLeftChannelOfFusion]
      exact fixedLeft_inner_couplingOrder left

/-- The inner trivalent step canonically carried by one middle state. -/
def middleInnerStep {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    CGFusionStep b c middle.first.intermediate where
  order := middle.first.p
  order_le := middle.first.p_le
  output_eq := rfl

private theorem middleSecondLeft_intermediate {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    middle.secondLeft.intermediate = middle.y := by
  unfold ValenceFiveMiddleCarrier.secondLeft
  exact fixedLeftChannelOfFusion_intermediate _ _ _ _ _ _ _

private theorem middle_eq_of_y_eq_p_eq {a b c d e : Nat}
    (left right : ValenceFiveMiddleCarrier a b c d e)
    (hy : left.y = right.y)
    (hp : left.first.p = right.first.p) : left = right := by
  cases left with
  | mk leftY leftFirst leftSuffix =>
      cases right with
      | mk rightY rightFirst rightSuffix =>
          dsimp only at hy hp
          subst rightY
          have hfirst : leftFirst = rightFirst :=
            fixedRightChannel_eq_of_p_eq leftFirst rightFirst hp
          subst rightFirst
          have hsuffix : leftSuffix = rightSuffix :=
            cgFusionStep_unique leftSuffix rightSuffix
          subst rightSuffix
          rfl

theorem middleOfInnerLeft_roundtrip {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    middleOfInnerLeft (middleInnerStep middle) middle.secondLeft = middle := by
  apply middle_eq_of_y_eq_p_eq
  · exact middleSecondLeft_intermediate middle
  · rfl

theorem middleOfInnerLeft_roundtripAt {a b c d e m : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (h : middle.first.intermediate = m)
    (inner : CGFusionStep b c m) :
    middleOfInnerLeft inner (middleSecondLeftAt middle h) = middle := by
  have horder : inner.order = middle.first.p := by
    have hinner := inner.output_eq
    have hmiddle : b + c - 2 * middle.first.p =
        middle.first.intermediate := rfl
    have hi := Nat.le_min.mp inner.order_le
    have hm := Nat.le_min.mp middle.first.p_le
    omega
  apply middle_eq_of_y_eq_p_eq
  · cases h
    exact middleSecondLeft_intermediate middle
  · exact horder

/-! ## 2. Duplicate-free common-middle reindexing -/

private theorem nodup_map_of_injective {A B : Type} (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := heq ▸ htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

private def middleCode {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) : Nat × Nat :=
  (middle.y, middle.first.p)

private theorem middleCode_injective {a b c d e : Nat}
    (left right : ValenceFiveMiddleCarrier a b c d e)
    (hcode : middleCode left = middleCode right) : left = right := by
  apply middle_eq_of_y_eq_p_eq
  · exact congrArg Prod.fst hcode
  · exact congrArg Prod.snd hcode

private instance middleDecidableEq (a b c d e : Nat) :
    DecidableEq (ValenceFiveMiddleCarrier a b c d e) := fun left right =>
  match decEq (middleCode left) (middleCode right) with
  | isTrue hcode => isTrue (middleCode_injective left right hcode)
  | isFalse hcode => isFalse (fun heq => hcode (congrArg middleCode heq))

private theorem middleFiber_nodup {a b c d e : Nat}
    (index : ValenceFiveTransientIndex a b c d e) :
    (valenceFiveMiddleFiber index).Nodup := by
  unfold valenceFiveMiddleFiber
  apply nodup_map_of_injective
  · intro left right heq
    apply fixedRightChannel_eq_of_p_eq
    exact congrArg (fun middle => middle.first.p) heq
  · exact fixedRightChannels_nodup a b c index.val

theorem valenceFiveMiddleCarriers_nodup (a b c d e : Nat) :
    (valenceFiveMiddleCarriers a b c d e).Nodup := by
  unfold valenceFiveMiddleCarriers
  apply nodup_flatMap_of_disjoint_blocks
  · exact attach_nodup_of_nodup _
      (valenceFiveTransientOutputs_nodup a b c d e)
  · intro index _
    exact middleFiber_nodup index
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftChannel, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightChannel, _, hrightEq⟩ := List.mem_map.mp hright
    have hy : left.val = right.val := by
      exact congrArg (fun middle => middle.y)
        (hleftEq.trans hrightEq.symm)
    exact hne (Subtype.ext hy)

theorem valenceFiveMiddleCarriers_complete {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    middle ∈ valenceFiveMiddleCarriers a b c d e := by
  let index : ValenceFiveTransientIndex a b c d e :=
    ⟨middle.y, valenceFiveMiddleCarrier_y_mem_transientOutputs middle⟩
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_attach _ index, ?_⟩
  apply List.mem_map.mpr
  refine ⟨middle.first, fixedRightChannels_complete middle.first, ?_⟩
  apply middle_eq_of_y_eq_p_eq
  · rfl
  · rfl

/-! ## 3. The fixed-inner fiber inside the written common-middle list -/

def valenceFiveMiddleAtInner {a b c d e m : Nat}
    (inner : CGFusionStep b c m) :
    List (ValenceFiveMiddleCarrier a b c d e) :=
  (fixedLeftChannels a m d e).map (middleOfInnerLeft inner)

def valenceFiveMiddleWithIntermediate (a b c d e m : Nat) :
    List (ValenceFiveMiddleCarrier a b c d e) :=
  (valenceFiveMiddleCarriers a b c d e).filter
    (fun middle => decide (middle.first.intermediate = m))

theorem valenceFiveMiddleAtInner_nodup {a b c d e m : Nat}
    (inner : CGFusionStep b c m) :
    (valenceFiveMiddleAtInner (a := a) (d := d) (e := e) inner).Nodup := by
  unfold valenceFiveMiddleAtInner
  apply nodup_map_of_injective
  · intro left right heq
    apply fixedLeftChannel_eq_of_k_eq
    exact congrArg
      (fun middle : ValenceFiveMiddleCarrier a b c d e => middle.first.r) heq
  · exact fixedLeftChannels_nodup a m d e

theorem mem_valenceFiveMiddleWithIntermediate_iff_atInner
    {a b c d e m : Nat} (inner : CGFusionStep b c m)
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    middle ∈ valenceFiveMiddleWithIntermediate a b c d e m ↔
      middle ∈ valenceFiveMiddleAtInner inner := by
  constructor
  · intro hmiddle
    have hparts := List.mem_filter.mp hmiddle
    have hintermediate : middle.first.intermediate = m :=
      of_decide_eq_true hparts.2
    apply List.mem_map.mpr
    refine ⟨middleSecondLeftAt middle hintermediate,
      fixedLeftChannels_complete _, ?_⟩
    exact middleOfInnerLeft_roundtripAt middle hintermediate inner
  · intro hmiddle
    obtain ⟨left, hleft, heq⟩ := List.mem_map.mp hmiddle
    subst middle
    apply List.mem_filter.mpr
    refine ⟨valenceFiveMiddleCarriers_complete _, decide_eq_true ?_⟩
    exact middleOfInnerLeft_first_intermediate inner left

/-! ## 4. Complete final carriers and the zero-extended second block -/

def valenceFiveInnerOutputs (b c : Nat) : List Nat :=
  (List.range (b + c + 1)).filter (fun m => fusionOK b c m)

private theorem range_nodup_local (bound : Nat) :
    (List.range bound).Nodup := by
  induction bound with
  | zero => exact List.nodup_nil
  | succ bound ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

theorem valenceFiveInnerOutputs_nodup (b c : Nat) :
    (valenceFiveInnerOutputs b c).Nodup :=
  List.filter_sublist.nodup (range_nodup_local (b + c + 1))

abbrev ValenceFiveInnerIndex (b c : Nat) :=
  {m // m ∈ valenceFiveInnerOutputs b c}

def innerStepOfIndex {b c : Nat} (index : ValenceFiveInnerIndex b c) :
    CGFusionStep b c index.val :=
  cgFusionStepOfFusionOK b c index.val
    (List.mem_filter.mp index.property).2

private theorem fixedRight_intermediate_le_total {a b c y : Nat}
    (right : FixedRightCGChannel a b c y) :
    right.intermediate ≤ b + c := by
  unfold FixedRightCGChannel.intermediate
  omega

theorem middle_intermediate_mem_innerOutputs {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    middle.first.intermediate ∈ valenceFiveInnerOutputs b c := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr (Nat.lt_succ_of_le
      (fixedRight_intermediate_le_total middle.first)),
    fixedRight_inner_fusionOK middle.first⟩

theorem target_m_mem_innerOutputs {a b c d e : Nat}
    (target : ValenceFiveRightCarrier a b c d e) :
    target.m ∈ valenceFiveInnerOutputs b c := by
  apply List.mem_filter.mpr
  have horder := Nat.le_min.mp target.inner.order_le
  have houtput := target.inner.output_eq
  exact ⟨List.mem_range.mpr (by omega), target.inner.fusionOK⟩

def valenceFiveRightFiber {a b c d e : Nat}
    (index : ValenceFiveInnerIndex b c) :
    List (ValenceFiveRightCarrier a b c d e) :=
  (fixedRightChannels a index.val d e).map fun second =>
    { m := index.val, inner := innerStepOfIndex index, second := second }

def valenceFiveRightCarriers (a b c d e : Nat) :
    List (ValenceFiveRightCarrier a b c d e) :=
  (valenceFiveInnerOutputs b c).attach.flatMap valenceFiveRightFiber

def valenceFiveSecondKernelAt {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e) : Q' :=
  if h : middle.first.intermediate = target.m then
    valenceFiveSecondBlockKernelAt middle target h
  else 0

theorem valenceFiveSecondKernelAt_nonnegative {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e) :
    (0 : Q') ≤ valenceFiveSecondKernelAt middle target := by
  unfold valenceFiveSecondKernelAt
  split
  · exact valenceFiveSecondBlockKernelAt_nonnegative _ _ _
  · exact Q'.le_refl' 0

/-- On the canonical fixed-`m` middle fiber, the zero-extended global entry
is exactly the local physical Schur entry. -/
theorem valenceFiveSecondKernelAt_middleOfInnerLeft
    {a b c d e : Nat} (target : ValenceFiveRightCarrier a b c d e)
    (left : FixedLeftCGChannel a target.m d e) :
    valenceFiveSecondKernelAt
        (middleOfInnerLeft target.inner left) target ≈
      physicalSchurRecouplingKernelAt left target.second := by
  cases target with
  | mk m inner second =>
      cases inner with
      | mk order orderLe output =>
          cases output
          have hleft := middleOfInnerLeft_secondLeftAt
            ({ order := order, order_le := orderLe, output_eq := rfl } :
              CGFusionStep b c (b + c - 2 * order)) left
          have hintermediate := middleOfInnerLeft_first_intermediate
            ({ order := order, order_le := orderLe, output_eq := rfl } :
              CGFusionStep b c (b + c - 2 * order)) left
          simp only [middleSecondLeftAt] at hleft
          unfold valenceFiveSecondKernelAt
          rw [dif_pos hintermediate]
          unfold valenceFiveSecondBlockKernelAt
          rw [hleft]
          exact Q'.eqv_refl _

/-! ## 5. Exact global row normalization -/

private def middleInnerIndex {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    ValenceFiveInnerIndex b c :=
  ⟨middle.first.intermediate,
    middle_intermediate_mem_innerOutputs middle⟩

private theorem second_row_fiber_mass {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e)
    (index : ValenceFiveInnerIndex b c) :
    listQSum (valenceFiveSecondKernelAt middle)
        (valenceFiveRightFiber (a := a) (d := d) (e := e) index) ≈
      deterministicKernel (fun _ : Unit => middleInnerIndex middle)
        () index := by
  by_cases hintermediate : middle.first.intermediate = index.val
  · have hindex : index = middleInnerIndex middle :=
      Subtype.ext hintermediate.symm
    subst index
    simp only [valenceFiveRightFiber, listQSum_map,
      valenceFiveSecondKernelAt, valenceFiveSecondBlockKernelAt,
      deterministicKernel, middleInnerIndex]
    exact physicalSchurRecoupling_list_row_normalized middle.secondLeft
  · have hindex : index ≠ middleInnerIndex middle := by
      intro heq
      exact hintermediate (congrArg Subtype.val heq).symm
    simp only [valenceFiveRightFiber, listQSum_map,
      valenceFiveSecondKernelAt, deterministicKernel,
      hintermediate, hindex, if_false]
    exact listQSum_zero _

theorem valenceFiveSecondKernel_row_normalized {a b c d e : Nat}
    (middle : ValenceFiveMiddleCarrier a b c d e) :
    listQSum (valenceFiveSecondKernelAt middle)
      (valenceFiveRightCarriers a b c d e) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun index => listQSum (valenceFiveSecondKernelAt middle)
        (valenceFiveRightFiber (a := a) (d := d) (e := e) index))
      (valenceFiveInnerOutputs b c).attach) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · refine Q'.eqv_trans _
      (listQSum
        (deterministicKernel (fun _ : Unit => middleInnerIndex middle) ())
        (valenceFiveInnerOutputs b c).attach) _ ?_ ?_
    · exact listQSum_congr
        (fun index => second_row_fiber_mass middle index)
        (valenceFiveInnerOutputs b c).attach
    · exact deterministicKernel_row_normalized
        (fun _ : Unit => middleInnerIndex middle) ()
        (valenceFiveInnerOutputs b c).attach
        (attach_nodup_of_nodup _
          (valenceFiveInnerOutputs_nodup b c))
        (List.mem_attach _ (middleInnerIndex middle))

/-! ## 6. Exact global column normalization -/

private theorem listQSum_eq_filter_of_zero
    (weight : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = false → weight item ≈ 0) →
      listQSum weight items ≈ listQSum weight (items.filter test)
  | [], _ => Q'.eqv_refl _
  | head :: tail, hzero => by
      have htail : ∀ item, item ∈ tail → test item = false →
          weight item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero weight test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero weight test tail htail)

private theorem listQSum_eqv_of_nodup_same_members_nonnegative
    {State : Type} [DecidableEq State]
    (value : State → Q') (left right : List State)
    (hleft : left.Nodup) (hright : right.Nodup)
    (hmembers : ∀ state, state ∈ left ↔ state ∈ right)
    (hnonnegative : ∀ state, (0 : Q') ≤ value state) :
    listQSum value left ≈ listQSum value right := by
  have hleftRight : listQSum value left ≤ listQSum value right :=
    listQSum_le_of_injective left right value value (fun state => state)
      hleft
      (fun state hstate => (hmembers state).mp hstate)
      (fun _ _ _ _ heq => heq)
      (fun _ _ => Q'.le_refl' _)
      (fun state _ => hnonnegative state)
  have hrightLeft : listQSum value right ≤ listQSum value left :=
    listQSum_le_of_injective right left value value (fun state => state)
      hright
      (fun state hstate => (hmembers state).mpr hstate)
      (fun _ _ _ _ heq => heq)
      (fun _ _ => Q'.le_refl' _)
      (fun state _ => hnonnegative state)
  exact Int.le_antisymm hleftRight hrightLeft

private theorem second_column_filter {a b c d e : Nat}
    (target : ValenceFiveRightCarrier a b c d e) :
    listQSum (fun middle => valenceFiveSecondKernelAt middle target)
        (valenceFiveMiddleCarriers a b c d e) ≈
      listQSum (fun middle => valenceFiveSecondKernelAt middle target)
        (valenceFiveMiddleWithIntermediate a b c d e target.m) := by
  apply listQSum_eq_filter_of_zero
  intro middle _ htest
  have hintermediate : middle.first.intermediate ≠ target.m :=
    of_decide_eq_false htest
  unfold valenceFiveSecondKernelAt
  rw [dif_neg hintermediate]
  exact Q'.eqv_refl _

private theorem second_column_reindex {a b c d e : Nat}
    (target : ValenceFiveRightCarrier a b c d e) :
    listQSum (fun middle => valenceFiveSecondKernelAt middle target)
        (valenceFiveMiddleWithIntermediate a b c d e target.m) ≈
      listQSum (fun middle => valenceFiveSecondKernelAt middle target)
        (valenceFiveMiddleAtInner (a := a) (d := d) (e := e)
          target.inner) := by
  apply listQSum_eqv_of_nodup_same_members_nonnegative
  · exact List.filter_sublist.nodup
      (valenceFiveMiddleCarriers_nodup a b c d e)
  · exact valenceFiveMiddleAtInner_nodup target.inner
  · intro middle
    exact mem_valenceFiveMiddleWithIntermediate_iff_atInner
      target.inner middle
  · intro middle
    exact valenceFiveSecondKernelAt_nonnegative middle target

private theorem second_column_inner_mass {a b c d e : Nat}
    (target : ValenceFiveRightCarrier a b c d e) :
    listQSum (fun middle => valenceFiveSecondKernelAt middle target)
        (valenceFiveMiddleAtInner (a := a) (d := d) (e := e)
          target.inner) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left => physicalSchurRecouplingKernelAt left target.second)
      (fixedLeftChannels a target.m d e)) _ ?_ ?_
  · unfold valenceFiveMiddleAtInner
    rw [listQSum_map]
    exact listQSum_congr
      (fun left => valenceFiveSecondKernelAt_middleOfInnerLeft target left)
      (fixedLeftChannels a target.m d e)
  · exact physicalSchurRecoupling_list_column_normalized target.second

theorem valenceFiveSecondKernel_column_normalized {a b c d e : Nat}
    (target : ValenceFiveRightCarrier a b c d e) :
    listQSum (fun middle => valenceFiveSecondKernelAt middle target)
      (valenceFiveMiddleCarriers a b c d e) ≈ 1 := by
  exact Q'.eqv_trans _ _ _ (second_column_filter target)
    (Q'.eqv_trans _ _ _ (second_column_reindex target)
      (second_column_inner_mass target))

/-! ## 7. The second block and the completed valence-five matrix -/

def valenceFiveSecondBistochasticKernel (a b c d e : Nat) :
    FiniteBistochasticQKernel
      (ValenceFiveMiddleCarrier a b c d e)
      (ValenceFiveRightCarrier a b c d e) where
  sources := valenceFiveMiddleCarriers a b c d e
  targets := valenceFiveRightCarriers a b c d e
  weight := valenceFiveSecondKernelAt
  weight_nonnegative := valenceFiveSecondKernelAt_nonnegative
  row_normalized := valenceFiveSecondKernel_row_normalized
  column_normalized := valenceFiveSecondKernel_column_normalized

/-- **The two aligned valence-five associators compose to one exact finite
bistochastic matrix from the complete left tree to the complete final right
tree.** -/
def valenceFiveBistochasticKernel (a b c d e : Nat) :
    FiniteBistochasticQKernel
      (ValenceFiveLeftCarrier a b c d e)
      (ValenceFiveRightCarrier a b c d e) :=
  compose (valenceFiveFirstBistochasticKernel a b c d e)
    (valenceFiveSecondBistochasticKernel a b c d e) rfl

end YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock

#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.middleOfInnerLeft_first_intermediate
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.middleOfInnerLeft_secondLeftAt
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.middleOfInnerLeft_roundtrip
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveMiddleCarriers_nodup
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveMiddleCarriers_complete
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.mem_valenceFiveMiddleWithIntermediate_iff_atInner
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.middle_intermediate_mem_innerOutputs
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.target_m_mem_innerOutputs
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveSecondKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveSecondKernelAt_middleOfInnerLeft
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveSecondKernel_row_normalized
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveSecondKernel_column_normalized
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveSecondBistochasticKernel
#print axioms YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock.valenceFiveBistochasticKernel
