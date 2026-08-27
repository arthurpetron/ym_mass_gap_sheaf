/-
# The third valence-six associator as a finite bistochastic matrix

After the first two valence-six moves, the written common carrier is organized
by the transient output `z`.  The third associator preserves instead the two
physical inner outputs

    b,c -> m,    m,d -> n,

and changes the channel `(a,n),e -> f` to `a,(n,e) -> f`.

This module enumerates the physical `(m,n)` sectors, constructs the canonical
change of variables between that carrier and the written `z` carrier, and
proves the two maps are inverse.  The canonical third matrix is an indexed sum
of physical Schur matrices.  Pulling its source coordinate back along the
proved finite equivalence gives a matrix whose written source list is
literally the prefix matrix's target list.  Exact composition therefore closes
the complete valence-six associator.

Constructive contract: bounded proof-carrying lists and exact `Q'` algebra
only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernelComposition
import YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
import YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock

namespace YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CanonicalValenceFourChannelBridge
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2OrderedRightGramOrthogonality
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixIteratedSchurTransport
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Complete physical inner-pair sectors -/

structure ValenceSixInnerPair (b c d : Nat) where
  m : Nat
  n : Nat
  innerBC : CGFusionStep b c m
  innerMD : CGFusionStep m d n

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

private theorem innerPair_eq_of_m_n {b c d : Nat}
    (left right : ValenceSixInnerPair b c d)
    (hm : left.m = right.m) (hn : left.n = right.n) : left = right := by
  cases left with
  | mk leftM leftN leftBC leftMD =>
      cases right with
      | mk rightM rightN rightBC rightMD =>
          dsimp only at hm hn
          subst rightM
          subst rightN
          have hBC : leftBC = rightBC :=
            cgFusionStep_unique leftBC rightBC
          subst rightBC
          have hMD : leftMD = rightMD :=
            cgFusionStep_unique leftMD rightMD
          subst rightMD
          rfl

private def innerPairCode {b c d : Nat}
    (pair : ValenceSixInnerPair b c d) : Nat × Nat :=
  (pair.m, pair.n)

private theorem innerPairCode_injective {b c d : Nat}
    (left right : ValenceSixInnerPair b c d)
    (hcode : innerPairCode left = innerPairCode right) : left = right := by
  apply innerPair_eq_of_m_n
  · exact congrArg Prod.fst hcode
  · exact congrArg Prod.snd hcode

private instance innerPairDecidableEq (b c d : Nat) :
    DecidableEq (ValenceSixInnerPair b c d) := fun left right =>
  match decEq (innerPairCode left) (innerPairCode right) with
  | isTrue hcode => isTrue (innerPairCode_injective left right hcode)
  | isFalse hcode =>
      isFalse (fun heq => hcode (congrArg innerPairCode heq))

private theorem fusionStep_output_mem_innerOutputs {a b output : Nat}
    (step : CGFusionStep a b output) :
    output ∈ valenceFiveInnerOutputs a b := by
  apply List.mem_filter.mpr
  have horder := Nat.le_min.mp step.order_le
  have hout := step.output_eq
  exact ⟨List.mem_range.mpr (by omega), step.fusionOK⟩

def valenceSixInnerPairFiber {b c d : Nat}
    (mIndex : ValenceFiveInnerIndex b c) :
    List (ValenceSixInnerPair b c d) :=
  (valenceFiveInnerOutputs mIndex.val d).attach.map fun nIndex =>
    { m := mIndex.val
      n := nIndex.val
      innerBC := innerStepOfIndex mIndex
      innerMD := innerStepOfIndex nIndex }

def valenceSixInnerPairs (b c d : Nat) :
    List (ValenceSixInnerPair b c d) :=
  (valenceFiveInnerOutputs b c).attach.flatMap
    valenceSixInnerPairFiber

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

private theorem innerPairFiber_nodup {b c d : Nat}
    (mIndex : ValenceFiveInnerIndex b c) :
    (valenceSixInnerPairFiber (d := d) mIndex).Nodup := by
  unfold valenceSixInnerPairFiber
  apply nodup_map_of_injective
  · intro left right heq
    apply Subtype.ext
    exact congrArg (fun pair => pair.n) heq
  · exact attach_nodup_of_nodup _
      (valenceFiveInnerOutputs_nodup mIndex.val d)

theorem valenceSixInnerPairs_nodup (b c d : Nat) :
    (valenceSixInnerPairs b c d).Nodup := by
  unfold valenceSixInnerPairs
  apply nodup_flatMap_of_disjoint_blocks
  · exact attach_nodup_of_nodup _ (valenceFiveInnerOutputs_nodup b c)
  · intro index _
    exact innerPairFiber_nodup index
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftN, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightN, _, hrightEq⟩ := List.mem_map.mp hright
    have hm : left.val = right.val := by
      exact congrArg (fun pair => pair.m)
        (hleftEq.trans hrightEq.symm)
    exact hne (Subtype.ext hm)

theorem valenceSixInnerPairs_complete {b c d : Nat}
    (pair : ValenceSixInnerPair b c d) :
    pair ∈ valenceSixInnerPairs b c d := by
  let mIndex : ValenceFiveInnerIndex b c :=
    ⟨pair.m, fusionStep_output_mem_innerOutputs pair.innerBC⟩
  let nIndex : ValenceFiveInnerIndex pair.m d :=
    ⟨pair.n, fusionStep_output_mem_innerOutputs pair.innerMD⟩
  apply List.mem_flatMap.mpr
  refine ⟨mIndex, List.mem_attach _ mIndex, ?_⟩
  apply List.mem_map.mpr
  refine ⟨nIndex, List.mem_attach _ nIndex, ?_⟩
  apply innerPair_eq_of_m_n
  · rfl
  · rfl

/-! ## 2. Canonical third Schur block sum -/

abbrev ValenceSixThirdLeftFamily (a e f : Nat)
    {b c d : Nat} (pair : ValenceSixInnerPair b c d) :=
  FixedLeftCGChannel a pair.n e f

abbrev ValenceSixThirdRightFamily (a e f : Nat)
    {b c d : Nat} (pair : ValenceSixInnerPair b c d) :=
  FixedRightCGChannel a pair.n e f

abbrev ValenceSixCanonicalThirdSource (a b c d e f : Nat) :=
  IndexedSource (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)

abbrev ValenceSixRightCarrier (a b c d e f : Nat) :=
  IndexedTarget (valenceSixInnerPairs b c d)
    (ValenceSixThirdRightFamily a e f)

def valenceSixCanonicalThirdBistochasticKernel (a b c d e f : Nat) :
    FiniteBistochasticQKernel
      (ValenceSixCanonicalThirdSource a b c d e f)
      (ValenceSixRightCarrier a b c d e f) :=
  indexedSum
    (valenceSixInnerPairs b c d)
    (valenceSixInnerPairs_nodup b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)

/-! ## 3. Exact change of variables from the written common carrier -/

def fixedRightInnerStep {a b c output : Nat}
    (right : FixedRightCGChannel a b c output) :
    CGFusionStep b c right.intermediate where
  order := right.p
  order_le := right.p_le
  output_eq := rfl

def valenceSixInnerPairOfMiddle {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    ValenceSixInnerPair b c d where
  m := middle.value.m
  n := middle.value.second.intermediate
  innerBC := middle.value.inner
  innerMD := fixedRightInnerStep middle.value.second

def valenceSixThirdLeftOfMiddle {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    FixedLeftCGChannel a middle.value.second.intermediate e f :=
  fixedLeftChannelOfFusion
    a middle.value.second.intermediate e f middle.index.val
    (fixedRight_outer_fusionOK middle.value.second)
    (valenceSixPrefixSuffix middle.index).fusionOK

def valenceSixMiddleToCanonical {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    ValenceSixCanonicalThirdSource a b c d e f where
  index := ⟨valenceSixInnerPairOfMiddle middle,
    valenceSixInnerPairs_complete (valenceSixInnerPairOfMiddle middle)⟩
  value := valenceSixThirdLeftOfMiddle middle

private theorem canonicalMiddle_z_mem_prefixOutputs {a b c d e f : Nat}
    (source : ValenceSixCanonicalThirdSource a b c d e f) :
    source.value.intermediate ∈ valenceSixPrefixOutputs a b c d e f := by
  apply List.mem_filter.mpr
  have hBC := source.index.val.innerBC.output_eq
  have hMD := source.index.val.innerMD.output_eq
  have hk := Nat.le_min.mp source.value.k_le
  exact ⟨List.mem_range.mpr (by
      unfold FixedLeftCGChannel.intermediate
      omega),
    fixedLeft_outer_fusionOK source.value⟩

def valenceSixCanonicalToMiddle {a b c d e f : Nat}
    (source : ValenceSixCanonicalThirdSource a b c d e f) :
    ValenceSixCommonMiddleCarrier a b c d e f where
  index := ⟨source.value.intermediate,
    canonicalMiddle_z_mem_prefixOutputs source⟩
  value :=
    { m := source.index.val.m
      inner := source.index.val.innerBC
      second := middleFirstOfInnerLeft source.index.val.innerMD source.value }

private theorem valenceFiveRight_eq_of_m_p {a b c d e : Nat}
    (left right : ValenceFiveRightCarrier a b c d e)
    (hm : left.m = right.m)
    (hp : left.second.p = right.second.p) : left = right := by
  cases left with
  | mk leftM leftInner leftSecond =>
      cases right with
      | mk rightM rightInner rightSecond =>
          dsimp only at hm hp
          subst rightM
          have hinner : leftInner = rightInner :=
            cgFusionStep_unique leftInner rightInner
          subst rightInner
          have hsecond : leftSecond = rightSecond :=
            fixedRightChannel_eq_of_p_eq leftSecond rightSecond hp
          subst rightSecond
          rfl

private def middleCode {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    (Nat × Nat) × Nat :=
  ((middle.index.val, middle.value.m), middle.value.second.p)

private theorem middleCode_injective {a b c d e f : Nat}
    (left right : ValenceSixCommonMiddleCarrier a b c d e f)
    (hcode : middleCode left = middleCode right) : left = right := by
  rcases left with ⟨leftIndex, leftValue⟩
  rcases right with ⟨rightIndex, rightValue⟩
  have hz : leftIndex.val = rightIndex.val :=
    congrArg (fun code => code.1.1) hcode
  have hindex : leftIndex = rightIndex := Subtype.ext hz
  subst rightIndex
  have hm : leftValue.m = rightValue.m :=
    congrArg (fun code => code.1.2) hcode
  have hp : leftValue.second.p = rightValue.second.p :=
    congrArg Prod.snd hcode
  have hvalue : leftValue = rightValue :=
    valenceFiveRight_eq_of_m_p leftValue rightValue hm hp
  subst rightValue
  rfl

private instance middleDecidableEq (a b c d e f : Nat) :
    DecidableEq (ValenceSixCommonMiddleCarrier a b c d e f) :=
  fun left right =>
    match decEq (middleCode left) (middleCode right) with
    | isTrue hcode => isTrue (middleCode_injective left right hcode)
    | isFalse hcode =>
        isFalse (fun heq => hcode (congrArg middleCode heq))

private def canonicalCode {a b c d e f : Nat}
    (source : ValenceSixCanonicalThirdSource a b c d e f) :
    (Nat × Nat) × Nat :=
  ((source.index.val.m, source.index.val.n), source.value.k)

private theorem canonicalCode_injective {a b c d e f : Nat}
    (left right : ValenceSixCanonicalThirdSource a b c d e f)
    (hcode : canonicalCode left = canonicalCode right) : left = right := by
  rcases left with ⟨leftIndex, leftValue⟩
  rcases right with ⟨rightIndex, rightValue⟩
  have hm : leftIndex.val.m = rightIndex.val.m :=
    congrArg (fun code => code.1.1) hcode
  have hn : leftIndex.val.n = rightIndex.val.n :=
    congrArg (fun code => code.1.2) hcode
  have hpair : leftIndex.val = rightIndex.val :=
    innerPair_eq_of_m_n leftIndex.val rightIndex.val hm hn
  have hindex : leftIndex = rightIndex := Subtype.ext hpair
  subst rightIndex
  have hk : leftValue.k = rightValue.k := congrArg Prod.snd hcode
  have hvalue : leftValue = rightValue :=
    fixedLeftChannel_eq_of_k_eq leftValue rightValue hk
  subst rightValue
  rfl

private instance canonicalDecidableEq (a b c d e f : Nat) :
    DecidableEq (ValenceSixCanonicalThirdSource a b c d e f) :=
  fun left right =>
    match decEq (canonicalCode left) (canonicalCode right) with
    | isTrue hcode => isTrue (canonicalCode_injective left right hcode)
    | isFalse hcode =>
        isFalse (fun heq => hcode (congrArg canonicalCode heq))

theorem valenceSixCanonicalToMiddle_leftInverse {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    valenceSixCanonicalToMiddle (valenceSixMiddleToCanonical middle) =
      middle := by
  apply middleCode_injective
  apply Prod.ext
  · apply Prod.ext
    · exact valenceSixThirdLeftOfMiddle_intermediate middle
    · rfl
  · rfl
  where
    valenceSixThirdLeftOfMiddle_intermediate
        (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
        (valenceSixThirdLeftOfMiddle middle).intermediate =
          middle.index.val :=
      fixedLeftChannelOfFusion_intermediate
        a middle.value.second.intermediate e f middle.index.val
        (fixedRight_outer_fusionOK middle.value.second)
        (valenceSixPrefixSuffix middle.index).fusionOK

theorem valenceSixMiddleToCanonical_rightInverse {a b c d e f : Nat}
    (source : ValenceSixCanonicalThirdSource a b c d e f) :
    valenceSixMiddleToCanonical (valenceSixCanonicalToMiddle source) =
      source := by
  apply canonicalCode_injective
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change source.index.val.m + d -
          2 * source.index.val.innerMD.order = source.index.val.n
      exact source.index.val.innerMD.output_eq
  · change couplingOrder a
        (source.index.val.m + d -
          2 * source.index.val.innerMD.order)
        source.value.intermediate = source.value.k
    rw [source.index.val.innerMD.output_eq]
    exact fixedLeft_inner_couplingOrder source.value

/-! ## 4. Written third matrix and complete composition -/

theorem valenceSixCommonMiddleCarriers_nodup (a b c d e f : Nat) :
    (valenceSixPrefixBistochasticKernel a b c d e f).targets.Nodup := by
  exact indexedTargets_nodup
    (valenceSixPrefixOutputs a b c d e f)
    (valenceSixPrefixOutputs_nodup a b c d e f)
    (ValenceSixPrefixLeftFamily a b c d)
    (ValenceSixPrefixRightFamily a b c d)
    (fun z => valenceFiveBistochasticKernel a b c d z)
    (fun z => valenceFiveRightCarriers_nodup a b c d z)

theorem valenceSixCommonMiddleCarriers_complete {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    middle ∈ (valenceSixPrefixBistochasticKernel a b c d e f).targets := by
  exact indexedTargets_complete
    (valenceSixPrefixOutputs a b c d e f)
    (ValenceSixPrefixLeftFamily a b c d)
    (ValenceSixPrefixRightFamily a b c d)
    (fun z => valenceFiveBistochasticKernel a b c d z)
    (fun z target => valenceFiveRightCarriers_complete target)
    middle

theorem valenceSixCanonicalThirdSources_nodup (a b c d e f : Nat) :
    (valenceSixCanonicalThirdBistochasticKernel a b c d e f).sources.Nodup := by
  exact indexedSources_nodup
    (valenceSixInnerPairs b c d)
    (valenceSixInnerPairs_nodup b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    (fun pair => fixedLeftChannels_nodup a pair.n e f)

theorem valenceSixCanonicalThirdSources_complete {a b c d e f : Nat}
    (source : ValenceSixCanonicalThirdSource a b c d e f) :
    source ∈
      (valenceSixCanonicalThirdBistochasticKernel a b c d e f).sources := by
  exact indexedSources_complete
    (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    (fun _ left => fixedLeftChannels_complete left)
    source

def valenceSixThirdKernelAt {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f)
    (target : ValenceSixRightCarrier a b c d e f) : Q' :=
  (valenceSixCanonicalThirdBistochasticKernel a b c d e f).weight
    (valenceSixMiddleToCanonical middle) target

theorem valenceSixThirdKernelAt_nonnegative {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f)
    (target : ValenceSixRightCarrier a b c d e f) :
    (0 : Q') ≤ valenceSixThirdKernelAt middle target :=
  (valenceSixCanonicalThirdBistochasticKernel a b c d e f).weight_nonnegative
    (valenceSixMiddleToCanonical middle) target

theorem valenceSixThirdKernel_row_normalized {a b c d e f : Nat}
    (middle : ValenceSixCommonMiddleCarrier a b c d e f) :
    listQSum (valenceSixThirdKernelAt middle)
        (valenceSixCanonicalThirdBistochasticKernel a b c d e f).targets ≈
      1 :=
  (valenceSixCanonicalThirdBistochasticKernel a b c d e f).row_normalized
    (valenceSixMiddleToCanonical middle)

theorem valenceSixThirdKernel_column_normalized {a b c d e f : Nat}
    (target : ValenceSixRightCarrier a b c d e f) :
    listQSum
        (fun middle => valenceSixThirdKernelAt middle target)
        (valenceSixPrefixBistochasticKernel a b c d e f).targets ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (valenceSixCanonicalThirdBistochasticKernel a b c d e f).weight
          source target)
      (valenceSixCanonicalThirdBistochasticKernel a b c d e f).sources) _ ?_ ?_
  · exact listQSum_equiv
      (valenceSixPrefixBistochasticKernel a b c d e f).targets
      (valenceSixCanonicalThirdBistochasticKernel a b c d e f).sources
      valenceSixMiddleToCanonical valenceSixCanonicalToMiddle
      valenceSixCanonicalToMiddle_leftInverse
      valenceSixMiddleToCanonical_rightInverse
      (valenceSixCommonMiddleCarriers_nodup a b c d e f)
      (valenceSixCanonicalThirdSources_nodup a b c d e f)
      (fun middle _ => valenceSixCanonicalThirdSources_complete
        (valenceSixMiddleToCanonical middle))
      (fun source _ => valenceSixCommonMiddleCarriers_complete
        (valenceSixCanonicalToMiddle source))
      (fun source =>
        (valenceSixCanonicalThirdBistochasticKernel a b c d e f).weight
          source target)
      (fun source =>
        (valenceSixCanonicalThirdBistochasticKernel a b c d e f).weight_nonnegative
          source target)
  · exact
      (valenceSixCanonicalThirdBistochasticKernel a b c d e f).column_normalized
        target

def valenceSixThirdBistochasticKernel (a b c d e f : Nat) :
    FiniteBistochasticQKernel
      (ValenceSixCommonMiddleCarrier a b c d e f)
      (ValenceSixRightCarrier a b c d e f) where
  sources := (valenceSixPrefixBistochasticKernel a b c d e f).targets
  targets := (valenceSixCanonicalThirdBistochasticKernel a b c d e f).targets
  weight := valenceSixThirdKernelAt
  weight_nonnegative := valenceSixThirdKernelAt_nonnegative
  row_normalized := valenceSixThirdKernel_row_normalized
  column_normalized := valenceSixThirdKernel_column_normalized

/-- **All three aligned valence-six associators compose to one exact finite
bistochastic matrix.** -/
def valenceSixBistochasticKernel (a b c d e f : Nat) :
    FiniteBistochasticQKernel
      (ValenceSixLeftCarrier a b c d e f)
      (ValenceSixRightCarrier a b c d e f) :=
  compose
    (valenceSixPrefixBistochasticKernel a b c d e f)
    (valenceSixThirdBistochasticKernel a b c d e f) rfl

/-! ## 5. The old dependent path inside the completed carriers -/

/-- The two physical inner outputs carried by one old three-step target. -/
def valenceSixInnerPairOfPath {a b c d e f : Nat}
    {chain : FixedLeftCGValenceSix a b c d e f}
    (target : ValenceSixRightTreeTarget chain) :
    ValenceSixInnerPair b c d where
  m := target.prior.first.intermediate
  n := target.prior.second.intermediate
  innerBC := fixedRightInnerStep target.prior.first
  innerMD := fixedRightInnerStep target.prior.second

/-- The canonical source of the third block selected by an old dependent
path. -/
def valenceSixCanonicalThirdSourceOfPath {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    ValenceSixCanonicalThirdSource a b c d e f where
  index := ⟨valenceSixInnerPairOfPath target,
    valenceSixInnerPairs_complete (valenceSixInnerPairOfPath target)⟩
  value := valenceSixThirdLeftChannel chain target.prior

/-- The final right-tree carrier selected by an old dependent path. -/
def valenceSixRightCarrierOfPath {a b c d e f : Nat}
    {chain : FixedLeftCGValenceSix a b c d e f}
    (target : ValenceSixRightTreeTarget chain) :
    ValenceSixRightCarrier a b c d e f where
  index := ⟨valenceSixInnerPairOfPath target,
    valenceSixInnerPairs_complete (valenceSixInnerPairOfPath target)⟩
  value := target.third

theorem valenceSixMiddleToCanonical_path {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    valenceSixMiddleToCanonical
        (valenceSixCommonMiddleOfPath chain target) =
      valenceSixCanonicalThirdSourceOfPath chain target := by
  apply canonicalCode_injective
  apply Prod.ext
  · apply Prod.ext <;> rfl
  · rfl

/-- At the canonical path coordinates, the written third-block entry is
literally the old third physical Schur factor. -/
theorem valenceSixThirdKernelAt_path {a b c d e f : Nat}
    (chain : FixedLeftCGValenceSix a b c d e f)
    (target : ValenceSixRightTreeTarget chain) :
    valenceSixThirdKernelAt
        (valenceSixCommonMiddleOfPath chain target)
        (valenceSixRightCarrierOfPath target) ≈
      physicalSchurRecouplingKernelAt
        (valenceSixThirdLeftChannel chain target.prior) target.third := by
  unfold valenceSixThirdKernelAt
  rw [valenceSixMiddleToCanonical_path chain target]
  exact indexedSumWeight_same
    (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    ⟨valenceSixInnerPairOfPath target,
      valenceSixInnerPairs_complete (valenceSixInnerPairOfPath target)⟩
    (valenceSixThirdLeftChannel chain target.prior)
    target.third

end YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixInnerPairs_nodup
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixInnerPairs_complete
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCanonicalThirdBistochasticKernel
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCanonicalToMiddle_leftInverse
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixMiddleToCanonical_rightInverse
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCommonMiddleCarriers_nodup
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCommonMiddleCarriers_complete
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCanonicalThirdSources_nodup
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCanonicalThirdSources_complete
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixThirdKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixThirdKernel_row_normalized
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixThirdKernel_column_normalized
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixThirdBistochasticKernel
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixBistochasticKernel
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixInnerPairOfPath
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixCanonicalThirdSourceOfPath
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixRightCarrierOfPath
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixMiddleToCanonical_path
#print axioms YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock.valenceSixThirdKernelAt_path
