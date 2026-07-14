/-
# Source-side colored strict canonical carrier

The root-only restriction does not exclude canonical trees whose vertices
cannot come from two compatible source families.  This module retains the
two switched source masks as a color certificate.  Both color classes are
compatible, and the terminal tree, background, and external masks are all
covered by their union.

Every genuine exceptional source maps into a duplicate-free finite colored
carrier.  The map is injective because the switched source masks recover the
original source pair, and its weight is exactly the source weight.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction
import YMGap.Continuum.XiExceptionalParallelSubmaskBlock

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalMergedResidualCarrier
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalCrossPairTreeNormalization
open YMGap.Continuum.XiExceptionalTreeBackgroundNormalization
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiAdmissibleSourceSwitch
open YMGap.Continuum.XiNonexceptionalTargetValidity
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction
open YMGap.Continuum.XiExceptionalParallelSubmaskBlock
open YMGap.Continuum.XiExceptionalTargetNodup

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def switchedSourceColors
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) : MaskPair Gamma.length :=
  switchedBranchCode Gamma b2 pair

theorem switchedSourceColors_left_at
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedSourceColors Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedSourceColors switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem switchedSourceColors_right_at
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedSourceColors Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedSourceColors switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem switchedSourceColors_union_at
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (unionBits (switchedSourceColors Gamma b2 pair).1
      (switchedSourceColors Gamma b2 pair).2).at i =
        (pair.1.at i || pair.2.at i) := by
  rw [unionBits_at,
    switchedSourceColors_left_at Gamma b2 pair i hi,
    switchedSourceColors_right_at Gamma b2 pair i hi]
  unfold switchedLeft switchedRight swapLeftMask swapRightMask bitMask
  cases forwardComponent Gamma.length (incAtDistinct Gamma)
      (fun j => pair.1.at j) (fun j => pair.2.at j)
      (predAt Gamma b2) i <;>
    cases pair.1.at i <;> cases pair.2.at i <;> rfl

private theorem union_true_of_differentBits (a b : Bool)
    (h : differentBits a b = true) : (a || b) = true := by
  cases a <;> cases b <;> simp_all [differentBits]

private theorem bit_index_lt_of_true {n : Nat}
    (bits : OccBitVec n) (i : Nat) (hbit : bits.at i = true) : i < n := by
  by_cases hlt : i < n
  · exact hlt
  · have hge : n ≤ i := by omega
    rw [bitVec_at_false_of_ge bits i hge] at hbit
    cases hbit

theorem routedLeftResidual_sub_switchedColorLeft
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbit : (routedLeftResidual Gamma qP b1 b2 entry).at i = true) :
    (switchedSourceColors Gamma b2 entry.1).1.at i = true := by
  unfold routedLeftResidual at hbit
  dsimp only at hbit
  rw [residualBits_at _ _ i hi] at hbit
  exact ((Bool.and_eq_true _ _).mp hbit).2

theorem routedRightResidual_sub_switchedColorRight
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbit : (routedRightResidual Gamma qP b1 b2 entry).at i = true) :
    (switchedSourceColors Gamma b2 entry.1).2.at i = true := by
  unfold routedRightResidual at hbit
  dsimp only at hbit
  rw [residualBits_at _ _ i hi] at hbit
  exact ((Bool.and_eq_true _ _).mp hbit).2

theorem entryUnsafeLeftBits_sub_switchedColorLeft
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbit : (entryUnsafeLeftBits Gamma qP b1 b2 entry).at i = true) :
    (switchedSourceColors Gamma b2 entry.1).1.at i = true := by
  unfold entryUnsafeLeftBits at hbit
  rw [unsafeLeftBits_at _ _ i hi] at hbit
  exact routedLeftResidual_sub_switchedColorLeft
    Gamma qP b1 b2 entry i hi ((Bool.and_eq_true _ _).mp hbit).2

theorem entryTreeBackground_sub_switchedColorLeft
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length)
    (hbit : (entryTreeBackground Gamma qP b1 b2 entry).at i = true) :
    (switchedSourceColors Gamma b2 entry.1).1.at i = true := by
  unfold entryTreeBackground at hbit
  rw [routedBackground_at _ _ i hi] at hbit
  exact routedLeftResidual_sub_switchedColorLeft
    Gamma qP b1 b2 entry i hi ((Bool.and_eq_true _ _).mp hbit).2

/-! ## Both normalization phases preserve source-color coverage -/

theorem entryCrossTreeState_all_sourceColors
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryCrossTreeState Gamma qP b1 b2 entry).AllGood
      (fun i => (unionBits
        (switchedSourceColors Gamma b2 entry.1).1
        (switchedSourceColors Gamma b2 entry.1).2).at i = true) := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hseedLt := (forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    path.seed_true).1
  refine
    { tree := ?_
      left := ?_
      right := ?_ }
  · intro i hiTree
    have hiPath : i ∈ path.indexWalk.vertices := by
      rw [entryCrossTreeState, OTree.ofWalk_vertices,
        conflictWalkOfDisagreement_vertices] at hiTree
      exact hiTree
    have hiLt := walk_vertices_lt_of_seed Gamma.length
      (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
      path.indexWalk hseedLt i hiPath
    have hdiff := walk_vertices_different_of_seed Gamma.length
      (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)
      (predAt Gamma b2) path.indexWalk path.seed_true i hiPath
    rw [switchedSourceColors_union_at Gamma b2 pair i hiLt]
    exact union_true_of_differentBits _ _ hdiff
  · intro i hi hleft
    rw [unionBits_at]
    rw [entryUnsafeLeftBits_sub_switchedColorLeft
      Gamma qP b1 b2 entry i hi hleft]
    rfl
  · intro i hi hright
    rw [unionBits_at]
    rw [routedRightResidual_sub_switchedColorRight
      Gamma qP b1 b2 entry i hi hright]
    cases (switchedSourceColors Gamma b2 entry.1).1.at i <;> rfl

theorem entryCrossExhaust_all_sourceColors
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryCrossExhaust Gamma qP b1 b2 entry).AllGood
      (fun i => (unionBits
        (switchedSourceColors Gamma b2 entry.1).1
        (switchedSourceColors Gamma b2 entry.1).2).at i = true) :=
  (entryCrossTreeState_all_sourceColors Gamma qP b1 b2 entry).exhaust

theorem entryTreeBackgroundState_all_sourceColors
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryTreeBackgroundState Gamma qP b1 b2 entry).AllGood
      (fun i => (unionBits
        (switchedSourceColors Gamma b2 entry.1).1
        (switchedSourceColors Gamma b2 entry.1).2).at i = true) := by
  have hcross := entryCrossExhaust_all_sourceColors
    Gamma qP b1 b2 entry
  refine
    { tree := hcross.tree
      background := ?_
      external := ?_ }
  · intro i hi hbg
    rw [unionBits_at]
    rw [entryTreeBackground_sub_switchedColorLeft
      Gamma qP b1 b2 entry i hi hbg]
    rfl
  · intro i hi hext
    change (unionBits
      (entryCrossExhaust Gamma qP b1 b2 entry).left
      (entryCrossExhaust Gamma qP b1 b2 entry).right).at i = true at hext
    rw [unionBits_at] at hext
    rcases (Bool.or_eq_true _ _).mp hext with hleft | hright
    · exact hcross.left i hi hleft
    · exact hcross.right i hi hright

theorem entryTreeExhaust_all_sourceColors
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryTreeExhaust Gamma qP b1 b2 entry).AllGood
      (fun i => (unionBits
        (switchedSourceColors Gamma b2 entry.1).1
        (switchedSourceColors Gamma b2 entry.1).2).at i = true) :=
  (entryTreeBackgroundState_all_sourceColors
    Gamma qP b1 b2 entry).exhaust

/-! ## Proof-free colored carrier and validity certificate -/

structure SourceColoredRootAttachmentCarrierCode (N : Nat) where
  carrier : RootAttachmentCarrierCode N
  colors : MaskPair N
deriving DecidableEq

def sourceSideColorValidB
    (Gamma : List (Polymer L))
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) : Bool :=
  familyCompatibleB (selectByBits Gamma code.colors.1) &&
    familyCompatibleB (selectByBits Gamma code.colors.2) &&
      code.carrier.tree.vertices.all (fun i =>
        code.colors.1.at i || code.colors.2.at i) &&
        occurrenceSubmaskB code.carrier.background
          (unionBits code.colors.1 code.colors.2) &&
          occurrenceSubmaskB code.carrier.external
            (unionBits code.colors.1 code.colors.2)

def entrySourceColoredRootAttachmentCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    SourceColoredRootAttachmentCarrierCode Gamma.length :=
  ⟨entryRootAttachmentCarrierCode Gamma qP b1 b2 entry,
    switchedSourceColors Gamma b2 entry.1⟩

theorem entrySourceColoredRootAttachmentCarrierCode_valid
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    sourceSideColorValidB Gamma
      (entrySourceColoredRootAttachmentCarrierCode
        Gamma qP b1 b2 entry) = true := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let afacts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    facts.source_admissible
  let final := entryTreeExhaust Gamma qP b1 b2 entry
  let colors := switchedSourceColors Gamma b2 pair
  have hleft : familyCompatibleB
      (selectByBits Gamma colors.1) = true := by
    simpa [colors, switchedSourceColors, leftFamily] using
      (switched_left_family_compatible Gamma qP b1 b2 pair afacts)
  have hright : familyCompatibleB
      (selectByBits Gamma colors.2) = true := by
    simpa [colors, switchedSourceColors, rightFamily] using
      (switched_right_family_compatible Gamma qP b1 b2 pair afacts)
  have hgood := entryTreeExhaust_all_sourceColors
    Gamma qP b1 b2 entry
  have htree :
      (oTreeToRootAttachmentCode
        (N := Gamma.length) final.tree).vertices.all
          (fun i => colors.1.at i || colors.2.at i) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    have hiFinal := (oTreeToRootAttachmentCode_vertices
      (N := Gamma.length) final.tree i).mp hi
    have hc := hgood.tree i hiFinal
    rw [unionBits_at] at hc
    exact hc
  have hbackground : occurrenceSubmaskB final.background
      (unionBits colors.1 colors.2) = true := by
    apply occurrenceSubmaskB_complete
    intro i hbit
    exact hgood.background i
      (bit_index_lt_of_true final.background i hbit) hbit
  have hexternal : occurrenceSubmaskB final.external
      (unionBits colors.1 colors.2) = true := by
    apply occurrenceSubmaskB_complete
    intro i hbit
    exact hgood.external i
      (bit_index_lt_of_true final.external i hbit) hbit
  unfold sourceSideColorValidB
    entrySourceColoredRootAttachmentCarrierCode
    entryRootAttachmentCarrierCode
  dsimp only
  rw [hleft, hright, htree, hbackground, hexternal]
  rfl

/-! ## Duplicate-free finite enumeration -/

def sourceColoredRootAttachmentCarrierCodes (N fuel : Nat) :
    List (SourceColoredRootAttachmentCarrierCode N) :=
  (rootAttachmentCarrierCodes N fuel).flatMap (fun carrier =>
    (maskPairs N).map (fun colors =>
      SourceColoredRootAttachmentCarrierCode.mk carrier colors))

theorem sourceColoredRootAttachmentCarrierCodes_nodup (N fuel : Nat) :
    (sourceColoredRootAttachmentCarrierCodes N fuel).Nodup := by
  unfold sourceColoredRootAttachmentCarrierCodes
  apply nodup_flatMap_map₂ SourceColoredRootAttachmentCarrierCode.mk
    (rootAttachmentCarrierCodes N fuel) (maskPairs N)
    (rootAttachmentCarrierCodes_nodup N fuel) (maskPairs_nodup N)
  intro carrier _ colors _ carrier' _ colors' _ h
  exact ⟨congrArg SourceColoredRootAttachmentCarrierCode.carrier h,
    congrArg SourceColoredRootAttachmentCarrierCode.colors h⟩

theorem entrySourceColoredRootAttachmentCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entrySourceColoredRootAttachmentCarrierCode Gamma qP b1 b2 entry ∈
      sourceColoredRootAttachmentCarrierCodes
        Gamma.length Gamma.length := by
  unfold sourceColoredRootAttachmentCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨entryRootAttachmentCarrierCode Gamma qP b1 b2 entry,
    entryRootAttachmentCarrierCode_mem Gamma qP b1 b2 entry, ?_⟩
  apply List.mem_map.mpr
  exact ⟨switchedSourceColors Gamma b2 entry.1,
    maskPairs_complete _, rfl⟩

theorem entrySourceColoredRootAttachmentCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : entrySourceColoredRootAttachmentCarrierCode
        Gamma qP b1 b2 entry1 =
      entrySourceColoredRootAttachmentCarrierCode
        Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have hcolors := congrArg
    SourceColoredRootAttachmentCarrierCode.colors hcode
  have hpairs := switchedBranchCode_injective_on_source
    Gamma qP b1 b2 entry1.1 entry2.1 entry1.2 entry2.2 hcolors
  exact Subtype.ext hpairs

/-! ## Exact source weight in the certified carrier -/

def sourceColoredRootAttachmentCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) : Q' :=
  if sourceSideColorValidB Gamma code then
    sourceRootStrictCarrierCodeWeight
      w Gamma qP b1 b2 label code.carrier
  else 0

theorem sourceColoredRootAttachmentCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    (0 : Q') ≤ sourceColoredRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label code := by
  unfold sourceColoredRootAttachmentCarrierCodeWeight
  split
  · exact sourceRootStrictCarrierCodeWeight_nonnegative
      hw Gamma qP b1 b2 label code.carrier
  · exact Q'.le_refl' _

theorem entrySourceColoredRootAttachmentCarrierCode_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    sourceColoredRootAttachmentCarrierCodeWeight
        w Gamma qP b1 b2 label
        (entrySourceColoredRootAttachmentCarrierCode
          Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  unfold sourceColoredRootAttachmentCarrierCodeWeight
  rw [entrySourceColoredRootAttachmentCarrierCode_valid
    Gamma qP b1 b2 entry]
  simp only [if_true]
  unfold entrySourceColoredRootAttachmentCarrierCode
  dsimp only
  rw [entry_sourceRootStrictCarrierCodeWeight_eq
    w Gamma qP b1 b2 label entry]
  exact entryRootAttachmentCarrierCode_strict_weight_eqv_source
    w Gamma qP b1 b2 label entry

theorem fullExceptionalSource_sum_le_sourceColoredCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight
          w qP b1 b2 Gamma label entry.1)
        (fullExceptionalSource Gamma qP b1 b2) ≤
      qListSum
        (sourceColoredRootAttachmentCarrierCodeWeight
          w Gamma qP b1 b2 label)
        (sourceColoredRootAttachmentCarrierCodes
          Gamma.length Gamma.length) := by
  apply qListSum_le_of_injective
    (fullExceptionalSource Gamma qP b1 b2)
    (sourceColoredRootAttachmentCarrierCodes
      Gamma.length Gamma.length)
    (fun entry => occurrencePairWeight
      w qP b1 b2 Gamma label entry.1)
    (sourceColoredRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label)
    (entrySourceColoredRootAttachmentCarrierCode Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2)
  · intro entry _
    exact entrySourceColoredRootAttachmentCarrierCode_mem
      Gamma qP b1 b2 entry
  · intro entry1 _ entry2 _ hcode
    exact entrySourceColoredRootAttachmentCarrierCode_injective
      Gamma qP b1 b2 entry1 entry2 hcode
  · intro entry _
    exact Q'.ge_of_eqv
      (entrySourceColoredRootAttachmentCarrierCode_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · intro code _
    exact sourceColoredRootAttachmentCarrierCodeWeight_nonnegative
      hw Gamma qP b1 b2 label code

/-! ## Closed certificate fence

The three-polymer payment fence is excluded for every possible coloring,
while its direct two-vertex trunk has a valid certificate. -/

private abbrev CTL := toyLattice
private instance instDecidableEqCTLPlaquette : DecidableEq CTL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def cp : CTL.Plaquette := (0, 0)
private def cq : CTL.Plaquette := (1, 0)
private def CX : Polymer CTL := [cp, cq]
private def CY : Polymer CTL := [cq, cp]
private def CZ : Polymer CTL := [cp, cp]
private def CGamma : List (Polymer CTL) := [CX, CY, CZ]

private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

private def zero3 : OccBitVec 3 := bits3 false false false
private def directTree : RootAttachmentTreeCode CGamma.length :=
  ⟨0, [(0, 1)]⟩
private def cliqueTrees : List (RootAttachmentTreeCode CGamma.length) :=
  [⟨0, [(0, 1), (0, 2)]⟩,
   ⟨0, [(0, 1), (1, 2)]⟩,
   ⟨0, [(0, 2), (0, 1)]⟩,
   ⟨0, [(0, 2), (2, 1)]⟩]

private def emptyPayloadColoredCode
    (tree : RootAttachmentTreeCode CGamma.length)
    (colors : MaskPair CGamma.length) :
    SourceColoredRootAttachmentCarrierCode CGamma.length :=
  ⟨⟨tree, zero3, zero3⟩, colors⟩

private def allCliqueColorings :
    List (SourceColoredRootAttachmentCarrierCode CGamma.length) :=
  cliqueTrees.flatMap (fun tree =>
    (maskPairs CGamma.length).map (emptyPayloadColoredCode tree))

theorem direct_tree_has_valid_source_color_certificate :
    sourceSideColorValidB CGamma
      (emptyPayloadColoredCode directTree
        (bits3 true false false, bits3 false true false)) = true := by
  decide

set_option maxRecDepth 10000 in
theorem incompatibility_clique_rejected_for_every_source_coloring :
    allCliqueColorings.all
      (fun code => !(sourceSideColorValidB CGamma code)) = true := by
  decide

#print axioms switchedSourceColors_union_at
#print axioms routedLeftResidual_sub_switchedColorLeft
#print axioms routedRightResidual_sub_switchedColorRight
#print axioms entryUnsafeLeftBits_sub_switchedColorLeft
#print axioms entryTreeBackground_sub_switchedColorLeft
#print axioms entryCrossTreeState_all_sourceColors
#print axioms entryCrossExhaust_all_sourceColors
#print axioms entryTreeBackgroundState_all_sourceColors
#print axioms entryTreeExhaust_all_sourceColors
#print axioms entrySourceColoredRootAttachmentCarrierCode_valid
#print axioms sourceColoredRootAttachmentCarrierCodes_nodup
#print axioms entrySourceColoredRootAttachmentCarrierCode_mem
#print axioms entrySourceColoredRootAttachmentCarrierCode_injective
#print axioms sourceColoredRootAttachmentCarrierCodeWeight_nonnegative
#print axioms entrySourceColoredRootAttachmentCarrierCode_weight_eqv_source
#print axioms fullExceptionalSource_sum_le_sourceColoredCarrier
#print axioms direct_tree_has_valid_source_color_certificate
#print axioms incompatibility_clique_rejected_for_every_source_coloring

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCarrier
