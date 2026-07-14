/-
# Adaptive two-layer ownership for every non-full C12 ear

There are 256 alternating source patterns obtained by freely choosing the
eight off-path occurrences `V4,...,V11`.  The through-V8 chart pays the 128
patterns with `V10` absent.  Of the remaining 128, the unique pattern with
all eight occurrences present is the native canonical source.  This leaves
exactly 127 partial `V10` patterns.

Every proper subset breaks the off-path path `V4-...-V11` at least once.
The carrier below colors the component connected to `V4` with the left
parity and everything after the first gap with the right parity.  Hence
`V4` and `V11` are both external, adjacent selected vertices have opposite
colors, and both target families are compatible.  The union of terminal and
external masks remembers the source, giving deterministic ownership.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned

namespace YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalOwnedFamilyExtension
open YMGap.Continuum.XiExceptionalExternalReserveLimitFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Native
open YMGap.Continuum.XiExceptionalGeneralLongArmC12OwnershipFence
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TwoSourceOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12TaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12RootTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12BadEndTaggedEarOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12AdjacentTagSplitOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward6BipartiteOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Outward8BipartiteOwned
open YMGap.Continuum.XiExceptionalGeneralLongArmC12Through8WithCanonicalOwned

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev G := YMGap.Continuum.XiExceptionalExternalReserveLimitFence.Gamma

set_option maxHeartbeats 10000000

def adaptivePair (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    MaskPair G.length :=
  (bits12 false true false true false x5 false x7 false x9 false x11,
    bits12 true false true false x4 false x6 false x8 false x10 false)

set_option maxRecDepth 1000000 in
theorem adaptivePair_mem (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    adaptivePair x4 x5 x6 x7 x8 x9 x10 x11 ∈
      exceptionalSourceCodes G qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete _, ?_⟩
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

def adaptiveEntry (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  ⟨adaptivePair x4 x5 x6 x7 x8 x9 x10 x11,
    adaptivePair_mem x4 x5 x6 x7 x8 x9 x10 x11⟩

def prefix4 (x4 : Bool) : Bool := x4
def prefix5 (x4 x5 : Bool) : Bool := prefix4 x4 && x5
def prefix6 (x4 x5 x6 : Bool) : Bool := prefix5 x4 x5 && x6
def prefix7 (x4 x5 x6 x7 : Bool) : Bool := prefix6 x4 x5 x6 && x7
def prefix8 (x4 x5 x6 x7 x8 : Bool) : Bool := prefix7 x4 x5 x6 x7 && x8
def prefix9 (x4 x5 x6 x7 x8 x9 : Bool) : Bool :=
  prefix8 x4 x5 x6 x7 x8 && x9
def prefix10 (x4 x5 x6 x7 x8 x9 x10 : Bool) : Bool :=
  prefix9 x4 x5 x6 x7 x8 x9 && x10
def fullPattern (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) : Bool :=
  prefix10 x4 x5 x6 x7 x8 x9 x10 && x11

def t4 (x4 : Bool) : Bool := x4 && !(prefix4 x4)
def t5 (x4 x5 : Bool) : Bool := x5 && prefix5 x4 x5
def t6 (x4 x5 x6 : Bool) : Bool := x6 && !(prefix6 x4 x5 x6)
def t7 (x4 x5 x6 x7 : Bool) : Bool := x7 && prefix7 x4 x5 x6 x7
def t8 (x4 x5 x6 x7 x8 : Bool) : Bool :=
  x8 && !(prefix8 x4 x5 x6 x7 x8)
def t9 (x4 x5 x6 x7 x8 x9 : Bool) : Bool :=
  x9 && prefix9 x4 x5 x6 x7 x8 x9
def t10 (x4 x5 x6 x7 x8 x9 x10 : Bool) : Bool :=
  x10 && !(prefix10 x4 x5 x6 x7 x8 x9 x10)
def t11 (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) : Bool :=
  x11 && fullPattern x4 x5 x6 x7 x8 x9 x10 x11

def adaptiveTerminalBits (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    OccBitVec G.length :=
  bits12 false false false false (t4 x4) (t5 x4 x5)
    (t6 x4 x5 x6) (t7 x4 x5 x6 x7) (t8 x4 x5 x6 x7 x8)
    (t9 x4 x5 x6 x7 x8 x9) (t10 x4 x5 x6 x7 x8 x9 x10)
    (t11 x4 x5 x6 x7 x8 x9 x10 x11)

def adaptiveExternalBits (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    OccBitVec G.length :=
  bits12 false false false false
    (x4 && !(t4 x4)) (x5 && !(t5 x4 x5))
    (x6 && !(t6 x4 x5 x6)) (x7 && !(t7 x4 x5 x6 x7))
    (x8 && !(t8 x4 x5 x6 x7 x8))
    (x9 && !(t9 x4 x5 x6 x7 x8 x9))
    (x10 && !(t10 x4 x5 x6 x7 x8 x9 x10))
    (x11 && !(t11 x4 x5 x6 x7 x8 x9 x10 x11))

def adaptiveTerminalList (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    List (Polymer TL) :=
  (if t4 x4 then [V4] else []) ++
    (if t5 x4 x5 then [V5] else []) ++
    (if t6 x4 x5 x6 then [V6] else []) ++
    (if t7 x4 x5 x6 x7 then [V7] else []) ++
    (if t8 x4 x5 x6 x7 x8 then [V8] else []) ++
    (if t9 x4 x5 x6 x7 x8 x9 then [V9] else []) ++
    (if t10 x4 x5 x6 x7 x8 x9 x10 then [V10] else []) ++
    (if t11 x4 x5 x6 x7 x8 x9 x10 x11 then [V11] else [])

def adaptiveExternalList (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    List (Polymer TL) :=
  (if x4 && !(t4 x4) then [V4] else []) ++
    (if x5 && !(t5 x4 x5) then [V5] else []) ++
    (if x6 && !(t6 x4 x5 x6) then [V6] else []) ++
    (if x7 && !(t7 x4 x5 x6 x7) then [V7] else []) ++
    (if x8 && !(t8 x4 x5 x6 x7 x8) then [V8] else []) ++
    (if x9 && !(t9 x4 x5 x6 x7 x8 x9) then [V9] else []) ++
    (if x10 && !(t10 x4 x5 x6 x7 x8 x9 x10) then [V10] else []) ++
    (if x11 && !(t11 x4 x5 x6 x7 x8 x9 x10 x11) then [V11] else [])

set_option maxRecDepth 1000000 in
theorem adaptiveTerminal_selection (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    selectByBits G (adaptiveTerminalBits x4 x5 x6 x7 x8 x9 x10 x11) =
      adaptiveTerminalList x4 x5 x6 x7 x8 x9 x10 x11 := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

set_option maxRecDepth 1000000 in
theorem adaptiveExternal_selection (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    selectByBits G (adaptiveExternalBits x4 x5 x6 x7 x8 x9 x10 x11) =
      adaptiveExternalList x4 x5 x6 x7 x8 x9 x10 x11 := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

def adaptiveCarrierCode (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    OccCarrierXiCodeAt G :=
  { carrier :=
      { start := 0
        chain := chainFromIndices
          (adaptiveTerminalBits x4 x5 x6 x7 x8 x9 x10 x11)
          shortEarTail }
    external := adaptiveExternalBits x4 x5 x6 x7 x8 x9 x10 x11 }

theorem adaptiveCarrierCode_mem (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11 ∈
      occurrenceCarrierXiCodes G := by
  unfold adaptiveCarrierCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨adaptiveExternalBits x4 x5 x6 x7 x8 x9 x10 x11,
    bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, chainFromIndices
    (adaptiveTerminalBits x4 x5 x6 x7 x8 x9 x10 x11)
    shortEarTail⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨chainFromIndices
    (adaptiveTerminalBits x4 x5 x6 x7 x8 x9 x10 x11)
    shortEarTail, ?_, rfl⟩
  apply chainFromIndices_mem G
    (adaptiveTerminalBits x4 x5 x6 x7 x8 x9 x10 x11)
    shortEarTail G.length
  · decide
  · intro i hi
    simp only [shortEarTail, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

def adaptiveErasedChain (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    ChainCode TL.Plaquette :=
  .step V1 (.step V2 (.step V3 (.terminal
    (adaptiveTerminalList x4 x5 x6 x7 x8 x9 x10 x11))))

theorem adaptiveCarrierCode_erasure (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    eraseOccCarrierXiCode G
        (adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11) =
      ((V0, adaptiveErasedChain x4 x5 x6 x7 x8 x9 x10 x11),
        adaptiveExternalList x4 x5 x6 x7 x8 x9 x10 x11) := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

def sourceLeftList (x5 x7 x9 x11 : Bool) : List (Polymer TL) :=
  [V1, V3] ++ (if x5 then [V5] else []) ++
    (if x7 then [V7] else []) ++ (if x9 then [V9] else []) ++
    (if x11 then [V11] else [])

def sourceRightList (x4 x6 x8 x10 : Bool) : List (Polymer TL) :=
  [V0, V2] ++ (if x4 then [V4] else []) ++
    (if x6 then [V6] else []) ++ (if x8 then [V8] else []) ++
    (if x10 then [V10] else [])

theorem adaptive_left (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    leftFamily G (adaptivePair x4 x5 x6 x7 x8 x9 x10 x11) =
      sourceLeftList x5 x7 x9 x11 := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

theorem adaptive_right (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    rightFamily G (adaptivePair x4 x5 x6 x7 x8 x9 x10 x11) =
      sourceRightList x4 x6 x8 x10 := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c05 : compatibleB V0 V5 = true := by rfl
private theorem c06 : compatibleB V0 V6 = true := by rfl
private theorem c07 : compatibleB V0 V7 = true := by rfl
private theorem c08 : compatibleB V0 V8 = true := by rfl
private theorem c09 : compatibleB V0 V9 = true := by rfl
private theorem c010 : compatibleB V0 V10 = true := by rfl
private theorem c15 : compatibleB V1 V5 = true := by rfl
private theorem c16 : compatibleB V1 V6 = true := by rfl
private theorem c17 : compatibleB V1 V7 = true := by rfl
private theorem c18 : compatibleB V1 V8 = true := by rfl
private theorem c19 : compatibleB V1 V9 = true := by rfl
private theorem c110 : compatibleB V1 V10 = true := by rfl
private theorem c25 : compatibleB V2 V5 = true := by rfl
private theorem c26 : compatibleB V2 V6 = true := by rfl
private theorem c27 : compatibleB V2 V7 = true := by rfl
private theorem c28 : compatibleB V2 V8 = true := by rfl
private theorem c29 : compatibleB V2 V9 = true := by rfl
private theorem c210 : compatibleB V2 V10 = true := by rfl
private theorem c35 : compatibleB V3 V5 = true := by rfl
private theorem c36 : compatibleB V3 V6 = true := by rfl
private theorem c37 : compatibleB V3 V7 = true := by rfl
private theorem c38 : compatibleB V3 V8 = true := by rfl
private theorem c39 : compatibleB V3 V9 = true := by rfl
private theorem c310 : compatibleB V3 V10 = true := by rfl
private theorem c46 : compatibleB V4 V6 = true := by rfl
private theorem c47 : compatibleB V4 V7 = true := by rfl
private theorem c48 : compatibleB V4 V8 = true := by rfl
private theorem c49 : compatibleB V4 V9 = true := by rfl
private theorem c410 : compatibleB V4 V10 = true := by rfl
private theorem c411 : compatibleB V4 V11 = true := by rfl
private theorem c57 : compatibleB V5 V7 = true := by rfl
private theorem c58 : compatibleB V5 V8 = true := by rfl
private theorem c59 : compatibleB V5 V9 = true := by rfl
private theorem c510 : compatibleB V5 V10 = true := by rfl
private theorem c511 : compatibleB V5 V11 = true := by rfl
private theorem c68 : compatibleB V6 V8 = true := by rfl
private theorem c69 : compatibleB V6 V9 = true := by rfl
private theorem c610 : compatibleB V6 V10 = true := by rfl
private theorem c611 : compatibleB V6 V11 = true := by rfl
private theorem c79 : compatibleB V7 V9 = true := by rfl
private theorem c710 : compatibleB V7 V10 = true := by rfl
private theorem c711 : compatibleB V7 V11 = true := by rfl
private theorem c810 : compatibleB V8 V10 = true := by rfl
private theorem c811 : compatibleB V8 V11 = true := by rfl
private theorem c911 : compatibleB V9 V11 = true := by rfl

set_option maxRecDepth 1000000 in
/-- Every proper off-path subset gives two compatible target layers and hence
an exact singleton payment. -/
theorem adaptiveCarrierCode_weight_eqv_source
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 x10 x11 = false)
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
        (adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11) ≈
      occurrencePairWeight w qAll markV0 badV3 G label
        (adaptivePair x4 x5 x6 x7 x8 x9 x10 x11) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 G label
      (adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11) =
        carrierXiCodeWeight w qAll markV0 badV3 G label
          (eraseOccCarrierXiCode G
            (adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11)) from rfl]
  rw [adaptiveCarrierCode_erasure]
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 G label
      (adaptivePair x4 x5 x6 x7 x8 x9 x10 x11)
      (adaptivePair_mem x4 x5 x6 x7 x8 x9 x10 x11)]
  rw [adaptive_left, adaptive_right]
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;>
    simp [fullPattern, prefix4, prefix5, prefix6, prefix7, prefix8,
      prefix9, prefix10] at hpartial <;>
    simp [adaptiveErasedChain, adaptiveTerminalList, adaptiveExternalList,
      t4, t5, t6, t7, t8,
      t9, t10, t11, fullPattern, prefix4, prefix5, prefix6, prefix7,
      prefix8, prefix9, prefix10, sourceLeftList, sourceRightList,
      carrierXiCodeWeight, carrierCodeWeight, qAll, mark_start,
      chainCodeWeight, c01, c12, c23, Bool.not_false, bad_finish,
      admissibleFamilyWeight, familyCompatibleB_cons,
      familyCompatibleB_nil, List.all_cons, List.all_nil,
      c05, c06, c07, c08, c09, c010,
      c15, c16, c17, c18, c19, c110,
      c25, c26, c27, c28, c29, c210,
      c35, c36, c37, c38, c39, c310,
      c46, c47, c48, c49, c410, c411,
      c57, c58, c59, c510, c511,
      c68, c69, c610, c611, c79, c710, c711,
      c810, c811, c911,
      familyActivity_cons, familyActivity_nil] <;>
    ring_qeqv

def adaptivePaidBlock
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 x10 x11 = false) :
    PaidResidualBlock qAll markV0 badV3 G
      (adaptiveEntry x4 x5 x6 x7 x8 x9 x10 x11) where
  block := [adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11]
  block_nodup := List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact adaptiveCarrierCode_mem x4 x5 x6 x7 x8 x9 x10 x11
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (adaptiveCarrierCode_weight_eqv_source
        x4 x5 x6 x7 x8 x9 x10 x11 hpartial w label)

def sourceTag10
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  other.1.2.at 10

def decodedAdaptive
    (other : ExceptionalSourceEntry G qAll markV0 badV3) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  adaptiveEntry (sourceTag4 other) (sourceTag5 other) (sourceTag6 other)
    (sourceTag7 other) (sourceTag8 other) (sourceTag9 other)
    (sourceTag10 other) (sourceTag11 other)

def adaptivePartialChartTest
    (other : ExceptionalSourceEntry G qAll markV0 badV3) : Bool :=
  decide (other = decodedAdaptive other) &&
    !(fullPattern (sourceTag4 other) (sourceTag5 other) (sourceTag6 other)
      (sourceTag7 other) (sourceTag8 other) (sourceTag9 other)
      (sourceTag10 other) (sourceTag11 other))

set_option maxRecDepth 1000000 in
theorem adaptivePartialChartTest_accepts
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 x10 x11 = false) :
    adaptivePartialChartTest
      (adaptiveEntry x4 x5 x6 x7 x8 x9 x10 x11) = true := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;>
    simp [fullPattern, prefix4, prefix5, prefix6, prefix7, prefix8,
      prefix9, prefix10] at hpartial <;> rfl

private def transportPaidResidualBlock
    {a b : ExceptionalSourceEntry G qAll markV0 badV3} (h : a = b)
    (block : PaidResidualBlock qAll markV0 badV3 G b) :
    PaidResidualBlock qAll markV0 badV3 G a := by
  cases h
  exact block

private theorem transportPaidResidualBlock_block
    {a b : ExceptionalSourceEntry G qAll markV0 badV3} (h : a = b)
    (block : PaidResidualBlock qAll markV0 badV3 G b) :
    (transportPaidResidualBlock h block).block = block.block := by
  cases h
  rfl

private theorem partialSelected_eq_decoded
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      adaptivePartialChartTest other = true }) :
    selected.1 = decodedAdaptive selected.1 := by
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp selected.2).1

private theorem partialSelected_not_full
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      adaptivePartialChartTest other = true }) :
    fullPattern (sourceTag4 selected.1) (sourceTag5 selected.1)
      (sourceTag6 selected.1) (sourceTag7 selected.1)
      (sourceTag8 selected.1) (sourceTag9 selected.1)
      (sourceTag10 selected.1) (sourceTag11 selected.1) = false := by
  have hn := ((Bool.and_eq_true _ _).mp selected.2).2
  cases h : fullPattern (sourceTag4 selected.1) (sourceTag5 selected.1)
      (sourceTag6 selected.1) (sourceTag7 selected.1)
      (sourceTag8 selected.1) (sourceTag9 selected.1)
      (sourceTag10 selected.1) (sourceTag11 selected.1)
  · rfl
  · simp [h] at hn

def adaptivePartialChartCert
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      adaptivePartialChartTest other = true }) :
    PaidResidualBlock qAll markV0 badV3 G selected.1 :=
  transportPaidResidualBlock (partialSelected_eq_decoded selected)
    (adaptivePaidBlock (sourceTag4 selected.1) (sourceTag5 selected.1)
      (sourceTag6 selected.1) (sourceTag7 selected.1)
      (sourceTag8 selected.1) (sourceTag9 selected.1)
      (sourceTag10 selected.1) (sourceTag11 selected.1)
      (partialSelected_not_full selected))

theorem adaptivePartialChartCert_block
    (selected : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      adaptivePartialChartTest other = true }) :
    (adaptivePartialChartCert selected).block =
      [adaptiveCarrierCode (sourceTag4 selected.1) (sourceTag5 selected.1)
        (sourceTag6 selected.1) (sourceTag7 selected.1)
        (sourceTag8 selected.1) (sourceTag9 selected.1)
        (sourceTag10 selected.1) (sourceTag11 selected.1)] := by
  simp [adaptivePartialChartCert, transportPaidResidualBlock_block]
  rfl

def recoveredBit (code : OccCarrierXiCodeAt G) (i : Nat) : Bool :=
  (terminalBitsOf code.carrier.chain).at i || code.external.at i

def adaptivePartialOwner (code : OccCarrierXiCodeAt G) :
    ExceptionalSourceEntry G qAll markV0 badV3 :=
  adaptiveEntry (recoveredBit code 4) (recoveredBit code 5)
    (recoveredBit code 6) (recoveredBit code 7) (recoveredBit code 8)
    (recoveredBit code 9) (recoveredBit code 10) (recoveredBit code 11)

set_option maxRecDepth 1000000 in
theorem adaptivePartialOwner_carrier
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool) :
    adaptivePartialOwner
        (adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11) =
      adaptiveEntry x4 x5 x6 x7 x8 x9 x10 x11 := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;> rfl

def adaptivePartialOwnedFamily :
    OwnedPaidResidualFamily qAll markV0 badV3 G where
  test := adaptivePartialChartTest
  cert := adaptivePartialChartCert
  owner := adaptivePartialOwner
  block_owner := by
    intro selected code hcode
    have hc : code = adaptiveCarrierCode
        (sourceTag4 selected.1) (sourceTag5 selected.1)
        (sourceTag6 selected.1) (sourceTag7 selected.1)
        (sourceTag8 selected.1) (sourceTag9 selected.1)
        (sourceTag10 selected.1) (sourceTag11 selected.1) := by
      change code ∈ (adaptivePartialChartCert selected).block at hcode
      rw [adaptivePartialChartCert_block] at hcode
      simpa using hcode
    rw [hc, adaptivePartialOwner_carrier]
    exact (partialSelected_eq_decoded selected).symm

theorem adaptivePartialOwnedFamily_accepts
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 x10 x11 = false) :
    adaptivePartialOwnedFamily.test
      (adaptiveEntry x4 x5 x6 x7 x8 x9 x10 x11) = true :=
  adaptivePartialChartTest_accepts x4 x5 x6 x7 x8 x9 x10 x11 hpartial

set_option maxRecDepth 1000000 in
/-- The predecessor chart rejects every `V10=true` source.  Exactly one of
these 128 sources is full/canonical; the other 127 are the new adaptive
region. -/
theorem outward8Chart_rejects_v10
    (x4 x5 x6 x7 x8 x9 x11 : Bool) :
    outward8ChartTest
      (adaptiveEntry x4 x5 x6 x7 x8 x9 true x11) = false := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x11 <;> decide

set_option maxRecDepth 1000000 in
theorem adaptiveCarrierCode_not_mem_canonical
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 x10 x11 = false) :
    adaptiveCarrierCode x4 x5 x6 x7 x8 x9 x10 x11 ∉
      canonicalRepairBlock := by
  cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;>
    cases x8 <;> cases x9 <;> cases x10 <;> cases x11 <;>
    simp [fullPattern, prefix4, prefix5, prefix6, prefix7, prefix8,
      prefix9, prefix10] at hpartial <;> decide

private theorem partial_blocks_disjoint_canonical
    (old : { other : ExceptionalSourceEntry G qAll markV0 badV3 //
      adaptivePartialOwnedFamily.test other = true })
    (code : OccCarrierXiCodeAt G)
    (hcode : code ∈ (adaptivePartialOwnedFamily.cert old).block) :
    code ∉ c12PaidResidualBlock.block := by
  have hc : code = adaptiveCarrierCode
      (sourceTag4 old.1) (sourceTag5 old.1) (sourceTag6 old.1)
      (sourceTag7 old.1) (sourceTag8 old.1) (sourceTag9 old.1)
      (sourceTag10 old.1) (sourceTag11 old.1) := by
    change code ∈ (adaptivePartialChartCert old).block at hcode
    rw [adaptivePartialChartCert_block] at hcode
    simpa using hcode
  subst code
  exact adaptiveCarrierCode_not_mem_canonical _ _ _ _ _ _ _ _
    (partialSelected_not_full old)

/-- Complete ownership for all 256 alternating C12 source patterns: 255
adaptive singleton blocks and the native nine-code block at the full cycle. -/
def adaptiveCompleteOwnedFamily :
    OwnedPaidResidualFamily qAll markV0 badV3 G :=
  extendOwnedFamily adaptivePartialOwnedFamily entry c12PaidResidualBlock
    partial_blocks_disjoint_canonical

theorem adaptiveComplete_accepts_canonical :
    adaptiveCompleteOwnedFamily.test entry = true :=
  extendOwnedFamily_accepts_fresh adaptivePartialOwnedFamily entry
    c12PaidResidualBlock partial_blocks_disjoint_canonical

theorem adaptiveComplete_accepts_partial
    (x4 x5 x6 x7 x8 x9 x10 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 x10 x11 = false) :
    adaptiveCompleteOwnedFamily.test
      (adaptiveEntry x4 x5 x6 x7 x8 x9 x10 x11) = true := by
  apply extendOwnedFamily_preserves_old adaptivePartialOwnedFamily entry
    c12PaidResidualBlock partial_blocks_disjoint_canonical
  exact adaptivePartialOwnedFamily_accepts
    x4 x5 x6 x7 x8 x9 x10 x11 hpartial

/-- Every one of the 127 non-full sources rejected above is accepted by the
complete adaptive owner. -/
theorem adaptiveComplete_accepts_missing_v10
    (x4 x5 x6 x7 x8 x9 x11 : Bool)
    (hpartial : fullPattern x4 x5 x6 x7 x8 x9 true x11 = false) :
    adaptiveCompleteOwnedFamily.test
      (adaptiveEntry x4 x5 x6 x7 x8 x9 true x11) = true :=
  adaptiveComplete_accepts_partial x4 x5 x6 x7 x8 x9 true x11 hpartial

def adaptiveCompleteGlobalFamily :
    GlobalPaidResidualFamily qAll markV0 badV3 G :=
  adaptiveCompleteOwnedFamily.toGlobal

def adaptiveCompleteAllocator : MixedRepairAllocator G qAll markV0 badV3 :=
  adaptiveCompleteOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptivePair_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptiveCarrierCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptivePaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptivePartialOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptiveCarrierCode_not_mem_canonical
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptiveCompleteOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptiveComplete_accepts_partial
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.outward8Chart_rejects_v10
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmC12AdaptivePartialCycleOwned.adaptiveComplete_accepts_missing_v10
