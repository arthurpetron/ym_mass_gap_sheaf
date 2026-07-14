/-
# Parametric non-full coverage plus the canonical full payer

This file closes the source-allocation bookkeeping for an arbitrary finite
long-arm chart.  A chart encodes full source-union masks as exceptional
entries and decodes them back.  Every non-full mask is sent constructively to
its first-cut singleton occurrence code.  The unique full mask is sent to the
canonical uniform short/long multi-code payer.

The two target branches are disjoint for a structural reason: cut codes have
a zero-step terminal chain, while every code in the canonical repair family
has a nonempty step chain.  No fixed-length enumeration is used.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence
import YMGap.Continuum.XiExceptionalOwnedFamilyExtension

namespace YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalOwnedFamilyExtension
open YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier
open YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Total first-cut decoding -/

def decodedCut (bits : List Bool) : CutPattern :=
  match firstCut bits with
  | some p => p
  | none => ⟨0, []⟩

theorem decodedCut_sourceBits {bits : List Bool}
    (hnfull : bits ≠ List.replicate bits.length true) :
    (decodedCut bits).sourceBits = bits := by
  cases hcut : firstCut bits with
  | none => exact False.elim (hnfull (firstCut_none_all_true hcut))
  | some p =>
      unfold decodedCut
      rw [hcut]
      exact firstCut_some_reconstruct hcut

theorem decodedCut_injective_on_nonfull {a b : List Bool}
    (ha : a ≠ List.replicate a.length true)
    (hb : b ≠ List.replicate b.length true)
    (hcut : decodedCut a = decodedCut b) : a = b := by
  rw [← decodedCut_sourceBits ha, ← decodedCut_sourceBits hb, hcut]

/-! ## Recovering the source union from an actual cut code -/

def terminalVectorOf {n : Nat} : OccChainCode n → OBits n
  | .terminal bits => bits
  | .step _ rest => terminalVectorOf rest

def recoveredSourceBits {Gamma : List (Polymer L)}
    (code : OccCarrierXiCodeAt Gamma) : List Bool :=
  mergeMasks (vectorList (terminalVectorOf code.carrier.chain))
    (vectorList code.external)

omit [DecidableEq L.Plaquette] in
theorem recoveredSourceBits_cutOccurrenceCode
    (Gamma : List (Polymer L)) (p : CutPattern)
    (hlen : p.pathLength = Gamma.length) :
    recoveredSourceBits (cutOccurrenceCode Gamma p hlen) = p.sourceBits := by
  change mergeMasks (vectorList (cutTerminalBits Gamma p hlen))
    (vectorList (cutExternalBits Gamma p hlen)) = p.sourceBits
  unfold cutTerminalBits cutExternalBits
  rw [vectorList_cast_listBits, vectorList_cast_listBits]
  exact p.masks_reconstruct

/-! ## A reversible source chart -/

structure PathSourceChart
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L)) where
  encode : List Bool → ExceptionalSourceEntry Gamma qP b1 b2
  decode : ExceptionalSourceEntry Gamma qP b1 b2 → List Bool
  decode_length : ∀ entry, (decode entry).length = Gamma.length
  decode_encode : ∀ bits, bits.length = Gamma.length →
    decode (encode bits) = bits

def fullSourceBits (Gamma : List (Polymer L)) : List Bool :=
  List.replicate Gamma.length true

def PathSourceChart.partialTest
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (chart : PathSourceChart qP b1 b2 Gamma)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  decide (entry = chart.encode (chart.decode entry)) &&
    !(decide (chart.decode entry = fullSourceBits Gamma))

theorem PathSourceChart.partialTest_accepts
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (chart : PathSourceChart qP b1 b2 Gamma)
    (bits : List Bool) (hlen : bits.length = Gamma.length)
    (hnfull : bits ≠ fullSourceBits Gamma) :
    chart.partialTest (chart.encode bits) = true := by
  unfold PathSourceChart.partialTest
  rw [chart.decode_encode bits hlen]
  simp [hnfull]

private theorem selected_eq_encode_decode
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (chart : PathSourceChart qP b1 b2 Gamma)
    (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      chart.partialTest entry = true }) :
    selected.1 = chart.encode (chart.decode selected.1) := by
  have h := (Bool.and_eq_true _ _).mp selected.2
  exact of_decide_eq_true h.1

private theorem selected_decode_nonfull
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (chart : PathSourceChart qP b1 b2 Gamma)
    (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      chart.partialTest entry = true }) :
    chart.decode selected.1 ≠ fullSourceBits Gamma := by
  have h := (Bool.and_eq_true _ _).mp selected.2
  intro heq
  unfold PathSourceChart.partialTest at selected
  simp [heq] at h

private theorem selected_pattern_length
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (chart : PathSourceChart qP b1 b2 Gamma)
    (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      chart.partialTest entry = true }) :
    (decodedCut (chart.decode selected.1)).pathLength = Gamma.length := by
  have hn : chart.decode selected.1 ≠
      List.replicate (chart.decode selected.1).length true := by
    rw [chart.decode_length]
    exact selected_decode_nonfull chart selected
  rw [← CutPattern.sourceBits_length, decodedCut_sourceBits hn,
    chart.decode_length]

/-! ## The non-full owned family -/

/-- The remaining geometry input for every selected non-full source is the
exact source/target weight normalization. -/
structure PartialCutWeightGeometry
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (chart : PathSourceChart qP b1 b2 Gamma) where
  normalization : ∀ selected : {
      entry : ExceptionalSourceEntry Gamma qP b1 b2 //
        chart.partialTest entry = true },
    CutOccurrenceWeightNormalization qP b1 b2 Gamma selected.1
      (decodedCut (chart.decode selected.1))
      (selected_pattern_length chart selected)

def PartialCutWeightGeometry.ownedNormalization
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {chart : PathSourceChart qP b1 b2 Gamma}
    (geom : PartialCutWeightGeometry chart) :
    CutOccurrenceOwnedNormalization qP b1 b2 Gamma where
  test := chart.partialTest
  pattern := fun selected => decodedCut (chart.decode selected.1)
  pattern_length := selected_pattern_length chart
  activity := fun selected => (geom.normalization selected).activity
  source_eqv := fun selected => (geom.normalization selected).source_eqv
  carrier_eqv := fun selected => (geom.normalization selected).carrier_eqv
  owner := fun code => chart.encode (recoveredSourceBits code)
  owner_code := by
    intro selected
    have hn : chart.decode selected.1 ≠
        List.replicate (chart.decode selected.1).length true := by
      rw [chart.decode_length]
      exact selected_decode_nonfull chart selected
    rw [recoveredSourceBits_cutOccurrenceCode,
      decodedCut_sourceBits hn]
    exact (selected_eq_encode_decode chart selected).symm

def PartialCutWeightGeometry.ownedFamily
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {chart : PathSourceChart qP b1 b2 Gamma}
    (geom : PartialCutWeightGeometry chart) :
    OwnedPaidResidualFamily qP b1 b2 Gamma :=
  geom.ownedNormalization.toOwnedPaidResidualFamily

theorem PartialCutWeightGeometry.accepts_nonfull
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {chart : PathSourceChart qP b1 b2 Gamma}
    (geom : PartialCutWeightGeometry chart)
    (bits : List Bool) (hlen : bits.length = Gamma.length)
    (hnfull : bits ≠ fullSourceBits Gamma) :
    geom.ownedFamily.test (chart.encode bits) = true :=
  chart.partialTest_accepts bits hlen hnfull

/-! ## Structural separation from the canonical multi-code block -/

omit [DecidableEq L.Plaquette] in
theorem cutOccurrenceCode_not_mem_repairCarrierFamily
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (p : CutPattern) (hlen : p.pathLength = Gamma.length) :
    cutOccurrenceCode Gamma p hlen ∉
      repairCarrierFamily Gamma k hGamma := by
  intro hmem
  rcases List.mem_cons.mp hmem with hshort | hlong
  · have hchain := congrArg
      (fun code : OccCarrierXiCodeAt Gamma => code.carrier.chain) hshort
    unfold cutOccurrenceCode shortCarrierCode at hchain
    cases hchain
  · simp only [longCarrierFamily, sideCarrierCodes, List.mem_append,
      List.mem_map] at hlong
    rcases hlong with ⟨i, hi, hcode⟩ | ⟨i, hi, hcode⟩
    · have hchain := congrArg
        (fun code : OccCarrierXiCodeAt Gamma => code.carrier.chain) hcode
      unfold cutOccurrenceCode longCarrierCode at hchain
      cases htail : inflatedTail k .even i with
      | nil =>
          have hlenTail := inflatedTail_length .even
            (occurrenceIndices_bound hi)
          rw [htail] at hlenTail
          simp only [List.length_nil] at hlenTail
          unfold ambientCount longCount at hlenTail
          omega
      | cons _ _ => rw [htail] at hchain; cases hchain
    · have hchain := congrArg
        (fun code : OccCarrierXiCodeAt Gamma => code.carrier.chain) hcode
      unfold cutOccurrenceCode longCarrierCode at hchain
      cases htail : inflatedTail k .odd i with
      | nil =>
          have hlenTail := inflatedTail_length .odd
            (occurrenceIndices_bound hi)
          rw [htail] at hlenTail
          simp only [List.length_nil] at hlenTail
          unfold ambientCount longCount at hlenTail
          omega
      | cons _ _ => rw [htail] at hchain; cases hchain

/-! ## Complete non-full/full allocation -/

structure CompleteCutCoverage
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L))
    (k : Nat) (hGamma : Gamma.length = ambientCount k) where
  chart : PathSourceChart qP b1 b2 Gamma
  partialGeometry : PartialCutWeightGeometry chart
  fullNormalization : UniformLongArmNormalization qP b1 b2 Gamma k hGamma
    (chart.encode (fullSourceBits Gamma))

def CompleteCutCoverage.fullEntry
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma) :
    ExceptionalSourceEntry Gamma qP b1 b2 :=
  coverage.chart.encode (fullSourceBits Gamma)

def CompleteCutCoverage.fullPaidBlock
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma) :
    PaidResidualBlock qP b1 b2 Gamma coverage.fullEntry :=
  uniformPaidResidualBlock coverage.fullNormalization

private theorem partial_blocks_disjoint_full
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma)
    (old : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      coverage.partialGeometry.ownedFamily.test entry = true })
    (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈
      (coverage.partialGeometry.ownedFamily.cert old).block) :
    code ∉ coverage.fullPaidBlock.block := by
  change code ∈
    (cutOccurrencePaidBlock
      (coverage.partialGeometry.normalization old)).block at hcode
  simp only [cutOccurrencePaidBlock, List.mem_cons,
    List.not_mem_nil, or_false] at hcode
  subst code
  change cutOccurrenceCode Gamma
      (decodedCut (coverage.chart.decode old.1))
      (selected_pattern_length coverage.chart old) ∉
    repairCarrierFamily Gamma k hGamma
  exact cutOccurrenceCode_not_mem_repairCarrierFamily Gamma k hGamma _ _

def CompleteCutCoverage.completeOwnedFamily
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma) :
    OwnedPaidResidualFamily qP b1 b2 Gamma :=
  extendOwnedFamily coverage.partialGeometry.ownedFamily coverage.fullEntry
    coverage.fullPaidBlock (partial_blocks_disjoint_full coverage)

theorem CompleteCutCoverage.accepts_nonfull
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma)
    (bits : List Bool) (hlen : bits.length = Gamma.length)
    (hnfull : bits ≠ fullSourceBits Gamma) :
    coverage.completeOwnedFamily.test (coverage.chart.encode bits) = true := by
  apply extendOwnedFamily_preserves_old
  exact coverage.partialGeometry.accepts_nonfull bits hlen hnfull

theorem CompleteCutCoverage.accepts_full
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma) :
    coverage.completeOwnedFamily.test coverage.fullEntry = true :=
  extendOwnedFamily_accepts_fresh coverage.partialGeometry.ownedFamily
    coverage.fullEntry coverage.fullPaidBlock
      (partial_blocks_disjoint_full coverage)

def CompleteCutCoverage.globalFamily
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma) :
    GlobalPaidResidualFamily qP b1 b2 Gamma :=
  coverage.completeOwnedFamily.toGlobal

def CompleteCutCoverage.allocator
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {k : Nat} {hGamma : Gamma.length = ambientCount k}
    (coverage : CompleteCutCoverage qP b1 b2 Gamma k hGamma) :
    MixedRepairAllocator Gamma qP b1 b2 :=
  coverage.completeOwnedFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.decodedCut_sourceBits
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.recoveredSourceBits_cutOccurrenceCode
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.PathSourceChart.partialTest_accepts
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.PartialCutWeightGeometry.ownedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.cutOccurrenceCode_not_mem_repairCarrierFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.CompleteCutCoverage.completeOwnedFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.CompleteCutCoverage.accepts_nonfull
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.CompleteCutCoverage.accepts_full
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCoverage.CompleteCutCoverage.allocator
