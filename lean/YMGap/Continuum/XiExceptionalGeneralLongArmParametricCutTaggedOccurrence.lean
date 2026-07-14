/-
# Actual occurrence-code realization of the parametric cut tag

The abstract cut-tagged carrier already proves reconstruction, ownership,
and exact rational payment.  This file realizes its two masks as an actual
`OccCarrierXiCodeAt Gamma`: the first missing position is the carrier start,
the terminal mask is the terminal chain word, and the external mask is the
external word.  Membership in the enumerated target space is proved for
every finite path length.

The final normalization structures isolate only the geometry-dependent
factorizations.  From those exact equalities they construct a genuine
`PaidResidualBlock`, and from a deterministic decoder they construct an
`OwnedPaidResidualFamily` and hence a globally disjoint allocator.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier
import YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator

namespace YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
open YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
open YMGap.Continuum.XiExceptionalGeneralLongArmGlobalAllocator
open YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedCarrier

local infix:50 " ≈ " => Q'.eqv

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Actual target occurrence code -/

def listBits : (bits : List Bool) → OBits bits.length
  | [] => .nil
  | b :: bs => .cons b (listBits bs)

def vectorList : {n : Nat} → OBits n → List Bool
  | 0, .nil => []
  | _ + 1, .cons b bs => b :: vectorList bs

theorem vectorList_listBits : ∀ bits : List Bool,
    vectorList (listBits bits) = bits
  | [] => rfl
  | b :: bs => by
      change b :: vectorList (listBits bs) = b :: bs
      rw [vectorList_listBits]

theorem vectorList_cast_listBits {bits : List Bool} {n : Nat}
    (h : bits.length = n) :
    vectorList (castBitVec h (listBits bits)) = bits := by
  cases h
  exact vectorList_listBits bits

def cutTerminalBits (Gamma : List (Polymer L)) (p : CutPattern)
    (hlen : p.pathLength = Gamma.length) : OBits Gamma.length :=
  castBitVec (p.terminalMask_length.trans hlen) (listBits p.terminalMask)

def cutExternalBits (Gamma : List (Polymer L)) (p : CutPattern)
    (hlen : p.pathLength = Gamma.length) : OBits Gamma.length :=
  castBitVec (p.externalMask_length.trans hlen) (listBits p.externalMask)

/-- The cut is present twice in the raw target data: as the carrier start and
as the first missing position reconstructed from the two masks. -/
def cutOccurrenceCode (Gamma : List (Polymer L)) (p : CutPattern)
    (hlen : p.pathLength = Gamma.length) : OccCarrierXiCodeAt Gamma where
  carrier :=
    { start := p.cut
      chain := chainFromIndices (cutTerminalBits Gamma p hlen) [] }
  external := cutExternalBits Gamma p hlen

omit [DecidableEq L.Plaquette] in
theorem cutOccurrenceCode_mem (Gamma : List (Polymer L)) (p : CutPattern)
    (hlen : p.pathLength = Gamma.length) :
    cutOccurrenceCode Gamma p hlen ∈ occurrenceCarrierXiCodes Gamma := by
  unfold cutOccurrenceCode occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨cutExternalBits Gamma p hlen, bitVectors_complete _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨p.cut,
    chainFromIndices (cutTerminalBits Gamma p hlen) []⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨p.cut, occurrenceIndices_complete ?_, ?_⟩
  · rw [← hlen]
    exact p.cut_lt_pathLength
  apply List.mem_map.mpr
  refine ⟨chainFromIndices (cutTerminalBits Gamma p hlen) [], ?_, rfl⟩
  exact chainFromIndices_mem Gamma (cutTerminalBits Gamma p hlen)
    [] Gamma.length (Nat.zero_le _) (fun _ h => False.elim (by cases h))

omit [DecidableEq L.Plaquette] in
/-- The actual occurrence code retains the complete abstract cut-tag. -/
theorem cutOccurrenceCode_injective
    (Gamma : List (Polymer L)) {p q : CutPattern}
    (hp : p.pathLength = Gamma.length)
    (hq : q.pathLength = Gamma.length)
    (hcode : cutOccurrenceCode Gamma p hp =
      cutOccurrenceCode Gamma q hq) : p = q := by
  have hcut : p.cut = q.cut := congrArg
    (fun code : OccCarrierXiCodeAt Gamma => code.carrier.start) hcode
  have hchain := congrArg
    (fun code : OccCarrierXiCodeAt Gamma => code.carrier.chain) hcode
  change chainFromIndices (cutTerminalBits Gamma p hp) [] =
    chainFromIndices (cutTerminalBits Gamma q hq) [] at hchain
  have hterminalBits : cutTerminalBits Gamma p hp =
      cutTerminalBits Gamma q hq := by
    injection hchain
  have hterminal : p.terminalMask = q.terminalMask := by
    have h := congrArg vectorList hterminalBits
    unfold cutTerminalBits at h
    rw [vectorList_cast_listBits, vectorList_cast_listBits] at h
    exact h
  have hexternalBits := congrArg
    (fun code : OccCarrierXiCodeAt Gamma => code.external) hcode
  have hexternal : p.externalMask = q.externalMask := by
    have h := congrArg vectorList hexternalBits
    unfold cutOccurrenceCode cutExternalBits at h
    rw [vectorList_cast_listBits, vectorList_cast_listBits] at h
    exact h
  apply encodeCutPattern_injective
  unfold encodeCutPattern
  calc
    CutTaggedCarrier.mk p.cut p.terminalMask p.externalMask =
      CutTaggedCarrier.mk q.cut p.terminalMask p.externalMask := by rw [hcut]
    _ = CutTaggedCarrier.mk q.cut q.terminalMask p.externalMask := by
      rw [hterminal]
    _ = CutTaggedCarrier.mk q.cut q.terminalMask q.externalMask := by
      rw [hexternal]

/-! ## Exact geometry normalization and singleton payment -/

/-- The two non-formal inputs for a concrete geometry: its source activity
is the masked source product, and the actual occurrence-code weight is the
two-layer cut-tagged product. -/
structure CutOccurrenceWeightNormalization
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L))
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (p : CutPattern) (hlen : p.pathLength = Gamma.length) where
  activity : Q' → (L.Plaquette → Rep) → Nat → Q'
  source_eqv : ∀ w label,
    occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≈
      cutTaggedSourceWeight (activity w label) p
  carrier_eqv : ∀ w label,
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (cutOccurrenceCode Gamma p hlen) ≈
      cutTaggedCarrierWeight (activity w label) (encodeCutPattern p)

theorem cutOccurrenceCode_weight_eqv_source
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    {p : CutPattern} {hlen : p.pathLength = Gamma.length}
    (norm : CutOccurrenceWeightNormalization qP b1 b2 Gamma entry p hlen)
    (w : Q') (label : L.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (cutOccurrenceCode Gamma p hlen) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  exact Q'.eqv_trans _ _ _ (norm.carrier_eqv w label)
    (Q'.eqv_trans _ _ _
      (cutTaggedCarrierWeight_eqv_source (norm.activity w label) p)
      (Q'.eqv_symm (norm.source_eqv w label)))

def cutOccurrencePaidBlock
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    {p : CutPattern} {hlen : p.pathLength = Gamma.length}
    (norm : CutOccurrenceWeightNormalization qP b1 b2 Gamma entry p hlen) :
    PaidResidualBlock qP b1 b2 Gamma entry where
  block := [cutOccurrenceCode Gamma p hlen]
  block_nodup := List.nodup_cons.mpr
    ⟨List.not_mem_nil, List.nodup_nil⟩
  block_mem := by
    intro code hcode
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    subst code
    exact cutOccurrenceCode_mem Gamma p hlen
  source_le := by
    intro w _hw label
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv
      (cutOccurrenceCode_weight_eqv_source norm w label)

/-! ## Source-owned charts and global disjointness -/

/-- A chart-wide exact realization.  The algebraic and target-enumeration
parts are already fixed above.  Concrete long-arm geometry supplies the
selected source's cut pattern, the two weight factorizations, and a decoder
which reads that source back from the actual occurrence code. -/
structure CutOccurrenceOwnedNormalization
    (qP b1 b2 : Polymer L → Bool) (Gamma : List (Polymer L)) where
  test : ExceptionalSourceEntry Gamma qP b1 b2 → Bool
  pattern : (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      test entry = true }) → CutPattern
  pattern_length : ∀ selected, (pattern selected).pathLength = Gamma.length
  activity : (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      test entry = true }) → Q' → (L.Plaquette → Rep) → Nat → Q'
  source_eqv : ∀ selected w label,
    occurrencePairWeight w qP b1 b2 Gamma label selected.1.1 ≈
      cutTaggedSourceWeight (activity selected w label) (pattern selected)
  carrier_eqv : ∀ selected w label,
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (cutOccurrenceCode Gamma (pattern selected)
          (pattern_length selected)) ≈
      cutTaggedCarrierWeight (activity selected w label)
        (encodeCutPattern (pattern selected))
  owner : OccCarrierXiCodeAt Gamma →
    ExceptionalSourceEntry Gamma qP b1 b2
  owner_code : ∀ selected,
    owner (cutOccurrenceCode Gamma (pattern selected)
      (pattern_length selected)) = selected.1

def CutOccurrenceOwnedNormalization.entryNormalization
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (norm : CutOccurrenceOwnedNormalization qP b1 b2 Gamma)
    (selected : { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      norm.test entry = true }) :
    CutOccurrenceWeightNormalization qP b1 b2 Gamma selected.1
      (norm.pattern selected) (norm.pattern_length selected) where
  activity := norm.activity selected
  source_eqv := norm.source_eqv selected
  carrier_eqv := norm.carrier_eqv selected

/-- Exact cut-tagged normalizations therefore instantiate the existing
source-owned global allocator interface without any finite enumeration. -/
def CutOccurrenceOwnedNormalization.toOwnedPaidResidualFamily
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (norm : CutOccurrenceOwnedNormalization qP b1 b2 Gamma) :
    OwnedPaidResidualFamily qP b1 b2 Gamma where
  test := norm.test
  cert := fun selected =>
    cutOccurrencePaidBlock (norm.entryNormalization selected)
  owner := norm.owner
  block_owner := by
    intro selected code hcode
    change code ∈
      (cutOccurrencePaidBlock
        (norm.entryNormalization selected)).block at hcode
    simp only [cutOccurrencePaidBlock, List.mem_cons,
      List.not_mem_nil, or_false] at hcode
    subst code
    exact norm.owner_code selected

def CutOccurrenceOwnedNormalization.globalFamily
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (norm : CutOccurrenceOwnedNormalization qP b1 b2 Gamma) :
    GlobalPaidResidualFamily qP b1 b2 Gamma :=
  norm.toOwnedPaidResidualFamily.toGlobal

def CutOccurrenceOwnedNormalization.allocator
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (norm : CutOccurrenceOwnedNormalization qP b1 b2 Gamma) :
    MixedRepairAllocator Gamma qP b1 b2 :=
  norm.toOwnedPaidResidualFamily.allocator

end YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence

#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.cutOccurrenceCode_mem
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.cutOccurrenceCode_injective
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.cutOccurrenceCode_weight_eqv_source
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.cutOccurrencePaidBlock
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.CutOccurrenceOwnedNormalization.toOwnedPaidResidualFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.CutOccurrenceOwnedNormalization.globalFamily
#print axioms YMGap.Continuum.XiExceptionalGeneralLongArmParametricCutTaggedOccurrence.CutOccurrenceOwnedNormalization.allocator
