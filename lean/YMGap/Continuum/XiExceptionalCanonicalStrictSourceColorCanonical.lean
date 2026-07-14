/-
# Canonical source coloring for strict canonical carriers

The source-color carrier retains the correct compatibility certificate, but
its Cartesian enumeration counts one payload once for every valid coloring.
Here each payload receives the first valid color pair in the fixed finite
`maskPairs` order.  A zero pair is used only as a total fallback.

Every genuine exceptional source has a valid switched-source coloring, so
the canonical search remains valid on every source image.  The resulting
finite enumeration contains exactly one code per root-attachment payload;
source membership, injectivity, and exact weight are preserved.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCarrier

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCanonical

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceBoundaryAll
open YMGap.Continuum.XiExceptionalCanonicalStrictAnalyticRootRestriction
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCarrier
open YMGap.Continuum.XiExceptionalTargetNodup

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Constructive first-valid search -/

def firstValidOr (p : alpha → Bool) (fallback : alpha) :
    List alpha → alpha
  | [] => fallback
  | x :: xs => if p x then x else firstValidOr p fallback xs

theorem firstValidOr_mem_or_fallback
    (p : alpha → Bool) (fallback : alpha) :
    ∀ xs : List alpha,
      firstValidOr p fallback xs ∈ xs ∨
        firstValidOr p fallback xs = fallback
  | [] => Or.inr rfl
  | x :: xs => by
      unfold firstValidOr
      cases hx : p x with
      | true => exact Or.inl List.mem_cons_self
      | false =>
          rcases firstValidOr_mem_or_fallback p fallback xs with hmem | heq
          · exact Or.inl (List.mem_cons_of_mem x hmem)
          · exact Or.inr heq

theorem firstValidOr_valid_of_exists
    (p : alpha → Bool) (fallback : alpha) :
    ∀ xs : List alpha,
      (∃ x, x ∈ xs ∧ p x = true) →
        p (firstValidOr p fallback xs) = true
  | [], hex => by
      obtain ⟨_, hmem, _⟩ := hex
      cases hmem
  | x :: xs, hex => by
      unfold firstValidOr
      cases hx : p x with
      | true => exact hx
      | false =>
          apply firstValidOr_valid_of_exists p fallback xs
          obtain ⟨y, hy, hpy⟩ := hex
          rcases List.mem_cons.mp hy with hyx | hytail
          · subst y
            rw [hx] at hpy
            cases hpy
          · exact ⟨y, hytail, hpy⟩

/-! ## One canonical color pair per payload -/

def zeroOccurrenceBits : (n : Nat) → OccBitVec n
  | 0 => .nil
  | n + 1 => .cons false (zeroOccurrenceBits n)

def zeroMaskPair (n : Nat) : MaskPair n :=
  (zeroOccurrenceBits n, zeroOccurrenceBits n)

def colorValidForCarrierB
    (Gamma : List (Polymer L))
    (carrier : RootAttachmentCarrierCode Gamma.length)
    (colors : MaskPair Gamma.length) : Bool :=
  sourceSideColorValidB Gamma ⟨carrier, colors⟩

def canonicalSourceColors
    (Gamma : List (Polymer L))
    (carrier : RootAttachmentCarrierCode Gamma.length) :
    MaskPair Gamma.length :=
  firstValidOr (colorValidForCarrierB Gamma carrier)
    (zeroMaskPair Gamma.length) (maskPairs Gamma.length)

theorem canonicalSourceColors_mem_maskPairs
    (Gamma : List (Polymer L))
    (carrier : RootAttachmentCarrierCode Gamma.length) :
    canonicalSourceColors Gamma carrier ∈ maskPairs Gamma.length := by
  unfold canonicalSourceColors
  rcases firstValidOr_mem_or_fallback
      (colorValidForCarrierB Gamma carrier)
      (zeroMaskPair Gamma.length) (maskPairs Gamma.length) with hmem | heq
  · exact hmem
  · rw [heq]
    exact maskPairs_complete _

theorem canonicalSourceColors_valid_of_exists
    (Gamma : List (Polymer L))
    (carrier : RootAttachmentCarrierCode Gamma.length)
    (hex : ∃ colors, colors ∈ maskPairs Gamma.length ∧
      sourceSideColorValidB Gamma ⟨carrier, colors⟩ = true) :
    sourceSideColorValidB Gamma
      ⟨carrier, canonicalSourceColors Gamma carrier⟩ = true := by
  exact firstValidOr_valid_of_exists
    (colorValidForCarrierB Gamma carrier)
    (zeroMaskPair Gamma.length) (maskPairs Gamma.length) hex

def canonicalSourceColorCode
    (Gamma : List (Polymer L))
    (carrier : RootAttachmentCarrierCode Gamma.length) :
    SourceColoredRootAttachmentCarrierCode Gamma.length :=
  ⟨carrier, canonicalSourceColors Gamma carrier⟩

theorem canonicalSourceColorCode_carrier
    (Gamma : List (Polymer L))
    (carrier : RootAttachmentCarrierCode Gamma.length) :
    (canonicalSourceColorCode Gamma carrier).carrier = carrier := rfl

theorem canonicalSourceColorCode_injective
    (Gamma : List (Polymer L))
    (carrier carrier' : RootAttachmentCarrierCode Gamma.length)
    (hcode : canonicalSourceColorCode Gamma carrier =
      canonicalSourceColorCode Gamma carrier') :
    carrier = carrier' :=
  congrArg SourceColoredRootAttachmentCarrierCode.carrier hcode

def canonicalSourceColorCarrierCodes
    (Gamma : List (Polymer L)) (fuel : Nat) :
    List (SourceColoredRootAttachmentCarrierCode Gamma.length) :=
  (rootAttachmentCarrierCodes Gamma.length fuel).map
    (canonicalSourceColorCode Gamma)

theorem canonicalSourceColorCarrierCodes_nodup
    (Gamma : List (Polymer L)) (fuel : Nat) :
    (canonicalSourceColorCarrierCodes Gamma fuel).Nodup := by
  unfold canonicalSourceColorCarrierCodes
  apply nodup_map_of_injOn
    (canonicalSourceColorCode Gamma)
    (rootAttachmentCarrierCodes Gamma.length fuel)
    (rootAttachmentCarrierCodes_nodup Gamma.length fuel)
  intro carrier _ carrier' _ hcode
  exact canonicalSourceColorCode_injective Gamma carrier carrier' hcode

theorem canonicalSourceColorCarrierCodes_payload_unique
    (Gamma : List (Polymer L)) (fuel : Nat)
    (code code' : SourceColoredRootAttachmentCarrierCode Gamma.length)
    (hcode : code ∈ canonicalSourceColorCarrierCodes Gamma fuel)
    (hcode' : code' ∈ canonicalSourceColorCarrierCodes Gamma fuel)
    (hcarrier : code.carrier = code'.carrier) :
    code = code' := by
  obtain ⟨carrier, _, rfl⟩ := List.mem_map.mp hcode
  obtain ⟨carrier', _, rfl⟩ := List.mem_map.mp hcode'
  have hcarrier' : carrier = carrier' := by
    simpa only [canonicalSourceColorCode_carrier] using hcarrier
  subst carrier'
  rfl

/-! ## Every genuine source survives canonical coloring -/

def entryCanonicalSourceColorCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    SourceColoredRootAttachmentCarrierCode Gamma.length :=
  canonicalSourceColorCode Gamma
    (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry)

theorem entryCanonicalSourceColors_valid
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    sourceSideColorValidB Gamma
      (entryCanonicalSourceColorCode Gamma qP b1 b2 entry) = true := by
  unfold entryCanonicalSourceColorCode canonicalSourceColorCode
  apply canonicalSourceColors_valid_of_exists
  refine ⟨switchedSourceColors Gamma b2 entry.1,
    maskPairs_complete _, ?_⟩
  exact entrySourceColoredRootAttachmentCarrierCode_valid
    Gamma qP b1 b2 entry

theorem entryCanonicalSourceColorCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    entryCanonicalSourceColorCode Gamma qP b1 b2 entry ∈
      canonicalSourceColorCarrierCodes Gamma Gamma.length := by
  unfold entryCanonicalSourceColorCode canonicalSourceColorCarrierCodes
  apply List.mem_map.mpr
  exact ⟨entryRootAttachmentCarrierCode Gamma qP b1 b2 entry,
    entryRootAttachmentCarrierCode_mem Gamma qP b1 b2 entry, rfl⟩

theorem entryCanonicalSourceColorCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : entryCanonicalSourceColorCode Gamma qP b1 b2 entry1 =
      entryCanonicalSourceColorCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have hcarrier := congrArg
    SourceColoredRootAttachmentCarrierCode.carrier hcode
  exact entryRootAttachmentCarrierCode_injective_all
    Gamma qP b1 b2 entry1 entry2 hcarrier

/-! ## Exact weight and the multiplicity-free finite majorant -/

def canonicalSourceColorCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) : Q' :=
  sourceColoredRootAttachmentCarrierCodeWeight
    w Gamma qP b1 b2 label code

def canonicalSourceColorCarrierMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum
    (canonicalSourceColorCarrierCodeWeight w Gamma qP b1 b2 label)
    (canonicalSourceColorCarrierCodes Gamma Gamma.length)

theorem canonicalSourceColorCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    (0 : Q') ≤ canonicalSourceColorCarrierCodeWeight
      w Gamma qP b1 b2 label code :=
  sourceColoredRootAttachmentCarrierCodeWeight_nonnegative
    hw Gamma qP b1 b2 label code

theorem entryCanonicalSourceColorCode_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    canonicalSourceColorCarrierCodeWeight
        w Gamma qP b1 b2 label
        (entryCanonicalSourceColorCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  unfold canonicalSourceColorCarrierCodeWeight
    sourceColoredRootAttachmentCarrierCodeWeight
  rw [entryCanonicalSourceColors_valid Gamma qP b1 b2 entry]
  simp only [if_true]
  unfold entryCanonicalSourceColorCode canonicalSourceColorCode
  dsimp only
  rw [entry_sourceRootStrictCarrierCodeWeight_eq
    w Gamma qP b1 b2 label entry]
  exact entryRootAttachmentCarrierCode_strict_weight_eqv_source
    w Gamma qP b1 b2 label entry

theorem fullExceptionalSource_sum_le_canonicalSourceColorCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight
          w qP b1 b2 Gamma label entry.1)
        (fullExceptionalSource Gamma qP b1 b2) ≤
      canonicalSourceColorCarrierMajorant
        w Gamma qP b1 b2 label := by
  unfold canonicalSourceColorCarrierMajorant
  apply qListSum_le_of_injective
    (fullExceptionalSource Gamma qP b1 b2)
    (canonicalSourceColorCarrierCodes Gamma Gamma.length)
    (fun entry => occurrencePairWeight
      w qP b1 b2 Gamma label entry.1)
    (canonicalSourceColorCarrierCodeWeight
      w Gamma qP b1 b2 label)
    (entryCanonicalSourceColorCode Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2)
  · intro entry _
    exact entryCanonicalSourceColorCode_mem Gamma qP b1 b2 entry
  · intro entry1 _ entry2 _ hcode
    exact entryCanonicalSourceColorCode_injective
      Gamma qP b1 b2 entry1 entry2 hcode
  · intro entry _
    exact Q'.ge_of_eqv
      (entryCanonicalSourceColorCode_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · intro code _
    exact canonicalSourceColorCarrierCodeWeight_nonnegative
      hw Gamma qP b1 b2 label code

/-! The canonical carrier is a genuine subenumeration of the prior colored
Cartesian carrier; no payload is replicated by the color search. -/

theorem canonicalSourceColorCode_mem_coloredEnumeration
    (Gamma : List (Polymer L)) (fuel : Nat)
    (carrier : RootAttachmentCarrierCode Gamma.length)
    (hcarrier : carrier ∈ rootAttachmentCarrierCodes
      Gamma.length fuel) :
    canonicalSourceColorCode Gamma carrier ∈
      sourceColoredRootAttachmentCarrierCodes Gamma.length fuel := by
  unfold canonicalSourceColorCode sourceColoredRootAttachmentCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨carrier, hcarrier, ?_⟩
  exact List.mem_map.mpr
    ⟨canonicalSourceColors Gamma carrier,
      canonicalSourceColors_mem_maskPairs Gamma carrier, rfl⟩

theorem canonicalSourceColorCarrierMajorant_le_coloredCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    canonicalSourceColorCarrierMajorant w Gamma qP b1 b2 label ≤
      qListSum
        (sourceColoredRootAttachmentCarrierCodeWeight
          w Gamma qP b1 b2 label)
        (sourceColoredRootAttachmentCarrierCodes
          Gamma.length Gamma.length) := by
  unfold canonicalSourceColorCarrierMajorant
    canonicalSourceColorCarrierCodeWeight
  apply qListSum_le_of_injective
    (canonicalSourceColorCarrierCodes Gamma Gamma.length)
    (sourceColoredRootAttachmentCarrierCodes
      Gamma.length Gamma.length)
    (sourceColoredRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label)
    (sourceColoredRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label)
    (fun code => code)
    (canonicalSourceColorCarrierCodes_nodup Gamma Gamma.length)
  · intro code hcode
    obtain ⟨carrier, hcarrier, rfl⟩ := List.mem_map.mp hcode
    exact canonicalSourceColorCode_mem_coloredEnumeration
      Gamma Gamma.length carrier hcarrier
  · intro code _ code' _ h
    exact h
  · intro code _
    exact Q'.le_refl' _
  · intro code _
    exact sourceColoredRootAttachmentCarrierCodeWeight_nonnegative
      hw Gamma qP b1 b2 label code

#print axioms firstValidOr_mem_or_fallback
#print axioms firstValidOr_valid_of_exists
#print axioms canonicalSourceColors_mem_maskPairs
#print axioms canonicalSourceColors_valid_of_exists
#print axioms canonicalSourceColorCode_injective
#print axioms canonicalSourceColorCarrierCodes_nodup
#print axioms canonicalSourceColorCarrierCodes_payload_unique
#print axioms entryCanonicalSourceColors_valid
#print axioms entryCanonicalSourceColorCode_mem
#print axioms entryCanonicalSourceColorCode_injective
#print axioms entryCanonicalSourceColorCode_weight_eqv_source
#print axioms fullExceptionalSource_sum_le_canonicalSourceColorCarrier
#print axioms canonicalSourceColorCode_mem_coloredEnumeration
#print axioms canonicalSourceColorCarrierMajorant_le_coloredCarrier

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCanonical
