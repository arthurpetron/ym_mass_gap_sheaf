/-
# Source-restricted fibre of the strict canonical carrier

The strict canonical tree does not globally retain the old trunk boundary.
For exceptional sources, the natural boundary candidate is the first child
carrying the terminal marker `b2`.  This module defines that source-independent
decoder and isolates the exact round-trip predicate.  On the resulting
source-defined subfamily, the canonical map is injective and preserves the
source weight exactly, with no length or multiplicity tag.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictAnalytic
import YMGap.Continuum.XiExceptionalCanonicalStrictFiberFence

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceFiber

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalSourceTreeFiber
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictAnalytic

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## First-`b2` trunk decoder -/

def prependUntilB2 (Gamma : List (Polymer L))
    (b2 : Polymer L → Bool) :
    Nat → List (Nat × Nat) → OccTreeCode Gamma.length
  | current, [] => .single current
  | current, (_, child) :: rest =>
      if b2 (polyAt Gamma child) then
        .prepend current (.single child)
      else
        .prepend current (prependUntilB2 Gamma b2 child rest)

def firstB2CoreLength (Gamma : List (Polymer L))
    (b2 : Polymer L → Bool) (code : RootAttachmentTreeCode Gamma.length) : Nat :=
  (prependUntilB2 Gamma b2 code.root code.attachments).height - 1

def firstB2CanonicalTreeDecoder (Gamma : List (Polymer L))
    (b2 : Polymer L → Bool) (code : RootAttachmentTreeCode Gamma.length) :
    OccTreeCode Gamma.length :=
  let core := prependUntilB2 Gamma b2 code.root code.attachments
  attachAll core (code.attachments.drop (core.height - 1))

def firstB2CanonicalCarrierDecoder (Gamma : List (Polymer L))
    (b2 : Polymer L → Bool)
    (code : RootAttachmentCarrierCode Gamma.length) :
    OccTreeCarrierCode Gamma.length :=
  ⟨firstB2CanonicalTreeDecoder Gamma b2 code.tree,
    code.background, code.external⟩

def CanonicalSourceRecoverable
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  firstB2CanonicalCarrierDecoder Gamma b2
      (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry) =
    entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry

def FirstB2SourceBoundary
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  firstB2CanonicalTreeDecoder Gamma b2
      (entryRootAttachmentCarrierCode Gamma qP b1 b2 entry).tree =
    (entryOccurrenceTreeCarrierCode Gamma qP b1 b2 entry).tree

theorem canonicalSourceRecoverable_of_firstB2Boundary
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hboundary : FirstB2SourceBoundary Gamma qP b1 b2 entry) :
    CanonicalSourceRecoverable Gamma qP b1 b2 entry := by
  unfold FirstB2SourceBoundary at hboundary
  unfold CanonicalSourceRecoverable firstB2CanonicalCarrierDecoder
  unfold entryRootAttachmentCarrierCode entryOccurrenceTreeCarrierCode at hboundary ⊢
  rw [hboundary]

abbrev RecoverableExceptionalSourceEntry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
    FirstB2SourceBoundary Gamma qP b1 b2 entry }

def recoverableEntryRootAttachmentCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : RecoverableExceptionalSourceEntry Gamma qP b1 b2) :
    RootAttachmentCarrierCode Gamma.length :=
  entryRootAttachmentCarrierCode Gamma qP b1 b2 entry.1

theorem entryRootAttachmentCarrierCode_injective_of_recoverable
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrec1 : CanonicalSourceRecoverable Gamma qP b1 b2 entry1)
    (hrec2 : CanonicalSourceRecoverable Gamma qP b1 b2 entry2)
    (hcode : entryRootAttachmentCarrierCode Gamma qP b1 b2 entry1 =
      entryRootAttachmentCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have hdecoded := congrArg
    (firstB2CanonicalCarrierDecoder Gamma b2) hcode
  rw [hrec1, hrec2] at hdecoded
  exact entryOccurrenceTreeCarrierCode_injective Gamma qP b1 b2
    entry1 entry2 hdecoded

theorem recoverableEntryRootAttachmentCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : RecoverableExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : recoverableEntryRootAttachmentCarrierCode
        Gamma qP b1 b2 entry1 =
      recoverableEntryRootAttachmentCarrierCode
        Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  apply Subtype.ext
  exact entryRootAttachmentCarrierCode_injective_of_recoverable
    Gamma qP b1 b2 entry1.1 entry2.1
    (canonicalSourceRecoverable_of_firstB2Boundary
      Gamma qP b1 b2 entry1.1 entry1.2)
    (canonicalSourceRecoverable_of_firstB2Boundary
      Gamma qP b1 b2 entry2.1 entry2.2) hcode

theorem recoverableEntryRootAttachmentCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : RecoverableExceptionalSourceEntry Gamma qP b1 b2) :
    recoverableEntryRootAttachmentCarrierCode Gamma qP b1 b2 entry ∈
      rootAttachmentCarrierCodes Gamma.length Gamma.length :=
  entryRootAttachmentCarrierCode_mem Gamma qP b1 b2 entry.1

theorem recoverableEntryRootAttachmentCarrierCode_strict_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : RecoverableExceptionalSourceEntry Gamma qP b1 b2) :
    strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label
        (recoverableEntryRootAttachmentCarrierCode
          Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1.1 :=
  entryRootAttachmentCarrierCode_strict_weight_eqv_source
    w Gamma qP b1 b2 label entry.1

theorem strictRootAttachmentCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) :
    (0 : Q') ≤ strictRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label code := by
  unfold strictRootAttachmentCarrierCodeWeight
  split
  · exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (strictRootAttachmentTreeWeight_nonnegative hw
          Gamma qP b1 b2 label code.tree)
        (familyActivity_nonneg hw
          (selectByBits Gamma code.background) label))
      (admissibleFamilyWeight_nonnegative hw qP label
        (selectByBits Gamma code.external))
  · exact Q'.le_refl' _

theorem recoverableExceptionalSource_sum_le_strictCarrier
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List
      (RecoverableExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup) :
    qListSum
        (fun entry => occurrencePairWeight
          w qP b1 b2 Gamma label entry.1.1) source ≤
      qListSum
        (strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (rootAttachmentCarrierCodes Gamma.length Gamma.length) := by
  apply qListSum_le_of_injective source
    (rootAttachmentCarrierCodes Gamma.length Gamma.length)
    (fun entry => occurrencePairWeight
      w qP b1 b2 Gamma label entry.1.1)
    (strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
    (recoverableEntryRootAttachmentCarrierCode Gamma qP b1 b2)
    hsource
  · intro entry _
    exact recoverableEntryRootAttachmentCarrierCode_mem
      Gamma qP b1 b2 entry
  · intro entry1 _ entry2 _ hcode
    exact recoverableEntryRootAttachmentCarrierCode_injective
      Gamma qP b1 b2 entry1 entry2 hcode
  · intro entry _
    exact Q'.ge_of_eqv
      (recoverableEntryRootAttachmentCarrierCode_strict_weight_eqv_source
        w Gamma qP b1 b2 label entry)
  · intro code _
    exact strictRootAttachmentCarrierCodeWeight_nonnegative hw
      Gamma qP b1 b2 label code

/-! ## Closed non-vacuity witness -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)
private def X : Polymer TL := [p]
private def Y : Polymer TL := [p, q]
private def Gamma2 : List (Polymer TL) := [X, Y]
private def bY : Polymer TL → Bool := fun Z => decide (Z = Y)
private def directCode : RootAttachmentTreeCode Gamma2.length :=
  ⟨0, [(0, 1)]⟩

theorem direct_two_occurrence_code_decodes_to_trunk :
    firstB2CanonicalTreeDecoder Gamma2 bY directCode =
      OccTreeCode.prepend 0 (.single 1) := by
  decide

#print axioms canonicalSourceRecoverable_of_firstB2Boundary
#print axioms entryRootAttachmentCarrierCode_injective_of_recoverable
#print axioms recoverableEntryRootAttachmentCarrierCode_injective
#print axioms recoverableEntryRootAttachmentCarrierCode_strict_weight_eqv_source
#print axioms strictRootAttachmentCarrierCodeWeight_nonnegative
#print axioms recoverableExceptionalSource_sum_le_strictCarrier
#print axioms direct_two_occurrence_code_decodes_to_trunk

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceFiber
