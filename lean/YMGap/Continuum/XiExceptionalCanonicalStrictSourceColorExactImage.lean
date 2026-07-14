/-
# Exact source image for canonical source-colored carriers

The compatibility-gated ambient carrier is too large: the three-star payment
fence contains fifteen accepted payloads, while only payloads produced by a
genuine exceptional source are relevant.  This module keeps the exact finite
image of `entryCanonicalSourceColorCode` instead of relaxing to an ambient
Boolean gate.

Membership in the image constructively reconstructs a source entry, and the
preimage is unique by the already proved source encoder injectivity.  The
image enumeration is duplicate-free, lies in the ambient canonical carrier,
and its weighted sum is exactly the original exceptional-source sum.  On the
closed three-star fence the exceptional source has two entries (rather than
the fifteen compatibility-valid ambient witnesses), total exact image weight
`5/256`, and this exact image fits the existing chain-times-`XiR` budget.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorPaymentFence

namespace YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImage

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalPathSafeSummation
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorCanonical
open YMGap.Continuum.XiExceptionalTargetNodup

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Exact finite image and constructive reconstruction -/

def exactCanonicalSourceImageCodes
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (SourceColoredRootAttachmentCarrierCode Gamma.length) :=
  (fullExceptionalSource Gamma qP b1 b2).map
    (entryCanonicalSourceColorCode Gamma qP b1 b2)

theorem exactCanonicalSourceImageCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (exactCanonicalSourceImageCodes Gamma qP b1 b2).Nodup := by
  unfold exactCanonicalSourceImageCodes
  apply nodup_map_of_injOn
    (entryCanonicalSourceColorCode Gamma qP b1 b2)
    (fullExceptionalSource Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2)
  intro entry _ entry' _ hcode
  exact entryCanonicalSourceColorCode_injective
    Gamma qP b1 b2 entry entry' hcode

theorem exactCanonicalSourceImageCode_mem_ambient
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length)
    (hcode : code ∈ exactCanonicalSourceImageCodes Gamma qP b1 b2) :
    code ∈ canonicalSourceColorCarrierCodes Gamma Gamma.length := by
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hcode
  exact entryCanonicalSourceColorCode_mem Gamma qP b1 b2 entry

private theorem any_decide_eq_true_iff [DecidableEq alpha] (x : alpha) :
    ∀ xs : List alpha,
      xs.any (fun y => decide (y = x)) = true ↔ x ∈ xs
  | [] => by simp
  | y :: ys => by
      cases hxy : decide (y = x) with
      | true =>
          have hyx : y = x := of_decide_eq_true hxy
          subst y
          simp
      | false =>
          have hyx : y ≠ x := by
            intro h
            subst y
            simp at hxy
          have hne : x ≠ y := fun h => hyx h.symm
          simp only [List.any_cons, hxy, Bool.false_or]
          rw [any_decide_eq_true_iff x ys]
          simp only [List.mem_cons, hne, false_or]

def exactCanonicalSourceImageB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) : Bool :=
  (exactCanonicalSourceImageCodes Gamma qP b1 b2).any
    (fun actual => decide (actual = code))

theorem exactCanonicalSourceImageB_true_iff_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    exactCanonicalSourceImageB Gamma qP b1 b2 code = true ↔
      code ∈ exactCanonicalSourceImageCodes Gamma qP b1 b2 := by
  unfold exactCanonicalSourceImageB
  exact any_decide_eq_true_iff code
    (exactCanonicalSourceImageCodes Gamma qP b1 b2)

theorem exactCanonicalSourceImageB_true_iff_entry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    exactCanonicalSourceImageB Gamma qP b1 b2 code = true ↔
      ∃ entry, entry ∈ fullExceptionalSource Gamma qP b1 b2 ∧
        entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code := by
  rw [exactCanonicalSourceImageB_true_iff_mem]
  constructor
  · intro hmem
    obtain ⟨entry, hentry, hcode⟩ := List.mem_map.mp hmem
    exact ⟨entry, hentry, hcode⟩
  · rintro ⟨entry, hentry, hcode⟩
    exact List.mem_map.mpr ⟨entry, hentry, hcode⟩

def findCanonicalSourceEntry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    List (ExceptionalSourceEntry Gamma qP b1 b2) →
      Option (ExceptionalSourceEntry Gamma qP b1 b2)
  | [] => none
  | entry :: rest =>
      if decide
          (entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code) then
        some entry
      else
        findCanonicalSourceEntry Gamma qP b1 b2 code rest

private theorem findCanonicalSourceEntry_some_of_exists
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    ∀ source : List (ExceptionalSourceEntry Gamma qP b1 b2),
      (∃ entry, entry ∈ source ∧
        entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code) →
      ∃ entry, findCanonicalSourceEntry Gamma qP b1 b2 code source =
        some entry
  | [], hex => by
      obtain ⟨_, hmem, _⟩ := hex
      cases hmem
  | entry :: rest, hex => by
      unfold findCanonicalSourceEntry
      cases hgate : decide
          (entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code) with
      | true => exact ⟨entry, rfl⟩
      | false =>
          apply findCanonicalSourceEntry_some_of_exists
            Gamma qP b1 b2 code rest
          obtain ⟨witness, hmem, hcode⟩ := hex
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst witness
            rw [decide_eq_true hcode] at hgate
            cases hgate
          · exact ⟨witness, htail, hcode⟩

private theorem findCanonicalSourceEntry_some_correct
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    ∀ (source : List (ExceptionalSourceEntry Gamma qP b1 b2)) entry,
      findCanonicalSourceEntry Gamma qP b1 b2 code source = some entry →
      entry ∈ source ∧
        entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code
  | [], _, h => by cases h
  | head :: rest, entry, h => by
      unfold findCanonicalSourceEntry at h
      cases hgate : decide
          (entryCanonicalSourceColorCode Gamma qP b1 b2 head = code) with
      | true =>
          simp [hgate] at h
          have hentry : entry = head := by
            exact h.symm
          subst entry
          exact ⟨List.mem_cons_self, of_decide_eq_true hgate⟩
      | false =>
          simp [hgate] at h
          have htail := findCanonicalSourceEntry_some_correct
            Gamma qP b1 b2 code rest entry h
          exact ⟨List.mem_cons_of_mem head htail.1, htail.2⟩

def exactCanonicalSourceReconstruct
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :
    Option (ExceptionalSourceEntry Gamma qP b1 b2) :=
  findCanonicalSourceEntry Gamma qP b1 b2 code
    (fullExceptionalSource Gamma qP b1 b2)

theorem exactCanonicalSourceReconstruct_some_of_image
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length)
    (himage : exactCanonicalSourceImageB Gamma qP b1 b2 code = true) :
    ∃ entry, exactCanonicalSourceReconstruct Gamma qP b1 b2 code =
        some entry ∧
      entry ∈ fullExceptionalSource Gamma qP b1 b2 ∧
        entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code := by
  have hex := (exactCanonicalSourceImageB_true_iff_entry
    Gamma qP b1 b2 code).mp himage
  obtain ⟨entry, hfind⟩ := findCanonicalSourceEntry_some_of_exists
    Gamma qP b1 b2 code (fullExceptionalSource Gamma qP b1 b2) hex
  have hcorrect := findCanonicalSourceEntry_some_correct
    Gamma qP b1 b2 code (fullExceptionalSource Gamma qP b1 b2)
      entry hfind
  exact ⟨entry, hfind, hcorrect⟩

def ExactCanonicalSourcePreimage
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length) :=
  { entry : ExceptionalSourceEntry Gamma qP b1 b2 //
      entry ∈ fullExceptionalSource Gamma qP b1 b2 ∧
        entryCanonicalSourceColorCode Gamma qP b1 b2 entry = code }

theorem exactCanonicalSourceImage_reconstruct_nonempty
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length)
    (himage : exactCanonicalSourceImageB Gamma qP b1 b2 code = true) :
    Nonempty (ExactCanonicalSourcePreimage Gamma qP b1 b2 code) := by
  obtain ⟨entry, hentry, hcode⟩ :=
    (exactCanonicalSourceImageB_true_iff_entry
      Gamma qP b1 b2 code).mp himage
  exact ⟨⟨entry, hentry, hcode⟩⟩

theorem exactCanonicalSourceImage_preimage_unique
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (code : SourceColoredRootAttachmentCarrierCode Gamma.length)
    (a b : ExactCanonicalSourcePreimage Gamma qP b1 b2 code) :
    a = b := by
  apply Subtype.ext
  exact entryCanonicalSourceColorCode_injective
    Gamma qP b1 b2 a.1 b.1 (a.2.2.trans b.2.2.symm)

/-! ## Exact image weight, with no ambient overcount -/

def exactCanonicalSourceImageMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum
    (canonicalSourceColorCarrierCodeWeight w Gamma qP b1 b2 label)
    (exactCanonicalSourceImageCodes Gamma qP b1 b2)

theorem exactCanonicalSourceImageMajorant_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    (0 : Q') ≤ exactCanonicalSourceImageMajorant
      w Gamma qP b1 b2 label := by
  unfold exactCanonicalSourceImageMajorant
  apply qListSum_nonnegative
  intro code _
  exact canonicalSourceColorCarrierCodeWeight_nonnegative
    hw Gamma qP b1 b2 label code

theorem exactCanonicalSourceImageMajorant_eqv_source_sum
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    exactCanonicalSourceImageMajorant w Gamma qP b1 b2 label ≈
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) := by
  unfold exactCanonicalSourceImageMajorant
    exactCanonicalSourceImageCodes
  rw [qListSum_map]
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr
      (fun entry => canonicalSourceColorCarrierCodeWeight
        w Gamma qP b1 b2 label
        (entryCanonicalSourceColorCode Gamma qP b1 b2 entry))
      (fun entry => occurrencePairWeight
        w qP b1 b2 Gamma label entry.1)
      (fullExceptionalSource Gamma qP b1 b2)
      (fun entry _ => entryCanonicalSourceColorCode_weight_eqv_source
        w Gamma qP b1 b2 label entry)) ?_
  have hfull := fullExceptionalSource_weight_eq
    w Gamma qP b1 b2 label
  unfold pathSafeSourceWeight at hfull
  exact Q'.eqv_of_eq hfull

/-! ## Closed exact-image audit on the three-star fence -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)
private def X : Polymer TL := [p, q]
private def Y : Polymer TL := [p]
private def Z : Polymer TL := [q]
private def Gamma3 : List (Polymer TL) := [X, Y, Z]
private def qAll : Polymer TL → Bool := fun _ => true
private def bX : Polymer TL → Bool := fun T => decide (T = X)
private def bY : Polymer TL → Bool := fun T => decide (T = Y)
private def labelOne : TL.Plaquette → Rep := fun _ => 1
private def half : Q' := Q'.mkPos 1 2 (by decide)

private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))
private def x3 : OccBitVec 3 := bits3 true false false
private def y3 : OccBitVec 3 := bits3 false true false
private def yz3 : OccBitVec 3 := bits3 false true true
private def pair1 : MaskPair Gamma3.length := (y3, x3)
private def pair2 : MaskPair Gamma3.length := (yz3, x3)

theorem star_exceptional_source_codes_exact :
    exceptionalSourceCodes Gamma3 qAll bX bY = [pair1, pair2] := by
  decide

theorem star_exact_source_image_has_two_codes :
    (exactCanonicalSourceImageCodes Gamma3 qAll bX bY).length = 2 := by
  unfold exactCanonicalSourceImageCodes fullExceptionalSource
  rw [List.length_map, List.length_attach]
  simpa using congrArg List.length star_exceptional_source_codes_exact

set_option maxRecDepth 10000 in
theorem star_exceptional_source_sum_eqv_five_over_256 :
    qListSum (occurrencePairWeight half qAll bX bY Gamma3 labelOne)
        (exceptionalSourceCodes Gamma3 qAll bX bY) ≈
      Q'.mkPos 5 256 (by decide) := by
  decide

theorem star_exact_source_image_majorant_eqv_five_over_256 :
    exactCanonicalSourceImageMajorant
        half Gamma3 qAll bX bY labelOne ≈
      Q'.mkPos 5 256 (by decide) := by
  exact Q'.eqv_trans _ _ _
    (exactCanonicalSourceImageMajorant_eqv_source_sum
      half Gamma3 qAll bX bY labelOne)
    star_exceptional_source_sum_eqv_five_over_256

theorem star_accepted_budget_eqv_4745_over_131072 :
    connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne ≈
      Q'.mkPos 4745 131072 (by decide) := by
  decide

theorem star_exact_source_image_pays_accepted_budget :
    exactCanonicalSourceImageMajorant
        half Gamma3 qAll bX bY labelOne ≤
      connectingChainMajorant half qAll bX bY Gamma3 labelOne *
        XiR half qAll Gamma3 labelOne := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv star_exact_source_image_majorant_eqv_five_over_256)
    (Q'.le_trans' _ _ _
      (by decide : Q'.mkPos 5 256 (by decide) ≤
        Q'.mkPos 4745 131072 (by decide))
      (Q'.ge_of_eqv star_accepted_budget_eqv_4745_over_131072))

#print axioms exactCanonicalSourceImageCodes_nodup
#print axioms exactCanonicalSourceImageCode_mem_ambient
#print axioms exactCanonicalSourceImageB_true_iff_mem
#print axioms exactCanonicalSourceImageB_true_iff_entry
#print axioms exactCanonicalSourceReconstruct_some_of_image
#print axioms exactCanonicalSourceImage_reconstruct_nonempty
#print axioms exactCanonicalSourceImage_preimage_unique
#print axioms exactCanonicalSourceImageMajorant_nonnegative
#print axioms exactCanonicalSourceImageMajorant_eqv_source_sum
#print axioms star_exceptional_source_codes_exact
#print axioms star_exact_source_image_has_two_codes
#print axioms star_exceptional_source_sum_eqv_five_over_256
#print axioms star_exact_source_image_majorant_eqv_five_over_256
#print axioms star_accepted_budget_eqv_4745_over_131072
#print axioms star_exact_source_image_pays_accepted_budget

end YMGap.Continuum.XiExceptionalCanonicalStrictSourceColorExactImage
