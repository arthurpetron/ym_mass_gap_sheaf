/-
# Located cutoff-one channel choices

The local positive-channel dispatcher is indexed by a Haar word, whereas the
global cutoff-one contraction must remember which physical lattice link owns
each local choice.  This module supplies precisely that structural bridge.

For every touched link it forms the exact valence-indexed local channel list
from that link's literal descriptor bucket, tags every choice by the physical
link, and retains the canonical touched-link order.  The resulting family is
consumed by `nestedListQSum`; no Cartesian product of global channel
assignments is materialized.

`NestedSelection` records the words that this nested traversal can actually
reach.  Its congruence theorem therefore needs equality only on reachable
words, rather than on arbitrary lists of located channels.

This file is intentionally structural.  It neither posits a global channel
plan nor claims an equality between a channel contraction and a lattice
coefficient.  Those require the subsequent endpoint-wiring and contraction
proofs.

# Constructive discipline

There is no `Classical`, assignment enumeration, `native_decide`,
`sorry`/`admit`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneDescriptorChannelTensor
import YMGap.Continuum.FactoredPositiveChannelTraceBound

namespace YMGap.Continuum.SU2QuaternionCutoffOneLocatedChannels

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PositiveChannelTraceBound
open YMGap.Continuum.FactoredPositiveChannelTraceBound
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneLocalChannelMass
open YMGap.Continuum.SU2QuaternionCutoffOneDescriptorChannelTensor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Physical-link-labelled local channel choices -/

/-- One admissible local positive channel together with the physical link
whose Haar bucket selected it. -/
structure CutoffOneLocatedChannel where
  physicalLink : Z4Link
  channel : CutoffOneLocalChannel
  deriving DecidableEq

/-- The exact local channel list for a supplied physical link and its literal
descriptor bucket.  The link is only a location tag; the choices depend on
the descriptor count, as proved by the descriptor-channel dispatcher. -/
def cutoffOneLocatedChannelChoices
    (physicalLink : Z4Link)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    List CutoffOneLocatedChannel :=
  (cutoffOneLocalChannelChoicesAtValence descriptors.length).map
    (fun channel =>
      { physicalLink := physicalLink
        channel := channel })

@[simp] theorem cutoffOneLocatedChannelChoices_length
    (physicalLink : Z4Link)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    (cutoffOneLocatedChannelChoices physicalLink descriptors).length =
      (cutoffOneLocalChannelChoicesAtValence descriptors.length).length := by
  simp [cutoffOneLocatedChannelChoices]

/-- The local choice lists in the exact canonical order of the touched-link
carrier.  Each list is computed from the literal occurrence bucket at the
same physical link. -/
def cutoffOneChannelChoiceLists
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    List (List CutoffOneLocatedChannel) :=
  (cutoffOneTouchedLinks n support).map (fun physicalLink =>
    cutoffOneLocatedChannelChoices physicalLink
      (cutoffOneLinkOccurrenceBucket
        orientationAt n support physicalLink))

@[simp] theorem cutoffOneChannelChoiceLists_length
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneChannelChoiceLists orientationAt n support).length =
      (cutoffOneTouchedLinks n support).length := by
  simp [cutoffOneChannelChoiceLists]

/-! ## 2. Reachable words of a structural nested sum -/

/-- `NestedSelection choiceLists selected` certifies that `selected` contains
one member of every successive local choice list, in the same order.

This is an indexed proposition rather than a materialized Cartesian product.
In particular, an empty local choice list has no selection. -/
inductive NestedSelection {A : Type} :
    List (List A) -> List A -> Prop where
  | nil : NestedSelection [] []
  | cons {choices remaining choice selected} :
      choice ∈ choices ->
      NestedSelection remaining selected ->
      NestedSelection (choices :: remaining) (choice :: selected)

theorem NestedSelection.length_eq {A : Type}
    {choiceLists : List (List A)} {selected : List A}
    (hselected : NestedSelection choiceLists selected) :
    selected.length = choiceLists.length := by
  induction hselected with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.length_cons]
      exact congrArg Nat.succ ih

/-! ## 3. Congruence only on reachable selections -/

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- A list sum only needs pointwise equivalence on members of the list. -/
private theorem listQSum_eqv_congr_of_mem {A : Type}
    {left right : A -> Q'} :
    forall values : List A,
      (forall value, value ∈ values -> left value ≈ right value) ->
      listQSum left values ≈ listQSum right values
  | [], _ => Q'.eqv_refl 0
  | value :: values, h =>
      q_add_congr
        (h value List.mem_cons_self)
        (listQSum_eqv_congr_of_mem values
          (fun tailValue htail =>
            h tailValue (List.mem_cons_of_mem value htail)))

/-- Equivalence on structurally reachable channel words transports through
the nested sum.  No hypothesis is required for malformed words, words of the
wrong length, or words whose entry is absent from its corresponding local
choice list. -/
theorem nestedListQSum_eqv_congr_on_nestedSelections {A : Type} :
    forall (choiceLists : List (List A))
      (left right : List A -> Q'),
      (forall selected,
        NestedSelection choiceLists selected ->
        left selected ≈ right selected) ->
      nestedListQSum choiceLists left ≈
        nestedListQSum choiceLists right
  | [], left, right, h => h [] NestedSelection.nil
  | choices :: remaining, left, right, h =>
      listQSum_eqv_congr_of_mem choices
        (fun choice hchoice =>
          nestedListQSum_eqv_congr_on_nestedSelections remaining
            (fun selected => left (choice :: selected))
            (fun selected => right (choice :: selected))
            (fun selected hselected =>
              h (choice :: selected)
                (NestedSelection.cons hchoice hselected)))

/-! ## Axiom audit -/

#print axioms cutoffOneLocatedChannelChoices
#print axioms cutoffOneChannelChoiceLists
#print axioms NestedSelection.length_eq
#print axioms nestedListQSum_eqv_congr_on_nestedSelections

end YMGap.Continuum.SU2QuaternionCutoffOneLocatedChannels
