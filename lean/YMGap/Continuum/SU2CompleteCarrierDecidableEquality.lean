/-
# Constructive equality for complete SU(2) recoupling carriers

The complete left- and right-tree carriers are proof-carrying structures,
but their data are determined by short tuples of natural channel labels.
This module exposes constructive decidable equality for the carriers needed
by finite rank reindexing at valences four, five, and six.

No proof field is inspected computationally.  Equality is decided on the
channel code and reconstructed from uniqueness of the corresponding fusion
steps and fixed-output channels.

Constructive contract: finite natural-number codes only; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
import YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
import YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

namespace YMGap.Continuum.SU2CompleteCarrierDecidableEquality

set_option autoImplicit false

open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

/-! ## 1. Uniqueness of proof-carrying fusion data -/

theorem cgFusionStep_unique {a b c : Nat}
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

/-! ## 2. Four- and five-valent carriers -/

instance fixedLeftCGChannelDecidableEq (a b c d : Nat) :
    DecidableEq (FixedLeftCGChannel a b c d) := fun left right =>
  if h : left.k = right.k then
    isTrue (fixedLeftChannel_eq_of_k_eq left right h)
  else
    isFalse (fun heq => h (congrArg FixedLeftCGChannel.k heq))

theorem valenceFiveLeftCarrier_eq_of_y_k_eq {a b c d e : Nat}
    (left right : ValenceFiveLeftCarrier a b c d e)
    (hy : left.y = right.y)
    (hk : left.firstLeft.k = right.firstLeft.k) : left = right := by
  cases left with
  | mk leftY leftFirst leftSuffix =>
      cases right with
      | mk rightY rightFirst rightSuffix =>
          dsimp only at hy hk
          subst rightY
          have hfirst : leftFirst = rightFirst :=
            fixedLeftChannel_eq_of_k_eq leftFirst rightFirst hk
          subst rightFirst
          have hsuffix : leftSuffix = rightSuffix :=
            cgFusionStep_unique leftSuffix rightSuffix
          subst rightSuffix
          rfl

def valenceFiveLeftCarrierCode {a b c d e : Nat}
    (carrier : ValenceFiveLeftCarrier a b c d e) : Nat × Nat :=
  (carrier.y, carrier.firstLeft.k)

theorem valenceFiveLeftCarrierCode_injective {a b c d e : Nat}
    (left right : ValenceFiveLeftCarrier a b c d e)
    (hcode : valenceFiveLeftCarrierCode left =
      valenceFiveLeftCarrierCode right) : left = right := by
  exact valenceFiveLeftCarrier_eq_of_y_k_eq left right
    (congrArg Prod.fst hcode) (congrArg Prod.snd hcode)

instance valenceFiveLeftCarrierDecidableEq (a b c d e : Nat) :
    DecidableEq (ValenceFiveLeftCarrier a b c d e) := fun left right =>
  match decEq (valenceFiveLeftCarrierCode left)
      (valenceFiveLeftCarrierCode right) with
  | isTrue hcode =>
      isTrue (valenceFiveLeftCarrierCode_injective left right hcode)
  | isFalse hcode =>
      isFalse (fun heq => hcode (congrArg valenceFiveLeftCarrierCode heq))

theorem valenceFiveRightCarrier_eq_of_m_p_eq {a b c d e : Nat}
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

def valenceFiveRightCarrierCode {a b c d e : Nat}
    (carrier : ValenceFiveRightCarrier a b c d e) : Nat × Nat :=
  (carrier.m, carrier.second.p)

theorem valenceFiveRightCarrierCode_injective {a b c d e : Nat}
    (left right : ValenceFiveRightCarrier a b c d e)
    (hcode : valenceFiveRightCarrierCode left =
      valenceFiveRightCarrierCode right) : left = right := by
  exact valenceFiveRightCarrier_eq_of_m_p_eq left right
    (congrArg Prod.fst hcode) (congrArg Prod.snd hcode)

instance valenceFiveRightCarrierDecidableEq (a b c d e : Nat) :
    DecidableEq (ValenceFiveRightCarrier a b c d e) := fun left right =>
  match decEq (valenceFiveRightCarrierCode left)
      (valenceFiveRightCarrierCode right) with
  | isTrue hcode =>
      isTrue (valenceFiveRightCarrierCode_injective left right hcode)
  | isFalse hcode =>
      isFalse (fun heq => hcode (congrArg valenceFiveRightCarrierCode heq))

/-! ## 3. Six-valent indexed carriers -/

theorem valenceSixInnerPair_eq_of_m_n_eq {b c d : Nat}
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

def valenceSixLeftCarrierCode {a b c d e f : Nat}
    (carrier : ValenceSixLeftCarrier a b c d e f) :
    (Nat × Nat) × Nat :=
  ((carrier.index.val, carrier.value.y), carrier.value.firstLeft.k)

theorem valenceSixLeftCarrierCode_injective {a b c d e f : Nat}
    (left right : ValenceSixLeftCarrier a b c d e f)
    (hcode : valenceSixLeftCarrierCode left =
      valenceSixLeftCarrierCode right) : left = right := by
  rcases left with ⟨leftIndex, leftValue⟩
  rcases right with ⟨rightIndex, rightValue⟩
  have hz : leftIndex.val = rightIndex.val :=
    congrArg (fun code => code.1.1) hcode
  have hindex : leftIndex = rightIndex := Subtype.ext hz
  subst rightIndex
  have hy : leftValue.y = rightValue.y :=
    congrArg (fun code => code.1.2) hcode
  have hk : leftValue.firstLeft.k = rightValue.firstLeft.k :=
    congrArg Prod.snd hcode
  have hvalue : leftValue = rightValue :=
    valenceFiveLeftCarrier_eq_of_y_k_eq leftValue rightValue hy hk
  subst rightValue
  rfl

instance valenceSixLeftCarrierDecidableEq (a b c d e f : Nat) :
    DecidableEq (ValenceSixLeftCarrier a b c d e f) := fun left right =>
  match decEq (valenceSixLeftCarrierCode left)
      (valenceSixLeftCarrierCode right) with
  | isTrue hcode =>
      isTrue (valenceSixLeftCarrierCode_injective left right hcode)
  | isFalse hcode =>
      isFalse (fun heq => hcode (congrArg valenceSixLeftCarrierCode heq))

def valenceSixRightCarrierCode {a b c d e f : Nat}
    (carrier : ValenceSixRightCarrier a b c d e f) :
    (Nat × Nat) × Nat :=
  ((carrier.index.val.m, carrier.index.val.n), carrier.value.p)

theorem valenceSixRightCarrierCode_injective {a b c d e f : Nat}
    (left right : ValenceSixRightCarrier a b c d e f)
    (hcode : valenceSixRightCarrierCode left =
      valenceSixRightCarrierCode right) : left = right := by
  rcases left with ⟨leftIndex, leftValue⟩
  rcases right with ⟨rightIndex, rightValue⟩
  have hm : leftIndex.val.m = rightIndex.val.m :=
    congrArg (fun code => code.1.1) hcode
  have hn : leftIndex.val.n = rightIndex.val.n :=
    congrArg (fun code => code.1.2) hcode
  have hpair : leftIndex.val = rightIndex.val :=
    valenceSixInnerPair_eq_of_m_n_eq leftIndex.val rightIndex.val hm hn
  have hindex : leftIndex = rightIndex := Subtype.ext hpair
  subst rightIndex
  have hp : leftValue.p = rightValue.p := congrArg Prod.snd hcode
  have hvalue : leftValue = rightValue :=
    fixedRightChannel_eq_of_p_eq leftValue rightValue hp
  subst rightValue
  rfl

instance valenceSixRightCarrierDecidableEq (a b c d e f : Nat) :
    DecidableEq (ValenceSixRightCarrier a b c d e f) := fun left right =>
  match decEq (valenceSixRightCarrierCode left)
      (valenceSixRightCarrierCode right) with
  | isTrue hcode =>
      isTrue (valenceSixRightCarrierCode_injective left right hcode)
  | isFalse hcode =>
      isFalse (fun heq => hcode (congrArg valenceSixRightCarrierCode heq))

theorem valenceSixRightCarriers_complete {a b c d e f : Nat}
    (target : ValenceSixRightCarrier a b c d e f) :
    target ∈ (valenceSixBistochasticKernel a b c d e f).targets := by
  change target ∈ indexedTargets
    (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
  exact indexedTargets_complete
    (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    (fun _ right => fixedRightChannels_complete right)
    target

#print axioms cgFusionStep_unique
#print axioms valenceFiveLeftCarrierCode_injective
#print axioms valenceFiveRightCarrierCode_injective
#print axioms valenceSixInnerPair_eq_of_m_n_eq
#print axioms valenceSixLeftCarrierCode_injective
#print axioms valenceSixRightCarrierCode_injective
#print axioms valenceSixRightCarriers_complete

end YMGap.Continuum.SU2CompleteCarrierDecidableEquality
