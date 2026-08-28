/-
# Sparse fundamental higher-valence recoupling is deterministic

A closed binary fundamental surface meets each ordinary link in exactly two
fundamental plaquettes; all remaining incident labels are vacuum.  Although
the geometric link can still have valence five or six, its invariant fusion
space is one-dimensional.  This module proves that fact directly on the
production right-tree carriers.

For valence five and six, the right carrier is a singleton whenever all
external doubled-spin labels are binary and their sum is exactly two.  The
vacuum word is handled separately below, and the two cases are joined into
the even-sparse condition needed by a closed surface.  Exact row
normalization then forces every entry of the completed higher-valence
recoupling matrix to equal one.  Thus ordinary surface links cost no retained
mass; only a genuine four-fundamental switching pivot can contribute the
nontrivial `1/4` factor.

This is local representation theory.  It does not construct the global
surface, choose its target column, or prove strand disconnection.

Constructive contract: proof-carrying fusion arithmetic, finite carrier
uniqueness, and exact `Q'` normalization only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.  The finite binary case split uses a bounded
one-million-heartbeat allowance.
-/

import YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
import YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

set_option maxHeartbeats 1000000

namespace YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock

local infix:50 " ≈ " => Q'.eqv

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

private theorem singleton_of_nodup_of_mem_of_unique {A : Type}
    (items : List A) (item : A) (hnodup : items.Nodup)
    (hmem : item ∈ items) (hunique : ∀ entry, entry = item) :
    items = [item] := by
  cases items with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons head tail =>
    have hhead := hunique head
    have htail : tail = [] := by
      cases tail with
      | nil => rfl
      | cons next rest =>
        have hparts := List.nodup_cons.mp hnodup
        have hnext := hunique next
        exact False.elim (hparts.1 (by
          rw [hnext, ← hhead]
          exact List.mem_cons_self))
    rw [hhead, htail]

/-! ## 1. Valence four with zero or two fundamental labels -/

theorem sparsePhysicalSchurRightCarrier_unique
    (a b c d : Nat) (hb : b ≤ 1) (hc : c ≤ 1)
    (hsum : a + b + c + d = 2)
    (left right : FixedRightCGChannel a b c d) : left = right := by
  have hleftP := Nat.le_min.mp left.p_le
  have hrightP := Nat.le_min.mp right.p_le
  have hleftR := Nat.le_min.mp left.r_le
  have hrightR := Nat.le_min.mp right.r_le
  have hleftDegree := left.degree_eq
  have hrightDegree := right.degree_eq
  have hp : left.p = right.p := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  exact fixedRightChannel_eq_of_p_eq left right hp

theorem sparsePhysicalSchurRightCarriers_eq_singleton
    (a b c d : Nat) (hb : b ≤ 1) (hc : c ≤ 1)
    (hsum : a + b + c + d = 2)
    (target : FixedRightCGChannel a b c d) :
    fixedRightChannels a b c d = [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (fixedRightChannels_nodup a b c d)
    (fixedRightChannels_complete target)
    (fun entry => sparsePhysicalSchurRightCarrier_unique
      a b c d hb hc hsum entry target)

theorem sparsePhysicalSchurKernel_eqv_one
    (a b c d : Nat) (hb : b ≤ 1) (hc : c ≤ 1)
    (hsum : a + b + c + d = 2)
    (source : FixedLeftCGChannel a b c d)
    (target : FixedRightCGChannel a b c d) :
    (physicalSchurBistochasticKernel a b c d).weight source target ≈ 1 := by
  have h := (physicalSchurBistochasticKernel a b c d).row_normalized source
  change listQSum
      ((physicalSchurBistochasticKernel a b c d).weight source)
      (fixedRightChannels a b c d) ≈ 1 at h
  rw [sparsePhysicalSchurRightCarriers_eq_singleton
    a b c d hb hc hsum target] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem zeroPhysicalSchurRightCarrier_unique
    (left right : FixedRightCGChannel 0 0 0 0) : left = right := by
  have hleftP := Nat.le_min.mp left.p_le
  have hrightP := Nat.le_min.mp right.p_le
  have hleftR := Nat.le_min.mp left.r_le
  have hrightR := Nat.le_min.mp right.r_le
  have hleftDegree := left.degree_eq
  have hrightDegree := right.degree_eq
  have hp : left.p = right.p := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  exact fixedRightChannel_eq_of_p_eq left right hp

theorem zeroPhysicalSchurRightCarriers_eq_singleton
    (target : FixedRightCGChannel 0 0 0 0) :
    fixedRightChannels 0 0 0 0 = [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (fixedRightChannels_nodup 0 0 0 0)
    (fixedRightChannels_complete target)
    (fun entry => zeroPhysicalSchurRightCarrier_unique entry target)

theorem zeroPhysicalSchurKernel_eqv_one
    (source : FixedLeftCGChannel 0 0 0 0)
    (target : FixedRightCGChannel 0 0 0 0) :
    (physicalSchurBistochasticKernel 0 0 0 0).weight source target ≈ 1 := by
  have h := (physicalSchurBistochasticKernel 0 0 0 0).row_normalized source
  change listQSum
      ((physicalSchurBistochasticKernel 0 0 0 0).weight source)
      (fixedRightChannels 0 0 0 0) ≈ 1 at h
  rw [zeroPhysicalSchurRightCarriers_eq_singleton target] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem evenSparsePhysicalSchurKernel_eqv_one
    (a b c d : Nat) (hb : b ≤ 1) (hc : c ≤ 1)
    (hevenSparse : a + b + c + d = 0 ∨ a + b + c + d = 2)
    (source : FixedLeftCGChannel a b c d)
    (target : FixedRightCGChannel a b c d) :
    (physicalSchurBistochasticKernel a b c d).weight source target ≈ 1 := by
  rcases hevenSparse with hzero | htwo
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    subst a
    subst b
    subst c
    subst d
    exact zeroPhysicalSchurKernel_eqv_one source target
  · exact sparsePhysicalSchurKernel_eqv_one
      a b c d hb hc htwo source target

/-! ## 2. Valence five with exactly two fundamental labels -/

theorem sparseValenceFiveRightCarrier_unique
    (a b c d e : Nat)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hsum : a + b + c + d + e = 2)
    (left right : ValenceFiveRightCarrier a b c d e) :
    left = right := by
  have hleftInner := left.inner.output_eq
  have hrightInner := right.inner.output_eq
  have hleftP := Nat.le_min.mp left.second.p_le
  have hrightP := Nat.le_min.mp right.second.p_le
  have hleftR := Nat.le_min.mp left.second.r_le
  have hrightR := Nat.le_min.mp right.second.r_le
  have hleftDegree := left.second.degree_eq
  have hrightDegree := right.second.degree_eq
  have hm : left.m = right.m := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  have hp : left.second.p = right.second.p := by
    unfold FixedRightCGChannel.intermediate at *
    omega
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

theorem sparseValenceFiveRightCarriers_eq_singleton
    (a b c d e : Nat)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hsum : a + b + c + d + e = 2)
    (target : ValenceFiveRightCarrier a b c d e) :
    valenceFiveRightCarriers a b c d e = [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (valenceFiveRightCarriers_nodup a b c d e)
    (valenceFiveRightCarriers_complete target)
    (fun entry => sparseValenceFiveRightCarrier_unique
      a b c d e hb hc hd hsum entry target)

theorem sparseValenceFiveKernel_eqv_one
    (a b c d e : Nat)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hsum : a + b + c + d + e = 2)
    (source : ValenceFiveLeftCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e) :
    (valenceFiveBistochasticKernel a b c d e).weight source target ≈ 1 := by
  have h := (valenceFiveBistochasticKernel a b c d e).row_normalized source
  change listQSum
      ((valenceFiveBistochasticKernel a b c d e).weight source)
      (valenceFiveRightCarriers a b c d e) ≈ 1 at h
  rw [sparseValenceFiveRightCarriers_eq_singleton
    a b c d e hb hc hd hsum target] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem sparseValenceFiveKernel_pos
    (a b c d e : Nat)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hsum : a + b + c + d + e = 2)
    (source : ValenceFiveLeftCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e) :
    (0 : Q') <
      (valenceFiveBistochasticKernel a b c d e).weight source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (sparseValenceFiveKernel_eqv_one
        a b c d e hb hc hd hsum source target))

/-! ## 2. The valence-five vacuum and even-sparse union -/

theorem zeroValenceFiveRightCarrier_unique
    (left right : ValenceFiveRightCarrier 0 0 0 0 0) :
    left = right := by
  have hleftInner := left.inner.output_eq
  have hrightInner := right.inner.output_eq
  have hleftP := Nat.le_min.mp left.second.p_le
  have hrightP := Nat.le_min.mp right.second.p_le
  have hleftR := Nat.le_min.mp left.second.r_le
  have hrightR := Nat.le_min.mp right.second.r_le
  have hleftDegree := left.second.degree_eq
  have hrightDegree := right.second.degree_eq
  have hm : left.m = right.m := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  have hp : left.second.p = right.second.p := by
    unfold FixedRightCGChannel.intermediate at *
    omega
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

theorem zeroValenceFiveRightCarriers_eq_singleton
    (target : ValenceFiveRightCarrier 0 0 0 0 0) :
    valenceFiveRightCarriers 0 0 0 0 0 = [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (valenceFiveRightCarriers_nodup 0 0 0 0 0)
    (valenceFiveRightCarriers_complete target)
    (fun entry => zeroValenceFiveRightCarrier_unique entry target)

theorem zeroValenceFiveKernel_eqv_one
    (source : ValenceFiveLeftCarrier 0 0 0 0 0)
    (target : ValenceFiveRightCarrier 0 0 0 0 0) :
    (valenceFiveBistochasticKernel 0 0 0 0 0).weight source target ≈ 1 := by
  have h := (valenceFiveBistochasticKernel 0 0 0 0 0).row_normalized source
  change listQSum
      ((valenceFiveBistochasticKernel 0 0 0 0 0).weight source)
      (valenceFiveRightCarriers 0 0 0 0 0) ≈ 1 at h
  rw [zeroValenceFiveRightCarriers_eq_singleton target] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem evenSparseValenceFiveKernel_eqv_one
    (a b c d e : Nat)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (hevenSparse : a + b + c + d + e = 0 ∨
      a + b + c + d + e = 2)
    (source : ValenceFiveLeftCarrier a b c d e)
    (target : ValenceFiveRightCarrier a b c d e) :
    (valenceFiveBistochasticKernel a b c d e).weight source target ≈ 1 := by
  rcases hevenSparse with hzero | htwo
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    have he0 : e = 0 := by omega
    subst a
    subst b
    subst c
    subst d
    subst e
    exact zeroValenceFiveKernel_eqv_one source target
  · exact sparseValenceFiveKernel_eqv_one
      a b c d e hb hc hd htwo source target

/-! ## 3. Valence six with exactly two fundamental labels -/

private theorem valenceSixInnerPair_eq_of_m_n {b c d : Nat}
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

private theorem sparseSixChain_unique
    (a b c d e f : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hsum : a + b + c + d + e + f = 2)
    (leftM leftBC leftN leftMD leftT leftP leftR : Nat)
    (rightM rightBC rightN rightMD rightT rightP rightR : Nat)
    (hleftBC : b + c = leftM + 2 * leftBC)
    (hrightBC : b + c = rightM + 2 * rightBC)
    (hleftMD : leftM + d = leftN + 2 * leftMD)
    (hrightMD : rightM + d = rightN + 2 * rightMD)
    (hleftT : leftN + e = leftT + 2 * leftP)
    (hrightT : rightN + e = rightT + 2 * rightP)
    (hleftFinal : a + leftT = f + 2 * leftR)
    (hrightFinal : a + rightT = f + 2 * rightR)
    (hleftBCb : leftBC ≤ b) (hleftBCc : leftBC ≤ c)
    (hrightBCb : rightBC ≤ b) (hrightBCc : rightBC ≤ c)
    (hleftMDd : leftMD ≤ d)
    (hrightMDd : rightMD ≤ d)
    (hleftPe : leftP ≤ e)
    (hrightPe : rightP ≤ e)
    (hleftRa : leftR ≤ a)
    (hrightRa : rightR ≤ a) :
    leftM = rightM ∧ leftN = rightN ∧ leftP = rightP := by
  have ha01 : a = 0 ∨ a = 1 := by omega
  have hb01 : b = 0 ∨ b = 1 := by omega
  have hc01 : c = 0 ∨ c = 1 := by omega
  have hd01 : d = 0 ∨ d = 1 := by omega
  have he01 : e = 0 ∨ e = 1 := by omega
  have hf01 : f = 0 ∨ f = 1 := by omega
  rcases ha01 with rfl | rfl <;>
    rcases hb01 with rfl | rfl <;>
    rcases hc01 with rfl | rfl <;>
    rcases hd01 with rfl | rfl <;>
    rcases he01 with rfl | rfl <;>
    rcases hf01 with rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem sparseValenceSixRightCarrier_unique
    (a b c d e f : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hsum : a + b + c + d + e + f = 2)
    (left right : ValenceSixRightCarrier a b c d e f) :
    left = right := by
  have hleftBC := left.index.val.innerBC.output_eq
  have hrightBC := right.index.val.innerBC.output_eq
  have hleftMD := left.index.val.innerMD.output_eq
  have hrightMD := right.index.val.innerMD.output_eq
  have hleftP := Nat.le_min.mp left.value.p_le
  have hrightP := Nat.le_min.mp right.value.p_le
  have hleftR := Nat.le_min.mp left.value.r_le
  have hrightR := Nat.le_min.mp right.value.r_le
  have hleftDegree := left.value.degree_eq
  have hrightDegree := right.value.degree_eq
  have hleftBCBound := Nat.le_min.mp left.index.val.innerBC.order_le
  have hrightBCBound := Nat.le_min.mp right.index.val.innerBC.order_le
  have hleftMDBound := Nat.le_min.mp left.index.val.innerMD.order_le
  have hrightMDBound := Nat.le_min.mp right.index.val.innerMD.order_le
  have hleftBC' : b + c = left.index.val.m +
      2 * left.index.val.innerBC.order := by
    have horder := Nat.le_min.mp left.index.val.innerBC.order_le
    omega
  have hrightBC' : b + c = right.index.val.m +
      2 * right.index.val.innerBC.order := by
    have horder := Nat.le_min.mp right.index.val.innerBC.order_le
    omega
  have hleftMD' : left.index.val.m + d = left.index.val.n +
      2 * left.index.val.innerMD.order := by
    have horder := Nat.le_min.mp left.index.val.innerMD.order_le
    omega
  have hrightMD' : right.index.val.m + d = right.index.val.n +
      2 * right.index.val.innerMD.order := by
    have horder := Nat.le_min.mp right.index.val.innerMD.order_le
    omega
  have hleftIntermediate : left.index.val.n + e =
      left.value.intermediate + 2 * left.value.p := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hrightIntermediate : right.index.val.n + e =
      right.value.intermediate + 2 * right.value.p := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hleftFinal : a + left.value.intermediate =
      f + 2 * left.value.r := by
    omega
  have hrightFinal : a + right.value.intermediate =
      f + 2 * right.value.r := by
    omega
  obtain ⟨hm, hn, hp⟩ := sparseSixChain_unique
    a b c d e f ha hb hc hd he hf hsum
    left.index.val.m left.index.val.innerBC.order
    left.index.val.n left.index.val.innerMD.order
    left.value.intermediate left.value.p left.value.r
    right.index.val.m right.index.val.innerBC.order
    right.index.val.n right.index.val.innerMD.order
    right.value.intermediate right.value.p right.value.r
    hleftBC' hrightBC' hleftMD' hrightMD'
    hleftIntermediate hrightIntermediate hleftFinal hrightFinal
    hleftBCBound.1 hleftBCBound.2 hrightBCBound.1 hrightBCBound.2
    hleftMDBound.2 hrightMDBound.2
    hleftP.2 hrightP.2
    hleftR.1 hrightR.1
  rcases left with ⟨leftIndex, leftValue⟩
  rcases right with ⟨rightIndex, rightValue⟩
  dsimp only at hm hn hp
  have hpair : leftIndex.val = rightIndex.val :=
    valenceSixInnerPair_eq_of_m_n leftIndex.val rightIndex.val hm hn
  have hindex : leftIndex = rightIndex := Subtype.ext hpair
  subst rightIndex
  have hvalue : leftValue = rightValue :=
    fixedRightChannel_eq_of_p_eq leftValue rightValue hp
  subst rightValue
  rfl

theorem valenceSixRightCarriers_nodup (a b c d e f : Nat) :
    (valenceSixCanonicalThirdBistochasticKernel a b c d e f).targets.Nodup :=
  indexedTargets_nodup
    (valenceSixInnerPairs b c d)
    (valenceSixInnerPairs_nodup b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    (fun pair => fixedRightChannels_nodup a pair.n e f)

theorem valenceSixRightCarriers_complete
    {a b c d e f : Nat}
    (target : ValenceSixRightCarrier a b c d e f) :
    target ∈
      (valenceSixCanonicalThirdBistochasticKernel a b c d e f).targets :=
  indexedTargets_complete
    (valenceSixInnerPairs b c d)
    (ValenceSixThirdLeftFamily a e f)
    (ValenceSixThirdRightFamily a e f)
    (fun pair => physicalSchurBistochasticKernel a pair.n e f)
    (fun _pair right => fixedRightChannels_complete right)
    target

theorem sparseValenceSixRightCarriers_eq_singleton
    (a b c d e f : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hsum : a + b + c + d + e + f = 2)
    (target : ValenceSixRightCarrier a b c d e f) :
    (valenceSixCanonicalThirdBistochasticKernel a b c d e f).targets =
      [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (valenceSixRightCarriers_nodup a b c d e f)
    (valenceSixRightCarriers_complete target)
    (fun entry => sparseValenceSixRightCarrier_unique
      a b c d e f ha hb hc hd he hf hsum entry target)

theorem sparseValenceSixKernel_eqv_one
    (a b c d e f : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hsum : a + b + c + d + e + f = 2)
    (source : ValenceSixLeftCarrier a b c d e f)
    (target : ValenceSixRightCarrier a b c d e f) :
    (valenceSixBistochasticKernel a b c d e f).weight source target ≈ 1 := by
  have h := (valenceSixBistochasticKernel a b c d e f).row_normalized source
  change listQSum
      ((valenceSixBistochasticKernel a b c d e f).weight source)
      (valenceSixCanonicalThirdBistochasticKernel a b c d e f).targets ≈ 1
    at h
  rw [sparseValenceSixRightCarriers_eq_singleton
    a b c d e f ha hb hc hd he hf hsum target] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem sparseValenceSixKernel_pos
    (a b c d e f : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hsum : a + b + c + d + e + f = 2)
    (source : ValenceSixLeftCarrier a b c d e f)
    (target : ValenceSixRightCarrier a b c d e f) :
    (0 : Q') <
      (valenceSixBistochasticKernel a b c d e f).weight source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (sparseValenceSixKernel_eqv_one
        a b c d e f ha hb hc hd he hf hsum source target))

/-! ## 4. The valence-six vacuum and even-sparse union -/

theorem zeroValenceSixRightCarrier_unique
    (left right : ValenceSixRightCarrier 0 0 0 0 0 0) :
    left = right := by
  have hleftBC := left.index.val.innerBC.output_eq
  have hrightBC := right.index.val.innerBC.output_eq
  have hleftMD := left.index.val.innerMD.output_eq
  have hrightMD := right.index.val.innerMD.output_eq
  have hleftP := Nat.le_min.mp left.value.p_le
  have hrightP := Nat.le_min.mp right.value.p_le
  have hleftR := Nat.le_min.mp left.value.r_le
  have hrightR := Nat.le_min.mp right.value.r_le
  have hleftDegree := left.value.degree_eq
  have hrightDegree := right.value.degree_eq
  have hm : left.index.val.m = right.index.val.m := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  have hn : left.index.val.n = right.index.val.n := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  have hp : left.value.p = right.value.p := by
    unfold FixedRightCGChannel.intermediate at *
    omega
  rcases left with ⟨leftIndex, leftValue⟩
  rcases right with ⟨rightIndex, rightValue⟩
  dsimp only at hm hn hp
  have hpair : leftIndex.val = rightIndex.val :=
    valenceSixInnerPair_eq_of_m_n leftIndex.val rightIndex.val hm hn
  have hindex : leftIndex = rightIndex := Subtype.ext hpair
  subst rightIndex
  have hvalue : leftValue = rightValue :=
    fixedRightChannel_eq_of_p_eq leftValue rightValue hp
  subst rightValue
  rfl

theorem zeroValenceSixRightCarriers_eq_singleton
    (target : ValenceSixRightCarrier 0 0 0 0 0 0) :
    (valenceSixCanonicalThirdBistochasticKernel 0 0 0 0 0 0).targets =
      [target] :=
  singleton_of_nodup_of_mem_of_unique _ target
    (valenceSixRightCarriers_nodup 0 0 0 0 0 0)
    (valenceSixRightCarriers_complete target)
    (fun entry => zeroValenceSixRightCarrier_unique entry target)

theorem zeroValenceSixKernel_eqv_one
    (source : ValenceSixLeftCarrier 0 0 0 0 0 0)
    (target : ValenceSixRightCarrier 0 0 0 0 0 0) :
    (valenceSixBistochasticKernel 0 0 0 0 0 0).weight source target ≈ 1 := by
  have h := (valenceSixBistochasticKernel 0 0 0 0 0 0).row_normalized source
  change listQSum
      ((valenceSixBistochasticKernel 0 0 0 0 0 0).weight source)
      (valenceSixCanonicalThirdBistochasticKernel 0 0 0 0 0 0).targets ≈ 1
    at h
  rw [zeroValenceSixRightCarriers_eq_singleton target] at h
  simpa only [listQSum, Q'.add_zero'] using h

theorem evenSparseValenceSixKernel_eqv_one
    (a b c d e f : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hevenSparse : a + b + c + d + e + f = 0 ∨
      a + b + c + d + e + f = 2)
    (source : ValenceSixLeftCarrier a b c d e f)
    (target : ValenceSixRightCarrier a b c d e f) :
    (valenceSixBistochasticKernel a b c d e f).weight source target ≈ 1 := by
  rcases hevenSparse with hzero | htwo
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    have he0 : e = 0 := by omega
    have hf0 : f = 0 := by omega
    subst a
    subst b
    subst c
    subst d
    subst e
    subst f
    exact zeroValenceSixKernel_eqv_one source target
  · exact sparseValenceSixKernel_eqv_one
      a b c d e f ha hb hc hd he hf htwo source target

end YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel

#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparsePhysicalSchurRightCarrier_unique
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparsePhysicalSchurKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.evenSparsePhysicalSchurKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceFiveRightCarrier_unique
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceFiveRightCarriers_eq_singleton
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceFiveKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceFiveKernel_pos
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.zeroValenceFiveKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.evenSparseValenceFiveKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceSixRightCarrier_unique
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceSixRightCarriers_eq_singleton
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceSixKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.sparseValenceSixKernel_pos
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.zeroValenceSixKernel_eqv_one
#print axioms YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel.evenSparseValenceSixKernel_eqv_one
