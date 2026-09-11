/-
# Constructive mixed-radix codec for fixed-incidence channels

The symbolic fixed-incidence carrier is intentionally never evaluated: even
at the smallest production cutoff it is enormous.  Nevertheless, the next
trajectory-gluing step needs a *canonical* natural-number coordinate for each
bounded channel field, not merely an existential position in a list of
functions.

This file supplies that coordinate by a least-significant-digit-first
mixed-radix codec.  For base `cutoff + 1`, the head key stores `index % base`
and the remaining keys store `index / base`.  The inverse reads the same keys
recursively.  All proofs are structural; in particular there is no choice,
no search through a function-valued list, and no `DecidableEq (A → Nat)`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceMixedRadixCodec

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge

/-! ## 1. Generic finite-list mixed-radix codec -/

/-- The number of base-`cutoff + 1` words carried by `keys`. -/
def boundedLabellingMixedRadixCount
    {A : Type} (cutoff : Nat) (keys : List A) : Nat :=
  (cutoff + 1) ^ keys.length

/-- Decode a natural number into a channel field supported on `keys`.
The head key is the least significant digit. -/
def boundedLabellingMixedRadixDecode
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    List A → Nat → A → Nat
  | [], _ => zeroLabellingOn
  | head :: rest, index =>
      setLabelOn
        (boundedLabellingMixedRadixDecode cutoff rest
          (index / (cutoff + 1)))
        head (index % (cutoff + 1))

/-- Read the digits on `keys` as a natural number.  Values away from `keys`
are ignored. -/
def boundedLabellingMixedRadixEncode
    {A : Type} (cutoff : Nat) :
    List A → (A → Nat) → Nat
  | [], _ => 0
  | head :: rest, label =>
      (cutoff + 1) *
          boundedLabellingMixedRadixEncode cutoff rest label +
        label head

@[simp] theorem boundedLabellingMixedRadixCount_nil
    {A : Type} (cutoff : Nat) :
    boundedLabellingMixedRadixCount (A := A) cutoff [] = 1 := by
  simp [boundedLabellingMixedRadixCount]

@[simp] theorem boundedLabellingMixedRadixCount_cons
    {A : Type} (cutoff : Nat) (head : A) (rest : List A) :
    boundedLabellingMixedRadixCount cutoff (head :: rest) =
      (cutoff + 1) * boundedLabellingMixedRadixCount cutoff rest := by
  simp [boundedLabellingMixedRadixCount, Nat.pow_succ, Nat.mul_comm]

theorem boundedLabellingMixedRadixCount_pos
    {A : Type} (cutoff : Nat) (keys : List A) :
    0 < boundedLabellingMixedRadixCount cutoff keys := by
  exact Nat.pow_pos (by omega)

/-- Every decoded digit is in the channel window on the listed keys. -/
theorem boundedLabellingMixedRadixDecode_le
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (index : Nat) (key : A),
      key ∈ keys →
      boundedLabellingMixedRadixDecode cutoff keys index key ≤ cutoff
  | [], _, key, hkey => False.elim (List.not_mem_nil hkey)
  | head :: rest, index, key, hkey => by
      simp only [boundedLabellingMixedRadixDecode]
      by_cases hsame : key = head
      · subst key
        simp only [setLabelOn, ↓reduceIte]
        have hmod : index % (cutoff + 1) < cutoff + 1 :=
          Nat.mod_lt index (by omega)
        omega
      · rw [show setLabelOn
            (boundedLabellingMixedRadixDecode cutoff rest
              (index / (cutoff + 1)))
            head (index % (cutoff + 1)) key =
            boundedLabellingMixedRadixDecode cutoff rest
              (index / (cutoff + 1)) key by
          simp [setLabelOn, hsame]]
        apply boundedLabellingMixedRadixDecode_le cutoff rest
        rcases List.mem_cons.mp hkey with heq | hrest
        · exact False.elim (hsame heq)
        · exact hrest

/-- Decoding is definitionally zero away from the finite key list. -/
theorem boundedLabellingMixedRadixDecode_eq_zero_of_not_mem
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (index : Nat) (key : A),
      key ∉ keys →
      boundedLabellingMixedRadixDecode cutoff keys index key = 0
  | [], _, key, _ => rfl
  | head :: rest, index, key, hkey => by
      have hne : key ≠ head := by
        intro heq
        exact hkey (heq ▸ List.mem_cons_self)
      have hrest : key ∉ rest := by
        intro hmem
        exact hkey (List.mem_cons_of_mem head hmem)
      simp only [boundedLabellingMixedRadixDecode]
      rw [show setLabelOn
            (boundedLabellingMixedRadixDecode cutoff rest
              (index / (cutoff + 1)))
            head (index % (cutoff + 1)) key =
            boundedLabellingMixedRadixDecode cutoff rest
              (index / (cutoff + 1)) key by
        simp [setLabelOn, hne]]
      exact boundedLabellingMixedRadixDecode_eq_zero_of_not_mem
        cutoff rest (index / (cutoff + 1)) key hrest

/-- Encoding depends only on values at the listed keys. -/
theorem boundedLabellingMixedRadixEncode_congr_on
    {A : Type} (cutoff : Nat) :
    ∀ (keys : List A) (left right : A → Nat),
      (∀ key, key ∈ keys → left key = right key) →
      boundedLabellingMixedRadixEncode cutoff keys left =
        boundedLabellingMixedRadixEncode cutoff keys right
  | [], _, _, _ => rfl
  | head :: rest, left, right, heq => by
      simp only [boundedLabellingMixedRadixEncode]
      rw [heq head List.mem_cons_self]
      rw [boundedLabellingMixedRadixEncode_congr_on cutoff rest left right]
      intro key hkey
      exact heq key (List.mem_cons_of_mem head hkey)

/-- A bounded word encodes below the exact mixed-radix count. -/
theorem boundedLabellingMixedRadixEncode_lt_count
    {A : Type} (cutoff : Nat) :
    ∀ (keys : List A) (label : A → Nat),
      (∀ key, key ∈ keys → label key ≤ cutoff) →
      boundedLabellingMixedRadixEncode cutoff keys label <
        boundedLabellingMixedRadixCount cutoff keys
  | [], _, _ => by
      simp [boundedLabellingMixedRadixEncode,
        boundedLabellingMixedRadixCount]
  | head :: rest, label, hbounded => by
      let base := cutoff + 1
      let tailIndex :=
        boundedLabellingMixedRadixEncode cutoff rest label
      have hdigit : label head < base := by
        exact Nat.lt_succ_iff.mpr
          (hbounded head List.mem_cons_self)
      have htail : tailIndex <
          boundedLabellingMixedRadixCount cutoff rest := by
        exact boundedLabellingMixedRadixEncode_lt_count
          cutoff rest label
          (fun key hkey =>
            hbounded key (List.mem_cons_of_mem head hkey))
      have htailSucc : tailIndex + 1 ≤
          boundedLabellingMixedRadixCount cutoff rest := by
        omega
      have hmul := Nat.mul_le_mul_left base htailSucc
      change base * tailIndex + label head <
        boundedLabellingMixedRadixCount cutoff (head :: rest)
      calc
        base * tailIndex + label head <
            base * tailIndex + base :=
          Nat.add_lt_add_left hdigit (base * tailIndex)
        _ = base * (tailIndex + 1) := by
          simp only [Nat.mul_add, Nat.mul_one]
        _ ≤ base * boundedLabellingMixedRadixCount cutoff rest := hmul
        _ = boundedLabellingMixedRadixCount cutoff (head :: rest) := by
          rw [boundedLabellingMixedRadixCount_cons]

/-- On a noduplicated key list, decoding the explicit encoding recovers every
listed value.  No support hypothesis is needed for this pointwise statement. -/
theorem boundedLabellingMixedRadixDecode_encode_apply_of_mem
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (label : A → Nat),
      keys.Nodup →
      (∀ key, key ∈ keys → label key ≤ cutoff) →
      ∀ key, key ∈ keys →
        boundedLabellingMixedRadixDecode cutoff keys
            (boundedLabellingMixedRadixEncode cutoff keys label) key =
          label key
  | [], _, _, _, key, hkey => False.elim (List.not_mem_nil hkey)
  | head :: rest, label, hnodup, hbounded, key, hkey => by
      have hparts := List.nodup_cons.mp hnodup
      let base := cutoff + 1
      let tailIndex :=
        boundedLabellingMixedRadixEncode cutoff rest label
      have hbase : 0 < base := by omega
      have hdigit : label head < base := by
        exact Nat.lt_succ_iff.mpr
          (hbounded head List.mem_cons_self)
      have hdiv : (base * tailIndex + label head) / base =
          tailIndex := by
        rw [Nat.mul_add_div hbase, Nat.div_eq_of_lt hdigit]
        omega
      have hmod : (base * tailIndex + label head) % base =
          label head := by
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hdigit
      simp only [boundedLabellingMixedRadixEncode,
        boundedLabellingMixedRadixDecode]
      change setLabelOn
          (boundedLabellingMixedRadixDecode cutoff rest
            ((base * tailIndex + label head) / base))
          head ((base * tailIndex + label head) % base) key = label key
      rw [hdiv, hmod]
      by_cases hsame : key = head
      · subst key
        simp [setLabelOn]
      · rw [show setLabelOn
              (boundedLabellingMixedRadixDecode cutoff rest tailIndex)
              head (label head) key =
              boundedLabellingMixedRadixDecode cutoff rest tailIndex key by
            simp [setLabelOn, hsame]]
        apply boundedLabellingMixedRadixDecode_encode_apply_of_mem
          cutoff rest label hparts.2
        · intro item hitem
          exact hbounded item (List.mem_cons_of_mem head hitem)
        · rcases List.mem_cons.mp hkey with heq | hrest
          · exact False.elim (hsame heq)
          · exact hrest

/-- Full decoder-after-encoder identity for bounded, zero-supported fields. -/
theorem boundedLabellingMixedRadixDecode_encode
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) (label : A → Nat)
    (hnodup : keys.Nodup)
    (hbounded : ∀ key, key ∈ keys → label key ≤ cutoff)
    (hsupported : ∀ key, key ∉ keys → label key = 0) :
    boundedLabellingMixedRadixDecode cutoff keys
        (boundedLabellingMixedRadixEncode cutoff keys label) = label := by
  funext key
  by_cases hkey : key ∈ keys
  · exact boundedLabellingMixedRadixDecode_encode_apply_of_mem
      cutoff keys label hnodup hbounded key hkey
  · rw [boundedLabellingMixedRadixDecode_eq_zero_of_not_mem
      cutoff keys
      (boundedLabellingMixedRadixEncode cutoff keys label) key hkey]
    exact (hsupported key hkey).symm

private theorem nat_div_lt_of_lt_mul_left
    (index base count : Nat)
    (hindex : index < base * count) :
    index / base < count := by
  by_cases hresult : index / base < count
  · exact hresult
  · have hcount : count ≤ index / base := Nat.le_of_not_gt hresult
    have hmul : base * count ≤ base * (index / base) :=
      Nat.mul_le_mul_left base hcount
    have hdecomp : base * (index / base) + index % base = index :=
      Nat.div_add_mod index base
    omega

/-- Encoding a decoded in-range word returns the original index. -/
theorem boundedLabellingMixedRadixEncode_decode
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (index : Nat),
      keys.Nodup →
      index < boundedLabellingMixedRadixCount cutoff keys →
      boundedLabellingMixedRadixEncode cutoff keys
          (boundedLabellingMixedRadixDecode cutoff keys index) = index
  | [], index, _, hindex => by
      have hzero : index = 0 := by
        simpa [boundedLabellingMixedRadixCount] using hindex
      subst index
      rfl
  | head :: rest, index, hnodup, hindex => by
      have hparts := List.nodup_cons.mp hnodup
      let base := cutoff + 1
      have hcount : boundedLabellingMixedRadixCount cutoff (head :: rest) =
          base * boundedLabellingMixedRadixCount cutoff rest := by
        exact boundedLabellingMixedRadixCount_cons cutoff head rest
      have hquotient : index / base <
          boundedLabellingMixedRadixCount cutoff rest := by
        apply nat_div_lt_of_lt_mul_left index base
          (boundedLabellingMixedRadixCount cutoff rest)
        rw [← hcount]
        exact hindex
      have htail := boundedLabellingMixedRadixEncode_decode
        cutoff rest (index / base) hparts.2 hquotient
      have htailEncode :
          boundedLabellingMixedRadixEncode cutoff rest
              (setLabelOn
                (boundedLabellingMixedRadixDecode cutoff rest
                  (index / base))
                head (index % base)) =
            boundedLabellingMixedRadixEncode cutoff rest
              (boundedLabellingMixedRadixDecode cutoff rest
                (index / base)) := by
        apply boundedLabellingMixedRadixEncode_congr_on
        intro key hkey
        have hne : key ≠ head := by
          intro heq
          exact hparts.1 (heq ▸ hkey)
        simp [setLabelOn, hne]
      simp only [boundedLabellingMixedRadixDecode,
        boundedLabellingMixedRadixEncode]
      change base *
          boundedLabellingMixedRadixEncode cutoff rest
            (setLabelOn
              (boundedLabellingMixedRadixDecode cutoff rest
                (index / base))
              head (index % base)) +
          setLabelOn
            (boundedLabellingMixedRadixDecode cutoff rest
              (index / base))
            head (index % base) head = index
      rw [htailEncode, htail]
      simp only [setLabelOn, ↓reduceIte]
      exact Nat.div_add_mod index base

/-- The decoder is injective on its exact finite range.  This is the key
reindexing fact for later `finSum` arguments. -/
theorem boundedLabellingMixedRadixDecode_injective_on_range
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) (hnodup : keys.Nodup)
    {left right : Nat}
    (hleft : left < boundedLabellingMixedRadixCount cutoff keys)
    (hright : right < boundedLabellingMixedRadixCount cutoff keys)
    (heq : boundedLabellingMixedRadixDecode cutoff keys left =
      boundedLabellingMixedRadixDecode cutoff keys right) :
    left = right := by
  calc
    left = boundedLabellingMixedRadixEncode cutoff keys
        (boundedLabellingMixedRadixDecode cutoff keys left) :=
      (boundedLabellingMixedRadixEncode_decode
        cutoff keys left hnodup hleft).symm
    _ = boundedLabellingMixedRadixEncode cutoff keys
        (boundedLabellingMixedRadixDecode cutoff keys right) := by
      rw [heq]
    _ = right := boundedLabellingMixedRadixEncode_decode
      cutoff keys right hnodup hright

/-! ## 2. Canonical finite carrier and completeness -/

/-- The recursive legacy carrier is zero-supported.  This structural fact is
the missing converse companion to `boundedLabellingsOn_sound`. -/
theorem boundedLabellingsOn_eq_zero_of_not_mem
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ (keys : List A) (label : A → Nat),
      label ∈ boundedLabellingsOn cutoff keys →
      ∀ key, key ∉ keys → label key = 0
  | [], label, hlabel, key, _ => by
      have heq : label = (zeroLabellingOn : A → Nat) := by
        simpa [boundedLabellingsOn] using hlabel
      rw [heq]
      rfl
  | head :: rest, label, hlabel, key, hkey => by
      obtain ⟨selected, _, hselectedBlock⟩ :=
        List.mem_flatMap.mp hlabel
      obtain ⟨tailLabel, htailLabel, heq⟩ :=
        List.mem_map.mp hselectedBlock
      rw [← heq]
      have hne : key ≠ head := by
        intro hsame
        exact hkey (hsame ▸ List.mem_cons_self)
      have hrest : key ∉ rest := by
        intro hmem
        exact hkey (List.mem_cons_of_mem head hmem)
      rw [show setLabelOn tailLabel head selected key = tailLabel key by
        simp [setLabelOn, hne]]
      exact boundedLabellingsOn_eq_zero_of_not_mem
        cutoff rest tailLabel htailLabel key hrest

/-- The legacy recursive list and the canonical codec have the same exact
symbolic cardinality.  The proof does not evaluate either carrier. -/
private theorem list_sum_map_const_nat
    {A : Type} (value : Nat) : ∀ items : List A,
    (items.map (fun _ => value)).sum = items.length * value
  | [] => by simp
  | _ :: rest => by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [list_sum_map_const_nat value rest, Nat.succ_mul]
      exact Nat.add_comm value (rest.length * value)

theorem boundedLabellingsOn_length_eq_mixedRadixCount
    {A : Type} [DecidableEq A] (cutoff : Nat) :
    ∀ keys : List A,
      (boundedLabellingsOn cutoff keys).length =
        boundedLabellingMixedRadixCount cutoff keys
  | [] => by
      simp [boundedLabellingsOn,
        boundedLabellingMixedRadixCount]
  | head :: rest => by
      simp [boundedLabellingsOn,
        boundedLabellingsOn_length_eq_mixedRadixCount cutoff rest,
        boundedLabellingMixedRadixCount, Nat.pow_succ, Nat.mul_comm]
      rw [list_sum_map_const_nat]
      simp

/-- The canonical carrier, listed by its mixed-radix coordinates. -/
def boundedLabellingMixedRadixCarrier
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) : List (A → Nat) :=
  (List.range (boundedLabellingMixedRadixCount cutoff keys)).map
    (boundedLabellingMixedRadixDecode cutoff keys)

theorem boundedLabellingMixedRadixCarrier_length
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) :
    (boundedLabellingMixedRadixCarrier cutoff keys).length =
      boundedLabellingMixedRadixCount cutoff keys := by
  simp [boundedLabellingMixedRadixCarrier]

/-- Every bounded zero-supported labelling has the explicit coordinate
returned by `boundedLabellingMixedRadixEncode`. -/
theorem boundedLabellingMixedRadix_complete_supported
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) (label : A → Nat)
    (hnodup : keys.Nodup)
    (hbounded : ∀ key, key ∈ keys → label key ≤ cutoff)
    (hsupported : ∀ key, key ∉ keys → label key = 0) :
    boundedLabellingMixedRadixEncode cutoff keys label <
        boundedLabellingMixedRadixCount cutoff keys ∧
      boundedLabellingMixedRadixDecode cutoff keys
          (boundedLabellingMixedRadixEncode cutoff keys label) = label := by
  exact ⟨boundedLabellingMixedRadixEncode_lt_count
      cutoff keys label hbounded,
    boundedLabellingMixedRadixDecode_encode
      cutoff keys label hnodup hbounded hsupported⟩

theorem boundedLabellingMixedRadix_complete_mem
    {A : Type} [DecidableEq A]
    (cutoff : Nat) (keys : List A) (label : A → Nat)
    (hnodup : keys.Nodup)
    (hbounded : ∀ key, key ∈ keys → label key ≤ cutoff)
    (hsupported : ∀ key, key ∉ keys → label key = 0) :
    label ∈ boundedLabellingMixedRadixCarrier cutoff keys := by
  have hcomplete := boundedLabellingMixedRadix_complete_supported
    cutoff keys label hnodup hbounded hsupported
  apply List.mem_map.mpr
  refine ⟨boundedLabellingMixedRadixEncode cutoff keys label,
    List.mem_range.mpr hcomplete.1, ?_⟩
  exact hcomplete.2

/-! ## 3. Fixed-incidence specialization -/

/-- Exact canonical middle dimension for fixed-incidence channel fields. -/
def adjacentEvenFixedIncidenceMixedRadixMiddleCount
    (K radius : Nat) : Nat :=
  boundedLabellingMixedRadixCount (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)

/-- Canonical channel assignment at a mixed-radix middle coordinate. -/
def adjacentEvenFixedIncidenceMixedRadixAssignmentAt
    (K radius middle : Nat) : FixedFaceLinkIncidence → Nat :=
  boundedLabellingMixedRadixDecode (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius) middle

/-- The explicit mixed-radix coordinate of a fixed-incidence assignment. -/
def adjacentEvenFixedIncidenceMixedRadixIndex
    (K radius : Nat) (assignment : FixedFaceLinkIncidence → Nat) : Nat :=
  boundedLabellingMixedRadixEncode (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius) assignment

/-- Face-field form of the canonical decoded assignment, zero-extended away
from the literal physical incidence set. -/
def adjacentEvenFixedIncidenceMixedRadixMiddleField
    (K radius middle : Nat) : FixedFaceChannelField :=
  adjacentEvenFixedIncidenceAssignmentField radius
    (adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius middle)

/-- The explicit and legacy symbolic carriers have the same middle
dimension, so adopting canonical coordinates does not change a Gram rank. -/
theorem adjacentEvenFixedIncidenceMiddleCount_eq_mixedRadix
    (K radius : Nat) :
    adjacentEvenFixedIncidenceMiddleCount K radius =
      adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius := by
  exact boundedLabellingsOn_length_eq_mixedRadixCount
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)

theorem adjacentEvenFixedIncidenceMixedRadixMiddleCount_pos
    (K radius : Nat) :
    0 < adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius := by
  exact boundedLabellingMixedRadixCount_pos
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)

theorem adjacentEvenFixedIncidenceMixedRadixAssignmentAt_le
    (K radius middle : Nat) (incidence : FixedFaceLinkIncidence)
    (hincidence : incidence ∈
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenFixedIncidenceMixedRadixAssignmentAt
        K radius middle incidence ≤ linkAuxiliaryCutoff K := by
  exact boundedLabellingMixedRadixDecode_le
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)
    middle incidence hincidence

theorem adjacentEvenFixedIncidenceMixedRadixAssignmentAt_eq_zero_of_not_mem
    (K radius middle : Nat) (incidence : FixedFaceLinkIncidence)
    (hincidence : incidence ∉
      adjacentEvenFixedFaceMajorIncidences radius) :
    adjacentEvenFixedIncidenceMixedRadixAssignmentAt
        K radius middle incidence = 0 := by
  exact boundedLabellingMixedRadixDecode_eq_zero_of_not_mem
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)
    middle incidence hincidence

theorem adjacentEvenFixedIncidenceMixedRadixMiddleField_le
    (K radius middle id : Nat) (link : Z4Link) :
    adjacentEvenFixedIncidenceMixedRadixMiddleField
        K radius middle id link ≤ linkAuxiliaryCutoff K := by
  unfold adjacentEvenFixedIncidenceMixedRadixMiddleField
  by_cases hincidence : (id, link) ∈
      adjacentEvenFixedFaceMajorIncidences radius
  · rw [adjacentEvenFixedIncidenceAssignmentField_of_mem
      radius
      (adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius middle)
      hincidence]
    exact adjacentEvenFixedIncidenceMixedRadixAssignmentAt_le
      K radius middle (id, link) hincidence
  · rw [adjacentEvenFixedIncidenceAssignmentField_of_not_mem
      radius
      (adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius middle)
      hincidence]
    exact Nat.zero_le _

/-- Explicit fixed-incidence realization: the codec itself supplies the
middle index, its bound, and exact recovery of the whole supported field. -/
theorem adjacentEvenFixedIncidenceMixedRadix_realized
    (K radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    (hbounded : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence ≤ linkAuxiliaryCutoff K)
    (hsupported : ∀ incidence,
      incidence ∉ adjacentEvenFixedFaceMajorIncidences radius →
        assignment incidence = 0) :
    adjacentEvenFixedIncidenceMixedRadixIndex K radius assignment <
        adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius ∧
      adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius
          (adjacentEvenFixedIncidenceMixedRadixIndex K radius assignment) =
        assignment := by
  exact boundedLabellingMixedRadix_complete_supported
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)
    assignment
    (adjacentEvenFixedFaceMajorIncidences_nodup radius)
    hbounded hsupported

/-- Every item of the pre-existing symbolic assignment list has its explicit
mixed-radix coordinate.  This is the bridge needed to replace existential
`getD` witnesses inside finite sums. -/
theorem adjacentEvenFixedIncidenceChannelAssignment_mixedRadix_realized
    (K radius : Nat) (assignment : FixedFaceLinkIncidence → Nat)
    (hassignment : assignment ∈
      adjacentEvenFixedIncidenceChannelAssignments K radius) :
    adjacentEvenFixedIncidenceMixedRadixIndex K radius assignment <
        adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius ∧
      adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius
          (adjacentEvenFixedIncidenceMixedRadixIndex K radius assignment) =
        assignment := by
  apply adjacentEvenFixedIncidenceMixedRadix_realized
  · intro incidence hincidence
    exact boundedLabellingsOn_sound
      (linkAuxiliaryCutoff K)
      (adjacentEvenFixedFaceMajorIncidences radius)
      assignment hassignment incidence hincidence
  · intro incidence hincidence
    exact boundedLabellingsOn_eq_zero_of_not_mem
      (linkAuxiliaryCutoff K)
      (adjacentEvenFixedFaceMajorIncidences radius)
      assignment hassignment incidence hincidence

/-- The canonical assignment decoder is injective on the exact middle range,
so finite sums over this range have no duplicate channel fields. -/
theorem adjacentEvenFixedIncidenceMixedRadixAssignmentAt_injective
    (K radius : Nat) {left right : Nat}
    (hleft : left <
      adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius)
    (hright : right <
      adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius)
    (heq : adjacentEvenFixedIncidenceMixedRadixAssignmentAt
        K radius left =
      adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius right) :
    left = right := by
  exact boundedLabellingMixedRadixDecode_injective_on_range
    (linkAuxiliaryCutoff K)
    (adjacentEvenFixedFaceMajorIncidences radius)
    (adjacentEvenFixedFaceMajorIncidences_nodup radius)
    hleft hright heq

/-! ## 4. Explicit trajectory coordinates -/

def adjacentEvenTrajectoryOutgoingMixedRadixIndex
    (K radius : Nat) (trajectory : FixedIncidenceTrajectoryState) : Nat :=
  adjacentEvenFixedIncidenceMixedRadixIndex K radius
    (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)

def adjacentEvenTrajectoryIncomingMixedRadixIndex
    (K radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Nat :=
  adjacentEvenFixedIncidenceMixedRadixIndex K radius
    (adjacentEvenTrajectoryIncomingIncidenceAssignment
      radius source trajectory)

theorem adjacentEvenTrajectoryOutgoingMixedRadix_realized
    {K radius : Nat} {trajectory : FixedIncidenceTrajectoryState}
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    adjacentEvenTrajectoryOutgoingMixedRadixIndex K radius trajectory <
        adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius ∧
      adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius
          (adjacentEvenTrajectoryOutgoingMixedRadixIndex
            K radius trajectory) =
        adjacentEvenTrajectoryOutgoingIncidenceAssignment
          radius trajectory := by
  exact adjacentEvenFixedIncidenceMixedRadix_realized
    K radius
    (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)
    (adjacentEvenTrajectoryOutgoingIncidenceAssignment_le htrajectory)
    (fun incidence hincidence => by
      simp [adjacentEvenTrajectoryOutgoingIncidenceAssignment, hincidence])

theorem adjacentEvenTrajectoryIncomingMixedRadix_realized
    {K radius : Nat} {source : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    adjacentEvenTrajectoryIncomingMixedRadixIndex
        K radius source trajectory <
        adjacentEvenFixedIncidenceMixedRadixMiddleCount K radius ∧
      adjacentEvenFixedIncidenceMixedRadixAssignmentAt K radius
          (adjacentEvenTrajectoryIncomingMixedRadixIndex
            K radius source trajectory) =
        adjacentEvenTrajectoryIncomingIncidenceAssignment
          radius source trajectory := by
  exact adjacentEvenFixedIncidenceMixedRadix_realized
    K radius
    (adjacentEvenTrajectoryIncomingIncidenceAssignment
      radius source trajectory)
    (adjacentEvenTrajectoryIncomingIncidenceAssignment_le
      hsource htrajectory)
    (fun incidence hincidence => by
      simp [adjacentEvenTrajectoryIncomingIncidenceAssignment, hincidence])

#print axioms boundedLabellingMixedRadixDecode_le
#print axioms boundedLabellingMixedRadixDecode_eq_zero_of_not_mem
#print axioms boundedLabellingMixedRadixEncode_lt_count
#print axioms boundedLabellingMixedRadixDecode_encode
#print axioms boundedLabellingMixedRadixEncode_decode
#print axioms boundedLabellingMixedRadixDecode_injective_on_range
#print axioms boundedLabellingsOn_eq_zero_of_not_mem
#print axioms boundedLabellingsOn_length_eq_mixedRadixCount
#print axioms boundedLabellingMixedRadix_complete_supported
#print axioms adjacentEvenFixedIncidenceMiddleCount_eq_mixedRadix
#print axioms adjacentEvenFixedIncidenceMixedRadix_realized
#print axioms adjacentEvenFixedIncidenceChannelAssignment_mixedRadix_realized
#print axioms adjacentEvenFixedIncidenceMixedRadixAssignmentAt_injective
#print axioms adjacentEvenTrajectoryOutgoingMixedRadix_realized
#print axioms adjacentEvenTrajectoryIncomingMixedRadix_realized

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceMixedRadixCodec
