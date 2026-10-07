/-
# Finite alternating square and mixed half-diamond

This file records the explicit finite index geometry for the alternating
half-shift square. It does not identify infinite sums or pay omitted shells.
-/

import YMGap.Continuum.ThetaParityConvolution

namespace YMGap.Continuum.ThetaAlternatingHalfDiamond

set_option autoImplicit false

open YMGap.Continuum.ThetaParityConvolution
open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_map)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem natAbs_eq_toNat (z : Int) (hz : 0 ≤ z) :
    z.natAbs = z.toNat := by
  have h : (z.natAbs : Int) = (z.toNat : Int) :=
    (Int.natAbs_of_nonneg hz).trans (Int.toNat_of_nonneg hz).symm
  exact_mod_cast h

/-- An index in the mixed half-diamond. -/
abbrev MixedIndex := Nat × Int

/-- The nonnegative square of side `N+1`. -/
def positiveSquareIndices (N : Nat) : List (Nat × Nat) :=
  cartesian (List.range (N+1)) (List.range (N+1))

/-- Mixed indices, filtered by the exact half-diamond condition. -/
def halfDiamondIndices (N : Nat) : List MixedIndex :=
  (cartesian (List.range (N+1)) (signedIndices N)).filter
    (fun p => decide (p.1 + p.2.natAbs ≤ N))

/-- Explicit map from the mixed half-diamond to the nonnegative square. -/
def encodeMixed (p : MixedIndex) : Nat × Nat :=
  let h := p.1
  let k := p.2
  if hk : k.natAbs ≤ h then
    (((h : Int) + k).toNat, ((h : Int) - k).toNat)
  else if hk : 0 ≤ k then
    (h + k.natAbs, k.natAbs - h - 1)
  else
    (k.natAbs - h - 1, h + k.natAbs)

/-- Parity decoder followed by the explicit even/odd inverse into the mixed
half-diamond coordinates. -/
def decodeMixed (p : Nat × Nat) : MixedIndex :=
  match decode (Int.ofNat p.1, Int.ofNat p.2) with
  | .inl (j,k) => (j.toNat, k)
  | .inr (j,k) =>
      if 0 ≤ k then (k.toNat, j+1) else ((-k-1).toNat, -(j+1))

/-- Membership in the nonnegative square is exactly the coordinate bounds. -/
theorem positiveSquareIndices_mem (N : Nat) (p : Nat × Nat) :
    p ∈ positiveSquareIndices N ↔ p.1 ≤ N ∧ p.2 ≤ N := by
  rw [positiveSquareIndices, mem_cartesian_iff]
  simp only [List.mem_range]
  constructor
  · intro hp
    exact ⟨by omega, by omega⟩
  · intro hp
    exact ⟨by omega, by omega⟩

/-- Membership in the filtered list is exactly the mixed half-diamond bound. -/
theorem halfDiamondIndices_mem (N : Nat) (p : MixedIndex) :
    p ∈ halfDiamondIndices N ↔ p.1 + p.2.natAbs ≤ N := by
  constructor
  · intro hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  · intro hp
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hp⟩
    rw [mem_cartesian_iff]
    constructor
    · exact List.mem_range.mpr (by omega)
    · exact (signedIndices_mem N p.2).2 (by
        constructor <;> omega)

/-- The parity-sector coordinates used to read an encoded mixed index. -/
def mixedParity (p : MixedIndex) : ParityIndex :=
  if hk : p.2.natAbs ≤ p.1 then
    .inl ((p.1 : Int), p.2)
  else if hk : 0 ≤ p.2 then
    .inr ((p.2.natAbs : Int)-1, (p.1 : Int))
  else
    .inr ((p.2.natAbs : Int)-1, -(p.1 : Int)-1)

/-- Interpret one parity-decoded pair as its mixed coordinates. -/
def parityToMixed : ParityIndex → MixedIndex
  | .inl (j,k) => (j.toNat, k)
  | .inr (j,k) =>
      if 0 ≤ k then (k.toNat, j+1) else ((-k-1).toNat, -(j+1))

/-- Convert a parity-encoded signed pair to its nonnegative square data. -/
def encodeParityNat (p : ParityIndex) : Nat × Nat :=
  ((encode p).1.toNat, (encode p).2.toNat)

/-- The explicit mixed formula is exactly the parity encoder on its even or
odd sector, with the nonnegative coordinates retained as Nat data. -/
theorem encodeMixed_as_parityNat (p : MixedIndex) :
    encodeMixed p = encodeParityNat (mixedParity p) := by
  rcases p with ⟨h,k⟩
  by_cases he : k.natAbs ≤ h
  · apply Prod.ext <;> simp [encodeMixed, mixedParity, encodeParityNat, encode, encodeEven, he] <;> omega
  · by_cases hk : 0 ≤ k
    · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      have hklt : h < k.natAbs := Nat.lt_of_not_ge he
      have hfirst : 0 ≤ (k.natAbs : Int) - 1 + h + 1 := by omega
      have hsecond : 0 ≤ (k.natAbs : Int) - 1 - (h : Int) := by
        have : (h : Int) < k.natAbs := by exact_mod_cast hklt
        omega
      apply Prod.ext <;> simp [encodeMixed, mixedParity, encodeParityNat, encode, encodeOdd,
        he, hk, hkabs, Int.toNat_of_nonneg hfirst,
        Int.toNat_of_nonneg hsecond] <;> omega
    · have hkneg : k < 0 := by omega
      have hkfalse : ¬ 0 ≤ k := by omega
      have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      have hklt : h < k.natAbs := Nat.lt_of_not_ge he
      have hfirst : 0 ≤ (k.natAbs : Int) - 1 - (h : Int) := by
        have : (h : Int) < k.natAbs := by exact_mod_cast hklt
        omega
      have hsecond : 0 ≤ (k.natAbs : Int) - 1 + (h : Int) + 1 := by omega
      apply Prod.ext <;> simp [encodeMixed, mixedParity, encodeParityNat, encode, encodeOdd,
        he, hkfalse, hkabs, Int.toNat_of_nonneg hfirst,
        Int.toNat_of_nonneg hsecond] <;> omega

/-- The parity decoder is a genuine inverse on every mixed index. -/
theorem parityToMixed_mixedParity (p : MixedIndex) :
    parityToMixed (mixedParity p) = p := by
  rcases p with ⟨h,k⟩
  by_cases he : k.natAbs ≤ h
  · simp [parityToMixed, mixedParity, he]
  · by_cases hk : 0 ≤ k
    · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      have hkpos : 1 ≤ k.natAbs := by
        have : 1 ≤ (k.natAbs : Int) := by omega
        exact_mod_cast this
      simp [parityToMixed, mixedParity, he, hk, hkabs]
    · have hkneg : k < 0 := by omega
      have hkfalse : ¬ 0 ≤ k := by omega
      have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      simp only [mixedParity, dif_neg he, dif_neg hk, parityToMixed]
      rw [if_neg (show ¬ 0 ≤ -(h : Int)-1 by omega)]
      apply Prod.ext
      · change (-(-(h : Int)-1)-1).toNat = h
        rw [show -(-(h : Int)-1)-1 = (h : Int) by omega]
        rfl
      · change -((k.natAbs : Int)-1+1) = k
        omega

/-- Both signed coordinates of the parity encoding of a mixed index are
nonnegative, so projecting through `Int.toNat` loses no information. -/
theorem mixedParity_encode_nonneg (p : MixedIndex) :
    0 ≤ (encode (mixedParity p)).1 ∧ 0 ≤ (encode (mixedParity p)).2 := by
  rcases p with ⟨h,k⟩
  by_cases he : k.natAbs ≤ h
  · have hbound : (k.natAbs : Int) ≤ (h : Int) := by exact_mod_cast he
    by_cases hk : 0 ≤ k
    · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      constructor <;> simp [mixedParity, encode, encodeEven, he, hkabs] <;> omega
    · have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      constructor <;> simp [mixedParity, encode, encodeEven, he, hkabs] <;> omega
  · have hklt : h < k.natAbs := Nat.lt_of_not_ge he
    by_cases hk : 0 ≤ k
    · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      have hgt : (h : Int) < (k.natAbs : Int) := by exact_mod_cast hklt
      constructor <;> simp [mixedParity, encode, encodeOdd, he, hk, hkabs] <;> omega
    · have hkfalse : ¬ 0 ≤ k := by omega
      have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      have hgt : (h : Int) < (k.natAbs : Int) := by exact_mod_cast hklt
      constructor <;> simp [mixedParity, encode, encodeOdd, he, hkfalse, hkabs] <;> omega

/-- The square coordinates of a mixed index are bounded by its Manhattan
radius `h+|k|`. -/
theorem mixedParity_encode_upper (p : MixedIndex) :
    (encode (mixedParity p)).1 ≤ (p.1 : Int) + p.2.natAbs ∧
      (encode (mixedParity p)).2 ≤ (p.1 : Int) + p.2.natAbs := by
  rcases p with ⟨h,k⟩
  by_cases he : k.natAbs ≤ h
  · have hbound : (k.natAbs : Int) ≤ (h : Int) := by exact_mod_cast he
    by_cases hk : 0 ≤ k
    · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      constructor <;> simp [mixedParity, encode, encodeEven, he, hkabs] <;> omega
    · have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      constructor <;> simp [mixedParity, encode, encodeEven, he, hkabs] <;> omega
  · have hklt : h < k.natAbs := Nat.lt_of_not_ge he
    by_cases hk : 0 ≤ k
    · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      have hgt : (h : Int) < (k.natAbs : Int) := by exact_mod_cast hklt
      constructor <;> simp [mixedParity, encode, encodeOdd, he, hk, hkabs] <;> omega
    · have hkfalse : ¬ 0 ≤ k := by omega
      have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      have hgt : (h : Int) < (k.natAbs : Int) := by exact_mod_cast hklt
      constructor <;> simp [mixedParity, encode, encodeOdd, he, hkfalse, hkabs] <;> omega

/-- The explicit mixed map sends every half-diamond point into the square. -/
theorem encodeMixed_bound (N : Nat) (p : MixedIndex)
    (hp : p.1 + p.2.natAbs ≤ N) :
    (encodeMixed p).1 ≤ N ∧ (encodeMixed p).2 ≤ N := by
  have hnonneg := mixedParity_encode_nonneg p
  have hupper := mixedParity_encode_upper p
  have hpI : (p.1 : Int) + (p.2.natAbs : Int) ≤ (N : Int) := by exact_mod_cast hp
  have hfirst : (encode (mixedParity p)).1.toNat ≤ N := by
    have hle : (encode (mixedParity p)).1 ≤ (N : Int) := Int.le_trans hupper.1 hpI
    have hcast := Int.toNat_of_nonneg hnonneg.1
    have hc : ((encode (mixedParity p)).1.toNat : Int) ≤ (N : Int) := by rw [hcast]; exact hle
    exact_mod_cast hc
  have hsecond : (encode (mixedParity p)).2.toNat ≤ N := by
    have hle : (encode (mixedParity p)).2 ≤ (N : Int) := Int.le_trans hupper.2 hpI
    have hcast := Int.toNat_of_nonneg hnonneg.2
    have hc : ((encode (mixedParity p)).2.toNat : Int) ≤ (N : Int) := by rw [hcast]; exact hle
    exact_mod_cast hc
  rw [encodeMixed_as_parityNat]
  exact ⟨hfirst, hsecond⟩

/-- Decoding the Nat projection of a nonnegative parity encoding returns the
same mixed index. -/
theorem decodeMixed_encodeParityNat (q : ParityIndex)
    (hq : 0 ≤ (encode q).1 ∧ 0 ≤ (encode q).2) :
    decodeMixed (encodeParityNat q) = parityToMixed q := by
  have hpair :
      (Int.ofNat ((encode q).1.toNat), Int.ofNat ((encode q).2.toNat)) = encode q := by
    apply Prod.ext
    · exact Int.toNat_of_nonneg hq.1
    · exact Int.toNat_of_nonneg hq.2
  change parityToMixed
    (decode (Int.ofNat ((encode q).1.toNat), Int.ofNat ((encode q).2.toNat))) =
      parityToMixed q
  rw [hpair, decode_encode]

/-- The two explicit maps are inverse on every mixed index. -/
theorem decodeMixed_encodeMixed (p : MixedIndex) :
    decodeMixed (encodeMixed p) = p := by
  calc
    decodeMixed (encodeMixed p) = decodeMixed (encodeParityNat (mixedParity p)) :=
      congrArg decodeMixed (encodeMixed_as_parityNat p)
    _ = parityToMixed (mixedParity p) :=
      decodeMixed_encodeParityNat (mixedParity p) (mixedParity_encode_nonneg p)
    _ = p := parityToMixed_mixedParity p

/-- On the decoded parity sector of a nonnegative square, mixed encoding
selects exactly the same sector. -/
theorem mixedParity_parityToMixed (q : ParityIndex)
    (hq : 0 ≤ (encode q).1 ∧ 0 ≤ (encode q).2) :
    mixedParity (parityToMixed q) = q := by
  cases q with
  | inl jk =>
      rcases jk with ⟨j,k⟩
      have hcoord := hq
      dsimp [encode, encodeEven] at hcoord
      have hj : 0 ≤ j := by omega
      have hbound : k.natAbs ≤ j.toNat := by
        by_cases hk : 0 ≤ k
        · have hkabs := Int.natAbs_of_nonneg hk
          have : k ≤ j := by omega
          have hc : (k.natAbs : Int) ≤ (j.toNat : Int) := by
            rw [hkabs, Int.toNat_of_nonneg hj]
            exact this
          exact_mod_cast hc
        · have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
          have : -k ≤ j := by omega
          have hc : (k.natAbs : Int) ≤ (j.toNat : Int) := by
            rw [hkabs, Int.toNat_of_nonneg hj]
            exact this
          exact_mod_cast hc
      simp [parityToMixed, mixedParity, hbound, Int.toNat_of_nonneg hj]
  | inr jk =>
      rcases jk with ⟨j,k⟩
      have hcoord := hq
      dsimp [encode, encodeOdd] at hcoord
      by_cases hk : 0 ≤ k
      · have hj1 : 0 ≤ j+1 := by omega
        have hknat : (k.toNat : Int) = k := Int.toNat_of_nonneg hk
        have habs : (j+1).natAbs = (j+1).toNat := by
          exact natAbs_eq_toNat (j+1) hj1
        have hnot : ¬ (j+1).natAbs ≤ k.toNat := by
          have hm : k ≤ j := by omega
          have hc : (k.toNat : Int) < ((j+1).toNat : Int) := by
            rw [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hj1]
            omega
          have : k.toNat < (j+1).toNat := by exact_mod_cast hc
          rw [habs]
          exact Nat.not_le_of_gt this
        simp only [parityToMixed, if_pos hk]
        change (if (j+1).natAbs ≤ k.toNat then
            Sum.inl ((k.toNat : Int), (j+1 : Int))
          else if 0 ≤ (j+1 : Int) then
            Sum.inr (((j+1).natAbs : Int)-1, (k.toNat : Int))
          else Sum.inr (((j+1).natAbs : Int)-1, -(k.toNat : Int)-1)) =
            Sum.inr (j,k)
        rw [if_neg hnot, if_pos hj1]
        apply congrArg Sum.inr
        apply Prod.ext
        · rw [habs, Int.toNat_of_nonneg hj1]
          omega
        · exact hknat
      · have hklt : k < 0 := by omega
        have hj1 : 0 ≤ j+1 := by omega
        have hfirst : 0 ≤ -k-1 := by omega
        have hknat : ((-k-1).toNat : Int) = -k-1 := Int.toNat_of_nonneg hfirst
        have hsecond : ((-(j+1)).natAbs : Int) = j+1 := by
          rw [Int.ofNat_natAbs_of_nonpos (by omega)]
          omega
        have hsecondNat : (-(j+1)).natAbs = (j+1).toNat := by
          have hcast : ((-(j+1)).natAbs : Int) = ((j+1).toNat : Int) := by
            rw [hsecond, Int.toNat_of_nonneg hj1]
          exact_mod_cast hcast
        have hnot : ¬ (-(j+1)).natAbs ≤ (-k-1).toNat := by
          have hm : -k-1 < j+1 := by omega
          have ha : (j+1).natAbs = (j+1).toNat := natAbs_eq_toNat (j+1) hj1
          have hmI : ((-k-1).toNat : Int) < ((j+1).toNat : Int) := by
            rw [Int.toNat_of_nonneg hfirst, Int.toNat_of_nonneg hj1]
            exact hm
          have hmNat : (-k-1).toNat < (j+1).toNat := by exact_mod_cast hmI
          rw [hsecondNat]
          exact Nat.not_le_of_gt hmNat
        have hneg : ¬ 0 ≤ -(j+1 : Int) := by omega
        simp only [parityToMixed, if_neg hk]
        change (if (-(j+1 : Int)).natAbs ≤ (-k-1).toNat then
            Sum.inl (((-k-1).toNat : Int), (-(j+1) : Int))
          else if 0 ≤ (-(j+1) : Int) then
            Sum.inr (((-(j+1 : Int)).natAbs : Int)-1, ((-k-1).toNat : Int))
          else Sum.inr (((-(j+1 : Int)).natAbs : Int)-1,
            -((-k-1).toNat : Int)-1)) = Sum.inr (j,k)
        rw [if_neg hnot, if_neg hneg]
        apply congrArg Sum.inr
        apply Prod.ext
        · rw [hsecondNat, Int.toNat_of_nonneg hj1]
          omega
        · rw [hknat]
          omega

/-- The mixed encoder is also a left inverse on the nonnegative square. -/
theorem encodeMixed_decodeMixed (p : Nat × Nat) :
    encodeMixed (decodeMixed p) = p := by
  let q := decode (Int.ofNat p.1, Int.ofNat p.2)
  have hdecode : encode q = (Int.ofNat p.1, Int.ofNat p.2) := by
    dsimp [q]
    exact encode_decode (Int.ofNat p.1, Int.ofNat p.2)
  have hq : 0 ≤ (encode q).1 ∧ 0 ≤ (encode q).2 := by
    rw [hdecode]
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  have hm : decodeMixed p = parityToMixed q := by
    dsimp [decodeMixed, q]
    rfl
  rw [hm, encodeMixed_as_parityNat, mixedParity_parityToMixed q hq]
  dsimp [encodeParityNat]
  rw [hdecode]
  simp [Int.toNat_of_nonneg]

/-- The parity decoder maps a square point into the exact mixed half-diamond
bound, with radius equal to one of the square coordinates. -/
theorem decodeMixed_bound (N : Nat) (p : Nat × Nat)
    (hp : p.1 ≤ N ∧ p.2 ≤ N) :
    (decodeMixed p).1 + (decodeMixed p).2.natAbs ≤ N := by
  let q := decode (Int.ofNat p.1, Int.ofNat p.2)
  have henc : encode q = (Int.ofNat p.1, Int.ofNat p.2) := by
    dsimp [q]
    exact encode_decode (Int.ofNat p.1, Int.ofNat p.2)
  have hpI1 : (p.1 : Int) ≤ (N : Int) := by exact_mod_cast hp.1
  have hpI2 : (p.2 : Int) ≤ (N : Int) := by exact_mod_cast hp.2
  have hdm : decodeMixed p = parityToMixed q := by
    dsimp [decodeMixed, q, parityToMixed]
  cases hq : q with
  | inl jk =>
      rcases jk with ⟨j,k⟩
      have heq : (j+k, j-k) = (Int.ofNat p.1, Int.ofNat p.2) := by
        simpa [q, hq, encode, encodeEven] using henc
      have hn := congrArg Prod.fst heq
      have hm := congrArg Prod.snd heq
      change j+k = (p.1 : Int) at hn
      change j-k = (p.2 : Int) at hm
      have hj : 0 ≤ j := by
        have hn' := congrArg (fun z : Int => z + (j-k)) hn
        have hm' := congrArg (fun z : Int => z + (j+k)) hm
        omega
      by_cases hk : 0 ≤ k
      · have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
        have hjnat : (j.toNat : Int) = j := Int.toNat_of_nonneg hj
        have hrad : (j.toNat : Int) + (k.natAbs : Int) ≤ (N : Int) := by
          rw [hjnat, hkabs]
          omega
        have hgoal : (j.toNat : Nat) + k.natAbs ≤ N := by exact_mod_cast hrad
        rw [hdm, hq]
        simpa [parityToMixed] using hgoal
      · have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
        have hjnat : (j.toNat : Int) = j := Int.toNat_of_nonneg hj
        have hrad : (j.toNat : Int) + (k.natAbs : Int) ≤ (N : Int) := by
          rw [hjnat, hkabs]
          omega
        have hgoal : (j.toNat : Nat) + k.natAbs ≤ N := by exact_mod_cast hrad
        rw [hdm, hq]
        simpa [parityToMixed] using hgoal
  | inr jk =>
      rcases jk with ⟨j,k⟩
      have heq : (j+k+1, j-k) = (Int.ofNat p.1, Int.ofNat p.2) := by
        simpa [q, hq, encode, encodeOdd] using henc
      have hn := congrArg Prod.fst heq
      have hm := congrArg Prod.snd heq
      change j+k+1 = (p.1 : Int) at hn
      change j-k = (p.2 : Int) at hm
      by_cases hk : 0 ≤ k
      · have hj1 : 0 ≤ j+1 := by omega
        have hknat : (k.toNat : Int) = k := Int.toNat_of_nonneg hk
        have hjnat : ((j+1).toNat : Int) = j+1 := Int.toNat_of_nonneg hj1
        have hrad : (k.toNat : Int) + ((j+1).natAbs : Int) ≤ (N : Int) := by
          rw [hknat, Int.natAbs_of_nonneg hj1]
          omega
        have hgoal : k.toNat + (j+1).natAbs ≤ N := by exact_mod_cast hrad
        rw [hdm, hq]
        simpa [parityToMixed, hk] using hgoal
      · have hklt : k < 0 := by omega
        have hfirst : 0 ≤ -k-1 := by omega
        have hj1 : 0 ≤ j+1 := by omega
        have hknat : ((-k-1).toNat : Int) = -k-1 := Int.toNat_of_nonneg hfirst
        have hjabs : ((-(j+1)).natAbs : Int) = j+1 := by
          rw [Int.ofNat_natAbs_of_nonpos (by omega)]
          omega
        have hrad : (-k-1).toNat + (-(j+1)).natAbs ≤ N := by
          have hradI : ((-k-1).toNat : Int) + ((-(j+1)).natAbs : Int) ≤ (N : Int) := by
            rw [hknat, hjabs]
            omega
          exact_mod_cast hradI
        rw [hdm, hq]
        simpa only [parityToMixed, if_neg hk] using hrad

/-- Inversion proves the mixed encoding is injective. -/
theorem encodeMixed_injective {p q : MixedIndex}
    (he : encodeMixed p = encodeMixed q) : p = q := by
  have h := congrArg decodeMixed he
  rw [decodeMixed_encodeMixed, decodeMixed_encodeMixed] at h
  exact h

private theorem rangeNodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro i hi j hj hij
      have hj' : j = n := List.mem_singleton.mp hj
      rw [hij, hj'] at hi
      exact Nat.lt_irrefl n (List.mem_range.mp hi)

private theorem signedIndicesNodup (N : Nat) : (signedIndices N).Nodup := by
  apply YMGap.Continuum.TorusWilsonAction.nodup_map_on
    (fun i : Nat => (i : Int) - (N : Int))
  · intro i hi j hj he
    change (i : Int) - (N : Int) = (j : Int) - (N : Int) at he
    omega
  · exact rangeNodup (2*N+1)

/-- The source square is duplicate-free. -/
theorem positiveSquareIndices_nodup (N : Nat) :
    (positiveSquareIndices N).Nodup := by
  unfold positiveSquareIndices
  exact cartesian_nodup _ _ (rangeNodup (N+1)) (rangeNodup (N+1))

/-- Filtering preserves duplicate-freeness of the mixed ambient rectangle. -/
theorem halfDiamondIndices_nodup (N : Nat) :
    (halfDiamondIndices N).Nodup := by
  unfold halfDiamondIndices
  exact (List.filter_sublist).nodup
    (cartesian_nodup _ _ (rangeNodup (N+1)) (signedIndicesNodup N))

/-- The image list is duplicate-free because `decodeMixed` is an explicit
left inverse. -/
theorem encodedHalfDiamond_nodup (N : Nat) :
    ((halfDiamondIndices N).map encodeMixed).Nodup := by
  apply YMGap.Continuum.TorusWilsonAction.nodup_map_on encodeMixed
  · intro p hp q hq he
    exact encodeMixed_injective he
  · exact halfDiamondIndices_nodup N

/-- The positive square and the encoded half-diamond are the same finite
domain, in permutation order. -/
theorem positiveSquare_halfDiamond_permutation (N : Nat) :
    (positiveSquareIndices N).Perm ((halfDiamondIndices N).map encodeMixed) := by
  apply YMGap.Continuum.TorusWilsonAction.perm_of_nodup_mem
    (positiveSquareIndices_nodup N) (encodedHalfDiamond_nodup N)
  intro p
  constructor
  · intro hp
    have hbounds := (positiveSquareIndices_mem N p).1 hp
    have hmixed := decodeMixed_bound N p hbounds
    exact List.mem_map.mpr
      ⟨decodeMixed p, (halfDiamondIndices_mem N _).2 hmixed,
        encodeMixed_decodeMixed p⟩
  · intro hp
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hp
    have hmixed := (halfDiamondIndices_mem N q).1 hq
    have hbounds := encodeMixed_bound N q hmixed
    have hmem : encodeMixed q ∈ positiveSquareIndices N :=
      (positiveSquareIndices_mem N _).2 hbounds
    simpa [he] using hmem

private theorem listQSum_perm {A : Type} (weight : A → Q')
    {xs ys : List A} (h : xs.Perm ys) :
    listQSum weight xs ≈ listQSum weight ys := by
  induction h with
  | nil => exact Q'.eqv_refl 0
  | cons x _ ih => exact Q'.add_eqv_congr_left (weight x) _ _ ih
  | swap x y rest =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => weight y | 1 => weight x | _ => listQSum weight rest)
  | trans _ _ ih₁ ih₂ => exact Q'.eqv_trans _ _ _ ih₁ ih₂

/-- Arbitrary rational weights, including signed ones, reindex exactly across
the finite square/half-diamond bijection. -/
theorem listQSum_positiveSquare_halfDiamond (weight : Nat × Nat → Q') (N : Nat) :
    listQSum weight (positiveSquareIndices N) ≈
      listQSum (fun p => weight (encodeMixed p)) (halfDiamondIndices N) := by
  have hp := listQSum_perm weight (positiveSquare_halfDiamond_permutation N)
  rw [listQSum_map] at hp
  exact hp

end YMGap.Continuum.ThetaAlternatingHalfDiamond

#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.positiveSquareIndices_mem
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.halfDiamondIndices_mem
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.encodeMixed_as_parityNat
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.parityToMixed_mixedParity
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.mixedParity_encode_nonneg
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.mixedParity_encode_upper
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.encodeMixed_bound
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.decodeMixed_encodeParityNat
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.decodeMixed_encodeMixed
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.mixedParity_parityToMixed
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.encodeMixed_decodeMixed
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.decodeMixed_bound
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.encodeMixed_injective
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.positiveSquareIndices_nodup
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.halfDiamondIndices_nodup
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.encodedHalfDiamond_nodup
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.positiveSquare_halfDiamond_permutation
#print axioms YMGap.Continuum.ThetaAlternatingHalfDiamond.listQSum_positiveSquare_halfDiamond
