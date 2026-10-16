/-
# Uniform central floor for the rational open-cube bulk profile

This leaf proves the pointwise estimate used by the PAPER bulk-source mass
argument.  For a side `s = 4*m` and an offset in the central half
`m <= r < 3*m`, the exact rational profile

    (v_s(r) / (4*s + v_s(r)))^s

is at least `3^(-6)`.  The proof is entirely finite and constructive:

* the central midpoint numerator satisfies the stronger bound
  `v_s(r) >= 3*s^2/4`;
* the existing checked cubic Euler estimate is iterated through six unit
  shifts to give `(s+6)^s <= 3^6*s^s`;
* all rational denominators are cleared in `Nat`, then lifted to the exact
  unnormalised rational representation `Q'`;
* the central half-carrier is an ordered sublist with `3*(s/2)^3` faces, so
  its coefficient squares give the normalized floor `3^(-36)/8`;
* the exceptional dyadic sides `s = 1, 2` are checked directly, yielding the
  same floor at every dyadic side `s = 2^j`.

Positive cross-time covariance, original/free comparison, continuum limit
and mass gap remain separate obligations.
-/

import YMGap.Continuum.CubicEulerBound
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor

set_option autoImplicit false

open scoped List

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.CubicEulerBoundProof
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

local infix:50 " ≈ " => Q'.eqv

/-- One fixed-exponent unit shift costs at most one factor of three. -/
theorem cubicEulerShiftStep (s k : Nat) (hs : 0 < s) :
    (s + k + 1) ^ s <= 3 * (s + k) ^ s := by
  have heuler := cubicEulerBound (s + k)
  have hbase : s + k <= s + k + 1 := Nat.le_succ _
  have hpow : (s + k) ^ k <= (s + k + 1) ^ k :=
    Nat.pow_le_pow_left hbase k
  have hleft :
      (s + k + 1) ^ s * (s + k) ^ k <=
        (s + k + 1) ^ (s + k) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_left _ hpow
  have hchain :
      (s + k + 1) ^ s * (s + k) ^ k <=
        3 * (s + k) ^ (s + k) :=
    Nat.le_trans hleft heuler
  have hright :
      3 * (s + k) ^ (s + k) =
        (3 * (s + k) ^ s) * (s + k) ^ k := by
    rw [Nat.pow_add]
    ac_rfl
  rw [hright] at hchain
  exact Nat.le_of_mul_le_mul_right hchain
    (Nat.pow_pos (by omega))

/-- Iterating the unit-shift estimate gives
`(s+k)^s <= 3^k*s^s` for every positive `s`. -/
theorem cubicEulerShift (s : Nat) (hs : 0 < s) :
    forall k : Nat, (s + k) ^ s <= 3 ^ k * s ^ s
  | 0 => by simp
  | k + 1 => by
      have hstep := cubicEulerShiftStep s k hs
      have hind := cubicEulerShift s hs k
      calc
        (s + (k + 1)) ^ s = (s + k + 1) ^ s := by rfl
        _ <= 3 * (s + k) ^ s := hstep
        _ <= 3 * (3 ^ k * s ^ s) := Nat.mul_le_mul_left 3 hind
        _ = 3 ^ (k + 1) * s ^ s := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem productAddOneIdentity (base left right : Nat) :
    (base + left + 1) * (base + right + 1) + 1 =
      base * base + base * (left + right + 2) +
        left * right + (left + right + 2) := by
  rw [show (2 : Nat) = 1 + 1 by decide]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  ac_rfl

private theorem centralProductIdentity
    (m leftOffset rightOffset : Nat)
    (hsum : leftOffset + rightOffset + 1 = 2 * m) :
    (2 * m + 2 * leftOffset + 1) *
          (2 * m + 2 * rightOffset + 1) + 1 =
      3 * (2 * m) * (2 * m) +
        2 * (2 * m) + 4 * leftOffset * rightOffset := by
  rw [productAddOneIdentity]
  have hdouble :
      2 * leftOffset + 2 * rightOffset + 2 = 2 * (2 * m) := by
    omega
  rw [hdouble]
  have hbase :
      (2 * m) * (2 * (2 * m)) = 2 * ((2 * m) * (2 * m)) := by
    ac_rfl
  have hoffset :
      (2 * leftOffset) * (2 * rightOffset) =
        4 * leftOffset * rightOffset := by
    rw [show 4 = 2 * 2 by decide]
    ac_rfl
  rw [hbase, hoffset]
  have hthree :
      (2 * m) * (2 * m) + 2 * ((2 * m) * (2 * m)) =
        3 * (2 * m) * (2 * m) := by
    rw [show (2 : Nat) = 1 + 1 by decide,
      show (3 : Nat) = 1 + 1 + 1 by decide]
    simp only [Nat.add_mul, Nat.one_mul]
    ac_rfl
  rw [hthree]
  ac_rfl

/-- On the central half of a side `4*m`, the midpoint numerator is at least
`3*(2*m)^2 = 3*s^2/4`. -/
theorem bulkProfileNumerator_central_floor
    (m r : Nat) (hm : 0 < m) (hlower : m <= r) (hupper : r < 3 * m) :
    3 * (2 * m) * (2 * m) <= bulkProfileNumerator (4 * m) r := by
  let leftOffset := r - m
  let rightOffset := 3 * m - r - 1
  have hsum : leftOffset + rightOffset + 1 = 2 * m := by
    dsimp [leftOffset, rightOffset]
    omega
  have hleft : 2 * r + 1 = 2 * m + 2 * leftOffset + 1 := by
    dsimp [leftOffset]
    omega
  have hright :
      2 * (4 * m) - 2 * r - 1 =
        2 * m + 2 * rightOffset + 1 := by
    dsimp [rightOffset]
    omega
  have hidentity := centralProductIdentity m leftOffset rightOffset hsum
  have hextra :
      1 <= 2 * (2 * m) + 4 * leftOffset * rightOffset := by
    have hpositive : 0 < 2 * (2 * m) := by omega
    omega
  have hproduct :
      3 * (2 * m) * (2 * m) <=
        (2 * m + 2 * leftOffset + 1) *
          (2 * m + 2 * rightOffset + 1) := by
    omega
  unfold bulkProfileNumerator
  rw [hleft, hright]
  exact hproduct

private theorem centralScaledNumeratorFloor
    (m r : Nat) (hm : 0 < m) (hlower : m <= r) (hupper : r < 3 * m) :
    4 * (4 * m) * (4 * m) <=
      6 * bulkProfileNumerator (4 * m) r := by
  have hcentral := bulkProfileNumerator_central_floor
    m r hm hlower hupper
  have hscaled := Nat.mul_le_mul_left 6 hcentral
  have hconstant :
      4 * (4 * m) * (4 * m) <=
        6 * (3 * (2 * m) * (2 * m)) := by
    calc
      4 * (4 * m) * (4 * m) = (4 * 4 * 4) * (m * m) := by ac_rfl
      _ = 64 * (m * m) := by rw [show 4 * 4 * 4 = 64 by decide]
      _ <= 72 * (m * m) := Nat.mul_le_mul_right (m * m) (by decide)
      _ = (6 * 3 * 2 * 2) * (m * m) := by
        rw [show 6 * 3 * 2 * 2 = 72 by decide]
      _ = 6 * (3 * (2 * m) * (2 * m)) := by ac_rfl
  exact Nat.le_trans hconstant hscaled

/-- The central numerator bound gives the denominator comparison
`s*(4*s+v) <= (s+6)*v`. -/
theorem bulkProfileDenominator_central_scaled_le
    (m r : Nat) (hm : 0 < m) (hlower : m <= r) (hupper : r < 3 * m) :
    (4 * m) * bulkProfileDenominator (4 * m) r <=
      (4 * m + 6) * bulkProfileNumerator (4 * m) r := by
  have hcore := centralScaledNumeratorFloor m r hm hlower hupper
  unfold bulkProfileDenominator
  calc
    (4 * m) * (4 * (4 * m) + bulkProfileNumerator (4 * m) r) =
        4 * (4 * m) * (4 * m) +
          (4 * m) * bulkProfileNumerator (4 * m) r := by
      simp only [Nat.mul_add]
      ac_rfl
    _ <= 6 * bulkProfileNumerator (4 * m) r +
          (4 * m) * bulkProfileNumerator (4 * m) r :=
      Nat.add_le_add_right hcore _
    _ = (4 * m + 6) * bulkProfileNumerator (4 * m) r := by
      rw [Nat.add_mul]
      ac_rfl

/-- Denominator-cleared profile estimate on the central half. -/
theorem bulkProfileDenominator_pow_central_le
    (m r : Nat) (hm : 0 < m) (hlower : m <= r) (hupper : r < 3 * m) :
    bulkProfileDenominator (4 * m) r ^ (4 * m) <=
      3 ^ 6 * bulkProfileNumerator (4 * m) r ^ (4 * m) := by
  let side := 4 * m
  let numerator := bulkProfileNumerator side r
  let denominator := bulkProfileDenominator side r
  have hside : 0 < side := by
    dsimp [side]
    omega
  have hscaled : side * denominator <= (side + 6) * numerator := by
    simpa only [side, numerator, denominator] using
      bulkProfileDenominator_central_scaled_le m r hm hlower hupper
  have hpow := Nat.pow_le_pow_left hscaled side
  simp only [Nat.mul_pow] at hpow
  have hshift := cubicEulerShift side hside 6
  have hright := Nat.mul_le_mul hshift (Nat.le_refl (numerator ^ side))
  have hchain := Nat.le_trans hpow hright
  have hcancel :
      denominator ^ side * side ^ side <=
        (3 ^ 6 * numerator ^ side) * side ^ side := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain
  have hresult := Nat.le_of_mul_le_mul_right hcancel
    (Nat.pow_pos hside)
  simpa only [side, numerator, denominator] using hresult

/-- The exact rational lower floor `3^(-6)`. -/
def bulkProfileFloor : Q' := Q'.mkPos 1 (3 ^ 6) (by decide)

private theorem divPosOfNat_num
    (numerator denominator : Nat)
    (hdenominator : (0 : Q') < Q'.ofNat denominator) :
    (Q'.divPos (Q'.ofNat numerator) (Q'.ofNat denominator)
      hdenominator).num = (numerator : Int) := by
  unfold Q'.divPos
  rw [Q'.mul_num_cast, Q'.ofNat_num_cast, Q'.recipPos_num,
    Q'.ofNat_den_cast, Int.mul_one]

private theorem divPosOfNat_den
    (numerator denominator : Nat)
    (hdenominator : (0 : Q') < Q'.ofNat denominator) :
    ((Q'.divPos (Q'.ofNat numerator) (Q'.ofNat denominator)
      hdenominator).den : Int) = (denominator : Int) := by
  unfold Q'.divPos
  rw [Q'.mul_den_cast, Q'.ofNat_den_cast, Q'.recipPos_den,
    Q'.ofNat_num_cast, Int.one_mul]

private theorem qpowDivPosOfNat_num
    (numerator denominator : Nat)
    (hdenominator : (0 : Q') < Q'.ofNat denominator) :
    forall exponent : Nat,
      ((Q'.divPos (Q'.ofNat numerator) (Q'.ofNat denominator)
        hdenominator) ^ exponent).num = (numerator ^ exponent : Nat)
  | 0 => rfl
  | exponent + 1 => by
      rw [Q'.pow_succ, Q'.mul_num_cast,
        divPosOfNat_num, qpowDivPosOfNat_num]
      rw [Nat.pow_succ, Nat.mul_comm]
      rw [Int.natCast_mul]

private theorem qpowDivPosOfNat_den
    (numerator denominator : Nat)
    (hdenominator : (0 : Q') < Q'.ofNat denominator) :
    forall exponent : Nat,
      (((Q'.divPos (Q'.ofNat numerator) (Q'.ofNat denominator)
        hdenominator) ^ exponent).den : Int) =
          (denominator ^ exponent : Nat)
  | 0 => rfl
  | exponent + 1 => by
      rw [Q'.pow_succ, Q'.mul_den_cast,
        divPosOfNat_den, qpowDivPosOfNat_den]
      rw [Nat.pow_succ, Nat.mul_comm]
      rw [Int.natCast_mul]

/-- On every central offset of a side divisible by four, the exact rational
profile is bounded below by `3^(-6)`. -/
theorem bulkProfile_central_floor
    (m r : Nat) (hm : 0 < m) (hlower : m <= r) (hupper : r < 3 * m) :
    bulkProfileFloor <=
      bulkProfile (4 * m) r (Nat.mul_pos (by decide) hm) := by
  have hpow := bulkProfileDenominator_pow_central_le
    m r hm hlower hupper
  unfold bulkProfileFloor bulkProfile
  show
    (Q'.mkPos 1 (3 ^ 6) _).num *
        (((Q'.divPos
          (Q'.ofNat (bulkProfileNumerator (4 * m) r))
          (Q'.ofNat (bulkProfileDenominator (4 * m) r))
          (bulkProfileDenominator_pos (4 * m) r
            (Nat.mul_pos (by decide) hm))) ^ (4 * m)).den : Int) <=
      ((Q'.divPos
        (Q'.ofNat (bulkProfileNumerator (4 * m) r))
        (Q'.ofNat (bulkProfileDenominator (4 * m) r))
        (bulkProfileDenominator_pos (4 * m) r
          (Nat.mul_pos (by decide) hm))) ^ (4 * m)).num *
        ((Q'.mkPos 1 (3 ^ 6) _).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den,
    qpowDivPosOfNat_num, qpowDivPosOfNat_den, Int.one_mul]
  exact_mod_cast (by
    simpa only [Nat.mul_comm] using hpow)

/-! ## Central source carrier and coefficient-square mass -/

/-- The central half of the one-dimensional offset range. -/
def centralBulkOffsets (m : Nat) : List Nat := List.range' m (2 * m)

/-- All three spatial orientations over the central half-cube. -/
def centralBulkSourceFaces (m : Nat) : List Z4Plaq :=
  (centralBulkOffsets m).flatMap fun rx =>
    (centralBulkOffsets m).flatMap fun ry =>
      (centralBulkOffsets m).flatMap fun rz =>
        bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz)

private theorem flatMapSublistSource
    {A B : Type} {source target : List A}
    (block : A -> List B) (hsublist : source <+ target) :
    source.flatMap block <+ target.flatMap block := by
  induction hsublist with
  | slnil => exact List.Sublist.slnil
  | cons item htail hinduction =>
      simpa only [List.flatMap_cons] using
        List.sublist_append_of_sublist_right (l₁ := block item) hinduction
  | cons₂ item htail hinduction =>
      simpa only [List.flatMap_cons] using
        List.Sublist.append (List.Sublist.refl (block item)) hinduction

private theorem flatMapSublistPointwise
    {A B : Type} (source : List A) (lower upper : A -> List B)
    (hsublist : forall item, item ∈ source -> lower item <+ upper item) :
    source.flatMap lower <+ source.flatMap upper := by
  induction source with
  | nil => exact List.Sublist.slnil
  | cons item rest hinduction =>
      simp only [List.flatMap_cons]
      exact List.Sublist.append
        (hsublist item List.mem_cons_self)
        (hinduction (fun other hother =>
          hsublist other (List.mem_cons_of_mem item hother)))

theorem centralBulkOffsets_sublist (m : Nat) :
    centralBulkOffsets m <+ List.range (4 * m) := by
  unfold centralBulkOffsets
  have htail : List.range' m (2 * m) <+ List.range' m (3 * m) :=
    List.range'_sublist_right.mpr (by omega)
  have hsuffix :
      List.range' m (2 * m) <+
        List.range' 0 m ++ List.range' m (3 * m) :=
    List.sublist_append_of_sublist_right (l₁ := List.range' 0 m) htail
  have happend :
      List.range' 0 m ++ List.range' m (3 * m) =
        List.range' 0 (4 * m) := by
    simpa only [Nat.zero_add, show m + 3 * m = 4 * m by omega] using
      (List.range'_append_1 (s := 0) (m := m) (n := 3 * m))
  rw [happend] at hsuffix
  simpa only [List.range_eq_range'] using hsuffix

/-- The explicit central half-carrier occurs in the same lexicographic order
inside the full formula-level source. -/
theorem centralBulkSourceFaces_sublist (m : Nat) :
    centralBulkSourceFaces m <+ bulkSourceFaces (4 * m) := by
  have hoffsets := centralBulkOffsets_sublist m
  have hz (rx ry : Nat) :
      (centralBulkOffsets m).flatMap (fun rz =>
          bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz)) <+
        (List.range (4 * m)).flatMap (fun rz =>
          bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz)) :=
    flatMapSublistSource
      (fun rz => bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz))
      hoffsets
  have hy (rx : Nat) :
      (centralBulkOffsets m).flatMap (fun ry =>
        (centralBulkOffsets m).flatMap (fun rz =>
          bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz))) <+
      (List.range (4 * m)).flatMap (fun ry =>
        (List.range (4 * m)).flatMap (fun rz =>
          bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz))) := by
    have hinner := flatMapSublistPointwise
      (centralBulkOffsets m)
      (fun ry => (centralBulkOffsets m).flatMap (fun rz =>
        bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz)))
      (fun ry => (List.range (4 * m)).flatMap (fun rz =>
        bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz)))
      (fun ry _ => hz rx ry)
    exact hinner.trans
      (flatMapSublistSource
        (fun ry => (List.range (4 * m)).flatMap (fun rz =>
          bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz)))
        hoffsets)
  unfold centralBulkSourceFaces bulkSourceFaces
  have hinner := flatMapSublistPointwise
    (centralBulkOffsets m)
    (fun rx => (centralBulkOffsets m).flatMap (fun ry =>
      (centralBulkOffsets m).flatMap (fun rz =>
        bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz))))
    (fun rx => (List.range (4 * m)).flatMap (fun ry =>
      (List.range (4 * m)).flatMap (fun rz =>
        bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz))))
    (fun rx _ => hy rx)
  exact hinner.trans
    (flatMapSublistSource
      (fun rx => (List.range (4 * m)).flatMap (fun ry =>
        (List.range (4 * m)).flatMap (fun rz =>
          bulkSourcePlanes.map (bulkSourceFaceAt (4 * m) rx ry rz))))
      hoffsets)

private theorem lengthFlatMapConst
    {A B : Type} (block : A -> List B) (count : Nat)
    (hlength : forall item, (block item).length = count) :
    forall items : List A,
      (items.flatMap block).length = items.length * count
  | [] => by simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | item :: rest => by
      rw [List.flatMap_cons, List.length_append, hlength item,
        lengthFlatMapConst block count hlength rest,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- The central half-carrier has exactly `3*(2*m)^3` faces. -/
theorem centralBulkSourceFaces_length (m : Nat) :
    (centralBulkSourceFaces m).length = 3 * (2 * m) ^ 3 := by
  unfold centralBulkSourceFaces centralBulkOffsets
  rw [lengthFlatMapConst _ ((2 * m) * ((2 * m) * 3))]
  · simp only [List.length_range']
    simp only [Nat.pow_succ, Nat.pow_zero]
    ac_rfl
  · intro rx
    rw [lengthFlatMapConst _ ((2 * m) * 3)]
    · simp only [List.length_range']
    · intro ry
      rw [lengthFlatMapConst _ 3]
      · simp only [List.length_range']
      · intro rz
        rfl

/-- Exact coefficient-square floor on the central half-carrier. -/
def bulkCoefficientSquareFloor : Q' := Q'.mkPos 1 (3 ^ 36) (by decide)

private theorem bulkProfileCubeSquareFloor_eqv :
    (bulkProfileFloor * (bulkProfileFloor * bulkProfileFloor)) *
        (bulkProfileFloor * (bulkProfileFloor * bulkProfileFloor)) ≈
      bulkCoefficientSquareFloor := by
  decide

/-- Every central source face has coefficient square at least `3^(-36)`. -/
theorem centralBulkSourceCoefficient_square_floor
    (m : Nat) (hm : 0 < m) {face : Z4Plaq}
    (hface : face ∈ centralBulkSourceFaces m) :
    bulkCoefficientSquareFloor <=
      bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face *
        bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face := by
  have hraw := hface
  unfold centralBulkSourceFaces at hraw
  obtain ⟨rx, hrx, hraw⟩ := List.mem_flatMap.mp hraw
  obtain ⟨ry, hry, hraw⟩ := List.mem_flatMap.mp hraw
  obtain ⟨rz, hrz, hraw⟩ := List.mem_flatMap.mp hraw
  obtain ⟨plane, hplane, hfaceEq⟩ := List.mem_map.mp hraw
  subst face
  have hrxBounds := List.mem_range'_1.mp hrx
  have hryBounds := List.mem_range'_1.mp hry
  have hrzBounds := List.mem_range'_1.mp hrz
  have hx := bulkProfile_central_floor m rx hm
    hrxBounds.1 (by omega)
  have hy := bulkProfile_central_floor m ry hm
    hryBounds.1 (by omega)
  have hz := bulkProfile_central_floor m rz hm
    hrzBounds.1 (by omega)
  have hfloor0 : (0 : Q') <= bulkProfileFloor := by decide
  have hx0 : (0 : Q') <=
      bulkProfile (4 * m) rx (Nat.mul_pos (by decide) hm) :=
    Q'.le_of_lt (bulkProfile_pos
      (Nat.mul_pos (by decide) hm) (by omega))
  have hy0 : (0 : Q') <=
      bulkProfile (4 * m) ry (Nat.mul_pos (by decide) hm) :=
    Q'.le_of_lt (bulkProfile_pos
      (Nat.mul_pos (by decide) hm) (by omega))
  have hz0 : (0 : Q') <=
      bulkProfile (4 * m) rz (Nat.mul_pos (by decide) hm) :=
    Q'.le_of_lt (bulkProfile_pos
      (Nat.mul_pos (by decide) hm) (by omega))
  have hfloorSquare0 :
      (0 : Q') <= bulkProfileFloor * bulkProfileFloor :=
    Q'.mul_nonneg _ _ hfloor0 hfloor0
  have hinner :
      bulkProfileFloor * bulkProfileFloor <=
        bulkProfile (4 * m) ry (Nat.mul_pos (by decide) hm) *
          bulkProfile (4 * m) rz (Nat.mul_pos (by decide) hm) :=
    Q'.mul_le_mul_of_nonneg hy hz hy0 hfloor0
  have hcube :
      bulkProfileFloor * (bulkProfileFloor * bulkProfileFloor) <=
        bulkProfile (4 * m) rx (Nat.mul_pos (by decide) hm) *
          (bulkProfile (4 * m) ry (Nat.mul_pos (by decide) hm) *
            bulkProfile (4 * m) rz (Nat.mul_pos (by decide) hm)) :=
    Q'.mul_le_mul_of_nonneg hx hinner hx0 hfloorSquare0
  have hcube0 :
      (0 : Q') <= bulkProfileFloor *
        (bulkProfileFloor * bulkProfileFloor) :=
    Q'.mul_nonneg _ _ hfloor0 hfloorSquare0
  have hcoefficient0 :
      (0 : Q') <=
        bulkProfile (4 * m) rx (Nat.mul_pos (by decide) hm) *
          (bulkProfile (4 * m) ry (Nat.mul_pos (by decide) hm) *
            bulkProfile (4 * m) rz (Nat.mul_pos (by decide) hm)) :=
    Q'.mul_nonneg _ _ hx0 (Q'.mul_nonneg _ _ hy0 hz0)
  have hsquare := Q'.mul_le_mul_of_nonneg
    hcube hcube hcoefficient0 hcube0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv bulkProfileCubeSquareFloor_eqv)
    (by
      simpa only [bulkSourceCoefficient, bulkSourceFaceAt,
        Nat.add_sub_cancel_left] using hsquare)

private theorem listQSumMono
    {A : Type} (lower upper : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> lower item <= upper item) ->
      listQSum lower items <= listQSum upper items
  | [], _ => Q'.le_refl' 0
  | item :: rest, hbound =>
      Q'.add_le_add
        (hbound item List.mem_cons_self)
        (listQSumMono lower upper rest
          (fun other hother =>
            hbound other (List.mem_cons_of_mem item hother)))

private theorem listQSumSublistLe
    {A : Type} (value : A -> Q')
    (hnonnegative : forall item, (0 : Q') <= value item) :
    forall {source target : List A}, source <+ target ->
      listQSum value source <= listQSum value target
  | [], target, _ =>
      listQSum_nonnegative_on value target
        (fun item _ => hnonnegative item)
  | source, head :: target, List.Sublist.cons _ htail => by
      have hinduction := listQSumSublistLe value hnonnegative htail
      have htailLe :
          listQSum value target <=
            value head + listQSum value target := by
        exact Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg
            (listQSum value target) (value head) (hnonnegative head))
          (Q'.le_of_eqv
            (Q'.add_comm_eqv (listQSum value target) (value head)))
      exact Q'.le_trans' _ _ _ hinduction
        htailLe
  | _ :: source, _ :: target, List.Sublist.cons₂ item htail =>
      Q'.add_le_add (Q'.le_refl' (value item))
        (listQSumSublistLe value hnonnegative htail)

private theorem listQSumConst {A : Type} (constant : Q') :
    forall items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _item :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSumConst constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv _ _)

/-- The full source coefficient-square mass dominates the exact central
half-carrier contribution `3*(2*m)^3 * 3^(-36)`. -/
theorem bulkSourceCoefficientMass_central_floor
    (m : Nat) (hm : 0 < m) :
    Q'.ofNat (3 * (2 * m) ^ 3) * bulkCoefficientSquareFloor <=
      listQSum
        (fun face =>
          bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face *
            bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face)
        (bulkSourceFaces (4 * m)) := by
  let value := fun face =>
    bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face *
      bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face
  have hpointwise :
      listQSum (fun _face => bulkCoefficientSquareFloor)
          (centralBulkSourceFaces m) <=
        listQSum value (centralBulkSourceFaces m) := by
    apply listQSumMono
    intro face hface
    exact centralBulkSourceCoefficient_square_floor m hm hface
  have hconstant := listQSumConst bulkCoefficientSquareFloor
    (centralBulkSourceFaces m)
  have hcentral :
      Q'.ofNat (centralBulkSourceFaces m).length *
          bulkCoefficientSquareFloor <=
        listQSum value (centralBulkSourceFaces m) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconstant) hpointwise
  have hfull := listQSumSublistLe value
    (fun face => SumOfSquares.q_mul_self_nonneg
      (bulkSourceCoefficient (4 * m) (Nat.mul_pos (by decide) hm) face))
    (centralBulkSourceFaces_sublist m)
  rw [centralBulkSourceFaces_length] at hcentral
  exact Q'.le_trans' _ _ _ hcentral hfull

/-- PAPER normalized coefficient-mass floor. -/
def normalizedBulkCoefficientMassFloor : Q' :=
  Q'.mkPos 1 (8 * 3 ^ 36) (by decide)

private theorem normalizedFloor_count_eqv (m : Nat) :
    normalizedBulkCoefficientMassFloor *
        Q'.ofNat (3 * (4 * m) ^ 3) ≈
      Q'.ofNat (3 * (2 * m) ^ 3) * bulkCoefficientSquareFloor := by
  show
    (normalizedBulkCoefficientMassFloor *
      Q'.ofNat (3 * (4 * m) ^ 3)).num *
        ((Q'.ofNat (3 * (2 * m) ^ 3) *
          bulkCoefficientSquareFloor).den : Int) =
      (Q'.ofNat (3 * (2 * m) ^ 3) *
        bulkCoefficientSquareFloor).num *
        ((normalizedBulkCoefficientMassFloor *
          Q'.ofNat (3 * (4 * m) ^ 3)).den : Int)
  simp only [normalizedBulkCoefficientMassFloor,
    bulkCoefficientSquareFloor, Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  exact_mod_cast (by
    simp only [Nat.pow_succ, Nat.pow_zero]
    ac_rfl)

/-- Exact normalized coefficient-square mass at any positive side. -/
def normalizedBulkSourceCoefficientMassAtSide (side : Nat) (hside : 0 < side) : Q' :=
  Q'.divPos
    (listQSum
      (fun face =>
        bulkSourceCoefficient side hside face *
          bulkSourceCoefficient side hside face)
      (bulkSourceFaces side))
    (Q'.ofNat (3 * side ^ 3))
    (by
      show (0 : Int) * (1 : Int) <
        ((3 * side ^ 3 : Nat) : Int) * (1 : Int)
      rw [Int.zero_mul, Int.mul_one]
      exact_mod_cast Nat.mul_pos (by decide)
        (Nat.pow_pos hside))

/-- Exact normalized coefficient-square mass at a side `4*m`. -/
def normalizedBulkSourceCoefficientMass (m : Nat) (hm : 0 < m) : Q' :=
  normalizedBulkSourceCoefficientMassAtSide
    (4 * m) (Nat.mul_pos (by decide) hm)

/-- For every side divisible by four, the normalized exact rational
coefficient-square mass is at least `3^(-36)/8`. -/
theorem normalizedBulkSourceCoefficientMass_floor
    (m : Nat) (hm : 0 < m) :
    normalizedBulkCoefficientMassFloor <=
      normalizedBulkSourceCoefficientMass m hm := by
  unfold normalizedBulkSourceCoefficientMass
    normalizedBulkSourceCoefficientMassAtSide
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalizedFloor_count_eqv m))
    (bulkSourceCoefficientMass_central_floor m hm)

theorem normalizedBulkSourceCoefficientMassAtSide_one_floor :
    normalizedBulkCoefficientMassFloor <=
      normalizedBulkSourceCoefficientMassAtSide 1 (by decide) := by
  decide

theorem normalizedBulkSourceCoefficientMassAtSide_two_floor :
    normalizedBulkCoefficientMassFloor <=
      normalizedBulkSourceCoefficientMassAtSide 2 (by decide) := by
  decide

/-- The PAPER normalized coefficient-mass floor holds at every dyadic side. -/
theorem normalizedBulkSourceCoefficientMassAtSide_dyadic_floor :
    forall scale : Nat,
      normalizedBulkCoefficientMassFloor <=
        normalizedBulkSourceCoefficientMassAtSide
          (2 ^ scale) (Nat.pow_pos (by decide))
  | 0 => normalizedBulkSourceCoefficientMassAtSide_one_floor
  | 1 => normalizedBulkSourceCoefficientMassAtSide_two_floor
  | scale + 2 => by
      have hside : 2 ^ (scale + 2) = 4 * 2 ^ scale := by
        rw [show scale + 2 = scale + 1 + 1 by omega,
          Nat.pow_succ, Nat.pow_succ]
        rw [show (4 : Nat) = 2 * 2 by decide]
        ac_rfl
      simpa only [normalizedBulkSourceCoefficientMass, hside] using
        normalizedBulkSourceCoefficientMass_floor
          (2 ^ scale) (Nat.pow_pos (by decide))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.cubicEulerShift
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.bulkProfileNumerator_central_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.bulkProfileDenominator_pow_central_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.bulkProfile_central_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.centralBulkSourceFaces_sublist
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.centralBulkSourceFaces_length
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.centralBulkSourceCoefficient_square_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.bulkSourceCoefficientMass_central_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.normalizedBulkSourceCoefficientMass_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkProfileFloor.normalizedBulkSourceCoefficientMassAtSide_dyadic_floor
