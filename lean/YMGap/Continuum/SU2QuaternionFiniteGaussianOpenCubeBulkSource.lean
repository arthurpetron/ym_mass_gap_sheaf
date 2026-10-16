/-
# Explicit rational bulk source on the internal comb carrier

This leaf encodes the formula-level PAPER bulk source used by the finite
open-cube Gaussian benchmark. At side `s` its ambient width is `s^2+1`, its
base cube is the `s`-by-`s`-by-`s` block beginning at `(s^2-s)/2`, and all
three spatial plaquette orientations carry the same rational product profile.

The source is an explicit duplicate-free enumeration with exactly `3*s^3`
faces, and membership is equivalent to the intended internal-face coordinate
filter; `idxOf` therefore gives a checked comb-face index. Its
coefficient-square mass is strictly positive. Finally the same finite source
is placed at two history times and fed to the checked weighted three-color
comb-curl covariance identity. The heavyweight original `spatialFaces`
equality, global trajectory and fringe-action compilers are intentionally not
imported here; these finite fields are exactly the data needed by those later
consumers.

No coefficient-profile uniform floor, positive cross-time covariance floor,
mode estimate, original/free comparison, continuum limit or mass gap is proved.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalFreeHistoryQuadratic
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Original ambient width used by the bulk source at side `s`. -/
def bulkSourceWidth (s : Nat) : Nat := s * s + 1

/-- Lower coordinate of the centered integer bulk cube. -/
def bulkSourceOffset (s : Nat) : Nat := (s * s - s) / 2

/-- Coordinate support of the bulk source; the surrounding face list already
enforces time zero and one of the three spatial orientations. -/
def BulkSourceBase (s : Nat) (face : Z4Plaq) : Prop :=
  bulkSourceOffset s ≤ face.1.1 ∧
  face.1.1 < bulkSourceOffset s + s ∧
  bulkSourceOffset s ≤ face.1.2.1 ∧
  face.1.2.1 < bulkSourceOffset s + s ∧
  bulkSourceOffset s ≤ face.1.2.2.1 ∧
  face.1.2.2.1 < bulkSourceOffset s + s

instance (s : Nat) (face : Z4Plaq) : Decidable (BulkSourceBase s face) := by
  unfold BulkSourceBase
  infer_instance

theorem bulkSourceOffset_add_side_le_square
    (s : Nat) (hs : 0 < s) : bulkSourceOffset s + s ≤ s * s := by
  have hsle : s ≤ s * s := by
    calc
      s = s * 1 := by omega
      _ ≤ s * s := Nat.mul_le_mul_left s hs
  have hsub : s * s - s + s = s * s := Nat.sub_add_cancel hsle
  have hdiv : (s * s - s) / 2 ≤ s * s - s := Nat.div_le_self _ _
  unfold bulkSourceOffset
  omega

/-- The three spatial orientations used by the bulk source. -/
def bulkSourcePlanes : List Z4Plane := [.p01, .p02, .p12]

/-- One explicitly offset bulk-source face. -/
def bulkSourceFaceAt
    (s rx ry rz : Nat) (plane : Z4Plane) : Z4Plaq :=
  ((bulkSourceOffset s + rx,
    bulkSourceOffset s + ry,
    bulkSourceOffset s + rz, 0), plane)

/-- Formula-level bulk source in offset-lexicographic order. -/
def bulkSourceFaces (s : Nat) : List Z4Plaq :=
  (List.range s).flatMap fun rx =>
    (List.range s).flatMap fun ry =>
      (List.range s).flatMap fun rz =>
        bulkSourcePlanes.map (bulkSourceFaceAt s rx ry rz)

private theorem range_nodup_local : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨range_nodup_local n,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = n := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact (Nat.lt_irrefl n) (List.mem_range.mp hleft)

private theorem nodup_map_inj_local
    {A B : Type} (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_inj_local map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective _ _ heq) ▸ hitem)

private theorem nodup_flatMap_tagged_local
    {A B : Type} (key : A → B) (block : B → List A)
    (hblock : ∀ tag, (block tag).Nodup)
    (htag : ∀ tag item, item ∈ block tag → key item = tag) :
    ∀ {tags : List B}, tags.Nodup → (tags.flatMap block).Nodup
  | [], _ => List.nodup_nil
  | tag :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      rw [List.flatMap_cons]
      refine List.nodup_append.mpr
        ⟨hblock tag,
          nodup_flatMap_tagged_local key block hblock htag hparts.2, ?_⟩
      intro left hleft right hright heq
      obtain ⟨otherTag, hotherTag, hrightBlock⟩ :=
        List.mem_flatMap.mp hright
      have hleftTag := htag tag left hleft
      have hrightTag := htag otherTag right hrightBlock
      rw [heq, hrightTag] at hleftTag
      exact hparts.1 (hleftTag ▸ hotherTag)

private theorem length_flatMap_const_local
    {A B : Type} (block : A → List B) (count : Nat)
    (hlength : ∀ item, (block item).length = count) :
    ∀ items : List A,
      (items.flatMap block).length = items.length * count
  | [] => by simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | head :: tail => by
      rw [List.flatMap_cons, List.length_append, hlength head,
        length_flatMap_const_local block count hlength tail,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem bulkSourcePlanes_nodup : bulkSourcePlanes.Nodup := by decide

private theorem bulkSourceFaceAt_internal
    {s rx ry rz : Nat} {plane : Z4Plane}
    (hrx : rx < s) (hry : ry < s) (hrz : rz < s)
    (hplane : plane ∈ bulkSourcePlanes) :
    bulkSourceFaceAt s rx ry rz plane ∈
      internalOpenCubeFaces (bulkSourceWidth s) := by
  have hs : 0 < s := Nat.zero_lt_of_lt hrx
  have hlimit := bulkSourceOffset_add_side_le_square s hs
  apply (internalOpenCubeFaces_mem_iff (bulkSourceWidth s) _).mpr
  simp only [bulkSourcePlanes, List.mem_cons, List.not_mem_nil,
    or_false] at hplane
  rcases hplane with rfl | rfl | rfl
  · change 0 = 0 ∧
      bulkSourceOffset s + rx + 1 < bulkSourceWidth s ∧
      bulkSourceOffset s + ry + 1 < bulkSourceWidth s ∧
      bulkSourceOffset s + rz < bulkSourceWidth s
    unfold bulkSourceWidth
    exact ⟨rfl, by omega, by omega, by omega⟩
  · change 0 = 0 ∧
      bulkSourceOffset s + rx + 1 < bulkSourceWidth s ∧
      bulkSourceOffset s + ry < bulkSourceWidth s ∧
      bulkSourceOffset s + rz + 1 < bulkSourceWidth s
    unfold bulkSourceWidth
    exact ⟨rfl, by omega, by omega, by omega⟩
  · change 0 = 0 ∧
      bulkSourceOffset s + rx < bulkSourceWidth s ∧
      bulkSourceOffset s + ry + 1 < bulkSourceWidth s ∧
      bulkSourceOffset s + rz + 1 < bulkSourceWidth s
    unfold bulkSourceWidth
    exact ⟨rfl, by omega, by omega, by omega⟩

private theorem bulkSourceFaceAt_base
    {s rx ry rz : Nat} {plane : Z4Plane}
    (hrx : rx < s) (hry : ry < s) (hrz : rz < s) :
    BulkSourceBase s (bulkSourceFaceAt s rx ry rz plane) := by
  unfold BulkSourceBase bulkSourceFaceAt
  dsimp only
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hrx _,
    Nat.le_add_right _ _, Nat.add_lt_add_left hry _,
    Nat.le_add_right _ _, Nat.add_lt_add_left hrz _⟩

private theorem internalOpenCubeFace_time_plane
    {width : Nat} (face : Z4Plaq)
    (hface : InternalOpenCubeFace width face) :
    face.1.2.2.2 = 0 ∧ face.2 ∈ bulkSourcePlanes := by
  rcases face with ⟨⟨x, y, z, time⟩, plane⟩
  cases plane with
  | p01 => exact ⟨hface.1, by simp [bulkSourcePlanes]⟩
  | p02 => exact ⟨hface.1, by simp [bulkSourcePlanes]⟩
  | p03 => exact False.elim hface.2
  | p12 => exact ⟨hface.1, by simp [bulkSourcePlanes]⟩
  | p13 => exact False.elim hface.2
  | p23 => exact False.elim hface.2

theorem bulkSourceFaces_mem_iff (s : Nat) (face : Z4Plaq) :
    face ∈ bulkSourceFaces s ↔
      face ∈ internalOpenCubeFaces (bulkSourceWidth s) ∧
        BulkSourceBase s face := by
  constructor
  · intro hface
    have hraw := hface
    unfold bulkSourceFaces at hraw
    obtain ⟨rx, hrx, hraw⟩ := List.mem_flatMap.mp hraw
    obtain ⟨ry, hry, hraw⟩ := List.mem_flatMap.mp hraw
    obtain ⟨rz, hrz, hraw⟩ := List.mem_flatMap.mp hraw
    obtain ⟨plane, hplane, rfl⟩ := List.mem_map.mp hraw
    exact ⟨bulkSourceFaceAt_internal
        (List.mem_range.mp hrx) (List.mem_range.mp hry)
        (List.mem_range.mp hrz) hplane,
      bulkSourceFaceAt_base
        (List.mem_range.mp hrx) (List.mem_range.mp hry)
        (List.mem_range.mp hrz)⟩
  · rcases face with ⟨⟨x, y, z, time⟩, plane⟩
    rintro ⟨hinternal, hbase⟩
    obtain ⟨htime, hplane⟩ := internalOpenCubeFace_time_plane
      (((x, y, z, time), plane) : Z4Plaq)
      ((internalOpenCubeFaces_mem_iff (bulkSourceWidth s) _).mp hinternal)
    change time = 0 at htime
    change plane ∈ bulkSourcePlanes at hplane
    unfold BulkSourceBase at hbase
    dsimp only at hbase
    obtain ⟨hbx0, hbx1, hby0, hby1, hbz0, hbz1⟩ := hbase
    unfold bulkSourceFaces
    apply List.mem_flatMap.mpr
    refine ⟨x - bulkSourceOffset s,
      List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨y - bulkSourceOffset s,
      List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨z - bulkSourceOffset s,
      List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    refine ⟨plane, hplane, ?_⟩
    unfold bulkSourceFaceAt
    rw [Nat.add_sub_of_le hbx0, Nat.add_sub_of_le hby0,
      Nat.add_sub_of_le hbz0, htime]

theorem bulkSourceFaces_nodup (s : Nat) : (bulkSourceFaces s).Nodup := by
  unfold bulkSourceFaces
  have hrange := range_nodup_local s
  apply nodup_flatMap_tagged_local
    (fun face : Z4Plaq => face.1.1 - bulkSourceOffset s) _ _ _ hrange
  · intro rx
    apply nodup_flatMap_tagged_local
      (fun face : Z4Plaq => face.1.2.1 - bulkSourceOffset s) _ _ _ hrange
    · intro ry
      apply nodup_flatMap_tagged_local
        (fun face : Z4Plaq => face.1.2.2.1 - bulkSourceOffset s) _ _ _ hrange
      · intro rz
        apply nodup_map_inj_local
          (bulkSourceFaceAt s rx ry rz)
          (fun left right heq => congrArg Prod.snd heq)
          bulkSourcePlanes_nodup
      · intro rz face hface
        obtain ⟨plane, _, rfl⟩ := List.mem_map.mp hface
        simp only [bulkSourceFaceAt, Nat.add_sub_cancel_left]
    · intro ry face hface
      obtain ⟨rz, _, hface⟩ := List.mem_flatMap.mp hface
      obtain ⟨plane, _, rfl⟩ := List.mem_map.mp hface
      simp only [bulkSourceFaceAt, Nat.add_sub_cancel_left]
  · intro rx face hface
    obtain ⟨ry, _, hface⟩ := List.mem_flatMap.mp hface
    obtain ⟨rz, _, hface⟩ := List.mem_flatMap.mp hface
    obtain ⟨plane, _, rfl⟩ := List.mem_map.mp hface
    simp only [bulkSourceFaceAt, Nat.add_sub_cancel_left]

/-- The formula-level bulk source has exactly three oriented faces per point
of its `s`-by-`s`-by-`s` coordinate block. -/
theorem bulkSourceFaces_length (s : Nat) :
    (bulkSourceFaces s).length = s * (s * (s * 3)) := by
  unfold bulkSourceFaces
  rw [length_flatMap_const_local _ (s * (s * 3))]
  · rw [List.length_range]
  · intro rx
    rw [length_flatMap_const_local _ (s * 3)]
    · rw [List.length_range]
    · intro ry
      rw [length_flatMap_const_local _ 3]
      · rw [List.length_range]
      · intro rz
        rfl

theorem bulkSourceFaces_length_cube (s : Nat) :
    (bulkSourceFaces s).length = 3 * s ^ 3 := by
  rw [bulkSourceFaces_length]
  simp only [Nat.pow_succ, Nat.pow_zero]
  ac_rfl

/-- Every bulk source face belongs to the formula-level internal open cube. -/
theorem bulkSourceFace_internal
    {s : Nat} {face : Z4Plaq}
    (hface : face ∈ bulkSourceFaces s) :
    face ∈ internalOpenCubeFaces (bulkSourceWidth s) :=
  (bulkSourceFaces_mem_iff s face).mp hface |>.1

/-- Total lookup of a bulk source face. -/
def selectedBulkSourceFace (s faceIndex : Nat) : Z4Plaq :=
  (bulkSourceFaces s).getD faceIndex ((0, 0, 0, 0), .p01)

theorem selectedBulkSourceFace_mem
    {s faceIndex : Nat} (hface : faceIndex < (bulkSourceFaces s).length) :
    selectedBulkSourceFace s faceIndex ∈ bulkSourceFaces s := by
  rw [selectedBulkSourceFace, ← List.getElem_eq_getD (h := hface)]
  exact List.getElem_mem hface

/-- Internal comb-face index of an enumerated original bulk source face. -/
def bulkSourceInternalFaceIndex (s faceIndex : Nat) : Nat :=
  (internalOpenCubeFaces (bulkSourceWidth s)).idxOf
    (selectedBulkSourceFace s faceIndex)

/-- The internal-face lookup at the mapped index recovers the exact original
bulk source face. -/
theorem selectedInternalOpenCubeFace_bulkSourceIndex
    {s faceIndex : Nat}
    (hface : faceIndex < (bulkSourceFaces s).length) :
    selectedInternalOpenCubeFace (bulkSourceWidth s)
        (bulkSourceInternalFaceIndex s faceIndex) =
      selectedBulkSourceFace s faceIndex := by
  exact selectedInternalOpenCubeFace_idxOf
    (bulkSourceFace_internal (selectedBulkSourceFace_mem hface))

/-- Numerator `v_s(r)` of the one-dimensional rational profile. -/
def bulkProfileNumerator (s r : Nat) : Nat :=
  (2 * r + 1) * (2 * s - 2 * r - 1)

/-- Positive denominator `4*s+v_s(r)`. -/
def bulkProfileDenominator (s r : Nat) : Nat :=
  4 * s + bulkProfileNumerator s r

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  change (0 : Int) * 1 < (n : Int) * 1
  simp only [Int.mul_one]
  exact_mod_cast hn

theorem bulkProfileDenominator_pos (s r : Nat) (hs : 0 < s) :
    (0 : Q') < Q'.ofNat (bulkProfileDenominator s r) := by
  apply ofNat_pos_of_pos
  unfold bulkProfileDenominator
  have hfour : 0 < 4 * s := Nat.mul_pos (by decide) hs
  omega

private theorem qpow_pos (value : Q') (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by rw [Q'.pow_zero]; decide
  | exponent + 1 => Q'.mul_pos hvalue (qpow_pos value hvalue exponent)

/-- One-dimensional rational profile
`(v_s(r)/(4*s+v_s(r)))^s`. -/
def bulkProfile (s r : Nat) (hs : 0 < s) : Q' :=
  (Q'.divPos
    (Q'.ofNat (bulkProfileNumerator s r))
    (Q'.ofNat (bulkProfileDenominator s r))
    (bulkProfileDenominator_pos s r hs)) ^ s

theorem bulkProfile_pos
    {s r : Nat} (hs : 0 < s) (hr : r < s) :
    (0 : Q') < bulkProfile s r hs := by
  have hnumerator : 0 < bulkProfileNumerator s r := by
    unfold bulkProfileNumerator
    apply Nat.mul_pos
    · omega
    · omega
  unfold bulkProfile
  apply qpow_pos
  exact Q'.divPos_pos _ _ (bulkProfileDenominator_pos s r hs)
    (ofNat_pos_of_pos hnumerator)

/-- Three-dimensional product coefficient, identical in all spatial
orientations. It is consumed only on `bulkSourceFaces s`. -/
def bulkSourceCoefficient (s : Nat) (hs : 0 < s) (face : Z4Plaq) : Q' :=
  bulkProfile s (face.1.1 - bulkSourceOffset s) hs *
    (bulkProfile s (face.1.2.1 - bulkSourceOffset s) hs *
      bulkProfile s (face.1.2.2.1 - bulkSourceOffset s) hs)

theorem bulkSourceCoefficient_pos
    {s : Nat} (hs : 0 < s) {face : Z4Plaq}
    (hface : face ∈ bulkSourceFaces s) :
    (0 : Q') < bulkSourceCoefficient s hs face := by
  have hbulk := (bulkSourceFaces_mem_iff s face).mp hface |>.2
  obtain ⟨hbx0, hbx1, hby0, hby1, hbz0, hbz1⟩ := hbulk
  have hrx : face.1.1 - bulkSourceOffset s < s := by omega
  have hry : face.1.2.1 - bulkSourceOffset s < s := by omega
  have hrz : face.1.2.2.1 - bulkSourceOffset s < s := by omega
  unfold bulkSourceCoefficient
  exact Q'.mul_pos (bulkProfile_pos hs hrx)
    (Q'.mul_pos (bulkProfile_pos hs hry) (bulkProfile_pos hs hrz))

/-- A concrete listed face witnessing nonempty positive coefficient mass. -/
def bulkSourceLowerFace (s : Nat) : Z4Plaq :=
  ((bulkSourceOffset s, bulkSourceOffset s, bulkSourceOffset s, 0), .p01)

private theorem bulkSourceLowerFace_internal (s : Nat) (hs : 0 < s) :
    bulkSourceLowerFace s ∈ internalOpenCubeFaces (bulkSourceWidth s) := by
  have hlimit := bulkSourceOffset_add_side_le_square s hs
  apply (internalOpenCubeFaces_mem_iff (bulkSourceWidth s) _).mpr
  change 0 = 0 ∧
    bulkSourceOffset s + 1 < bulkSourceWidth s ∧
    bulkSourceOffset s + 1 < bulkSourceWidth s ∧
    bulkSourceOffset s < bulkSourceWidth s
  unfold bulkSourceWidth
  exact ⟨rfl, by omega, by omega, by omega⟩

private theorem bulkSourceLowerFace_base (s : Nat) (hs : 0 < s) :
    BulkSourceBase s (bulkSourceLowerFace s) := by
  unfold BulkSourceBase bulkSourceLowerFace
  dsimp only
  exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right hs,
    Nat.le_refl _, Nat.lt_add_of_pos_right hs,
    Nat.le_refl _, Nat.lt_add_of_pos_right hs⟩

theorem bulkSourceLowerFace_mem (s : Nat) (hs : 0 < s) :
    bulkSourceLowerFace s ∈ bulkSourceFaces s :=
  (bulkSourceFaces_mem_iff s _).mpr
    ⟨bulkSourceLowerFace_internal s hs, bulkSourceLowerFace_base s hs⟩

theorem bulkSourceLowerFace_coefficient (s : Nat) (hs : 0 < s) :
    bulkSourceCoefficient s hs (bulkSourceLowerFace s) =
      bulkProfile s 0 hs * (bulkProfile s 0 hs * bulkProfile s 0 hs) := by
  unfold bulkSourceCoefficient bulkSourceLowerFace
  simp only [Nat.sub_self]

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      value witness ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have htailLe := listQSum_member_le_nonnegative_local
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail
        have hsumLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ htailLe hsumLe

private theorem listQSum_pos_of_mem_local
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      (0 : Q') < value witness →
      (0 : Q') < listQSum value items
  | [], _, _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem, hwitness => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.pos_of_lt_of_le hwitness
          (Q'.add_le_self_of_nonneg
            (value head) (listQSum value tail)
            (listQSum_nonnegative_on value tail
              (fun item hitem =>
                hnonnegative item (List.mem_cons_of_mem head hitem))))
      · have htailPositive := listQSum_pos_of_mem_local
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail hwitness
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.pos_of_lt_of_le htailPositive htailLe

/-- The explicit source has strictly positive coefficient-square mass at every
positive side. This is finite coefficient mass, not an OS-norm floor. -/
theorem bulkSourceCoefficientMass_pos (s : Nat) (hs : 0 < s) :
    (0 : Q') < listQSum
      (fun face =>
        bulkSourceCoefficient s hs face * bulkSourceCoefficient s hs face)
      (bulkSourceFaces s) := by
  apply listQSum_pos_of_mem_local
    (fun face =>
      bulkSourceCoefficient s hs face * bulkSourceCoefficient s hs face)
    (bulkSourceFaces s)
  · intro face hface
    exact Q'.le_of_lt (Q'.mul_pos
      (bulkSourceCoefficient_pos hs hface)
      (bulkSourceCoefficient_pos hs hface))
  · exact bulkSourceLowerFace_mem s hs
  · exact Q'.mul_pos
      (bulkSourceCoefficient_pos hs (bulkSourceLowerFace_mem s hs))
      (bulkSourceCoefficient_pos hs (bulkSourceLowerFace_mem s hs))

/-- A fully explicit side-dependent lower bound for the source
coefficient-square mass. The uniform profile bound remains separate. -/
theorem bulkSourceCoefficientMass_lowerFaceSquare (s : Nat) (hs : 0 < s) :
    bulkSourceCoefficient s hs (bulkSourceLowerFace s) *
        bulkSourceCoefficient s hs (bulkSourceLowerFace s) ≤
      listQSum
        (fun face =>
          bulkSourceCoefficient s hs face * bulkSourceCoefficient s hs face)
        (bulkSourceFaces s) := by
  apply listQSum_member_le_nonnegative_local
  · intro face hface
    exact Q'.le_of_lt (Q'.mul_pos
      (bulkSourceCoefficient_pos hs hface)
      (bulkSourceCoefficient_pos hs hface))
  · exact bulkSourceLowerFace_mem s hs

/-- Source coefficient as a total function of the enumerated face index. -/
def bulkSourceIndexWeight (s : Nat) (hs : 0 < s) (faceIndex : Nat) : Q' :=
  bulkSourceCoefficient s hs (selectedBulkSourceFace s faceIndex)

theorem bulkSourceIndexWeight_pos
    {s faceIndex : Nat} (hs : 0 < s)
    (hface : faceIndex < (bulkSourceFaces s).length) :
    (0 : Q') < bulkSourceIndexWeight s hs faceIndex :=
  bulkSourceCoefficient_pos hs (selectedBulkSourceFace_mem hface)

/-- Three-color Heron-pulled curl row for the actual bulk source face at one
history time. -/
def bulkSourceHeronColorCurlRow
    (timeBonds s stage time rowIndex coordinate : Nat) : Q' :=
  combGaugeFreeHistoryHeronColorCurlRow
    timeBonds (bulkSourceWidth s) stage
    (fun _ => time) (bulkSourceInternalFaceIndex s) rowIndex coordinate

/-- Literal weighted radial source polynomial at one history time. -/
def bulkSourceHeronRadialSquare
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) : RatPoly :=
  combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    timeBonds (bulkSourceWidth s) stage (bulkSourceFaces s).length
    (bulkSourceIndexWeight s hs) (fun _ => time)
    (bulkSourceInternalFaceIndex s)

/-- Actual finite Gaussian covariance of the same explicit bulk source placed
at two history times. -/
def bulkSourceHeronRadialPairCovariance
    (timeBonds s : Nat) (hs : 0 < s)
    (stage sourceTime directionTime : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount (bulkSourceWidth s))
  finiteGaussianCovariance
    (coordinateCount + (coordinateCount + coordinateCount))
    (bulkSourceHeronRadialSquare timeBonds s hs stage sourceTime)
    (bulkSourceHeronRadialSquare timeBonds s hs stage directionTime)

/-- The corresponding explicit weighted cross-Gram-square trace. -/
def bulkSourceHeronCrossGramSquareTrace
    (timeBonds s : Nat) (hs : 0 < s)
    (stage sourceTime directionTime : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount (bulkSourceWidth s))
  finiteWeightedCrossGramSquareTrace
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * (bulkSourceFaces s).length) (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (bulkSourceHeronColorCurlRow timeBonds s stage sourceTime)
    (bulkSourceHeronColorCurlRow timeBonds s stage directionTime)

/-- Checked square-root-free covariance identity for the formula-level rational bulk
source at two time placements. The remaining denominator problem is a positive
lower bound for this exact weighted trace (or its exact-covariance limit). -/
theorem bulkSourceHeronRadialPairCovariance_trace
    (timeBonds s : Nat) (hs : 0 < s)
    (stage sourceTime directionTime : Nat) :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount (bulkSourceWidth s))
    finiteGaussianCovariance
        (coordinateCount + (coordinateCount + coordinateCount))
        (combGaugeFreeHistoryHeronWeightedCurlRadialSquare
          timeBonds (bulkSourceWidth s) stage (bulkSourceFaces s).length
          (bulkSourceIndexWeight s hs) (fun _ => sourceTime)
          (bulkSourceInternalFaceIndex s))
        (combGaugeFreeHistoryHeronWeightedCurlRadialSquare
          timeBonds (bulkSourceWidth s) stage (bulkSourceFaces s).length
          (bulkSourceIndexWeight s hs) (fun _ => directionTime)
          (bulkSourceInternalFaceIndex s)) ≈
      2 * finiteWeightedCrossGramSquareTrace
        (coordinateCount + (coordinateCount + coordinateCount))
        (3 * (bulkSourceFaces s).length) (3 * (bulkSourceFaces s).length)
        (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
        (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
        (combGaugeFreeHistoryHeronColorCurlRow
          timeBonds (bulkSourceWidth s) stage
          (fun _ => sourceTime) (bulkSourceInternalFaceIndex s))
        (combGaugeFreeHistoryHeronColorCurlRow
          timeBonds (bulkSourceWidth s) stage
          (fun _ => directionTime) (bulkSourceInternalFaceIndex s)) := by
  exact combGaugeFreeHistoryHeronWeightedCurlRadialPairCovariance_trace
    timeBonds (bulkSourceWidth s) stage
    (bulkSourceFaces s).length (bulkSourceFaces s).length
    (bulkSourceIndexWeight s hs) (bulkSourceIndexWeight s hs)
    (fun _ => sourceTime) (bulkSourceInternalFaceIndex s)
    (fun _ => directionTime) (bulkSourceInternalFaceIndex s)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceFace_internal
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceFaces_mem_iff
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceFaces_nodup
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceFaces_length
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceFaces_length_cube
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceOffset_add_side_le_square
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.selectedInternalOpenCubeFace_bulkSourceIndex
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceCoefficient_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceLowerFace_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceLowerFace_coefficient
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceCoefficientMass_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceCoefficientMass_lowerFaceSquare
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource.bulkSourceHeronRadialPairCovariance_trace
