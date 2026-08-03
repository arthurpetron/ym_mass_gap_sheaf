/-
# Embed the 128 binary surfaces in the actual cutoff-one BF4 slab

`BF4CutoffOneBinarySurfaceCertificate` uses the compact 24-face ordering of
the unit four-cube.  The exact BF4 integrand uses the 72-face corrected slab
and 116 literal link blocks.  This module embeds the compact masks into that
ordering and checks closure against the actual oriented plaquette boundaries.

This proves the finite incidence-reindexing bridge: every one of the 128
certified masks is a genuine closed cutoff-one slab label, and every bounded
literal slab mask satisfying even incidence occurs in that list.  The proof
uses a rank-65 GF(2) elimination certificate and reconstructs all pivot bits
from the seven free coordinates.

## Axiom gate

Finite list/bit-mask kernel computation only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or `noncomputable`
declaration.
-/

import YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
import YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

namespace YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding

open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

/-- The compact 24-face order embedded in the literal 72-face slab order. -/
def activeHypercubeSlabFaceIds : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13,
   15, 19, 20, 23, 25, 29, 39, 40, 41, 44, 49, 59]

def embedSurfaceMaskFrom (compactMask start : Nat) : List Nat → Nat
  | [] => 0
  | faceId :: rest =>
      (if compactMask.testBit start then 2 ^ faceId else 0) +
        embedSurfaceMaskFrom compactMask (start + 1) rest

/-- Embed one 24-bit mask in the exact corrected-slab face ordering. -/
def embedBinarySurfaceMask (compactMask : Nat) : Nat :=
  embedSurfaceMaskFrom compactMask 0 activeHypercubeSlabFaceIds

def embeddedBinarySurfaceMasks : List Nat :=
  binarySurfaceMasks.map embedBinarySurfaceMask

/-- Whether a literal slab plaquette contains the link at one block index. -/
def slabFaceMeetsBlock (block : Nat)
    (face : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq) : Bool :=
  (orientedPlaquetteBoundary face).any fun entry =>
    decide ((boundaryCompleteSlabLinks 1).idxOf entry.link = block)

def sumFaceBits (block : Nat) :
    List (Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Plaq) → Nat
  | [] => 0
  | indexedFace :: rest =>
      (if slabFaceMeetsBlock block indexedFace.2
        then 2 ^ indexedFace.1 else 0) +
        sumFaceBits block rest

def enumerateSlabFacesFrom :
    Nat →
      List YMGap.Continuum.ClusterCount4DProgress.Z4Plaq →
      List (Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Plaq)
  | _, [] => []
  | index, face :: rest =>
      (index, face) :: enumerateSlabFacesFrom (index + 1) rest

/-- The 72-bit face-incidence row of one actual slab link block. -/
def slabEdgeFaceIncidenceMask (block : Nat) : Nat :=
  sumFaceBits block
    (enumerateSlabFacesFrom 0 (boundaryCompleteSlabPlaquettes 1))

def slabMaskIntersectionCount (carrier mask : Nat) : Nat :=
  ((List.range 72).filter fun faceId =>
    carrier.testBit faceId && mask.testBit faceId).length

/-- Literal mod-two closure on all 116 corrected-slab link blocks. -/
def slabSurfaceIsClosed (mask : Nat) : Bool :=
  (List.range (boundaryCompleteSlabLinks 1).length).all fun block =>
    decide (slabMaskIntersectionCount
      (slabEdgeFaceIncidenceMask block) mask % 2 = 0)

def embeddedSurfaceLabelling (compactMask : Nat) : EdgeLabelling :=
  fun faceId => if (embedBinarySurfaceMask compactMask).testBit faceId then 1 else 0

theorem activeHypercubeSlabFaceIds_spec :
    activeHypercubeSlabFaceIds.length = 24 ∧
    activeHypercubeSlabFaceIds.Nodup ∧
    activeHypercubeSlabFaceIds.all (fun faceId => decide (faceId < 72)) = true := by
  decide

/-- The seven compact generators have these exact 72-face embeddings. -/
theorem embeddedBinarySurfaceBasis_exact :
    binarySurfaceBasis.map embedBinarySurfaceMask =
      [18691732308373, 2199023257766, 8397112, 17592219632064,
       562950490335744, 576460752883810304, 577045142733586432] := by
  decide

/-- All 128 compact masks embed injectively and satisfy the literal 116-link
closure equations of the corrected slab. -/
theorem embeddedBinarySurfaceMasks_sound :
    embeddedBinarySurfaceMasks.length = 128 ∧
    embeddedBinarySurfaceMasks.Nodup ∧
    embeddedBinarySurfaceMasks.all slabSurfaceIsClosed = true := by
  decide

/-- Embedding preserves the number of selected faces on the full certified
surface list. -/
theorem embeddedBinarySurfaceMasks_preserve_face_count :
    binarySurfaceMasks.all (fun mask =>
      decide (slabMaskIntersectionCount ((2 ^ 72) - 1)
        (embedBinarySurfaceMask mask) = surfaceFaceCount mask)) = true := by
  decide

/-- The two vacuum-row surfaces in actual slab coordinates. -/
theorem embeddedVacuumRowSurfaceMasks_exact :
    vacuumRowSurfaceMasks.map embedBinarySurfaceMask =
      [0, 17592219632064] := by
  decide

theorem embeddedSurfaceLabelling_le_one (compactMask faceId : Nat) :
    embeddedSurfaceLabelling compactMask faceId ≤ 1 := by
  unfold embeddedSurfaceLabelling
  split <;> decide

/-! ## Executable rank-65 elimination certificate -/

/-- Reduce a GF(2) row against a descending-pivot XOR basis. -/
def reduceXorRow : Nat → List (Nat × Nat) → Nat
  | row, [] => row
  | row, pivotRow :: rest =>
      reduceXorRow
        (if row.testBit pivotRow.1 then Nat.xor row pivotRow.2 else row)
        rest

def highestSetBitBelow : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, row =>
      if row.testBit width then width else highestSetBitBelow width row

/-- Insert one nonzero row while keeping pivots in descending order. -/
def insertXorPivotRow (entry : Nat × Nat) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => [entry]
  | head :: rest =>
      if head.1 < entry.1
      then entry :: head :: rest
      else head :: insertXorPivotRow entry rest

def buildXorEchelon (width : Nat) :
    List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], basis => basis
  | row :: rest, basis =>
      let reduced := reduceXorRow row basis
      let updated :=
        if reduced = 0 then basis
        else insertXorPivotRow
          (highestSetBitBelow width reduced, reduced) basis
      buildXorEchelon width rest updated

/-- GF(2) dot parity of the low `width` bits. -/
def xorDotBelow : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | width + 1, left, right =>
      ((left.testBit width && right.testBit width) ^^
        xorDotBelow width left right)

/-- Recursive count used to relate Boolean XOR parity to the original
list-based incidence count. -/
def bitIntersectionCountBelow : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | width + 1, left, right =>
      (if left.testBit width && right.testBit width then 1 else 0) +
        bitIntersectionCountBelow width left right

theorem xorDotBelow_false_iff_even : ∀ width left right,
    xorDotBelow width left right = false ↔
      bitIntersectionCountBelow width left right % 2 = 0
  | 0, _, _ => by simp [xorDotBelow, bitIntersectionCountBelow]
  | width + 1, left, right => by
      simp only [xorDotBelow, bitIntersectionCountBelow]
      have induction := xorDotBelow_false_iff_even width left right
      generalize (left.testBit width && right.testBit width) = bit
      generalize xorDotBelow width left right = tail at induction ⊢
      generalize bitIntersectionCountBelow width left right = count at induction ⊢
      cases bit <;> cases tail <;> simp_all <;> omega

def listIntersectionCountBelow (width left right : Nat) : Nat :=
  ((List.range width).filter fun bit =>
    left.testBit bit && right.testBit bit).length

theorem listIntersectionCountBelow_eq_recursive : ∀ width left right,
    listIntersectionCountBelow width left right =
      bitIntersectionCountBelow width left right
  | 0, _, _ => by simp [listIntersectionCountBelow, bitIntersectionCountBelow]
  | width + 1, left, right => by
      unfold listIntersectionCountBelow
      rw [List.range_succ, List.filter_append, List.length_append]
      change listIntersectionCountBelow width left right +
          (List.filter (fun bit =>
            left.testBit bit && right.testBit bit) [width]).length = _
      rw [listIntersectionCountBelow_eq_recursive]
      simp only [bitIntersectionCountBelow]
      simp only [List.filter_cons, List.filter_nil]
      generalize (left.testBit width && right.testBit width) = bit
      cases bit <;> simp <;> omega

theorem xorDotBelow_false_iff_list_even (width left right : Nat) :
    xorDotBelow width left right = false ↔
      listIntersectionCountBelow width left right % 2 = 0 := by
  rw [listIntersectionCountBelow_eq_recursive]
  exact xorDotBelow_false_iff_even width left right

theorem slabMaskIntersectionCount_eq_list (carrier mask : Nat) :
    slabMaskIntersectionCount carrier mask =
      listIntersectionCountBelow 72 carrier mask := by
  rfl

def XorOrthogonal (width row mask : Nat) : Prop :=
  xorDotBelow width row mask = false

instance (width row mask : Nat) : Decidable (XorOrthogonal width row mask) :=
  inferInstanceAs (Decidable (_ = false))

theorem xorDotBelow_xor_left : ∀ width left right mask,
    xorDotBelow width (Nat.xor left right) mask =
      (xorDotBelow width left mask ^^ xorDotBelow width right mask)
  | 0, _, _, _ => rfl
  | width + 1, left, right, mask => by
      simp only [xorDotBelow,
        xorDotBelow_xor_left width left right mask]
      have hbit : (Nat.xor left right).testBit width =
          (left.testBit width ^^ right.testBit width) := by
        change (left ^^^ right).testBit width = _
        exact Nat.testBit_xor left right width
      rw [hbit]
      generalize left.testBit width = leftBit
      generalize right.testBit width = rightBit
      generalize mask.testBit width = maskBit
      generalize xorDotBelow width left mask = leftTail
      generalize xorDotBelow width right mask = rightTail
      cases leftBit <;> cases rightBit <;> cases maskBit <;>
        cases leftTail <;> cases rightTail <;> decide

theorem xorOrthogonal_xor
    {width left right mask : Nat}
    (hleft : XorOrthogonal width left mask)
    (hright : XorOrthogonal width right mask) :
    XorOrthogonal width (Nat.xor left right) mask := by
  unfold XorOrthogonal at hleft hright ⊢
  rw [xorDotBelow_xor_left, hleft, hright]
  rfl

def AllXorOrthogonal (width mask : Nat) (basis : List (Nat × Nat)) : Prop :=
  ∀ pivotRow, pivotRow ∈ basis → XorOrthogonal width pivotRow.2 mask

theorem reduceXorRow_orthogonal
    {width mask row : Nat} {basis : List (Nat × Nat)}
    (hrow : XorOrthogonal width row mask)
    (hbasis : AllXorOrthogonal width mask basis) :
    XorOrthogonal width (reduceXorRow row basis) mask := by
  induction basis generalizing row with
  | nil => exact hrow
  | cons head rest induction =>
      unfold reduceXorRow
      apply induction
      · split
        · exact xorOrthogonal_xor hrow
            (hbasis head List.mem_cons_self)
        · exact hrow
      · intro pivotRow hpivotRow
        exact hbasis pivotRow (List.mem_cons_of_mem head hpivotRow)

theorem insertXorPivotRow_allOrthogonal
    {width mask : Nat} {basis : List (Nat × Nat)} {entry : Nat × Nat}
    (hentry : XorOrthogonal width entry.2 mask)
    (hbasis : AllXorOrthogonal width mask basis) :
    AllXorOrthogonal width mask (insertXorPivotRow entry basis) := by
  induction basis with
  | nil =>
      intro pivotRow hpivotRow
      simp only [insertXorPivotRow, List.mem_cons, List.not_mem_nil,
        or_false] at hpivotRow
      rw [hpivotRow]
      exact hentry
  | cons head rest induction =>
      unfold insertXorPivotRow
      split
      · intro pivotRow hpivotRow
        simp only [List.mem_cons] at hpivotRow
        rcases hpivotRow with rfl | rfl | hpivotRow
        · exact hentry
        · exact hbasis _ List.mem_cons_self
        · exact hbasis pivotRow
            (List.mem_cons_of_mem head hpivotRow)
      · intro pivotRow hpivotRow
        rcases List.mem_cons.mp hpivotRow with rfl | hpivotRow
        · exact hbasis _ List.mem_cons_self
        · exact induction
            (fun other hother =>
              hbasis other (List.mem_cons_of_mem head hother))
            pivotRow hpivotRow

/-- Kernel preservation for the executable elimination: every output pivot
row is orthogonal to any mask orthogonal to the input rows. -/
theorem buildXorEchelon_allOrthogonal
    (width mask : Nat) :
    ∀ (rows : List Nat) (basis : List (Nat × Nat)),
      (∀ row, row ∈ rows → XorOrthogonal width row mask) →
      AllXorOrthogonal width mask basis →
      AllXorOrthogonal width mask (buildXorEchelon width rows basis)
  | [], basis, _, hbasis => hbasis
  | row :: rest, basis, hrows, hbasis => by
      let reduced := reduceXorRow row basis
      have hreduced : XorOrthogonal width reduced mask :=
        reduceXorRow_orthogonal
          (hrows row List.mem_cons_self) hbasis
      change AllXorOrthogonal width mask
        (buildXorEchelon width rest
          (if reduced = 0 then basis
           else insertXorPivotRow
             (highestSetBitBelow width reduced, reduced) basis))
      by_cases hzero : reduced = 0
      · rw [if_pos hzero]
        exact buildXorEchelon_allOrthogonal width mask rest basis
          (fun other hother =>
            hrows other (List.mem_cons_of_mem row hother))
          hbasis
      · rw [if_neg hzero]
        exact buildXorEchelon_allOrthogonal width mask rest
          (insertXorPivotRow
            (highestSetBitBelow width reduced, reduced) basis)
          (fun other hother =>
            hrows other (List.mem_cons_of_mem row hother))
          (insertXorPivotRow_allOrthogonal hreduced hbasis)

def slabIncidenceRows : List Nat :=
  (List.range (boundaryCompleteSlabLinks 1).length).map
    slabEdgeFaceIncidenceMask

def slabIncidenceXorEchelon : List (Nat × Nat) :=
  buildXorEchelon 72 slabIncidenceRows []

def slabIncidencePivotColumns : List Nat :=
  slabIncidenceXorEchelon.map Prod.fst

def slabIncidenceFreeColumns : List Nat :=
  (List.range 72).filter fun column =>
    decide (column ∉ slabIncidencePivotColumns)

/-- The literal 116-by-72 incidence table reduces to 65 pivots and exactly
seven free columns. -/
theorem slabIncidenceXorEchelon_spec :
    slabIncidenceXorEchelon.length = 65 ∧
    slabIncidencePivotColumns =
      [71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56,
       55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40,
       38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23,
       22, 21, 20, 18, 17, 16, 15, 14, 13, 12, 11, 10, 8, 7, 5, 4, 2] ∧
    slabIncidenceFreeColumns = [0, 1, 3, 6, 9, 19, 39] := by
  decide

/-- Semantic half of the elimination certificate: actual row-orthogonality
passes to every one of the 65 computed pivot rows. -/
theorem slabIncidenceXorEchelon_kernel_preserved
    (mask : Nat)
    (hrows : ∀ row, row ∈ slabIncidenceRows →
      XorOrthogonal 72 row mask) :
    AllXorOrthogonal 72 mask slabIncidenceXorEchelon := by
  exact buildXorEchelon_allOrthogonal 72 mask slabIncidenceRows []
    hrows (by
      intro pivotRow hpivotRow
      simp at hpivotRow)

/-- Literal even-incidence closure is exactly orthogonality to every original
row of the 116-by-72 incidence table. -/
theorem slabSurfaceIsClosed_rows
    (mask : Nat) (hclosed : slabSurfaceIsClosed mask = true) :
    ∀ row, row ∈ slabIncidenceRows → XorOrthogonal 72 row mask := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨block, hblock, rfl⟩
  apply (xorDotBelow_false_iff_list_even 72
    (slabEdgeFaceIncidenceMask block) mask).2
  rw [← slabMaskIntersectionCount_eq_list]
  exact of_decide_eq_true
    (List.all_eq_true.mp hclosed block hblock)

/-- Every literally closed slab surface satisfies all 65 computed echelon
constraints. -/
theorem slabSurfaceIsClosed_echelon
    (mask : Nat) (hclosed : slabSurfaceIsClosed mask = true) :
    AllXorOrthogonal 72 mask slabIncidenceXorEchelon :=
  slabIncidenceXorEchelon_kernel_preserved mask
    (slabSurfaceIsClosed_rows mask hclosed)

def selectedFreeColumns (compactMask : Nat) : List Nat :=
  slabIncidenceFreeColumns.filter fun faceId =>
    (embedBinarySurfaceMask compactMask).testBit faceId

/-- Each of the seven embedded generators owns one distinct free coordinate,
so their coefficient bits are read directly from columns
`[0,1,3,6,9,19,39]`. -/
theorem embeddedBinarySurfaceBasis_free_coordinates :
    binarySurfaceBasis.map selectedFreeColumns =
      [[0], [1], [3], [6], [9], [19], [39]] := by
  decide

/-! ## Constructive kernel completeness from the seven free bits -/

theorem xorDotBelow_eq_of_right_bits_eq : ∀ width row left right,
    (∀ column, column < width →
      left.testBit column = right.testBit column) →
    xorDotBelow width row left = xorDotBelow width row right
  | 0, _, _, _, _ => rfl
  | width + 1, row, left, right, hbits => by
      simp only [xorDotBelow]
      rw [hbits width (Nat.lt_succ_self width)]
      rw [xorDotBelow_eq_of_right_bits_eq width row left right
        (fun column hcolumn => hbits column (by omega))]

theorem xorDotBelow_add_eq_of_left_high_false : ∀ extra base row mask,
    (∀ column, base ≤ column → column < base + extra →
      row.testBit column = false) →
    xorDotBelow (base + extra) row mask = xorDotBelow base row mask
  | 0, _, _, _, _ => by simp
  | extra + 1, base, row, mask, hhigh => by
      rw [Nat.add_succ, xorDotBelow]
      have htop : row.testBit (base + extra) = false :=
        hhigh (base + extra) (by omega) (by omega)
      rw [htop]
      simp only [Bool.false_and, Bool.false_xor]
      exact xorDotBelow_add_eq_of_left_high_false extra base row mask
        (fun column hbase hcolumn => hhigh column hbase (by omega))

theorem testBit_eq_of_orthogonal_triangular
    {width pivot row left right : Nat}
    (hpivot : pivot < width)
    (hpivotBit : row.testBit pivot = true)
    (hhigh : ∀ column, pivot < column → column < width →
      row.testBit column = false)
    (hlower : ∀ column, column < pivot →
      left.testBit column = right.testBit column)
    (hleft : XorOrthogonal width row left)
    (hright : XorOrthogonal width row right) :
    left.testBit pivot = right.testBit pivot := by
  have hwidth : pivot + 1 + (width - (pivot + 1)) = width := by omega
  have htruncateLeft :=
    xorDotBelow_add_eq_of_left_high_false (width - (pivot + 1))
      (pivot + 1) row left
      (fun column hbase hcolumn => hhigh column (by omega) (by omega))
  have htruncateRight :=
    xorDotBelow_add_eq_of_left_high_false (width - (pivot + 1))
      (pivot + 1) row right
      (fun column hbase hcolumn => hhigh column (by omega) (by omega))
  rw [hwidth] at htruncateLeft htruncateRight
  have hlowerDot : xorDotBelow pivot row left =
      xorDotBelow pivot row right :=
    xorDotBelow_eq_of_right_bits_eq pivot row left right hlower
  unfold XorOrthogonal at hleft hright
  have hleft' : xorDotBelow (pivot + 1) row left = false := by
    rw [← htruncateLeft]
    exact hleft
  have hright' : xorDotBelow (pivot + 1) row right = false := by
    rw [← htruncateRight]
    exact hright
  simp only [xorDotBelow, hpivotBit, Bool.true_and] at hleft' hright'
  rw [hlowerDot] at hleft'
  generalize left.testBit pivot = leftBit at hleft' ⊢
  generalize right.testBit pivot = rightBit at hright' ⊢
  generalize xorDotBelow pivot row right = tail at hleft' hright'
  cases leftBit <;> cases rightBit <;> cases tail <;> simp_all

def slabIncidenceXorEchelonTriangularB : Bool :=
  slabIncidenceXorEchelon.all fun entry =>
    entry.2.testBit entry.1 &&
      (List.range 72).all fun column =>
        decide (entry.1 < column → entry.2.testBit column = false)

theorem slabIncidenceXorEchelonTriangularB_spec :
    slabIncidenceXorEchelonTriangularB = true := by
  decide

theorem slabIncidenceXorEchelon_triangular
    (entry : Nat × Nat) (hentry : entry ∈ slabIncidenceXorEchelon) :
    entry.2.testBit entry.1 = true ∧
      ∀ column, entry.1 < column → column < 72 →
        entry.2.testBit column = false := by
  have hcheck := List.all_eq_true.mp
    slabIncidenceXorEchelonTriangularB_spec entry hentry
  rw [Bool.and_eq_true] at hcheck
  refine ⟨hcheck.1, ?_⟩
  intro column hpivot hcolumn
  exact (of_decide_eq_true
    (List.all_eq_true.mp hcheck.2 column
      (List.mem_range.mpr hcolumn))) hpivot

/-- Two bounded masks in the computed kernel are equal if their seven free
bits agree.  The proof reconstructs pivot bits from low to high. -/
theorem slabIncidenceXorEchelon_kernel_unique_of_freeBits
    (left right : Nat)
    (hleftBound : left < 2 ^ 72)
    (hrightBound : right < 2 ^ 72)
    (hleft : AllXorOrthogonal 72 left slabIncidenceXorEchelon)
    (hright : AllXorOrthogonal 72 right slabIncidenceXorEchelon)
    (hfree : ∀ column, column ∈ slabIncidenceFreeColumns →
      left.testBit column = right.testBit column) :
    left = right := by
  have hprefix : ∀ limit, limit ≤ 72 → ∀ column, column < limit →
      left.testBit column = right.testBit column := by
    intro limit hlimit
    induction limit with
    | zero =>
        intro column hcolumn
        omega
    | succ limit induction =>
        intro column hcolumn
        by_cases hlt : column < limit
        · exact induction (by omega) column hlt
        · have hcolumnEq : column = limit := by omega
          subst column
          by_cases hfreeColumn : limit ∈ slabIncidenceFreeColumns
          · exact hfree limit hfreeColumn
          · have hpivotColumn : limit ∈ slabIncidencePivotColumns := by
              by_cases hpivot : limit ∈ slabIncidencePivotColumns
              · exact hpivot
              · exact False.elim (hfreeColumn (by
                  unfold slabIncidenceFreeColumns
                  exact List.mem_filter.mpr
                    ⟨List.mem_range.mpr (by omega), by simpa using hpivot⟩))
            rcases List.mem_map.mp hpivotColumn with
              ⟨entry, hentry, hentryPivot⟩
            have htriangular :=
              slabIncidenceXorEchelon_triangular entry hentry
            exact testBit_eq_of_orthogonal_triangular
              (by omega)
              (by simpa [hentryPivot] using htriangular.1)
              (fun other hlimitOther hotherBound => by
                exact htriangular.2 other (by omega) hotherBound)
              (fun other hother => induction (by omega) other hother)
              (hleft entry hentry)
              (hright entry hentry)
  apply Nat.eq_of_testBit_eq
  intro column
  by_cases hcolumn : column < 72
  · exact hprefix 72 (by omega) column hcolumn
  · have hpow : 2 ^ 72 ≤ 2 ^ column :=
      Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hleftBound hpow)]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hrightBound hpow)]

theorem slabSurfaceIsClosed_unique_of_freeBits
    (left right : Nat)
    (hleftBound : left < 2 ^ 72)
    (hrightBound : right < 2 ^ 72)
    (hleft : slabSurfaceIsClosed left = true)
    (hright : slabSurfaceIsClosed right = true)
    (hfree : ∀ column, column ∈ slabIncidenceFreeColumns →
      left.testBit column = right.testBit column) :
    left = right :=
  slabIncidenceXorEchelon_kernel_unique_of_freeBits left right
    hleftBound hrightBound
    (slabSurfaceIsClosed_echelon left hleft)
    (slabSurfaceIsClosed_echelon right hright)
    hfree

/-- Read the seven free slab bits as a compact coefficient in `[0,128)`. -/
def compactCoefficientFromSlabMask (mask : Nat) : Nat :=
  (if mask.testBit 0 then 1 else 0) +
  (if mask.testBit 1 then 2 else 0) +
  (if mask.testBit 3 then 4 else 0) +
  (if mask.testBit 6 then 8 else 0) +
  (if mask.testBit 9 then 16 else 0) +
  (if mask.testBit 19 then 32 else 0) +
  (if mask.testBit 39 then 64 else 0)

def embeddedSurfaceMatchingFreeBits (mask : Nat) : Nat :=
  embedBinarySurfaceMask
    (xorBasisMask (compactCoefficientFromSlabMask mask) binarySurfaceBasis)

theorem compactCoefficientFromSlabMask_lt_128 (mask : Nat) :
    compactCoefficientFromSlabMask mask < 128 := by
  unfold compactCoefficientFromSlabMask
  generalize mask.testBit 0 = b0
  generalize mask.testBit 1 = b1
  generalize mask.testBit 3 = b3
  generalize mask.testBit 6 = b6
  generalize mask.testBit 9 = b9
  generalize mask.testBit 19 = b19
  generalize mask.testBit 39 = b39
  cases b0 <;> cases b1 <;> cases b3 <;> cases b6 <;>
    cases b9 <;> cases b19 <;> cases b39 <;> decide

theorem embeddedSurfaceMatchingFreeBits_spec
    (mask column : Nat) (hcolumn : column ∈ slabIncidenceFreeColumns) :
    (embeddedSurfaceMatchingFreeBits mask).testBit column =
      mask.testBit column := by
  have hfreeExact := slabIncidenceXorEchelon_spec.2.2
  rw [hfreeExact] at hcolumn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcolumn
  rcases hcolumn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold embeddedSurfaceMatchingFreeBits compactCoefficientFromSlabMask
    generalize mask.testBit 0 = b0
    generalize mask.testBit 1 = b1
    generalize mask.testBit 3 = b3
    generalize mask.testBit 6 = b6
    generalize mask.testBit 9 = b9
    generalize mask.testBit 19 = b19
    generalize mask.testBit 39 = b39
    cases b0 <;> cases b1 <;> cases b3 <;> cases b6 <;>
      cases b9 <;> cases b19 <;> cases b39 <;> decide

theorem embeddedBinarySurfaceMasks_bounded :
    embeddedBinarySurfaceMasks.all (fun mask =>
      decide (mask < 2 ^ 72)) = true := by
  decide

theorem embeddedSurfaceMatchingFreeBits_mem (mask : Nat) :
    embeddedSurfaceMatchingFreeBits mask ∈ embeddedBinarySurfaceMasks := by
  apply List.mem_map.mpr
  refine ⟨xorBasisMask (compactCoefficientFromSlabMask mask)
    binarySurfaceBasis, ?_, rfl⟩
  apply List.mem_map.mpr
  exact ⟨compactCoefficientFromSlabMask mask,
    List.mem_range.mpr (compactCoefficientFromSlabMask_lt_128 mask), rfl⟩

/-- Completeness of the 128-mask surface list for the literal 72-face slab:
a bounded mask is closed exactly when it occurs in the embedded list. -/
theorem slabSurfaceIsClosed_iff_mem_embeddedBinarySurfaceMasks
    (mask : Nat) (hbound : mask < 2 ^ 72) :
    slabSurfaceIsClosed mask = true ↔
      mask ∈ embeddedBinarySurfaceMasks := by
  constructor
  · intro hclosed
    have htargetMem := embeddedSurfaceMatchingFreeBits_mem mask
    have htargetClosed := List.all_eq_true.mp
      embeddedBinarySurfaceMasks_sound.2.2 _ htargetMem
    have htargetBound := of_decide_eq_true
      (List.all_eq_true.mp embeddedBinarySurfaceMasks_bounded _ htargetMem)
    have heq := slabSurfaceIsClosed_unique_of_freeBits
      mask (embeddedSurfaceMatchingFreeBits mask)
      hbound htargetBound hclosed htargetClosed
      (fun column hcolumn =>
        embeddedSurfaceMatchingFreeBits_spec mask column hcolumn |>.symm)
    rw [heq]
    exact htargetMem
  · intro hmem
    exact List.all_eq_true.mp
      embeddedBinarySurfaceMasks_sound.2.2 mask hmem

end YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding

#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.activeHypercubeSlabFaceIds_spec
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.embeddedBinarySurfaceBasis_exact
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.embeddedBinarySurfaceMasks_sound
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.embeddedBinarySurfaceMasks_preserve_face_count
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.embeddedVacuumRowSurfaceMasks_exact
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.slabIncidenceXorEchelon_spec
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.slabIncidenceXorEchelon_kernel_preserved
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.slabSurfaceIsClosed_echelon
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.embeddedBinarySurfaceBasis_free_coordinates
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.slabIncidenceXorEchelon_kernel_unique_of_freeBits
#print axioms YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding.slabSurfaceIsClosed_iff_mem_embeddedBinarySurfaceMasks
