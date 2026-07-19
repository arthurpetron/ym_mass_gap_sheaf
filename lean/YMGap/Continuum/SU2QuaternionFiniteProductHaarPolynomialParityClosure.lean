/-
# Lazy all-parity closure for finite-product quaternion Haar

This leaf generalizes the historical eight-coordinate parity-sector and
complement recursion to an arbitrary finite number of quaternion blocks.

The parity label of a monomial is the lazy function

  coordinate |-> exponentAt monomial coordinate % 2.

Membership in a carried prefix is tested by a scalar-coordinate recursion;
neither a parity vector nor the family of all parity vectors is constructed.
For one chosen label, a raw polynomial is stably split into its matching
sector and complement.  The sector has the chosen parity, every complement
term carries a concrete mismatching coordinate, and both pieces preserve the
literal finite-block support convention.

The arbitrary-block parity-orthogonality theorem kills the two cross terms,
giving an exact Pythagorean Haar-square identity.  A length recursion then
proves all-parity positivity from a single abstract input: square positivity
for every polynomial already lying in one fixed lazy parity sector.  The
remaining mathematical obligation is therefore isolated without enumerating
the `2^(4 * blockCount)` possible labels.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialParityClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical lazy parity assignments and prefix matching -/

/-- The canonical coordinate-parity assignment of one monomial.  It is a
function and is never converted to a finite vector. -/
def canonicalFiniteQuaternionParity
    (monomial : List Nat) (coordinate : Nat) : Nat :=
  exponentAt monomial coordinate % 2

/-- Boolean matching of the first `coordinateCount` scalar coordinates.
The recursion is lazy in the count and allocates no coordinate list. -/
def parityPrefixMatches : Nat → (Nat → Nat) → List Nat → Bool
  | 0, _, _ => true
  | coordinateCount + 1, parity, monomial =>
      decide
          (exponentAt monomial coordinateCount % 2 = parity coordinateCount) &&
        parityPrefixMatches coordinateCount parity monomial

/-- Matching on the scalar prefix carried by `blockCount` quaternions. -/
def finiteQuaternionParityMatches
    (blockCount : Nat) (parity : Nat → Nat)
    (monomial : List Nat) : Bool :=
  parityPrefixMatches (4 * blockCount) parity monomial

/-- A successful prefix test gives all of its coordinate equations. -/
theorem parityPrefixMatches_true
    (parity : Nat → Nat) (monomial : List Nat) : ∀ coordinateCount,
    parityPrefixMatches coordinateCount parity monomial = true →
      ∀ coordinate, coordinate < coordinateCount →
        exponentAt monomial coordinate % 2 = parity coordinate
  | 0, _, _, hcoordinate => False.elim (by omega)
  | coordinateCount + 1, hmatch, coordinate, hcoordinate => by
      have hparts := (Bool.and_eq_true _ _).mp hmatch
      by_cases hlast : coordinate = coordinateCount
      · subst coordinate
        exact of_decide_eq_true hparts.1
      · exact parityPrefixMatches_true parity monomial coordinateCount
          hparts.2 coordinate (by omega)

/-- Every monomial matches its own canonical assignment at every finite
prefix. -/
theorem parityPrefixMatches_canonical
    (monomial : List Nat) : ∀ coordinateCount,
    parityPrefixMatches coordinateCount
      (canonicalFiniteQuaternionParity monomial) monomial = true
  | 0 => rfl
  | coordinateCount + 1 => by
      simp only [parityPrefixMatches, canonicalFiniteQuaternionParity,
        decide_true, Bool.true_and]
      exact parityPrefixMatches_canonical monomial coordinateCount

theorem finiteQuaternionParityMatches_canonical
    (blockCount : Nat) (monomial : List Nat) :
    finiteQuaternionParityMatches blockCount
      (canonicalFiniteQuaternionParity monomial) monomial = true :=
  parityPrefixMatches_canonical monomial (4 * blockCount)

/-- A failed prefix test constructively exposes one mismatching scalar
coordinate. -/
theorem parityPrefixMatches_false_witness
    (parity : Nat → Nat) (monomial : List Nat) : ∀ coordinateCount,
    parityPrefixMatches coordinateCount parity monomial = false →
      ∃ coordinate, coordinate < coordinateCount ∧
        exponentAt monomial coordinate % 2 ≠ parity coordinate
  | 0, hfalse => by
      change true = false at hfalse
      cases hfalse
  | coordinateCount + 1, hfalse => by
      by_cases hlast :
          exponentAt monomial coordinateCount % 2 = parity coordinateCount
      · have hdecision : decide
            (exponentAt monomial coordinateCount % 2 =
              parity coordinateCount) = true :=
          decide_eq_true hlast
        simp only [parityPrefixMatches, hdecision, Bool.true_and] at hfalse
        obtain ⟨coordinate, hcoordinate, hmismatch⟩ :=
          parityPrefixMatches_false_witness
            parity monomial coordinateCount hfalse
        exact ⟨coordinate, by omega, hmismatch⟩
      · exact ⟨coordinateCount, by omega, hlast⟩

/-! ## 2. Stable sector and complement -/

/-- The sub-polynomial matching one lazy parity assignment on the carried
coordinate prefix. -/
def finiteParitySector
    (blockCount : Nat) (parity : Nat → Nat) : RatPoly → RatPoly
  | [] => []
  | term :: polynomial =>
      if finiteQuaternionParityMatches blockCount parity term.1 = true then
        term :: finiteParitySector blockCount parity polynomial
      else finiteParitySector blockCount parity polynomial

/-- The complementary stable sub-polynomial. -/
def finiteParityComplement
    (blockCount : Nat) (parity : Nat → Nat) : RatPoly → RatPoly
  | [] => []
  | term :: polynomial =>
      if finiteQuaternionParityMatches blockCount parity term.1 = true then
        finiteParityComplement blockCount parity polynomial
      else term :: finiteParityComplement blockCount parity polynomial

theorem finiteParitySector_all
    (blockCount : Nat) (parity : Nat → Nat) : ∀ polynomial : RatPoly,
    AllFiniteQuaternionCoordinateParity blockCount parity
      (finiteParitySector blockCount parity polynomial)
  | [] => by
      intro term hterm
      simp [finiteParitySector] at hterm
  | head :: tail => by
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteParitySector, if_pos hhead]
        intro term hterm
        simp only [List.mem_cons] at hterm
        cases hterm with
        | inl heq =>
            subst term
            exact parityPrefixMatches_true parity head.1
              (4 * blockCount) hhead
        | inr hterm =>
            exact finiteParitySector_all
              blockCount parity tail term hterm
      · simp only [finiteParitySector, if_neg hhead]
        exact finiteParitySector_all blockCount parity tail

/-- Every complement term contains a concrete mismatching carried scalar
coordinate. -/
theorem finiteParityComplement_mismatch
    (blockCount : Nat) (parity : Nat → Nat) : ∀ polynomial : RatPoly,
    ∀ term, term ∈ finiteParityComplement blockCount parity polynomial →
      ∃ coordinate, coordinate < 4 * blockCount ∧
        exponentAt term.1 coordinate % 2 ≠ parity coordinate
  | [], term, hterm => by
      simp [finiteParityComplement] at hterm
  | head :: tail, term, hterm => by
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteParityComplement, if_pos hhead] at hterm
        exact finiteParityComplement_mismatch
          blockCount parity tail term hterm
      · simp only [finiteParityComplement, if_neg hhead,
          List.mem_cons] at hterm
        cases hterm with
        | inl heq =>
            subst term
            have hfalse :
                finiteQuaternionParityMatches
                  blockCount parity head.1 = false := by
              cases hvalue :
                  finiteQuaternionParityMatches blockCount parity head.1 with
              | false => rfl
              | true => exact (hhead hvalue).elim
            exact parityPrefixMatches_false_witness
              parity head.1 (4 * blockCount) hfalse
        | inr hterm =>
            exact finiteParityComplement_mismatch
              blockCount parity tail term hterm

theorem finiteParitySector_supported
    (blockCount : Nat) (parity : Nat → Nat) : ∀ polynomial : RatPoly,
    SupportedQuaternionBlocks blockCount polynomial →
      SupportedQuaternionBlocks blockCount
        (finiteParitySector blockCount parity polynomial)
  | [], _ => by
      intro term hterm
      simp [finiteParitySector] at hterm
  | head :: tail, hsupport => by
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteParitySector, if_pos hhead]
        intro term hterm
        simp only [List.mem_cons] at hterm
        cases hterm with
        | inl heq =>
            subst term
            exact hsupport head (by simp)
        | inr hterm =>
            exact finiteParitySector_supported blockCount parity tail
              (fun source hsource => hsupport source (by simp [hsource]))
              term hterm
      · simp only [finiteParitySector, if_neg hhead]
        exact finiteParitySector_supported blockCount parity tail
          (fun source hsource => hsupport source (by simp [hsource]))

theorem finiteParityComplement_supported
    (blockCount : Nat) (parity : Nat → Nat) : ∀ polynomial : RatPoly,
    SupportedQuaternionBlocks blockCount polynomial →
      SupportedQuaternionBlocks blockCount
        (finiteParityComplement blockCount parity polynomial)
  | [], _ => by
      intro term hterm
      simp [finiteParityComplement] at hterm
  | head :: tail, hsupport => by
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteParityComplement, if_pos hhead]
        exact finiteParityComplement_supported blockCount parity tail
          (fun source hsource => hsupport source (by simp [hsource]))
      · simp only [finiteParityComplement, if_neg hhead]
        intro term hterm
        simp only [List.mem_cons] at hterm
        cases hterm with
        | inl heq =>
            subst term
            exact hsupport head (by simp)
        | inr hterm =>
            exact finiteParityComplement_supported blockCount parity tail
              (fun source hsource => hsupport source (by simp [hsource]))
              term hterm

theorem finiteParityComplement_length_le
    (blockCount : Nat) (parity : Nat → Nat) : ∀ polynomial : RatPoly,
    (finiteParityComplement blockCount parity polynomial).length ≤
      polynomial.length
  | [] => by simp [finiteParityComplement]
  | head :: tail => by
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteParityComplement, if_pos hhead,
          List.length_cons]
        have htail := finiteParityComplement_length_le
          blockCount parity tail
        omega
      · simp only [finiteParityComplement, if_neg hhead,
          List.length_cons]
        exact Nat.succ_le_succ
          (finiteParityComplement_length_le blockCount parity tail)

/-! ## 3. Exact bilinear splitting -/

private theorem finiteHaarRow_parity_split
    (blockCount : Nat) (parity : Nat → Nat) (left : RatTerm) :
    ∀ right : RatPoly,
    finiteHaarRow blockCount left right ≈
      finiteHaarRow blockCount left
          (finiteParitySector blockCount parity right) +
        finiteHaarRow blockCount left
          (finiteParityComplement blockCount parity right)
  | [] => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | head :: tail => by
      let cell := (left.2 * head.2) *
        finiteProductHaarMono blockCount (monoMul left.1 head.1)
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteHaarRow, finiteParitySector,
          finiteParityComplement, if_pos hhead]
        refine Q'.eqv_trans _
          (cell +
            (finiteHaarRow blockCount left
                (finiteParitySector blockCount parity tail) +
              finiteHaarRow blockCount left
                (finiteParityComplement blockCount parity tail))) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ _
            (finiteHaarRow_parity_split
              blockCount parity left tail)
        · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      · simp only [finiteHaarRow, finiteParitySector,
          finiteParityComplement, if_neg hhead]
        refine Q'.eqv_trans _
          (cell +
            (finiteHaarRow blockCount left
                (finiteParitySector blockCount parity tail) +
              finiteHaarRow blockCount left
                (finiteParityComplement blockCount parity tail))) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ _
            (finiteHaarRow_parity_split
              blockCount parity left tail)
        refine Q'.eqv_trans _
          ((cell + finiteHaarRow blockCount left
              (finiteParitySector blockCount parity tail)) +
            finiteHaarRow blockCount left
              (finiteParityComplement blockCount parity tail)) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((finiteHaarRow blockCount left
                (finiteParitySector blockCount parity tail) + cell) +
            finiteHaarRow blockCount left
              (finiteParityComplement blockCount parity tail)) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
        exact Q'.add_assoc_eqv _ _ _

private theorem finiteHaarBilinear_parity_split_left
    (blockCount : Nat) (parity : Nat → Nat) : ∀ left right : RatPoly,
    finiteHaarBilinear blockCount left right ≈
      finiteHaarBilinear blockCount
          (finiteParitySector blockCount parity left) right +
        finiteHaarBilinear blockCount
          (finiteParityComplement blockCount parity left) right
  | [], _ => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | head :: tail, right => by
      by_cases hhead :
          finiteQuaternionParityMatches blockCount parity head.1 = true
      · simp only [finiteHaarBilinear, finiteParitySector,
          finiteParityComplement, if_pos hhead]
        refine Q'.eqv_trans _
          (finiteHaarRow blockCount head right +
            (finiteHaarBilinear blockCount
                (finiteParitySector blockCount parity tail) right +
              finiteHaarBilinear blockCount
                (finiteParityComplement blockCount parity tail) right)) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ _
            (finiteHaarBilinear_parity_split_left
              blockCount parity tail right)
        · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
      · simp only [finiteHaarBilinear, finiteParitySector,
          finiteParityComplement, if_neg hhead]
        refine Q'.eqv_trans _
          (finiteHaarRow blockCount head right +
            (finiteHaarBilinear blockCount
                (finiteParitySector blockCount parity tail) right +
              finiteHaarBilinear blockCount
                (finiteParityComplement blockCount parity tail) right)) _ ?_ ?_
        · exact Q'.add_eqv_congr_left _ _ _
            (finiteHaarBilinear_parity_split_left
              blockCount parity tail right)
        refine Q'.eqv_trans _
          ((finiteHaarRow blockCount head right +
              finiteHaarBilinear blockCount
                (finiteParitySector blockCount parity tail) right) +
            finiteHaarBilinear blockCount
              (finiteParityComplement blockCount parity tail) right) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((finiteHaarBilinear blockCount
                (finiteParitySector blockCount parity tail) right +
              finiteHaarRow blockCount head right) +
            finiteHaarBilinear blockCount
              (finiteParityComplement blockCount parity tail) right) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
        exact Q'.add_assoc_eqv _ _ _

private theorem finiteHaarBilinear_parity_split_right
    (blockCount : Nat) (parity : Nat → Nat) : ∀ left right : RatPoly,
    finiteHaarBilinear blockCount left right ≈
      finiteHaarBilinear blockCount left
          (finiteParitySector blockCount parity right) +
        finiteHaarBilinear blockCount left
          (finiteParityComplement blockCount parity right)
  | [], _ => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | head :: tail, right => by
      refine Q'.eqv_trans _
        ((finiteHaarRow blockCount head
              (finiteParitySector blockCount parity right) +
            finiteHaarRow blockCount head
              (finiteParityComplement blockCount parity right)) +
          (finiteHaarBilinear blockCount tail
              (finiteParitySector blockCount parity right) +
            finiteHaarBilinear blockCount tail
              (finiteParityComplement blockCount parity right))) _ ?_ ?_
      · exact QPoly.q_add_congr
          (finiteHaarRow_parity_split blockCount parity head right)
          (finiteHaarBilinear_parity_split_right
            blockCount parity tail right)
      · exact QPoly.q_interchange _ _ _ _

/-- Exact splitting of the left polynomial argument by one lazy parity
assignment. -/
theorem finiteProductHaar_parity_split_left
    (blockCount : Nat) (parity : Nat → Nat)
    (left right : RatPoly) :
    finiteProductHaar blockCount (polyMul left right) ≈
      finiteProductHaar blockCount
          (polyMul (finiteParitySector blockCount parity left) right) +
        finiteProductHaar blockCount
          (polyMul (finiteParityComplement blockCount parity left) right) := by
  refine Q'.eqv_trans _ (finiteHaarBilinear blockCount left right) _
    (finiteProductHaar_polyMul_eq_bilinear blockCount left right) ?_
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount
        (finiteParitySector blockCount parity left) right +
      finiteHaarBilinear blockCount
        (finiteParityComplement blockCount parity left) right) _
    (finiteHaarBilinear_parity_split_left
      blockCount parity left right) ?_
  exact QPoly.q_add_congr
    (Q'.eqv_symm (finiteProductHaar_polyMul_eq_bilinear
      blockCount (finiteParitySector blockCount parity left) right))
    (Q'.eqv_symm (finiteProductHaar_polyMul_eq_bilinear
      blockCount (finiteParityComplement blockCount parity left) right))

/-- Exact splitting of the right polynomial argument by one lazy parity
assignment. -/
theorem finiteProductHaar_parity_split_right
    (blockCount : Nat) (parity : Nat → Nat)
    (left right : RatPoly) :
    finiteProductHaar blockCount (polyMul left right) ≈
      finiteProductHaar blockCount
          (polyMul left (finiteParitySector blockCount parity right)) +
        finiteProductHaar blockCount
          (polyMul left (finiteParityComplement blockCount parity right)) := by
  refine Q'.eqv_trans _ (finiteHaarBilinear blockCount left right) _
    (finiteProductHaar_polyMul_eq_bilinear blockCount left right) ?_
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount left
        (finiteParitySector blockCount parity right) +
      finiteHaarBilinear blockCount left
        (finiteParityComplement blockCount parity right)) _
    (finiteHaarBilinear_parity_split_right
      blockCount parity left right) ?_
  exact QPoly.q_add_congr
    (Q'.eqv_symm (finiteProductHaar_polyMul_eq_bilinear
      blockCount left (finiteParitySector blockCount parity right)))
    (Q'.eqv_symm (finiteProductHaar_polyMul_eq_bilinear
      blockCount left (finiteParityComplement blockCount parity right)))

/-! ## 4. Cross-term cancellation and Pythagorean splitting -/

private theorem coordinateMismatch_to_finiteMismatch
    {blockCount coordinate : Nat} {left right : List Nat}
    (hcoordinate : coordinate < 4 * blockCount)
    (hmismatch : exponentAt left coordinate % 2 ≠
      exponentAt right coordinate % 2) :
    FiniteQuaternionParityMismatch blockCount left right := by
  let block := coordinate / 4
  let component := coordinate % 4
  have hcomponent : component < 4 := by
    exact Nat.mod_lt coordinate (by omega)
  have hdecompose : 4 * block + component = coordinate := by
    dsimp [block, component]
    have hdivision := Nat.mod_add_div coordinate 4
    omega
  have hblock : block < blockCount := by
    by_cases hresult : block < blockCount
    · exact hresult
    · have hle : blockCount ≤ block := Nat.le_of_not_gt hresult
      have hmul : 4 * blockCount ≤ 4 * block :=
        Nat.mul_le_mul_left 4 hle
      have hdivision : 4 * block + component = coordinate := by
        exact hdecompose
      omega
  refine ⟨block, hblock, component, hcomponent, ?_⟩
  simpa only [hdecompose] using hmismatch

private theorem finiteMismatch_of_match_and_complement
    {blockCount : Nat} {parity : Nat → Nat}
    {left right : RatTerm}
    (hleft : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt left.1 coordinate % 2 = parity coordinate)
    (hright : ∃ coordinate, coordinate < 4 * blockCount ∧
      exponentAt right.1 coordinate % 2 ≠ parity coordinate) :
    FiniteQuaternionParityMismatch blockCount left.1 right.1 := by
  obtain ⟨coordinate, hcoordinate, hright⟩ := hright
  have hcross : exponentAt left.1 coordinate % 2 ≠
      exponentAt right.1 coordinate % 2 := by
    intro heq
    exact hright (heq.symm.trans (hleft coordinate hcoordinate))
  exact coordinateMismatch_to_finiteMismatch hcoordinate hcross

private theorem finiteQuaternionParityMismatch_symm
    {blockCount : Nat} {left right : List Nat}
    (hmismatch : FiniteQuaternionParityMismatch blockCount left right) :
    FiniteQuaternionParityMismatch blockCount right left := by
  obtain ⟨block, hblock, component, hcomponent, hmismatch⟩ := hmismatch
  exact ⟨block, hblock, component, hcomponent, hmismatch.symm⟩

theorem finiteProductHaar_sector_complement_zero
    (blockCount : Nat) (parity : Nat → Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount
        (polyMul
          (finiteParitySector blockCount parity polynomial)
          (finiteParityComplement blockCount parity polynomial)) ≈ 0 := by
  apply finiteProductHaar_mul_cross_parity_zero
  intro left hleft right hright
  exact finiteMismatch_of_match_and_complement
    (finiteParitySector_all blockCount parity polynomial left hleft)
    (finiteParityComplement_mismatch
      blockCount parity polynomial right hright)

theorem finiteProductHaar_complement_sector_zero
    (blockCount : Nat) (parity : Nat → Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount
        (polyMul
          (finiteParityComplement blockCount parity polynomial)
          (finiteParitySector blockCount parity polynomial)) ≈ 0 := by
  apply finiteProductHaar_mul_cross_parity_zero
  intro left hleft right hright
  exact finiteQuaternionParityMismatch_symm
    (finiteMismatch_of_match_and_complement
      (finiteParitySector_all blockCount parity polynomial right hright)
      (finiteParityComplement_mismatch
        blockCount parity polynomial left hleft))

/-- **Exact arbitrary-block Pythagorean parity identity.** -/
theorem finiteProductHaar_parity_square_split
    (blockCount : Nat) (parity : Nat → Nat) (polynomial : RatPoly) :
    finiteProductHaar blockCount (polyMul polynomial polynomial) ≈
      finiteProductHaar blockCount
          (polyMul
            (finiteParitySector blockCount parity polynomial)
            (finiteParitySector blockCount parity polynomial)) +
        finiteProductHaar blockCount
          (polyMul
            (finiteParityComplement blockCount parity polynomial)
            (finiteParityComplement blockCount parity polynomial)) := by
  refine Q'.eqv_trans _
    (finiteProductHaar blockCount
        (polyMul (finiteParitySector blockCount parity polynomial) polynomial) +
      finiteProductHaar blockCount
        (polyMul
          (finiteParityComplement blockCount parity polynomial)
          polynomial)) _
    (finiteProductHaar_parity_split_left
      blockCount parity polynomial polynomial) ?_
  refine Q'.eqv_trans _
    ((finiteProductHaar blockCount
          (polyMul
            (finiteParitySector blockCount parity polynomial)
            (finiteParitySector blockCount parity polynomial)) +
        finiteProductHaar blockCount
          (polyMul
            (finiteParitySector blockCount parity polynomial)
            (finiteParityComplement blockCount parity polynomial))) +
      (finiteProductHaar blockCount
          (polyMul
            (finiteParityComplement blockCount parity polynomial)
            (finiteParitySector blockCount parity polynomial)) +
        finiteProductHaar blockCount
          (polyMul
            (finiteParityComplement blockCount parity polynomial)
            (finiteParityComplement blockCount parity polynomial)))) _
    (QPoly.q_add_congr
      (finiteProductHaar_parity_split_right blockCount parity
        (finiteParitySector blockCount parity polynomial) polynomial)
      (finiteProductHaar_parity_split_right blockCount parity
        (finiteParityComplement blockCount parity polynomial) polynomial)) ?_
  refine Q'.eqv_trans _
    ((finiteProductHaar blockCount
          (polyMul
            (finiteParitySector blockCount parity polynomial)
            (finiteParitySector blockCount parity polynomial)) + 0) +
      (0 + finiteProductHaar blockCount
        (polyMul
          (finiteParityComplement blockCount parity polynomial)
          (finiteParityComplement blockCount parity polynomial)))) _
    (QPoly.q_add_congr
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (finiteProductHaar_sector_complement_zero
          blockCount parity polynomial))
      (QPoly.q_add_congr
        (finiteProductHaar_complement_sector_zero
          blockCount parity polynomial)
        (Q'.eqv_refl _))) ?_
  exact QPoly.q_add_congr
    (QPoly.q_add_zero_eqv _)
    (QPoly.q_zero_add_eqv _)

/-! ## 5. Generic length-recursive all-parity closure -/

/-- The one remaining input for all-parity positivity: positivity on every
already-fixed lazy coordinate-parity sector. -/
def FixedParitySquarePositive (blockCount : Nat) : Prop :=
  ∀ (parity : Nat → Nat) (polynomial : RatPoly),
    SupportedQuaternionBlocks blockCount polynomial →
      AllFiniteQuaternionCoordinateParity blockCount parity polynomial →
        (0 : Q') ≤
          finiteProductHaar blockCount
            (polyMul polynomial polynomial)

private theorem finiteProductHaar_square_nonneg_fuel
    (blockCount : Nat)
    (hfixed : FixedParitySquarePositive blockCount) :
    ∀ (fuel : Nat) (polynomial : RatPoly),
      polynomial.length ≤ fuel →
      SupportedQuaternionBlocks blockCount polynomial →
        (0 : Q') ≤
          finiteProductHaar blockCount
            (polyMul polynomial polynomial)
  | 0, [], _, hsupport =>
      hfixed (canonicalFiniteQuaternionParity []) [] hsupport
        (by intro term hterm; simp at hterm)
  | 0, _ :: _, hlength, _ => by simp at hlength
  | fuel + 1, [], _, hsupport =>
      hfixed (canonicalFiniteQuaternionParity []) [] hsupport
        (by intro term hterm; simp at hterm)
  | fuel + 1, head :: tail, hlength, hsupport => by
      let parity := canonicalFiniteQuaternionParity head.1
      let sector := finiteParitySector blockCount parity (head :: tail)
      let complement := finiteParityComplement
        blockCount parity (head :: tail)
      have hsectorSupport : SupportedQuaternionBlocks blockCount sector :=
        finiteParitySector_supported
          blockCount parity (head :: tail) hsupport
      have hsectorParity :
          AllFiniteQuaternionCoordinateParity
            blockCount parity sector :=
        finiteParitySector_all blockCount parity (head :: tail)
      have hcomplementSupport :
          SupportedQuaternionBlocks blockCount complement :=
        finiteParityComplement_supported
          blockCount parity (head :: tail) hsupport
      have hheadMatch :
          finiteQuaternionParityMatches blockCount parity head.1 = true := by
        exact finiteQuaternionParityMatches_canonical blockCount head.1
      have hcomplementLength : complement.length ≤ fuel := by
        have htailLength := finiteParityComplement_length_le
          blockCount parity tail
        have heq : complement =
            finiteParityComplement blockCount parity tail := by
          simp only [complement, finiteParityComplement,
            hheadMatch, if_pos]
        rw [heq]
        simp only [List.length_cons] at hlength
        omega
      have hsectorNonnegative :
          (0 : Q') ≤ finiteProductHaar blockCount
            (polyMul sector sector) :=
        hfixed parity sector hsectorSupport hsectorParity
      have hcomplementNonnegative :
          (0 : Q') ≤ finiteProductHaar blockCount
            (polyMul complement complement) :=
        finiteProductHaar_square_nonneg_fuel
          blockCount hfixed fuel complement
          hcomplementLength hcomplementSupport
      have hsum : (0 : Q') ≤
          finiteProductHaar blockCount (polyMul sector sector) +
            finiteProductHaar blockCount
              (polyMul complement complement) :=
        Q'.zero_le_add _ _
          hsectorNonnegative hcomplementNonnegative
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv (Q'.eqv_symm
          (finiteProductHaar_parity_square_split
            blockCount parity (head :: tail))))

/-- **Generic arbitrary-block all-parity closure.**  Fixed-parity square
positivity implies square positivity for every finitely supported polynomial,
without enumerating parity assignments. -/
theorem finiteProductHaar_square_nonneg_of_fixedParity
    (blockCount : Nat) (hfixed : FixedParitySquarePositive blockCount)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blockCount polynomial) :
    (0 : Q') ≤
      finiteProductHaar blockCount
        (polyMul polynomial polynomial) :=
  finiteProductHaar_square_nonneg_fuel
    blockCount hfixed polynomial.length polynomial
    (Nat.le_refl _) hsupport

#print axioms parityPrefixMatches_true
#print axioms parityPrefixMatches_canonical
#print axioms parityPrefixMatches_false_witness
#print axioms finiteParitySector_all
#print axioms finiteParityComplement_mismatch
#print axioms finiteParitySector_supported
#print axioms finiteParityComplement_supported
#print axioms finiteParityComplement_length_le
#print axioms finiteProductHaar_parity_split_left
#print axioms finiteProductHaar_parity_split_right
#print axioms finiteProductHaar_sector_complement_zero
#print axioms finiteProductHaar_complement_sector_zero
#print axioms finiteProductHaar_parity_square_split
#print axioms finiteProductHaar_square_nonneg_of_fixedParity

end YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialParityClosure
