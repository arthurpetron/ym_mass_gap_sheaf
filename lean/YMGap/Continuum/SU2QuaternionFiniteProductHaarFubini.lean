/-
# Constructive blockwise Fubini for finite quaternion products

The finite-product quaternion carrier assigns four consecutive scalar
coordinates to every quaternion block.  This leaf performs one normalized
block integration directly on the raw exponent-list carrier.

Integration does not delete coordinates or renumber later blocks.  Instead,
the four exponents of the selected block are replaced by zero, while the
coefficient is multiplied by that block's exact `S^3` moment.  The mask is
length preserving, so every global link index remains stable.

For a block inside the finite carrier, clearing its exponents leaves the
entire out-of-carrier tail literally unchanged.  A constructive Nodup
induction then isolates the selected factor in the finite product moment and
proves the exact Fubini identity

  finiteProductHaar n (integrateQuaternionBlock b p)
    ~= finiteProductHaar n p,       b < n.

No support hypothesis on `p` is needed for this identity.  A separate
finite-block support predicate and its preservation theorem are included for
later global-link wiring and positivity arguments.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- Swap the first two factors of a three-factor product, up to rational
setoid equality. -/
private theorem q_mul_left_swap (a b c : Q') :
    a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ ((b * a) * c) _
      (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-! ## 1. A length-preserving four-coordinate mask -/

/-- The scalar coordinate belongs to the four-coordinate quaternion block. -/
def coordinateInQuaternionBlock (block coordinate : Nat) : Prop :=
  4 * block ≤ coordinate ∧ coordinate < 4 * block + 4

instance coordinateInQuaternionBlockDecidable
    (block coordinate : Nat) :
    Decidable (coordinateInQuaternionBlock block coordinate) := by
  unfold coordinateInQuaternionBlock
  infer_instance

/-- Clear one quaternion block while traversing an exponent list from the
supplied global coordinate.  The recursion never pads or truncates the list.
-/
def clearQuaternionBlockFrom (block : Nat) :
    Nat → List Nat → List Nat
  | _, [] => []
  | coordinate, exponent :: tail =>
      (if coordinateInQuaternionBlock block coordinate then 0 else exponent) ::
        clearQuaternionBlockFrom block (coordinate + 1) tail

/-- Replace the four exponents in `block` by zero, retaining all coordinate
positions and all trailing-zero aliases of the raw carrier. -/
def clearQuaternionBlock (block : Nat) (monomial : List Nat) : List Nat :=
  clearQuaternionBlockFrom block 0 monomial

/-- Coordinate lookup through the mask, from an arbitrary starting index. -/
theorem exponentAt_clearQuaternionBlockFrom (block start : Nat) :
    ∀ (monomial : List Nat) (offset : Nat),
      exponentAt (clearQuaternionBlockFrom block start monomial) offset =
        if coordinateInQuaternionBlock block (start + offset) then 0
        else exponentAt monomial offset
  | [], offset => by
      simp [clearQuaternionBlockFrom, exponentAt]
  | exponent :: tail, 0 => by
      simp [clearQuaternionBlockFrom, exponentAt]
  | exponent :: tail, offset + 1 => by
      change
        exponentAt
            (clearQuaternionBlockFrom block (start + 1) tail) offset =
          if coordinateInQuaternionBlock block (start + (offset + 1))
          then 0 else exponentAt tail offset
      have hcoordinate : (start + 1) + offset =
          start + (offset + 1) := by omega
      simpa only [hcoordinate] using
        (exponentAt_clearQuaternionBlockFrom
          block (start + 1) tail offset)

/-- Coordinate lookup through the mask from coordinate zero. -/
theorem exponentAt_clearQuaternionBlock
    (block : Nat) (monomial : List Nat) (coordinate : Nat) :
    exponentAt (clearQuaternionBlock block monomial) coordinate =
      if coordinateInQuaternionBlock block coordinate then 0
      else exponentAt monomial coordinate := by
  simpa only [clearQuaternionBlock, Nat.zero_add] using
    (exponentAt_clearQuaternionBlockFrom block 0 monomial coordinate)

/-- Every component of the selected block is cleared. -/
theorem exponentAt_clearQuaternionBlock_self
    (monomial : List Nat) (block component : Nat)
    (hcomponent : component < 4) :
    exponentAt (clearQuaternionBlock block monomial)
        (4 * block + component) = 0 := by
  have hin : coordinateInQuaternionBlock block
      (4 * block + component) := by
    unfold coordinateInQuaternionBlock
    exact ⟨by omega, by omega⟩
  simp only [exponentAt_clearQuaternionBlock, hin, if_true]

/-- Clearing one block leaves every component of a distinct block literally
unchanged. -/
theorem exponentAt_clearQuaternionBlock_of_ne
    (monomial : List Nat) {source target component : Nat}
    (hne : source ≠ target) (hcomponent : component < 4) :
    exponentAt (clearQuaternionBlock target monomial)
        (4 * source + component) =
      exponentAt monomial (4 * source + component) := by
  have hout : ¬ coordinateInQuaternionBlock target
      (4 * source + component) := by
    unfold coordinateInQuaternionBlock
    intro hinside
    omega
  simp only [exponentAt_clearQuaternionBlock, hout, if_false]

/-- The mask preserves the exact raw exponent-list length. -/
theorem clearQuaternionBlockFrom_length (block start : Nat) :
    ∀ monomial : List Nat,
      (clearQuaternionBlockFrom block start monomial).length = monomial.length
  | [] => rfl
  | exponent :: tail => by
      simp only [clearQuaternionBlockFrom, List.length_cons]
      rw [clearQuaternionBlockFrom_length block (start + 1) tail]

theorem clearQuaternionBlock_length
    (block : Nat) (monomial : List Nat) :
    (clearQuaternionBlock block monomial).length = monomial.length :=
  clearQuaternionBlockFrom_length block 0 monomial

/-- Dropping coordinates after masking advances the global traversal index by
the same number of coordinates. -/
theorem clearQuaternionBlockFrom_drop (block start : Nat) :
    ∀ (monomial : List Nat) (count : Nat),
      (clearQuaternionBlockFrom block start monomial).drop count =
        clearQuaternionBlockFrom block (start + count)
          (monomial.drop count)
  | monomial, 0 => by simp
  | [], count + 1 => by simp [clearQuaternionBlockFrom]
  | exponent :: tail, count + 1 => by
      change
        (clearQuaternionBlockFrom block (start + 1) tail).drop count =
          clearQuaternionBlockFrom block (start + (count + 1))
            (tail.drop count)
      have hcoordinate : (start + 1) + count =
          start + (count + 1) := by omega
      simpa only [hcoordinate] using
        (clearQuaternionBlockFrom_drop
          block (start + 1) tail count)

/-- Once traversal has passed the selected four-coordinate block, the mask is
the literal identity. -/
theorem clearQuaternionBlockFrom_of_block_before
    (block start : Nat) (hstart : 4 * block + 4 ≤ start) :
    ∀ monomial : List Nat,
      clearQuaternionBlockFrom block start monomial = monomial
  | [] => rfl
  | exponent :: tail => by
      have hout : ¬ coordinateInQuaternionBlock block start := by
        unfold coordinateInQuaternionBlock
        intro hinside
        omega
      simp only [clearQuaternionBlockFrom, hout, if_false]
      rw [clearQuaternionBlockFrom_of_block_before
        block (start + 1) (by omega) tail]

/-- Clearing an in-range block leaves the whole out-of-carrier exponent tail
literally unchanged.  This is the support fact that removes any hypothesis
from the Fubini evaluation theorem below. -/
theorem clearQuaternionBlock_drop_of_lt
    (monomial : List Nat) {blockCount block : Nat}
    (hblock : block < blockCount) :
    (clearQuaternionBlock block monomial).drop (4 * blockCount) =
      monomial.drop (4 * blockCount) := by
  calc
    (clearQuaternionBlock block monomial).drop (4 * blockCount) =
        clearQuaternionBlockFrom block (0 + 4 * blockCount)
          (monomial.drop (4 * blockCount)) :=
      clearQuaternionBlockFrom_drop block 0 monomial (4 * blockCount)
    _ = monomial.drop (4 * blockCount) := by
      apply clearQuaternionBlockFrom_of_block_before
      omega

/-- Clearing coordinate masks commutes by literal list equality.  This holds
even when the two block indices coincide. -/
theorem clearQuaternionBlockFrom_comm (left right start : Nat) :
    ∀ monomial : List Nat,
      clearQuaternionBlockFrom left start
          (clearQuaternionBlockFrom right start monomial) =
        clearQuaternionBlockFrom right start
          (clearQuaternionBlockFrom left start monomial)
  | [] => rfl
  | exponent :: tail => by
      simp only [clearQuaternionBlockFrom]
      by_cases hleft : coordinateInQuaternionBlock left start
      · by_cases hright : coordinateInQuaternionBlock right start
        · simp only [hleft, hright, if_true]
          rw [clearQuaternionBlockFrom_comm
            left right (start + 1) tail]
        · simp only [hleft, hright, if_true, if_false]
          rw [clearQuaternionBlockFrom_comm
            left right (start + 1) tail]
      · by_cases hright : coordinateInQuaternionBlock right start
        · simp only [hleft, hright, if_true, if_false]
          rw [clearQuaternionBlockFrom_comm
            left right (start + 1) tail]
        · simp only [hleft, hright, if_false]
          rw [clearQuaternionBlockFrom_comm
            left right (start + 1) tail]

theorem clearQuaternionBlock_comm
    (left right : Nat) (monomial : List Nat) :
    clearQuaternionBlock left (clearQuaternionBlock right monomial) =
      clearQuaternionBlock right (clearQuaternionBlock left monomial) :=
  clearQuaternionBlockFrom_comm left right 0 monomial

/-! ## 2. Isolating the selected block moment -/

/-- The selected block has normalized moment one after it is cleared. -/
theorem quaternionBlockMoment_clear_self
    (monomial : List Nat) (block : Nat) :
    quaternionBlockMoment block (clearQuaternionBlock block monomial) ≈ 1 := by
  unfold quaternionBlockMoment
  simpa only [Nat.add_zero] using
    (show
      sphereMoment4
          (exponentAt (clearQuaternionBlock block monomial) (4 * block + 0))
          (exponentAt (clearQuaternionBlock block monomial) (4 * block + 1))
          (exponentAt (clearQuaternionBlock block monomial) (4 * block + 2))
          (exponentAt (clearQuaternionBlock block monomial) (4 * block + 3)) ≈
        1 from by
      rw [exponentAt_clearQuaternionBlock_self monomial block 0 (by omega),
    exponentAt_clearQuaternionBlock_self monomial block 1 (by omega),
    exponentAt_clearQuaternionBlock_self monomial block 2 (by omega),
    exponentAt_clearQuaternionBlock_self monomial block 3 (by omega)]
      exact sphereMoment4_one)

/-- Every distinct block moment is literally unchanged by the mask. -/
theorem quaternionBlockMoment_clear_of_ne
    (monomial : List Nat) {source target : Nat}
    (hne : source ≠ target) :
    quaternionBlockMoment source (clearQuaternionBlock target monomial) =
      quaternionBlockMoment source monomial := by
  unfold quaternionBlockMoment
  simpa only [Nat.add_zero] using
    (show
      sphereMoment4
          (exponentAt (clearQuaternionBlock target monomial)
            (4 * source + 0))
          (exponentAt (clearQuaternionBlock target monomial)
            (4 * source + 1))
          (exponentAt (clearQuaternionBlock target monomial)
            (4 * source + 2))
          (exponentAt (clearQuaternionBlock target monomial)
            (4 * source + 3)) =
        sphereMoment4
          (exponentAt monomial (4 * source + 0))
          (exponentAt monomial (4 * source + 1))
          (exponentAt monomial (4 * source + 2))
          (exponentAt monomial (4 * source + 3)) from by
      rw [exponentAt_clearQuaternionBlock_of_ne monomial hne
          (by omega : 0 < 4),
        exponentAt_clearQuaternionBlock_of_ne monomial hne
          (by omega : 1 < 4),
        exponentAt_clearQuaternionBlock_of_ne monomial hne
          (by omega : 2 < 4),
        exponentAt_clearQuaternionBlock_of_ne monomial hne
          (by omega : 3 < 4)])

/-- A block product omitting the selected block is literally unchanged by
clearing that block. -/
theorem quaternionBlockMomentProduct_clear_of_not_mem
    (monomial : List Nat) (target : Nat) : ∀ blocks : List Nat,
    target ∉ blocks →
      quaternionBlockMomentProduct (clearQuaternionBlock target monomial)
          blocks =
        quaternionBlockMomentProduct monomial blocks
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead : head ≠ target := by
        intro heq
        apply hnot
        rw [← heq]
        exact List.mem_cons_self
      have htail : target ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      change
        quaternionBlockMoment head (clearQuaternionBlock target monomial) *
              quaternionBlockMomentProduct
                (clearQuaternionBlock target monomial) tail =
          quaternionBlockMoment head monomial *
              quaternionBlockMomentProduct monomial tail
      rw [quaternionBlockMoment_clear_of_ne monomial hhead,
        quaternionBlockMomentProduct_clear_of_not_mem
          monomial target tail htail]

/-- A selected factor can be integrated out of any Nodup block product that
contains it. -/
theorem quaternionBlockMoment_mul_clear_product
    (monomial : List Nat) (block : Nat) : ∀ blocks : List Nat,
    blocks.Nodup → block ∈ blocks →
      quaternionBlockMoment block monomial *
          quaternionBlockMomentProduct
            (clearQuaternionBlock block monomial) blocks ≈
        quaternionBlockMomentProduct monomial blocks
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases heq : block = head
      · subst head
        have htail := quaternionBlockMomentProduct_clear_of_not_mem
          monomial block tail hparts.1
        change
          quaternionBlockMoment block monomial *
              (quaternionBlockMoment block
                  (clearQuaternionBlock block monomial) *
                quaternionBlockMomentProduct
                  (clearQuaternionBlock block monomial) tail) ≈
            quaternionBlockMoment block monomial *
              quaternionBlockMomentProduct monomial tail
        rw [htail]
        exact Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _
            ((1 : Q') * quaternionBlockMomentProduct monomial tail) _
            (Q'.mul_eqv_congr_right _ _ _
              (quaternionBlockMoment_clear_self monomial block))
            (Q'.one_mul_eqv _))
      · have htailMem : block ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left heq
        have hheadNe : head ≠ block := by
          intro h
          exact heq h.symm
        have ih := quaternionBlockMoment_mul_clear_product
          monomial block tail hparts.2 htailMem
        change
          quaternionBlockMoment block monomial *
              (quaternionBlockMoment head
                  (clearQuaternionBlock block monomial) *
                quaternionBlockMomentProduct
                  (clearQuaternionBlock block monomial) tail) ≈
            quaternionBlockMoment head monomial *
              quaternionBlockMomentProduct monomial tail
        rw [quaternionBlockMoment_clear_of_ne monomial hheadNe]
        exact Q'.eqv_trans _
          (quaternionBlockMoment head monomial *
            (quaternionBlockMoment block monomial *
              quaternionBlockMomentProduct
                (clearQuaternionBlock block monomial) tail)) _
          (q_mul_left_swap
            (quaternionBlockMoment block monomial)
            (quaternionBlockMoment head monomial)
            (quaternionBlockMomentProduct
              (clearQuaternionBlock block monomial) tail))
          (Q'.mul_eqv_congr_left _ _ _ ih)

private theorem rangeNodupLocal (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

/-- Monomial Fubini: the selected block moment times the residual finite
product moment is the original finite product moment.  The out-of-carrier
zero branch is handled exactly and needs no support assumption. -/
theorem quaternionBlockMoment_mul_finiteProductHaarMono_clear
    (blockCount block : Nat) (hblock : block < blockCount)
    (monomial : List Nat) :
    quaternionBlockMoment block monomial *
        finiteProductHaarMono blockCount
          (clearQuaternionBlock block monomial) ≈
      finiteProductHaarMono blockCount monomial := by
  have hdrop := clearQuaternionBlock_drop_of_lt monomial hblock
  unfold finiteProductHaarMono
  rw [hdrop]
  by_cases htail : allZero (monomial.drop (4 * blockCount)) = true
  · simp only [htail, if_true]
    exact quaternionBlockMoment_mul_clear_product
      monomial block (List.range blockCount)
      (rangeNodupLocal blockCount) (List.mem_range.mpr hblock)
  · have hfalse :
        allZero (monomial.drop (4 * blockCount)) = false := by
      cases hvalue : allZero (monomial.drop (4 * blockCount)) with
      | false => rfl
      | true => exact (htail hvalue).elim
    simp only [hfalse]
    exact Q'.mul_zero_eqv _

/-! ## 3. Partial integration on raw polynomials -/

/-- Integrate one term over one normalized quaternion block. -/
def integrateQuaternionBlockTerm (block : Nat) (term : RatTerm) : RatTerm :=
  (clearQuaternionBlock block term.1,
    term.2 * quaternionBlockMoment block term.1)

/-- Constructive partial integration over one quaternion block.  Literal zero
coefficients and duplicate residual monomials are deliberately retained. -/
def integrateQuaternionBlock (block : Nat) (polynomial : RatPoly) : RatPoly :=
  polynomial.map (integrateQuaternionBlockTerm block)

/-- Raw support in the first `blockCount` quaternion blocks, matching the
repository's existing length-based `Supported8` convention. -/
def SupportedQuaternionBlocks
    (blockCount : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → term.1.length ≤ 4 * blockCount

/-- Partial integration preserves every finite quaternion-block support
bound, independently of which block is integrated. -/
theorem integrateQuaternionBlock_supported
    (block : Nat) {blockCount : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blockCount polynomial) :
    SupportedQuaternionBlocks blockCount
      (integrateQuaternionBlock block polynomial) := by
  intro term hterm
  unfold integrateQuaternionBlock at hterm
  rw [List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  unfold integrateQuaternionBlockTerm
  simpa only [clearQuaternionBlock_length] using
    (hsupport source hsource)

/-- **Exact one-block Fubini theorem.**  Integrating any carried quaternion
block before evaluating the full finite product leaves the value unchanged.
No support or normalization hypothesis on the raw polynomial is required. -/
theorem finiteProductHaar_integrateQuaternionBlock
    (blockCount block : Nat) (hblock : block < blockCount) :
    ∀ polynomial : RatPoly,
      finiteProductHaar blockCount
          (integrateQuaternionBlock block polynomial) ≈
        finiteProductHaar blockCount polynomial
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      change
        (term.2 * quaternionBlockMoment block term.1) *
              finiteProductHaarMono blockCount
                (clearQuaternionBlock block term.1) +
            finiteProductHaar blockCount
              (integrateQuaternionBlock block polynomial) ≈
          term.2 * finiteProductHaarMono blockCount term.1 +
            finiteProductHaar blockCount polynomial
      exact q_add_congr
        (Q'.eqv_trans _
          (term.2 *
            (quaternionBlockMoment block term.1 *
              finiteProductHaarMono blockCount
                (clearQuaternionBlock block term.1))) _
          (Q'.mul_assoc_eqv term.2
            (quaternionBlockMoment block term.1)
            (finiteProductHaarMono blockCount
              (clearQuaternionBlock block term.1)))
          (Q'.mul_eqv_congr_left term.2 _ _
            (quaternionBlockMoment_mul_finiteProductHaarMono_clear
              blockCount block hblock term.1)))
        (finiteProductHaar_integrateQuaternionBlock
          blockCount block hblock polynomial)

/-! ## 4. Finite schedules and evaluation-level Fubini reordering -/

/-- Apply a finite schedule of normalized one-block integrations. -/
def integrateQuaternionBlocks : List Nat → RatPoly → RatPoly
  | [], polynomial => polynomial
  | block :: blocks, polynomial =>
      integrateQuaternionBlocks blocks
        (integrateQuaternionBlock block polynomial)

/-- Every in-range finite integration schedule has the same full-product
evaluation as the original polynomial. -/
theorem finiteProductHaar_integrateQuaternionBlocks
    (blockCount : Nat) : ∀ (blocks : List Nat) (polynomial : RatPoly),
    (∀ block, block ∈ blocks → block < blockCount) →
      finiteProductHaar blockCount
          (integrateQuaternionBlocks blocks polynomial) ≈
        finiteProductHaar blockCount polynomial
  | [], polynomial, _ => Q'.eqv_refl _
  | block :: blocks, polynomial, hblocks => by
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount
          (integrateQuaternionBlock block polynomial)) _ ?_ ?_
      · exact finiteProductHaar_integrateQuaternionBlocks
          blockCount blocks (integrateQuaternionBlock block polynomial)
          (fun selected hselected =>
            hblocks selected (List.mem_cons_of_mem block hselected))
      · exact finiteProductHaar_integrateQuaternionBlock
          blockCount block (hblocks block List.mem_cons_self) polynomial

/-- Evaluation-level finite Fubini: permuting any in-range integration
schedule does not change the resulting full finite-product value. -/
theorem finiteProductHaar_integrateQuaternionBlocks_perm
    (blockCount : Nat) {left right : List Nat}
    (hperm : left.Perm right)
    (hleft : ∀ block, block ∈ left → block < blockCount)
    (polynomial : RatPoly) :
    finiteProductHaar blockCount
        (integrateQuaternionBlocks left polynomial) ≈
      finiteProductHaar blockCount
        (integrateQuaternionBlocks right polynomial) := by
  have hright : ∀ block, block ∈ right → block < blockCount := by
    intro block hblock
    exact hleft block ((hperm.mem_iff).mpr hblock)
  exact Q'.eqv_trans _ (finiteProductHaar blockCount polynomial) _
    (finiteProductHaar_integrateQuaternionBlocks
      blockCount left polynomial hleft)
    (Q'.eqv_symm
      (finiteProductHaar_integrateQuaternionBlocks
        blockCount right polynomial hright))

#print axioms exponentAt_clearQuaternionBlock
#print axioms exponentAt_clearQuaternionBlock_self
#print axioms clearQuaternionBlock_length
#print axioms clearQuaternionBlock_drop_of_lt
#print axioms clearQuaternionBlock_comm
#print axioms quaternionBlockMoment_clear_self
#print axioms quaternionBlockMoment_clear_of_ne
#print axioms quaternionBlockMoment_mul_clear_product
#print axioms quaternionBlockMoment_mul_finiteProductHaarMono_clear
#print axioms integrateQuaternionBlock_supported
#print axioms finiteProductHaar_integrateQuaternionBlock
#print axioms finiteProductHaar_integrateQuaternionBlocks
#print axioms finiteProductHaar_integrateQuaternionBlocks_perm

end YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
