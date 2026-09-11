/-
# Parity-sector orthogonality for any finite quaternion product

The historical quaternion parity split was hard-coded to the eight scalar
coordinates of two quaternion blocks.  This leaf supplies the corresponding
dimension-uniform statement for the finite physical-link carrier.

A mismatch is carried as a constructive witness: one block below
`blockCount` and one of its four scalar components.  No parity vector and no
family of all parity assignments is materialized.  At the witness
coordinate, the exponent sum of a monomial pairing is odd, so that block's
exact `S^3` moment is zero.  A list induction propagates the zero through the
finite block-moment product, including its position in `List.range
blockCount`.

The monomial result is lifted through the raw finite Haar row and bilinear
folds.  Finally, two polynomial sectors described by lazy parity functions
`Nat -> Nat` are exactly orthogonal whenever one carried block/component
witnesses different assigned residues.  No structural support hypothesis is
needed: an out-of-carrier tail already lies in the zero branch of
`finiteProductHaarMono`.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-! ## 1. Lazy finite-block parity mismatch witnesses -/

/-- A coordinate-parity mismatch inside one specified quaternion block. -/
def QuaternionBlockParityMismatch
    (block : Nat) (left right : List Nat) : Prop :=
  ∃ component, component < 4 ∧
    exponentAt left (4 * block + component) % 2 ≠
      exponentAt right (4 * block + component) % 2

/-- A parity mismatch in one of the carried quaternion blocks.  This is an
existential witness, not a materialized vector of all coordinate parities. -/
def FiniteQuaternionParityMismatch
    (blockCount : Nat) (left right : List Nat) : Prop :=
  ∃ block, block < blockCount ∧
    QuaternionBlockParityMismatch block left right

/-- Two lazy coordinate-parity assignments differ at one carried
block/component.  This form is tailored to recursive per-block sector
decomposition. -/
def FiniteQuaternionParityAssignmentsMismatch
    (blockCount : Nat) (left right : Nat → Nat) : Prop :=
  ∃ block, block < blockCount ∧
    ∃ component, component < 4 ∧
      left (4 * block + component) ≠
        right (4 * block + component)

/-! ## 2. The mismatched block moment is zero -/

/-- If one scalar parity differs, the paired monomial has an odd exponent in
that scalar and hence zero exact sphere moment in the whole block. -/
theorem quaternionBlockMoment_monoMul_zero_of_parityMismatch
    (block : Nat) (left right : List Nat)
    (hmismatch : QuaternionBlockParityMismatch block left right) :
    quaternionBlockMoment block (monoMul left right) = 0 := by
  obtain ⟨component, hcomponent, hmismatch⟩ := hmismatch
  have hcases : component = 0 ∨ component = 1 ∨
      component = 2 ∨ component = 3 := by
    omega
  unfold quaternionBlockMoment
  simp only [exponentAt_monoMul]
  rcases hcases with hzero | hone | htwo | hthree
  · subst component
    simp only [Nat.add_zero] at hmismatch
    have hodd :
        (exponentAt left (4 * block) +
          exponentAt right (4 * block)) % 2 ≠ 0 := by
      omega
    simp [sphereMoment4, hodd]
  · subst component
    have hodd :
        (exponentAt left (4 * block + 1) +
          exponentAt right (4 * block + 1)) % 2 ≠ 0 := by
      omega
    simp [sphereMoment4, hodd]
  · subst component
    have hodd :
        (exponentAt left (4 * block + 2) +
          exponentAt right (4 * block + 2)) % 2 ≠ 0 := by
      omega
    simp [sphereMoment4, hodd]
  · subst component
    have hodd :
        (exponentAt left (4 * block + 3) +
          exponentAt right (4 * block + 3)) % 2 ≠ 0 := by
      omega
    simp [sphereMoment4, hodd]

/-- A zero block factor annihilates an arbitrary finite ordered block-moment
product whenever that block occurs in the order. -/
theorem quaternionBlockMomentProduct_zero_of_mem
    (monomial : List Nat) (block : Nat)
    (hzero : quaternionBlockMoment block monomial = 0) :
    ∀ (blocks : List Nat), block ∈ blocks →
      quaternionBlockMomentProduct monomial blocks ≈ 0
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
          subst head
          change
            quaternionBlockMoment block monomial *
                quaternionBlockMomentProduct monomial tail ≈ 0
          rw [hzero]
          exact Q'.zero_mul_eqv _
      | inr htail =>
          change
            quaternionBlockMoment head monomial *
                quaternionBlockMomentProduct monomial tail ≈ 0
          refine Q'.eqv_trans _
            (quaternionBlockMoment head monomial * 0) _
            (Q'.mul_eqv_congr_left _ _ _
              (quaternionBlockMomentProduct_zero_of_mem
                monomial block hzero tail htail)) ?_
          exact Q'.mul_zero_eqv _

/-! ## 3. Arbitrary-block monomial orthogonality -/

/-- **Dimension-uniform monomial parity orthogonality.**  A mismatch in any
carried block makes the full finite product-Haar monomial pairing zero. -/
theorem finiteProductHaarMono_cross_parity_zero
    (blockCount : Nat) (left right : List Nat)
    (hmismatch : FiniteQuaternionParityMismatch
      blockCount left right) :
    finiteProductHaarMono blockCount (monoMul left right) ≈ 0 := by
  obtain ⟨block, hblock, hmismatch⟩ := hmismatch
  have hzero : quaternionBlockMoment block (monoMul left right) = 0 :=
    quaternionBlockMoment_monoMul_zero_of_parityMismatch
      block left right hmismatch
  unfold finiteProductHaarMono
  by_cases htail :
      allZero ((monoMul left right).drop (4 * blockCount)) = true
  · rw [if_pos htail]
    exact quaternionBlockMomentProduct_zero_of_mem
      (monoMul left right) block hzero (List.range blockCount)
      (List.mem_range.mpr hblock)
  · have hfalse :
        allZero ((monoMul left right).drop (4 * blockCount)) = false := by
      cases hvalue :
          allZero ((monoMul left right).drop (4 * blockCount)) with
      | false => rfl
      | true => exact (htail hvalue).elim
    rw [hfalse]
    exact Q'.eqv_refl 0

/-! ## 4. Lifting the zero through finite polynomial folds -/

private theorem finiteHaarCell_cross_parity_zero
    (blockCount : Nat) (left right : RatTerm)
    (hmismatch : FiniteQuaternionParityMismatch
      blockCount left.1 right.1) :
    (left.2 * right.2) *
        finiteProductHaarMono blockCount
          (monoMul left.1 right.1) ≈ 0 := by
  refine Q'.eqv_trans _ ((left.2 * right.2) * 0) _
    (Q'.mul_eqv_congr_left _ _ _
      (finiteProductHaarMono_cross_parity_zero
        blockCount left.1 right.1 hmismatch)) ?_
  exact Q'.mul_zero_eqv _

theorem finiteHaarRow_cross_parity_zero
    (blockCount : Nat) (left : RatTerm) : ∀ right : RatPoly,
    (∀ term, term ∈ right →
      FiniteQuaternionParityMismatch blockCount left.1 term.1) →
    finiteHaarRow blockCount left right ≈ 0
  | [], _ => Q'.eqv_refl 0
  | term :: polynomial, hmismatch => by
      change
        (left.2 * term.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 term.1) +
            finiteHaarRow blockCount left polynomial ≈ 0
      refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
      · exact q_add_congr
          (finiteHaarCell_cross_parity_zero
            blockCount left term (hmismatch term (by simp)))
          (finiteHaarRow_cross_parity_zero
            blockCount left polynomial (fun other hother =>
              hmismatch other (by simp [hother])))
      · exact QPoly.q_zero_add_eqv 0

theorem finiteHaarBilinear_cross_parity_zero
    (blockCount : Nat) : ∀ left right : RatPoly,
    (∀ leftTerm, leftTerm ∈ left →
      ∀ rightTerm, rightTerm ∈ right →
        FiniteQuaternionParityMismatch
          blockCount leftTerm.1 rightTerm.1) →
    finiteHaarBilinear blockCount left right ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | term :: polynomial, right, hmismatch => by
      change
        finiteHaarRow blockCount term right +
            finiteHaarBilinear blockCount polynomial right ≈ 0
      refine Q'.eqv_trans _ ((0 : Q') + 0) _ ?_ ?_
      · exact q_add_congr
          (finiteHaarRow_cross_parity_zero
            blockCount term right (fun other hother =>
              hmismatch term (by simp) other hother))
          (finiteHaarBilinear_cross_parity_zero
            blockCount polynomial right
            (fun other hother final hfinal =>
              hmismatch other (by simp [hother]) final hfinal))
      · exact QPoly.q_zero_add_eqv 0

/-- If every cross pair of literal terms has a carried parity mismatch, the
complete raw polynomial product has zero finite product-Haar expectation. -/
theorem finiteProductHaar_mul_cross_parity_zero
    (blockCount : Nat) (left right : RatPoly)
    (hmismatch : ∀ leftTerm, leftTerm ∈ left →
      ∀ rightTerm, rightTerm ∈ right →
        FiniteQuaternionParityMismatch
          blockCount leftTerm.1 rightTerm.1) :
    finiteProductHaar blockCount (polyMul left right) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (finiteProductHaar_polyMul_eq_bilinear blockCount left right)
    (finiteHaarBilinear_cross_parity_zero
      blockCount left right hmismatch)

/-! ## 5. Orthogonality of lazy parity assignments -/

/-- Terms drawn from two different lazy carried-coordinate assignments have
an explicit finite-block parity-mismatch witness. -/
theorem finiteQuaternionParityMismatch_of_assignments
    {blockCount : Nat} {leftParity rightParity : Nat → Nat}
    {left right : RatTerm}
    (hmismatch : FiniteQuaternionParityAssignmentsMismatch
      blockCount leftParity rightParity)
    (hleft : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt left.1 coordinate % 2 = leftParity coordinate)
    (hright : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt right.1 coordinate % 2 = rightParity coordinate) :
    FiniteQuaternionParityMismatch blockCount left.1 right.1 := by
  obtain ⟨block, hblock, component, hcomponent, hvalues⟩ := hmismatch
  refine ⟨block, hblock, component, hcomponent, ?_⟩
  have hcoordinate : 4 * block + component < 4 * blockCount := by
    omega
  have hl := hleft (4 * block + component) hcoordinate
  have hr := hright (4 * block + component) hcoordinate
  intro heq
  exact hvalues (hl.symm.trans (heq.trans hr))

/-- **Exact orthogonality of different arbitrary-block parity sectors.**
The sector labels are lazy functions and only one block/component mismatch
witness is inspected. -/
theorem finiteProductHaar_distinct_parity_sectors_zero
    (blockCount : Nat) (leftParity rightParity : Nat → Nat)
    (left right : RatPoly)
    (hmismatch : FiniteQuaternionParityAssignmentsMismatch
      blockCount leftParity rightParity)
    (hleft : AllFiniteQuaternionCoordinateParity
      blockCount leftParity left)
    (hright : AllFiniteQuaternionCoordinateParity
      blockCount rightParity right) :
    finiteProductHaar blockCount (polyMul left right) ≈ 0 := by
  apply finiteProductHaar_mul_cross_parity_zero
  intro leftTerm hleftTerm rightTerm hrightTerm
  exact finiteQuaternionParityMismatch_of_assignments hmismatch
    (hleft leftTerm hleftTerm) (hright rightTerm hrightTerm)

#print axioms quaternionBlockMoment_monoMul_zero_of_parityMismatch
#print axioms quaternionBlockMomentProduct_zero_of_mem
#print axioms finiteProductHaarMono_cross_parity_zero
#print axioms finiteHaarRow_cross_parity_zero
#print axioms finiteHaarBilinear_cross_parity_zero
#print axioms finiteProductHaar_mul_cross_parity_zero
#print axioms finiteQuaternionParityMismatch_of_assignments
#print axioms finiteProductHaar_distinct_parity_sectors_zero

end YMGap.Continuum.SU2QuaternionFiniteProductHaarParitySectors
