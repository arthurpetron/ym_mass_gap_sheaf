/-
# Solid zonal SU(2) characters in the arbitrary-insertion Haar quotient

For a quaternion word built from four factors, the ordinary character obeys

  `chi_(n+2) = 2 s chi_(n+1) - chi_n`.

Its polynomially homogeneous (solid zonal) version replaces the last unit by
the product of the four squared radii.  This file proves, for every spin at
once, that the two recurrences define the same element of the exact
arbitrary-insertion product-Haar quotient.  The result is algebraic: each
radius is a proved unit under normalized `S^3` Haar.

The successor theorem still required for the full even-spin BF4
normalization is harmonic annihilation of the positive-degree solid zonal
polynomial in the selected head block.  That analytic statement is not
assumed here.
-/

import YMGap.Continuum.BF4CompactActionSphereShift

namespace YMGap.Continuum.SU2QuaternionSolidZonalCharacter

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## Block degree bookkeeping -/

/-- Every monomial has one exact total degree in a quaternion block. -/
def HasQuaternionBlockDegree
    (block degree : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    quaternionBlockDegree term.1 block = degree

/-- The variable monomial has exponent one at its named coordinate and zero
everywhere else.  This local syntactic lemma is useful for proving block
homogeneity without asking Lean to decide a quantified proposition. -/
theorem exponentAt_varMono
    (coordinate index : Nat) :
    exponentAt (varMono coordinate) index =
      if index = coordinate then 1 else 0 := by
  induction coordinate generalizing index with
  | zero =>
      cases index with
      | zero => rfl
      | succ index =>
          change ([1].getD (index + 1) 0) =
            if index + 1 = 0 then 1 else 0
          rw [List.getD_cons_succ, List.getD_nil]
          rw [if_neg (Nat.succ_ne_zero index)]
  | succ coordinate induction =>
      cases index with
      | zero => rfl
      | succ index =>
          change exponentAt (varMono coordinate) index =
            if index + 1 = coordinate + 1 then 1 else 0
          rw [induction]
          by_cases h : index = coordinate
          · subst index
            simp
          · simp [h]

/-- Degree of one coordinate variable relative to a quaternion block. -/
theorem quaternionBlockDegree_varMono
    (source offset block : Nat) (hoffset : offset < 4) :
    quaternionBlockDegree (varMono (4 * source + offset)) block =
      if block = source then 1 else 0 := by
  unfold quaternionBlockDegree
  simp only [exponentAt_varMono]
  by_cases hblock : block = source
  · subst block
    have hoffsetCases :
        offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by
      omega
    rcases hoffsetCases with rfl | rfl | rfl | rfl
    · have h1 : 4 * source + 1 ≠ 4 * source := by omega
      have h2 : 4 * source + 2 ≠ 4 * source := by omega
      have h3 : 4 * source + 3 ≠ 4 * source := by omega
      simp only [if_true, if_neg h1, if_neg h2, if_neg h3,
        Nat.add_zero]
    · have h0 : 4 * source ≠ 4 * source + 1 := by omega
      have h2 : 4 * source + 2 ≠ 4 * source + 1 := by omega
      have h3 : 4 * source + 3 ≠ 4 * source + 1 := by omega
      simp only [if_true, if_neg h0, if_neg h2, if_neg h3,
        Nat.zero_add, Nat.add_zero]
    · have h0 : 4 * source ≠ 4 * source + 2 := by omega
      have h1 : 4 * source + 1 ≠ 4 * source + 2 := by omega
      have h3 : 4 * source + 3 ≠ 4 * source + 2 := by omega
      simp only [if_true, if_neg h0, if_neg h1, if_neg h3,
        Nat.zero_add, Nat.add_zero]
    · have h0 : 4 * source ≠ 4 * source + 3 := by omega
      have h1 : 4 * source + 1 ≠ 4 * source + 3 := by omega
      have h2 : 4 * source + 2 ≠ 4 * source + 3 := by omega
      simp only [if_true, if_neg h0, if_neg h1, if_neg h2,
        Nat.zero_add, Nat.add_zero]
  · have h0 : 4 * block ≠ 4 * source + offset := by omega
    have h1 : 4 * block + 1 ≠ 4 * source + offset := by omega
    have h2 : 4 * block + 2 ≠ 4 * source + offset := by omega
    have h3 : 4 * block + 3 ≠ 4 * source + offset := by omega
    simp only [if_neg hblock, if_neg h0, if_neg h1,
      if_neg h2, if_neg h3, Nat.zero_add]

theorem hasQuaternionBlockDegree_zero
    (block degree : Nat) :
    HasQuaternionBlockDegree block degree polyZero := by
  intro term hterm
  simp [polyZero] at hterm

theorem hasQuaternionBlockDegree_coordinate
    (source offset block : Nat) (hoffset : offset < 4) :
    HasQuaternionBlockDegree block
      (if block = source then 1 else 0)
      (polyVar (4 * source + offset)) := by
  intro term hterm
  simp only [polyVar, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  exact quaternionBlockDegree_varMono source offset block hoffset

theorem hasQuaternionBlockDegree_radius
    (source block : Nat) :
    HasQuaternionBlockDegree block
      (if block = source then 2 else 0)
      (quaternionRadiusPolynomial source) :=
  quaternionRadiusPolynomial_blockDegree source block

private theorem blockDegree_monoMul
    (left right : List Nat) (block : Nat) :
    quaternionBlockDegree (monoMul left right) block =
      quaternionBlockDegree left block +
      quaternionBlockDegree right block := by
  have exponentAt_monoMul_local
      (first second : List Nat) (index : Nat) :
      exponentAt (monoMul first second) index =
        exponentAt first index + exponentAt second index := by
    induction first generalizing second index with
    | nil => simp [monoMul, exponentAt]
    | cons x xs induction =>
        cases second with
        | nil => simp [monoMul, exponentAt]
        | cons y ys =>
            cases index with
            | zero => simp [monoMul, exponentAt]
            | succ index =>
                change exponentAt (monoMul xs ys) index =
                  exponentAt xs index + exponentAt ys index
                exact induction ys index
  unfold quaternionBlockDegree
  rw [exponentAt_monoMul_local, exponentAt_monoMul_local,
    exponentAt_monoMul_local, exponentAt_monoMul_local]
  omega

theorem hasQuaternionBlockDegree_one (block : Nat) :
    HasQuaternionBlockDegree block 0 polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [quaternionBlockDegree, exponentAt]

theorem HasQuaternionBlockDegree.smul
    {block degree : Nat} {polynomial : RatPoly}
    (h : HasQuaternionBlockDegree block degree polynomial)
    (scale : Q') :
    HasQuaternionBlockDegree block degree
      (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq]
  exact h source hsource

theorem HasQuaternionBlockDegree.neg
    {block degree : Nat} {polynomial : RatPoly}
    (h : HasQuaternionBlockDegree block degree polynomial) :
    HasQuaternionBlockDegree block degree (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, htermEq⟩ := List.mem_map.mp hterm
  rw [← htermEq]
  exact h source hsource

theorem HasQuaternionBlockDegree.add
    {block degree : Nat} {left right : RatPoly}
    (hleft : HasQuaternionBlockDegree block degree left)
    (hright : HasQuaternionBlockDegree block degree right) :
    HasQuaternionBlockDegree block degree (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

theorem HasQuaternionBlockDegree.mul
    {block leftDegree rightDegree : Nat}
    {left right : RatPoly}
    (hleft : HasQuaternionBlockDegree block leftDegree left)
    (hright : HasQuaternionBlockDegree block rightDegree right) :
    HasQuaternionBlockDegree block (leftDegree + rightDegree)
      (polyMul left right) := by
  intro term hterm
  obtain ⟨source, hsource, htargetTerm⟩ :=
    List.mem_flatMap.mp hterm
  obtain ⟨target, htarget, htermEq⟩ :=
    List.mem_map.mp htargetTerm
  rw [← htermEq, blockDegree_monoMul,
    hleft source hsource, hright target htarget]

theorem HasQuaternionBlockDegree.relabel
    {block first second : Nat} {polynomial : RatPoly}
    (hdegree : first = second)
    (h : HasQuaternionBlockDegree block first polynomial) :
    HasQuaternionBlockDegree block second polynomial := by
  rw [← hdegree]
  exact h

/-- All four coordinate polynomials of a polynomial quaternion have the same
degree in the selected quaternion block. -/
structure HasPolyQuaternionBlockDegree
    (block degree : Nat) (quaternion : PolyQuaternion) : Prop where
  scalar : HasQuaternionBlockDegree block degree quaternion.scalar
  iPart : HasQuaternionBlockDegree block degree quaternion.iPart
  jPart : HasQuaternionBlockDegree block degree quaternion.jPart
  kPart : HasQuaternionBlockDegree block degree quaternion.kPart

theorem hasPolyQuaternionBlockDegree_coordinateVariable
    (source block : Nat) :
    HasPolyQuaternionBlockDegree block
      (if block = source then 1 else 0)
      (PolyQuaternion.coordinateVariable source) := by
  constructor
  · exact hasQuaternionBlockDegree_coordinate source 0 block (by omega)
  · exact hasQuaternionBlockDegree_coordinate source 1 block (by omega)
  · exact hasQuaternionBlockDegree_coordinate source 2 block (by omega)
  · exact hasQuaternionBlockDegree_coordinate source 3 block (by omega)

theorem HasPolyQuaternionBlockDegree.conj
    {block degree : Nat} {quaternion : PolyQuaternion}
    (h : HasPolyQuaternionBlockDegree block degree quaternion) :
    HasPolyQuaternionBlockDegree block degree
      (PolyQuaternion.conj quaternion) := by
  constructor
  · exact h.scalar
  · exact h.iPart.neg
  · exact h.jPart.neg
  · exact h.kPart.neg

theorem HasPolyQuaternionBlockDegree.mul
    {block leftDegree rightDegree : Nat}
    {left right : PolyQuaternion}
    (hleft : HasPolyQuaternionBlockDegree block leftDegree left)
    (hright : HasPolyQuaternionBlockDegree block rightDegree right) :
    HasPolyQuaternionBlockDegree block (leftDegree + rightDegree)
      (PolyQuaternion.mul left right) := by
  constructor
  · exact (hleft.scalar.mul hright.scalar).add
      (((hleft.iPart.mul hright.iPart).add
        ((hleft.jPart.mul hright.jPart).add
          (hleft.kPart.mul hright.kPart))).neg)
  · exact (hleft.scalar.mul hright.iPart).add
      ((hleft.iPart.mul hright.scalar).add
        ((hleft.jPart.mul hright.kPart).add
          ((hleft.kPart.mul hright.jPart).neg)))
  · exact (hleft.scalar.mul hright.jPart).add
      ((hleft.jPart.mul hright.scalar).add
        ((hleft.kPart.mul hright.iPart).add
          ((hleft.iPart.mul hright.kPart).neg)))
  · exact (hleft.scalar.mul hright.kPart).add
      ((hleft.kPart.mul hright.scalar).add
        ((hleft.iPart.mul hright.jPart).add
          ((hleft.jPart.mul hright.iPart).neg)))

theorem HasPolyQuaternionBlockDegree.relabel
    {block first second : Nat} {quaternion : PolyQuaternion}
    (hdegree : first = second)
    (h : HasPolyQuaternionBlockDegree block first quaternion) :
    HasPolyQuaternionBlockDegree block second quaternion := by
  rw [← hdegree]
  exact h

/-- Equality in the exact product-Haar carrier with every polynomial left
insertion retained. -/
def QuaternionHaarCarrierEqv
    (blocks : Nat) (left right : RatPoly) : Prop :=
  ∀ insertion : RatPoly,
    quaternionHaar blocks (polyMul insertion left) ≈
      quaternionHaar blocks (polyMul insertion right)

theorem QuaternionHaarCarrierEqv.refl
    (blocks : Nat) (polynomial : RatPoly) :
    QuaternionHaarCarrierEqv blocks polynomial polynomial := by
  intro insertion
  exact Q'.eqv_refl _

theorem QuaternionHaarCarrierEqv.symm
    {blocks : Nat} {left right : RatPoly}
    (h : QuaternionHaarCarrierEqv blocks left right) :
    QuaternionHaarCarrierEqv blocks right left := by
  intro insertion
  exact Q'.eqv_symm (h insertion)

theorem QuaternionHaarCarrierEqv.trans
    {blocks : Nat} {first middle last : RatPoly}
    (hfirst : QuaternionHaarCarrierEqv blocks first middle)
    (hlast : QuaternionHaarCarrierEqv blocks middle last) :
    QuaternionHaarCarrierEqv blocks first last := by
  intro insertion
  exact Q'.eqv_trans _ _ _
    (hfirst insertion) (hlast insertion)

theorem QuaternionHaarCarrierEqv.add
    {blocks : Nat} {left left' right right' : RatPoly}
    (hleft : QuaternionHaarCarrierEqv blocks left left')
    (hright : QuaternionHaarCarrierEqv blocks right right') :
    QuaternionHaarCarrierEqv blocks
      (polyAdd left right) (polyAdd left' right') := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul insertion left) +
      quaternionHaar blocks (polyMul insertion right)) _
    (quaternionHaar_polyMul_add_right blocks insertion left right) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul insertion left') +
      quaternionHaar blocks (polyMul insertion right')) _
    (Q'.add_eqv_congr' (hleft insertion) (hright insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_add_right blocks insertion left' right')

theorem QuaternionHaarCarrierEqv.smul
    {blocks : Nat} (scale : Q') {left right : RatPoly}
    (h : QuaternionHaarCarrierEqv blocks left right) :
    QuaternionHaarCarrierEqv blocks
      (polySmul scale left) (polySmul scale right) := by
  intro insertion
  refine Q'.eqv_trans _
    (scale * quaternionHaar blocks (polyMul insertion left)) _
    (quaternionHaar_polyMul_smul_right
      blocks scale insertion left) ?_
  refine Q'.eqv_trans _
    (scale * quaternionHaar blocks (polyMul insertion right)) _
    (Q'.mul_eqv_congr_left scale _ _ (h insertion)) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_smul_right
      blocks scale insertion right)

theorem QuaternionHaarCarrierEqv.mul_left
    {blocks : Nat} (factor : RatPoly) {left right : RatPoly}
    (h : QuaternionHaarCarrierEqv blocks left right) :
    QuaternionHaarCarrierEqv blocks
      (polyMul factor left) (polyMul factor right) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks insertion factor left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) right)) _
    (h (polyMul insertion factor)) ?_
  exact quaternionHaar_polyMul_assoc
    blocks insertion factor right

theorem QuaternionHaarCarrierEqv.mul_right
    {blocks : Nat} {left right : RatPoly}
    (h : QuaternionHaarCarrierEqv blocks left right)
    (factor : RatPoly) :
    QuaternionHaarCarrierEqv blocks
      (polyMul left factor) (polyMul right factor) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul factor left))) _
    (quaternionHaar_polyMul_middle_comm
      blocks insertion left factor) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks insertion factor left)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion factor) right)) _
    (h (polyMul insertion factor)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul factor right))) _
    (quaternionHaar_polyMul_assoc
      blocks insertion factor right) ?_
  exact quaternionHaar_polyMul_middle_comm
    blocks insertion factor right

theorem QuaternionHaarCarrierEqv.mul
    {blocks : Nat} {left left' right right' : RatPoly}
    (hleft : QuaternionHaarCarrierEqv blocks left left')
    (hright : QuaternionHaarCarrierEqv blocks right right') :
    QuaternionHaarCarrierEqv blocks
      (polyMul left right) (polyMul left' right') :=
  QuaternionHaarCarrierEqv.trans
    (QuaternionHaarCarrierEqv.mul_right hleft right)
    (QuaternionHaarCarrierEqv.mul_left left' hright)

/-- The literal polynomial unit is a unit in every Haar carrier. -/
theorem quaternionHaarCarrierEqv_one_mul
    (blocks : Nat) (polynomial : RatPoly) :
    QuaternionHaarCarrierEqv blocks
      (polyMul polyOne polynomial) polynomial := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul polynomial polyOne))) _
    (quaternionHaar_polyMul_middle_comm
      blocks insertion polyOne polynomial) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion polynomial) polyOne)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc
        blocks insertion polynomial polyOne)) ?_
  exact quaternionHaar_polyMul_one_right
    blocks (polyMul insertion polynomial)

/-- Product of the squared radii of any four quaternion blocks. -/
def fourQuaternionRadiusProductAt
    (block0 block1 block2 block3 : Nat) : RatPoly :=
  polyMul (quaternionRadiusPolynomial block0)
    (polyMul (quaternionRadiusPolynomial block1)
      (polyMul (quaternionRadiusPolynomial block2)
        (quaternionRadiusPolynomial block3)))

/-- Product of the first four squared quaternion radii. -/
def fourQuaternionRadiusProduct : RatPoly :=
  fourQuaternionRadiusProductAt 0 1 2 3

/-- Every one of the four radius factors is exactly one in the 116-block
arbitrary-insertion Haar carrier. -/
theorem fourQuaternionRadiusProductAt_eq_one
    (blocks block0 block1 block2 block3 : Nat)
    (h0 : block0 < blocks) (h1 : block1 < blocks)
    (h2 : block2 < blocks) (h3 : block3 < blocks) :
    QuaternionHaarCarrierEqv blocks
      (fourQuaternionRadiusProductAt block0 block1 block2 block3)
      polyOne := by
  intro insertion
  unfold fourQuaternionRadiusProductAt
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul
        (polyMul
          (polyMul (polyMul insertion
              (quaternionRadiusPolynomial block0))
            (quaternionRadiusPolynomial block1))
          (quaternionRadiusPolynomial block2))
        (quaternionRadiusPolynomial block3))) _ ?_ ?_
  · refine Q'.eqv_trans _
      (quaternionHaar blocks
        (polyMul
          (polyMul insertion (quaternionRadiusPolynomial block0))
          (polyMul (quaternionRadiusPolynomial block1)
            (polyMul (quaternionRadiusPolynomial block2)
              (quaternionRadiusPolynomial block3))))) _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc blocks _ _ _)) ?_
    refine Q'.eqv_trans _
      (quaternionHaar blocks
        (polyMul
          (polyMul
            (polyMul insertion (quaternionRadiusPolynomial block0))
            (quaternionRadiusPolynomial block1))
          (polyMul (quaternionRadiusPolynomial block2)
            (quaternionRadiusPolynomial block3)))) _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_assoc blocks _ _ _)) ?_
    exact Q'.eqv_symm
      (quaternionHaar_polyMul_assoc blocks _ _ _)
  · refine Q'.eqv_trans _
      (quaternionHaar blocks
        (polyMul
          (polyMul
            (polyMul insertion (quaternionRadiusPolynomial block0))
            (quaternionRadiusPolynomial block1))
          (quaternionRadiusPolynomial block2))) _
      (quaternionHaar_mul_radius blocks block3 h3 _) ?_
    refine Q'.eqv_trans _
      (quaternionHaar blocks
        (polyMul
          (polyMul insertion (quaternionRadiusPolynomial block0))
          (quaternionRadiusPolynomial block1))) _
      (quaternionHaar_mul_radius blocks block2 h2 _) ?_
    refine Q'.eqv_trans _
      (quaternionHaar blocks
        (polyMul insertion (quaternionRadiusPolynomial block0))) _
      (quaternionHaar_mul_radius blocks block1 h1 _) ?_
    refine Q'.eqv_trans _
      (quaternionHaar blocks insertion) _
      (quaternionHaar_mul_radius blocks block0 h0 insertion) ?_
    exact Q'.eqv_symm
      (quaternionHaar_polyMul_one_right blocks insertion)

/-- Specialization to the first four blocks of the literal BF4 carrier. -/
theorem fourQuaternionRadiusProduct_eq_one_116 :
    QuaternionHaarCarrierEqv 116
      fourQuaternionRadiusProduct polyOne := by
  exact fourQuaternionRadiusProductAt_eq_one
    116 0 1 2 3 (by omega) (by omega) (by omega) (by omega)

/-- Homogeneous zonal-character recurrence.  `radiusProduct` replaces the
unit in the Chebyshev recurrence. -/
def solidZonalCharacterPolynomial
    (scalar radiusProduct : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | 1 => polySmul 2 scalar
  | spin + 2 =>
      polyAdd
        (polyMul (polySmul 2 scalar)
          (solidZonalCharacterPolynomial scalar radiusProduct (spin + 1)))
        (polySmul (-1)
          (polyMul radiusProduct
            (solidZonalCharacterPolynomial scalar radiusProduct spin)))

/-- The solid recurrence is homogeneous of degree `spin` in every block in
which the scalar is linear and the radius product is quadratic. -/
theorem solidZonalCharacterPolynomial_blockDegree
    {block : Nat} {scalar radiusProduct : RatPoly}
    (hscalar : HasQuaternionBlockDegree block 1 scalar)
    (hradius : HasQuaternionBlockDegree block 2 radiusProduct) :
    ∀ spin,
      HasQuaternionBlockDegree block spin
        (solidZonalCharacterPolynomial scalar radiusProduct spin)
  | 0 => hasQuaternionBlockDegree_one block
  | 1 => hscalar.smul 2
  | spin + 2 => by
      apply HasQuaternionBlockDegree.add
      · exact HasQuaternionBlockDegree.relabel (by omega)
          ((hscalar.smul 2).mul
            (solidZonalCharacterPolynomial_blockDegree
              hscalar hradius (spin + 1)))
      · exact HasQuaternionBlockDegree.relabel (by omega)
          ((hradius.mul
            (solidZonalCharacterPolynomial_blockDegree
              hscalar hradius spin)).smul (-1))

/-- Solidification for any product-Haar carrier once the displayed radius
polynomial is a proved unit in its arbitrary-insertion quotient. -/
theorem solidZonalCharacterPolynomial_eq_character_of_radius_eq_one
    {blocks : Nat} (scalar radiusProduct : RatPoly)
    (hradius : QuaternionHaarCarrierEqv blocks radiusProduct polyOne) :
    ∀ spin,
    QuaternionHaarCarrierEqv blocks
      (solidZonalCharacterPolynomial
        scalar radiusProduct spin)
      (characterPolynomial scalar spin)
  | 0 => QuaternionHaarCarrierEqv.refl blocks polyOne
  | 1 => QuaternionHaarCarrierEqv.refl blocks (polySmul 2 scalar)
  | spin + 2 => by
      apply QuaternionHaarCarrierEqv.add
      · exact QuaternionHaarCarrierEqv.mul_left
          (polySmul 2 scalar)
          (solidZonalCharacterPolynomial_eq_character_of_radius_eq_one
            scalar radiusProduct hradius (spin + 1))
      · apply QuaternionHaarCarrierEqv.smul (-1)
        exact QuaternionHaarCarrierEqv.trans
          (QuaternionHaarCarrierEqv.mul
            hradius
            (solidZonalCharacterPolynomial_eq_character_of_radius_eq_one
              scalar radiusProduct hradius spin))
          (quaternionHaarCarrierEqv_one_mul
            blocks (characterPolynomial scalar spin))

/-- **All-spin solidification in the exact 116-block Haar carrier.** -/
theorem solidZonalCharacterPolynomial_eq_character_116
    (scalar : RatPoly) (spin : Nat) :
    QuaternionHaarCarrierEqv 116
      (solidZonalCharacterPolynomial
        scalar fourQuaternionRadiusProduct spin)
      (characterPolynomial scalar spin) :=
  solidZonalCharacterPolynomial_eq_character_of_radius_eq_one
    scalar fourQuaternionRadiusProduct
    fourQuaternionRadiusProduct_eq_one_116 spin

end YMGap.Continuum.SU2QuaternionSolidZonalCharacter

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.fourQuaternionRadiusProduct_eq_one_116
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.fourQuaternionRadiusProductAt_eq_one
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.exponentAt_varMono
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.quaternionBlockDegree_varMono
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.hasQuaternionBlockDegree_coordinate
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.hasPolyQuaternionBlockDegree_coordinateVariable
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.HasPolyQuaternionBlockDegree.mul
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.solidZonalCharacterPolynomial_blockDegree
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.solidZonalCharacterPolynomial_eq_character_of_radius_eq_one
#print axioms YMGap.Continuum.SU2QuaternionSolidZonalCharacter.solidZonalCharacterPolynomial_eq_character_116
