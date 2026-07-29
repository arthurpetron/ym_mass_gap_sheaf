/-
# All-degree positivity for arbitrary-product quaternion Haar

The preceding module proves positivity inside one coordinate-parity sector.
Here a computable Boolean scan splits an arbitrary finite polynomial into
such sectors.  A parity mismatch in any retained coordinate makes the
corresponding product-Haar monomial moment exactly zero.  Well-founded
recursion on the complementary list then assembles the sector squares.

The capstone theorem applies to any finite number of quaternion blocks; its
`blocks = 10` specialization is the forty-coordinate BF4 double-Haar
positivity theorem.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

namespace YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

private theorem exponentAt_monoMul
    (left right : List Nat) (index : Nat) :
    exponentAt (monoMul left right) index =
      exponentAt left index + exponentAt right index := by
  induction left generalizing right index with
  | nil => simp [monoMul, exponentAt]
  | cons x xs induction =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases index with
          | zero => simp [monoMul, exponentAt]
          | succ index =>
              change exponentAt (monoMul xs ys) index =
                exponentAt xs index + exponentAt ys index
              exact induction ys index

private theorem monoMul_drop_of_length_le
    (left right : List Nat) (coordinates : Nat)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).drop coordinates =
      left.drop coordinates := by
  induction coordinates generalizing left right with
  | zero =>
      cases right with
      | nil => cases left <;> rfl
      | cons y ys => simp at hright
  | succ coordinates induction =>
      cases left with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le hright
      | cons x xs =>
          cases right with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at hright
              simp [monoMul,
                induction xs ys (by omega)]

private theorem monoMul_length_le
    {left right : List Nat} {coordinates : Nat}
    (hleft : left.length ≤ coordinates)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).length ≤ coordinates := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop_of_length_le
    left right coordinates hright]
  exact List.drop_eq_nil_of_le hleft

private theorem allZero_of_drop_nil
    (values : List Nat) (hvalues : values = []) :
    allZero values = true := by
  rw [hvalues]
  rfl

/-! ## A computable parity signature -/

def coordinateParitySameRange
    (start : Nat) : Nat → List Nat → List Nat → Bool
  | 0, _, _ => true
  | coordinates + 1, left, right =>
      decide
          (exponentAt left start % 2 =
            exponentAt right start % 2) &&
        coordinateParitySameRange
          (start + 1) coordinates left right

def quaternionParitySame
    (blocks : Nat) (left right : List Nat) : Bool :=
  coordinateParitySameRange
    0 (4 * blocks) left right

private theorem coordinateParitySameRange_true
    (left right : List Nat) :
    ∀ (start coordinates : Nat),
      coordinateParitySameRange
          start coordinates left right = true →
      ∀ index, start ≤ index →
        index < start + coordinates →
        exponentAt left index % 2 =
          exponentAt right index % 2
  | _, 0, _, _, _, hindex => by omega
  | start, coordinates + 1, hsame,
      index, hstart, hindex => by
      unfold coordinateParitySameRange at hsame
      rw [Bool.and_eq_true] at hsame
      rcases hsame with ⟨hhead, htail⟩
      have hhead :
          exponentAt left start % 2 =
            exponentAt right start % 2 := by
        exact of_decide_eq_true hhead
      by_cases heq : index = start
      · subst index
        exact hhead
      · exact coordinateParitySameRange_true
          left right (start + 1) coordinates
          htail index (by omega) (by omega)

theorem quaternionParitySame_true
    {blocks : Nat} {left right : List Nat}
    (hsame :
      quaternionParitySame blocks left right = true) :
    SameQuaternionParity blocks left right := by
  intro index hindex
  exact coordinateParitySameRange_true
    left right 0 (4 * blocks) hsame
    index (by omega) (by omega)

private theorem coordinateParitySameRange_of_equalities
    (left right : List Nat) :
    ∀ (start coordinates : Nat),
      (∀ index, start ≤ index →
        index < start + coordinates →
        exponentAt left index % 2 =
          exponentAt right index % 2) →
      coordinateParitySameRange
          start coordinates left right = true
  | _, 0, _ => rfl
  | start, coordinates + 1, hequalities => by
      have hhead :
          decide
              (exponentAt left start % 2 =
                exponentAt right start % 2) =
            true :=
        decide_eq_true
          (hequalities start
            (Nat.le_refl _) (by omega))
      have htail :=
        coordinateParitySameRange_of_equalities
          left right (start + 1) coordinates
          (fun index hstart hindex =>
            hequalities index (by omega) (by omega))
      unfold coordinateParitySameRange
      rw [hhead, htail]
      rfl

theorem quaternionParitySame_of_same
    {blocks : Nat} {left right : List Nat}
    (hsame :
      SameQuaternionParity blocks left right) :
    quaternionParitySame blocks left right = true := by
  unfold quaternionParitySame
  exact coordinateParitySameRange_of_equalities
    left right 0 (4 * blocks)
    (fun index hstart hindex =>
      hsame index (by omega))

private theorem coordinateParitySameRange_false
    (left right : List Nat) :
    ∀ (start coordinates : Nat),
      coordinateParitySameRange
          start coordinates left right = false →
      ∃ index,
        start ≤ index ∧
        index < start + coordinates ∧
        exponentAt left index % 2 ≠
          exponentAt right index % 2
  | _, 0, hfalse => by
      simp [coordinateParitySameRange] at hfalse
  | start, coordinates + 1, hfalse => by
      by_cases hhead :
          exponentAt left start % 2 =
            exponentAt right start % 2
      · have htail :
          coordinateParitySameRange
              (start + 1) coordinates left right =
            false := by
          simpa [coordinateParitySameRange,
            hhead] using hfalse
        obtain ⟨index, hstart, hindex,
            hmismatch⟩ :=
          coordinateParitySameRange_false
            left right (start + 1)
            coordinates htail
        exact ⟨index, by omega, by omega,
          hmismatch⟩
      · exact ⟨start, Nat.le_refl _,
          by omega, hhead⟩

theorem quaternionParitySame_false
    {blocks : Nat} {left right : List Nat}
    (hsame :
      quaternionParitySame blocks left right = false) :
    ∃ index, index < 4 * blocks ∧
      exponentAt left index % 2 ≠
        exponentAt right index % 2 := by
  obtain ⟨index, hstart, hindex, hmismatch⟩ :=
    coordinateParitySameRange_false
      left right 0 (4 * blocks) hsame
  exact ⟨index, by omega, hmismatch⟩

/-! ## Exact cross-sector annihilation -/

private theorem quaternionHaarRange_cross_parity_zero
    (left right : List Nat) :
    ∀ (start blocks index : Nat),
      start ≤ index →
      index < start + 4 * blocks →
      exponentAt left index % 2 ≠
        exponentAt right index % 2 →
      quaternionHaarRange start blocks
          (monoMul left right) ≈ 0
  | _, 0, _, _, hindex, _ => by omega
  | start, blocks + 1, index,
      hstart, hindex, hmismatch => by
      unfold quaternionHaarRange
      by_cases hhead : index < start + 4
      · have hcases :
          index = start ∨ index = start + 1 ∨
            index = start + 2 ∨
              index = start + 3 := by
          omega
        have hzero :
            sphereMoment4
                (exponentAt
                  (monoMul left right) start)
                (exponentAt
                  (monoMul left right) (start + 1))
                (exponentAt
                  (monoMul left right) (start + 2))
                (exponentAt
                  (monoMul left right) (start + 3)) =
              0 := by
          rcases hcases with
            hcase | hcase | hcase | hcase
          · subst index
            simp only [exponentAt_monoMul]
            have hodd :
                (exponentAt left start +
                    exponentAt right start) % 2 ≠ 0 := by
              omega
            simp [sphereMoment4, hodd]
          · subst index
            simp only [exponentAt_monoMul]
            have hodd :
                (exponentAt left (start + 1) +
                    exponentAt right (start + 1)) % 2 ≠ 0 := by
              omega
            simp [sphereMoment4, hodd]
          · subst index
            simp only [exponentAt_monoMul]
            have hodd :
                (exponentAt left (start + 2) +
                    exponentAt right (start + 2)) % 2 ≠ 0 := by
              omega
            simp [sphereMoment4, hodd]
          · subst index
            simp only [exponentAt_monoMul]
            have hodd :
                (exponentAt left (start + 3) +
                    exponentAt right (start + 3)) % 2 ≠ 0 := by
              omega
            simp [sphereMoment4, hodd]
        rw [hzero]
        exact Q'.zero_mul_eqv _
      · have htail :=
          quaternionHaarRange_cross_parity_zero
            left right (start + 4) blocks index
            (by omega) (by omega) hmismatch
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ htail)
          (Q'.mul_zero_eqv _)

private theorem exponentAt_drop
    (monomial : List Nat) :
    ∀ (offset index : Nat),
      exponentAt (monomial.drop offset) index =
        exponentAt monomial (offset + index)
  | 0, index => by
      simp [exponentAt]
  | offset + 1, index => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons exponent rest =>
          have hindex :
              offset + 1 + index =
                (offset + index) + 1 := by
            omega
          rw [hindex]
          simp only [List.drop_succ_cons]
          unfold exponentAt
          simp only [List.getD_cons_succ]
          exact exponentAt_drop rest offset index

private theorem quaternionHaarPrefix_drop_eq_range
    (monomial : List Nat) :
    ∀ (start blocks : Nat),
      quaternionHaarPrefix blocks
          (monomial.drop start) ≈
        quaternionHaarRange start blocks monomial
  | _, 0 => Q'.eqv_refl 1
  | start, blocks + 1 => by
      unfold quaternionHaarPrefix quaternionHaarRange
      rw [exponentAt_drop monomial start 0,
        exponentAt_drop monomial start 1,
        exponentAt_drop monomial start 2,
        exponentAt_drop monomial start 3]
      simp only [Nat.add_zero]
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      have induction :=
        quaternionHaarPrefix_drop_eq_range
          monomial (start + 4) blocks
      simpa [List.drop_drop, Nat.add_assoc] using
        induction

private theorem quaternionHaarPrefix_eq_range
    (monomial : List Nat) (blocks : Nat) :
    quaternionHaarPrefix blocks monomial ≈
      quaternionHaarRange 0 blocks monomial := by
  simpa using
    quaternionHaarPrefix_drop_eq_range
      monomial 0 blocks

theorem quaternionHaarMono_cross_parity_zero
    (blocks : Nat) (left right : List Nat)
    (hleft : left.length ≤ 4 * blocks)
    (hright : right.length ≤ 4 * blocks)
    (hmismatch :
      quaternionParitySame blocks left right = false) :
    quaternionHaarMono blocks
        (monoMul left right) ≈ 0 := by
  have hlength :
      (monoMul left right).length ≤
        4 * blocks :=
    monoMul_length_le hleft hright
  have htail :
      allZero
          ((monoMul left right).drop
            (4 * blocks)) =
        true :=
    allZero_of_drop_nil _
      (List.drop_eq_nil_of_le hlength)
  obtain ⟨index, hindex, hparity⟩ :=
    quaternionParitySame_false hmismatch
  unfold quaternionHaarMono
  rw [if_pos htail]
  refine Q'.eqv_trans _
    (quaternionHaarRange 0 blocks
      (monoMul left right)) _
    (quaternionHaarPrefix_eq_range
      (monoMul left right) blocks) ?_
  exact quaternionHaarRange_cross_parity_zero
    left right 0 blocks index
    (by omega) (by omega) hparity

private theorem quaternionHaarRow_cross_zero
    (blocks : Nat) (source : RatTerm)
    (hsource :
      source.1.length ≤ 4 * blocks) :
    ∀ target : RatPoly,
      SupportedQuaternionBlocks blocks target →
      (∀ term, term ∈ target →
        quaternionParitySame
          blocks source.1 term.1 = false) →
      quaternionHaarRow blocks source target ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | term :: rest, hsupport, hmismatch => by
      change
        (source.2 * term.2) *
              quaternionHaarMono blocks
                (monoMul source.1 term.1) +
            quaternionHaarRow
              blocks source rest ≈ 0
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (quaternionHaarMono_cross_parity_zero
                blocks source.1 term.1 hsource
                (hsupport term (by simp))
                (hmismatch term (by simp))))
            (Q'.mul_zero_eqv _))
          (quaternionHaarRow_cross_zero
            blocks source hsource rest
            (fun other hother =>
              hsupport other (by simp [hother]))
            (fun other hother =>
              hmismatch other (by simp [hother])))
      · exact QPoly.q_zero_add_eqv 0

private theorem quaternionHaar_cross_zero
    (blocks : Nat) :
    ∀ left right : RatPoly,
      SupportedQuaternionBlocks blocks left →
      SupportedQuaternionBlocks blocks right →
      (∀ source, source ∈ left →
        ∀ target, target ∈ right →
          quaternionParitySame
            blocks source.1 target.1 = false) →
      quaternionHaarBilinear
        blocks left right ≈ 0
  | [], _, _, _, _ => Q'.eqv_refl 0
  | source :: rest, right,
      hleft, hright, hmismatch => by
      change
        quaternionHaarRow blocks source right +
            quaternionHaarBilinear
              blocks rest right ≈ 0
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact QPoly.q_add_congr
          (quaternionHaarRow_cross_zero
            blocks source
            (hleft source (by simp))
            right hright
            (fun target htarget =>
              hmismatch source (by simp)
                target htarget))
          (quaternionHaar_cross_zero
            blocks rest right
            (fun term hterm =>
              hleft term (by simp [hterm]))
            hright
            (fun leftTerm hleftTerm
                rightTerm hrightTerm =>
              hmismatch leftTerm
                (by simp [hleftTerm])
                rightTerm hrightTerm))
      · exact QPoly.q_zero_add_eqv 0

theorem quaternionHaar_polyMul_cross_parity_zero
    (blocks : Nat) (left right : RatPoly)
    (hleft :
      SupportedQuaternionBlocks blocks left)
    (hright :
      SupportedQuaternionBlocks blocks right)
    (hmismatch :
      ∀ source, source ∈ left →
        ∀ target, target ∈ right →
          quaternionParitySame
            blocks source.1 target.1 = false) :
    quaternionHaar blocks
        (polyMul left right) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul
      blocks left right)
    (quaternionHaar_cross_zero
      blocks left right hleft hright hmismatch)

/-! ## Sector splitting and well-founded assembly -/

def quaternionParitySector
    (blocks : Nat) (reference : List Nat) :
    RatPoly → RatPoly
  | [] => []
  | term :: rest =>
      if quaternionParitySame
          blocks reference term.1 then
        term ::
          quaternionParitySector
            blocks reference rest
      else
        quaternionParitySector
          blocks reference rest

def quaternionParityComplement
    (blocks : Nat) (reference : List Nat) :
    RatPoly → RatPoly
  | [] => []
  | term :: rest =>
      if quaternionParitySame
          blocks reference term.1 then
        quaternionParityComplement
          blocks reference rest
      else
        term ::
          quaternionParityComplement
            blocks reference rest

private theorem bool_false_of_not_true
    {value : Bool} (hvalue : ¬ value = true) :
    value = false := by
  cases h : value with
  | false => rfl
  | true => exact (hvalue h).elim

theorem quaternionParitySector_all
    (blocks : Nat) (reference : List Nat) :
    ∀ polynomial,
      ∀ term, term ∈
          quaternionParitySector
            blocks reference polynomial →
        SameQuaternionParity
          blocks reference term.1
  | [], term, hterm => by
      simp [quaternionParitySector] at hterm
  | head :: rest, term, hterm => by
      unfold quaternionParitySector at hterm
      split at hterm
      next hsame =>
        simp only [List.mem_cons] at hterm
        rcases hterm with rfl | hterm
        · exact quaternionParitySame_true hsame
        · exact quaternionParitySector_all
            blocks reference rest term hterm
      next _ =>
        exact quaternionParitySector_all
          blocks reference rest term hterm

theorem quaternionParityComplement_false
    (blocks : Nat) (reference : List Nat) :
    ∀ polynomial,
      ∀ term, term ∈
          quaternionParityComplement
            blocks reference polynomial →
        quaternionParitySame
          blocks reference term.1 = false
  | [], term, hterm => by
      simp [quaternionParityComplement] at hterm
  | head :: rest, term, hterm => by
      unfold quaternionParityComplement at hterm
      split at hterm
      next _ =>
        exact quaternionParityComplement_false
          blocks reference rest term hterm
      next hsame =>
        simp only [List.mem_cons] at hterm
        rcases hterm with rfl | hterm
        · exact bool_false_of_not_true hsame
        · exact quaternionParityComplement_false
            blocks reference rest term hterm

private theorem quaternionParitySector_supported
    (blocks : Nat) (reference : List Nat) :
    ∀ polynomial,
      SupportedQuaternionBlocks blocks polynomial →
      SupportedQuaternionBlocks blocks
        (quaternionParitySector
          blocks reference polynomial)
  | [], _ => by
      intro term hterm
      simp [quaternionParitySector] at hterm
  | head :: rest, hsupport => by
      unfold quaternionParitySector
      split
      next _ =>
        intro term hterm
        simp only [List.mem_cons] at hterm
        rcases hterm with rfl | hterm
        · exact hsupport term (by simp)
        · exact quaternionParitySector_supported
            blocks reference rest
            (fun other hother =>
              hsupport other (by simp [hother]))
            term hterm
      next _ =>
        exact quaternionParitySector_supported
          blocks reference rest
          (fun other hother =>
            hsupport other (by simp [hother]))

private theorem quaternionParityComplement_supported
    (blocks : Nat) (reference : List Nat) :
    ∀ polynomial,
      SupportedQuaternionBlocks blocks polynomial →
      SupportedQuaternionBlocks blocks
        (quaternionParityComplement
          blocks reference polynomial)
  | [], _ => by
      intro term hterm
      simp [quaternionParityComplement] at hterm
  | head :: rest, hsupport => by
      unfold quaternionParityComplement
      split
      next _ =>
        exact quaternionParityComplement_supported
          blocks reference rest
          (fun other hother =>
            hsupport other (by simp [hother]))
      next _ =>
        intro term hterm
        simp only [List.mem_cons] at hterm
        rcases hterm with rfl | hterm
        · exact hsupport term (by simp)
        · exact quaternionParityComplement_supported
            blocks reference rest
            (fun other hother =>
              hsupport other (by simp [hother]))
            term hterm

private theorem quaternionParityComplement_length_le
    (blocks : Nat) (reference : List Nat) :
    ∀ polynomial,
      (quaternionParityComplement
        blocks reference polynomial).length ≤
      polynomial.length
  | [] => by simp [quaternionParityComplement]
  | head :: rest => by
      unfold quaternionParityComplement
      split
      next _ =>
        have induction :=
          quaternionParityComplement_length_le
            blocks reference rest
        simp only [List.length_cons]
        omega
      next _ =>
        have induction :=
          quaternionParityComplement_length_le
            blocks reference rest
        simp only [List.length_cons]
        omega

private theorem quaternionHaar_append
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks (left ++ right) ≈
        quaternionHaar blocks left +
          quaternionHaar blocks right
  | [], right =>
      Q'.eqv_symm
        (QPoly.q_zero_add_eqv _)
  | term :: rest, right => by
      change
        term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks (rest ++ right) ≈
          (term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest) +
            quaternionHaar blocks right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaar_append
            blocks rest right))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv _ _ _))

private theorem quaternionHaar_polyMul_cons_left
    (blocks : Nat) (head : RatTerm)
    (rest right : RatPoly) :
    quaternionHaar blocks
        (polyMul (head :: rest) right) ≈
      quaternionHaar blocks
          (polyMul [head] right) +
        quaternionHaar blocks
          (polyMul rest right) := by
  have hmul :
      polyMul (head :: rest) right =
        polyMul [head] right ++
          polyMul rest right := by
    simp [polyMul]
  rw [hmul]
  exact quaternionHaar_append blocks _ _

private theorem quaternionHaar_parity_split_left
    (blocks : Nat) (reference : List Nat) :
    ∀ polynomial right : RatPoly,
      quaternionHaar blocks
          (polyMul polynomial right) ≈
        quaternionHaar blocks
            (polyMul
              (quaternionParitySector
                blocks reference polynomial)
              right) +
          quaternionHaar blocks
            (polyMul
              (quaternionParityComplement
                blocks reference polynomial)
              right)
  | [], right => by
      simp [quaternionParitySector,
        quaternionParityComplement, polyMul]
      exact Q'.eqv_symm
        (QPoly.q_zero_add_eqv 0)
  | head :: rest, right => by
      by_cases hsame :
          quaternionParitySame
            blocks reference head.1 = true
      · simp only [quaternionParitySector,
          quaternionParityComplement, if_pos hsame]
        refine Q'.eqv_trans _
          (quaternionHaar blocks
                (polyMul [head] right) +
            quaternionHaar blocks
                (polyMul rest right)) _
          (quaternionHaar_polyMul_cons_left
            blocks head rest right) ?_
        refine Q'.eqv_trans _
          (quaternionHaar blocks
                (polyMul [head] right) +
            (quaternionHaar blocks
                (polyMul
                  (quaternionParitySector
                    blocks reference rest) right) +
              quaternionHaar blocks
                (polyMul
                  (quaternionParityComplement
                    blocks reference rest) right))) _
          (Q'.add_eqv_congr_left _ _ _
            (quaternionHaar_parity_split_left
              blocks reference rest right)) ?_
        refine Q'.eqv_trans _
          ((quaternionHaar blocks
                (polyMul [head] right) +
              quaternionHaar blocks
                (polyMul
                  (quaternionParitySector
                    blocks reference rest) right)) +
            quaternionHaar blocks
              (polyMul
                (quaternionParityComplement
                  blocks reference rest) right)) _
          (Q'.eqv_symm
            (Q'.add_assoc_eqv _ _ _)) ?_
        exact Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm
            (quaternionHaar_polyMul_cons_left
              blocks head
              (quaternionParitySector
                blocks reference rest) right))
      · have hfalse :=
          bool_false_of_not_true hsame
        simp only [quaternionParitySector,
          quaternionParityComplement, if_neg hsame]
        refine Q'.eqv_trans _
          (quaternionHaar blocks
                (polyMul [head] right) +
            quaternionHaar blocks
                (polyMul rest right)) _
          (quaternionHaar_polyMul_cons_left
            blocks head rest right) ?_
        refine Q'.eqv_trans _
          (quaternionHaar blocks
                (polyMul [head] right) +
            (quaternionHaar blocks
                (polyMul
                  (quaternionParitySector
                    blocks reference rest) right) +
              quaternionHaar blocks
                (polyMul
                  (quaternionParityComplement
                    blocks reference rest) right))) _
          (Q'.add_eqv_congr_left _ _ _
            (quaternionHaar_parity_split_left
              blocks reference rest right)) ?_
        refine Q'.eqv_trans _
          ((quaternionHaar blocks
                (polyMul [head] right) +
              quaternionHaar blocks
                (polyMul
                  (quaternionParitySector
                    blocks reference rest) right)) +
            quaternionHaar blocks
              (polyMul
                (quaternionParityComplement
                  blocks reference rest) right)) _
          (Q'.eqv_symm
            (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((quaternionHaar blocks
                (polyMul
                  (quaternionParitySector
                    blocks reference rest) right) +
              quaternionHaar blocks
                (polyMul [head] right)) +
            quaternionHaar blocks
              (polyMul
                (quaternionParityComplement
                  blocks reference rest) right)) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_comm_eqv _ _)) ?_
        refine Q'.eqv_trans _
          (quaternionHaar blocks
                (polyMul
                  (quaternionParitySector
                    blocks reference rest) right) +
            (quaternionHaar blocks
                (polyMul [head] right) +
              quaternionHaar blocks
                (polyMul
                  (quaternionParityComplement
                    blocks reference rest) right))) _
          (Q'.add_assoc_eqv _ _ _) ?_
        exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (quaternionHaar_polyMul_cons_left
              blocks head
              (quaternionParityComplement
                blocks reference rest) right))

private theorem quaternionHaar_parity_split_right
    (blocks : Nat) (reference : List Nat)
    (left polynomial : RatPoly) :
    quaternionHaar blocks
        (polyMul left polynomial) ≈
      quaternionHaar blocks
          (polyMul left
            (quaternionParitySector
              blocks reference polynomial)) +
        quaternionHaar blocks
          (polyMul left
            (quaternionParityComplement
              blocks reference polynomial)) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul polynomial left)) _
    (quaternionHaar_polyMul_comm
      blocks left polynomial) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
          (polyMul
            (quaternionParitySector
              blocks reference polynomial) left) +
      quaternionHaar blocks
          (polyMul
            (quaternionParityComplement
              blocks reference polynomial) left)) _
    (quaternionHaar_parity_split_left
      blocks reference polynomial left) ?_
  exact QPoly.q_add_congr
    (quaternionHaar_polyMul_comm
      blocks
      (quaternionParitySector
        blocks reference polynomial) left)
    (quaternionHaar_polyMul_comm
      blocks
      (quaternionParityComplement
        blocks reference polynomial) left)

private theorem quaternionHaar_sector_complement_zero
    (blocks : Nat) (reference : List Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks
        (polyMul
          (quaternionParitySector
            blocks reference polynomial)
          (quaternionParityComplement
            blocks reference polynomial)) ≈ 0 := by
  apply quaternionHaar_polyMul_cross_parity_zero
  · exact quaternionParitySector_supported
      blocks reference polynomial hsupport
  · exact quaternionParityComplement_supported
      blocks reference polynomial hsupport
  · intro source hsource target htarget
    have hsourceParity :=
      quaternionParitySector_all
        blocks reference polynomial
        source hsource
    have htargetFalse :=
      quaternionParityComplement_false
        blocks reference polynomial
        target htarget
    by_cases hsame :
        quaternionParitySame
          blocks source.1 target.1 = true
    · have hsourceTarget :=
        quaternionParitySame_true hsame
      have hreferenceTarget :
          SameQuaternionParity
            blocks reference target.1 := by
        intro index hindex
        exact (hsourceParity index hindex).trans
          (hsourceTarget index hindex)
      have hreferenceSame :
          quaternionParitySame
            blocks reference target.1 = true := by
        exact quaternionParitySame_of_same
          hreferenceTarget
      exact Bool.noConfusion
        (hreferenceSame.symm.trans htargetFalse)
    · exact bool_false_of_not_true hsame

private theorem quaternionHaar_complement_sector_zero
    (blocks : Nat) (reference : List Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks
        (polyMul
          (quaternionParityComplement
            blocks reference polynomial)
          (quaternionParitySector
            blocks reference polynomial)) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_comm blocks _ _)
    (quaternionHaar_sector_complement_zero
      blocks reference polynomial hsupport)

theorem quaternionHaar_parity_square_split
    (blocks : Nat) (reference : List Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    quaternionHaar blocks
        (polyMul polynomial polynomial) ≈
      quaternionHaar blocks
          (polyMul
            (quaternionParitySector
              blocks reference polynomial)
            (quaternionParitySector
              blocks reference polynomial)) +
        quaternionHaar blocks
          (polyMul
            (quaternionParityComplement
              blocks reference polynomial)
            (quaternionParityComplement
              blocks reference polynomial)) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks
          (polyMul
            (quaternionParitySector
              blocks reference polynomial)
            polynomial) +
      quaternionHaar blocks
          (polyMul
            (quaternionParityComplement
              blocks reference polynomial)
            polynomial)) _
    (quaternionHaar_parity_split_left
      blocks reference polynomial polynomial) ?_
  refine Q'.eqv_trans _
    ((quaternionHaar blocks
          (polyMul
            (quaternionParitySector
              blocks reference polynomial)
            (quaternionParitySector
              blocks reference polynomial)) +
        quaternionHaar blocks
          (polyMul
            (quaternionParitySector
              blocks reference polynomial)
            (quaternionParityComplement
              blocks reference polynomial))) +
      (quaternionHaar blocks
          (polyMul
            (quaternionParityComplement
              blocks reference polynomial)
            (quaternionParitySector
              blocks reference polynomial)) +
        quaternionHaar blocks
          (polyMul
            (quaternionParityComplement
              blocks reference polynomial)
            (quaternionParityComplement
              blocks reference polynomial)))) _
    (QPoly.q_add_congr
      (quaternionHaar_parity_split_right
        blocks reference
        (quaternionParitySector
          blocks reference polynomial)
        polynomial)
      (quaternionHaar_parity_split_right
        blocks reference
        (quaternionParityComplement
          blocks reference polynomial)
        polynomial)) ?_
  refine Q'.eqv_trans _
    ((quaternionHaar blocks
          (polyMul
            (quaternionParitySector
              blocks reference polynomial)
            (quaternionParitySector
              blocks reference polynomial)) + 0) +
      (0 +
        quaternionHaar blocks
          (polyMul
            (quaternionParityComplement
              blocks reference polynomial)
            (quaternionParityComplement
              blocks reference polynomial)))) _
    (QPoly.q_add_congr
      (QPoly.q_add_congr
        (Q'.eqv_refl _)
        (quaternionHaar_sector_complement_zero
          blocks reference polynomial hsupport))
      (QPoly.q_add_congr
        (quaternionHaar_complement_sector_zero
          blocks reference polynomial hsupport)
        (Q'.eqv_refl _))) ?_
  exact QPoly.q_add_congr
    (QPoly.q_add_zero_eqv _)
    (QPoly.q_zero_add_eqv _)

private theorem quaternionHaar_square_nonnegative_fuel :
    ∀ (fuel blocks : Nat) (polynomial : RatPoly),
      polynomial.length ≤ fuel →
      SupportedQuaternionBlocks blocks polynomial →
      (0 : Q') ≤
        quaternionHaar blocks
          (polyMul polynomial polynomial)
  | 0, blocks, [], _, _ =>
      quaternionHaar_square_nonnegative_of_parity
        blocks []
        (by intro term hterm; simp at hterm)
        (by
          intro left hleft
          simp at hleft)
  | 0, _, _ :: _, hlength, _ => by
      simp at hlength
  | _ + 1, blocks, [], _, _ =>
      quaternionHaar_square_nonnegative_of_parity
        blocks []
        (by intro term hterm; simp at hterm)
        (by
          intro left hleft
          simp at hleft)
  | fuel + 1, blocks, head :: rest,
      hlength, hsupport => by
      let sector :=
        quaternionParitySector
          blocks head.1 (head :: rest)
      let complement :=
        quaternionParityComplement
          blocks head.1 (head :: rest)
      have hsectorSupport :
          SupportedQuaternionBlocks
            blocks sector :=
        quaternionParitySector_supported
          blocks head.1 (head :: rest) hsupport
      have hsectorParity :
          ∀ left, left ∈ sector →
            ∀ right, right ∈ sector →
              SameQuaternionParity
                blocks left.1 right.1 := by
        intro left hleft right hright
        have hleftParity :=
          quaternionParitySector_all
            blocks head.1 (head :: rest)
            left hleft
        have hrightParity :=
          quaternionParitySector_all
            blocks head.1 (head :: rest)
            right hright
        intro index hindex
        exact (hleftParity index hindex).symm.trans
          (hrightParity index hindex)
      have hcomplementSupport :
          SupportedQuaternionBlocks
            blocks complement :=
        quaternionParityComplement_supported
          blocks head.1 (head :: rest) hsupport
      have hcomplementLength :
          complement.length ≤ fuel := by
        have htailLength :=
          quaternionParityComplement_length_le
            blocks head.1 rest
        have hheadSame :
            quaternionParitySame
              blocks head.1 head.1 = true := by
          exact quaternionParitySame_of_same
            (fun index hindex => rfl)
        change
          (quaternionParityComplement
            blocks head.1 (head :: rest)).length ≤
            fuel
        rw [show
          quaternionParityComplement
              blocks head.1 (head :: rest) =
            quaternionParityComplement
              blocks head.1 rest by
          simp [quaternionParityComplement,
            hheadSame]]
        simp only [List.length_cons] at hlength
        omega
      have hsectorNonnegative :
          (0 : Q') ≤
            quaternionHaar blocks
              (polyMul sector sector) :=
        quaternionHaar_square_nonnegative_of_parity
          blocks sector
          hsectorSupport hsectorParity
      have hcomplementNonnegative :
          (0 : Q') ≤
            quaternionHaar blocks
              (polyMul complement complement) :=
        quaternionHaar_square_nonnegative_fuel
          fuel blocks complement
          hcomplementLength hcomplementSupport
      have hsum :
          (0 : Q') ≤
            quaternionHaar blocks
                (polyMul sector sector) +
              quaternionHaar blocks
                (polyMul complement complement) :=
        Q'.zero_le_add _ _
          hsectorNonnegative
          hcomplementNonnegative
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (quaternionHaar_parity_square_split
              blocks head.1 (head :: rest)
              hsupport)))

/-- The exact normalized Haar moment functional on `SU(2)^blocks` is
positive on the square of every finite supported rational polynomial. -/
theorem quaternionHaar_square_nonnegative
    (blocks : Nat) (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    (0 : Q') ≤
      quaternionHaar blocks
        (polyMul polynomial polynomial) :=
  quaternionHaar_square_nonnegative_fuel
    polynomial.length blocks polynomial
    (Nat.le_refl _) hsupport

/-- Forty-coordinate BF4 specialization. -/
theorem tenfoldHaar_square_nonnegative
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    (0 : Q') ≤
      tenfoldHaar
        (polyMul polynomial polynomial) :=
  quaternionHaar_square_nonnegative
    10 polynomial hsupport

end YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity

#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity.quaternionHaarMono_cross_parity_zero
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity.quaternionHaar_parity_square_split
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity.quaternionHaar_square_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity.tenfoldHaar_square_nonnegative
