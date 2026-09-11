/-
# Sphere-ideal descent for arbitrary finite products of quaternion moments

The finite-product quaternion carrier assigns one four-coordinate block to
each lattice link.  This file proves that its exact product moment descends
through the unit-sphere relation in every carried block, not merely in the
two historical boundary blocks.

For block `b`, the sparse polynomial generator is

  x_(4b)^2 + x_(4b+1)^2 + x_(4b+2)^2 + x_(4b+3)^2.

Its four monomials are built directly, without polynomial squaring or
normalization.  Their lengths are bounded by `4 * blockCount` whenever
`b < blockCount`; consequently monomial multiplication preserves the entire
tail beyond the finite carrier.  This support fact is load-bearing because it
makes the out-of-carrier zero branch identical on all four radius terms.

The moment proof is constructive.  A Nodup induction isolates the unique
selected block in `List.range blockCount`; all other block moments are
literally unchanged, while the selected factor is discharged by the exact
four-coordinate recurrence `sphereMoment4_radius`.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-! ## 1. Sparse coordinate-square and block-radius generators -/

/-- The trailing-zero-trimmed monomial with exponent two at exactly one
coordinate and exponent zero before it. -/
def coordinateSquareMonomial : Nat → List Nat
  | 0 => [2]
  | coordinate + 1 => 0 :: coordinateSquareMonomial coordinate

/-- The square monomial for one scalar component of one quaternion block. -/
def quaternionBlockSquareMonomial
    (block component : Nat) : List Nat :=
  coordinateSquareMonomial (4 * block + component)

/-- The four-term radius-square polynomial of one quaternion block.  This is
an explicit sparse list; no raw polynomial product is materialized. -/
def quaternionBlockRadiusPolynomial (block : Nat) : RatPoly :=
  [ (quaternionBlockSquareMonomial block 0, 1),
    (quaternionBlockSquareMonomial block 1, 1),
    (quaternionBlockSquareMonomial block 2, 1),
    (quaternionBlockSquareMonomial block 3, 1) ]

@[simp] theorem coordinateSquareMonomial_length
    (coordinate : Nat) :
    (coordinateSquareMonomial coordinate).length = coordinate + 1 := by
  induction coordinate with
  | zero => rfl
  | succ coordinate ih =>
      simp [coordinateSquareMonomial, ih]

@[simp] theorem quaternionBlockSquareMonomial_length
    (block component : Nat) :
    (quaternionBlockSquareMonomial block component).length =
      4 * block + component + 1 := by
  exact coordinateSquareMonomial_length (4 * block + component)

/-- Exact coordinate lookup in the sparse square monomial. -/
@[simp] theorem exponentAt_nil (coordinate : Nat) :
    exponentAt [] coordinate = 0 := by
  unfold exponentAt
  exact List.getD_nil

@[simp] theorem exponentAt_cons_zero
    (head : Nat) (tail : List Nat) :
    exponentAt (head :: tail) 0 = head := by
  unfold exponentAt
  exact List.getD_cons_zero

@[simp] theorem exponentAt_cons_succ
    (head : Nat) (tail : List Nat) (coordinate : Nat) :
    exponentAt (head :: tail) (coordinate + 1) =
      exponentAt tail coordinate := by
  unfold exponentAt
  exact List.getD_cons_succ

theorem exponentAt_coordinateSquareMonomial
    (coordinate query : Nat) :
    exponentAt (coordinateSquareMonomial coordinate) query =
      if query = coordinate then 2 else 0 := by
  induction coordinate generalizing query with
  | zero =>
      cases query with
      | zero =>
          simp only [coordinateSquareMonomial, exponentAt_cons_zero,
            if_pos]
      | succ query =>
          simp only [coordinateSquareMonomial, exponentAt_cons_succ,
            exponentAt_nil]
          have hne : query + 1 ≠ 0 := by omega
          rw [if_neg hne]
  | succ coordinate ih =>
      cases query with
      | zero =>
          simp only [coordinateSquareMonomial, exponentAt_cons_zero]
          have hne : 0 ≠ coordinate + 1 := by omega
          rw [if_neg hne]
      | succ query =>
          simp only [coordinateSquareMonomial, exponentAt_cons_succ]
          rw [ih query]
          by_cases h : query = coordinate
          . subst coordinate
            simp only [if_pos]
          . have hsucc : query + 1 ≠ coordinate + 1 := by omega
            rw [if_neg h, if_neg hsucc]

/-- Exponents add coordinatewise under raw monomial multiplication. -/
theorem exponentAt_monoMul (left right : List Nat) (coordinate : Nat) :
    exponentAt (monoMul left right) coordinate =
      exponentAt left coordinate + exponentAt right coordinate := by
  induction left generalizing right coordinate with
  | nil => simp [monoMul, exponentAt]
  | cons head tail ih =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons other rest =>
          cases coordinate with
          | zero => simp [monoMul, exponentAt]
          | succ coordinate =>
              change exponentAt (monoMul tail rest) coordinate =
                exponentAt tail coordinate + exponentAt rest coordinate
              exact ih rest coordinate

/-- Multiplying by a monomial supported before `boundary` leaves the entire
exponent tail from `boundary` onward literally unchanged. -/
theorem monoMul_drop_of_right_length_le
    (left right : List Nat) (boundary : Nat)
    (hsupport : right.length ≤ boundary) :
    (monoMul left right).drop boundary = left.drop boundary := by
  induction boundary generalizing left right with
  | zero =>
      cases right with
      | nil => cases left <;> rfl
      | cons head tail => simp at hsupport
  | succ boundary ih =>
      cases left with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le hsupport
      | cons head tail =>
          cases right with
          | nil => simp [monoMul]
          | cons other rest =>
              simp only [List.length_cons] at hsupport
              simp [monoMul, ih tail rest (by omega)]

/-- A square in block `block < blockCount` cannot create an exponent beyond
the finite product carrier. -/
theorem monoMul_drop_quaternionBlockSquare
    (monomial : List Nat)
    {blockCount block component : Nat}
    (hblock : block < blockCount)
    (hcomponent : component < 4) :
    (monoMul monomial
        (quaternionBlockSquareMonomial block component)).drop
        (4 * blockCount) =
      monomial.drop (4 * blockCount) := by
  apply monoMul_drop_of_right_length_le
  rw [quaternionBlockSquareMonomial_length]
  omega

/-- The Boolean tail-support test is therefore identical after multiplying by
an in-range block square. -/
theorem allZero_drop_monoMul_quaternionBlockSquare
    (monomial : List Nat)
    {blockCount block component : Nat}
    (hblock : block < blockCount)
    (hcomponent : component < 4) :
    allZero
        ((monoMul monomial
          (quaternionBlockSquareMonomial block component)).drop
            (4 * blockCount)) =
      allZero (monomial.drop (4 * blockCount)) := by
  exact congrArg allZero
    (monoMul_drop_quaternionBlockSquare monomial hblock hcomponent)

/-! ## 2. The selected block and all unchanged blocks -/

/-- Exponent lookup after multiplying by one block-coordinate square. -/
theorem exponentAt_monoMul_quaternionBlockSquare
    (monomial : List Nat) (block component query : Nat) :
    exponentAt
        (monoMul monomial
          (quaternionBlockSquareMonomial block component)) query =
      exponentAt monomial query +
        if query = 4 * block + component then 2 else 0 := by
  unfold quaternionBlockSquareMonomial
  rw [exponentAt_monoMul, exponentAt_coordinateSquareMonomial]

/-- A square inserted in one quaternion block leaves every different block
moment literally unchanged. -/
theorem quaternionBlockMoment_monoMul_square_of_ne
    (monomial : List Nat)
    {source target component : Nat}
    (hne : source ≠ target) (hcomponent : component < 4) :
    quaternionBlockMoment source
        (monoMul monomial
          (quaternionBlockSquareMonomial target component)) =
      quaternionBlockMoment source monomial := by
  have h0 : 4 * source ≠ 4 * target + component := by omega
  have h1 : 4 * source + 1 ≠ 4 * target + component := by omega
  have h2 : 4 * source + 2 ≠ 4 * target + component := by omega
  have h3 : 4 * source + 3 ≠ 4 * target + component := by omega
  unfold quaternionBlockMoment
  simp only [exponentAt_monoMul_quaternionBlockSquare,
    h0, h1, h2, h3, if_false, Nat.add_zero]

/-- The selected block moment obeys the exact unit-sphere recurrence. -/
theorem quaternionBlockMoment_mul_blockRadius
    (monomial : List Nat) (block : Nat) :
    quaternionBlockMoment block
        (monoMul monomial (quaternionBlockSquareMonomial block 0)) +
      (quaternionBlockMoment block
          (monoMul monomial (quaternionBlockSquareMonomial block 1)) +
        (quaternionBlockMoment block
            (monoMul monomial (quaternionBlockSquareMonomial block 2)) +
          quaternionBlockMoment block
            (monoMul monomial
              (quaternionBlockSquareMonomial block 3)))) ≈
      quaternionBlockMoment block monomial := by
  have h01' : 4 * block + 1 ≠ 4 * block := by omega
  have h02' : 4 * block + 2 ≠ 4 * block := by omega
  have h03' : 4 * block + 3 ≠ 4 * block := by omega
  have h10 : 4 * block ≠ 4 * block + 1 := by omega
  have h12 : 4 * block + 2 ≠ 4 * block + 1 := by omega
  have h13 : 4 * block + 3 ≠ 4 * block + 1 := by omega
  have h20 : 4 * block ≠ 4 * block + 2 := by omega
  have h21 : 4 * block + 1 ≠ 4 * block + 2 := by omega
  have h23 : 4 * block + 3 ≠ 4 * block + 2 := by omega
  have h30 : 4 * block ≠ 4 * block + 3 := by omega
  have h31 : 4 * block + 1 ≠ 4 * block + 3 := by omega
  have h32 : 4 * block + 2 ≠ 4 * block + 3 := by omega
  unfold quaternionBlockMoment
  simp only [exponentAt_monoMul_quaternionBlockSquare,
    h01', h02', h03', h10, h12, h13, h20, h21, h23,
    h30, h31, h32, if_false, if_true, Nat.add_zero]
  exact sphereMoment4_radius
    (exponentAt monomial (4 * block))
    (exponentAt monomial (4 * block + 1))
    (exponentAt monomial (4 * block + 2))
    (exponentAt monomial (4 * block + 3))

/-- If a block list omits the selected block, its entire product moment is
literally unchanged by a square in that selected block. -/
theorem quaternionBlockMomentProduct_monoMul_square_of_not_mem
    (monomial : List Nat) (target component : Nat)
    (hcomponent : component < 4) : ∀ blocks : List Nat,
    target ∉ blocks →
      quaternionBlockMomentProduct
          (monoMul monomial
            (quaternionBlockSquareMonomial target component)) blocks =
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
        quaternionBlockMoment head
              (monoMul monomial
                (quaternionBlockSquareMonomial target component)) *
            quaternionBlockMomentProduct
              (monoMul monomial
                (quaternionBlockSquareMonomial target component)) tail =
          quaternionBlockMoment head monomial *
            quaternionBlockMomentProduct monomial tail
      rw [quaternionBlockMoment_monoMul_square_of_ne
          monomial hhead hcomponent,
        quaternionBlockMomentProduct_monoMul_square_of_not_mem
          monomial target component hcomponent tail htail]

private theorem four_mul_factor (a b c d factor : Q') :
    a * factor + (b * factor + (c * factor + d * factor)) ≈
      (a + (b + (c + d))) * factor := by
  have hcd : c * factor + d * factor ≈ (c + d) * factor :=
    Q'.eqv_symm (Q'.add_mul_eqv c d factor)
  have hbcd : b * factor + (c * factor + d * factor) ≈
      (b + (c + d)) * factor :=
    Q'.eqv_trans _ (b * factor + (c + d) * factor) _
      (Q'.add_eqv_congr_left _ _ _ hcd)
      (Q'.eqv_symm (Q'.add_mul_eqv b (c + d) factor))
  exact Q'.eqv_trans _
    (a * factor + (b + (c + d)) * factor) _
    (Q'.add_eqv_congr_left _ _ _ hbcd)
    (Q'.eqv_symm (Q'.add_mul_eqv a (b + (c + d)) factor))

private theorem four_left_factor (factor a b c d : Q') :
    factor * a + (factor * b + (factor * c + factor * d)) ≈
      factor * (a + (b + (c + d))) := by
  have hcd : factor * c + factor * d ≈ factor * (c + d) :=
    Q'.eqv_symm (Q'.mul_add_eqv factor c d)
  have hbcd : factor * b + (factor * c + factor * d) ≈
      factor * (b + (c + d)) :=
    Q'.eqv_trans _ (factor * b + factor * (c + d)) _
      (Q'.add_eqv_congr_left _ _ _ hcd)
      (Q'.eqv_symm (Q'.mul_add_eqv factor b (c + d)))
  exact Q'.eqv_trans _
    (factor * a + factor * (b + (c + d))) _
    (Q'.add_eqv_congr_left _ _ _ hbcd)
    (Q'.eqv_symm (Q'.mul_add_eqv factor a (b + (c + d))))

/-! ## 3. Radius descent through a Nodup block product -/

/-- A Nodup block product containing the selected block obeys the same
four-term radius recurrence. -/
theorem quaternionBlockMomentProduct_mul_blockRadius
    (monomial : List Nat) (block : Nat) : ∀ blocks : List Nat,
    blocks.Nodup → block ∈ blocks →
      quaternionBlockMomentProduct
          (monoMul monomial
            (quaternionBlockSquareMonomial block 0)) blocks +
        (quaternionBlockMomentProduct
            (monoMul monomial
              (quaternionBlockSquareMonomial block 1)) blocks +
          (quaternionBlockMomentProduct
              (monoMul monomial
                (quaternionBlockSquareMonomial block 2)) blocks +
            quaternionBlockMomentProduct
              (monoMul monomial
                (quaternionBlockSquareMonomial block 3)) blocks)) ≈
        quaternionBlockMomentProduct monomial blocks
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases heq : block = head
      · subst head
        have htail0 :=
          quaternionBlockMomentProduct_monoMul_square_of_not_mem
            monomial block 0 (by decide) tail hparts.1
        have htail1 :=
          quaternionBlockMomentProduct_monoMul_square_of_not_mem
            monomial block 1 (by decide) tail hparts.1
        have htail2 :=
          quaternionBlockMomentProduct_monoMul_square_of_not_mem
            monomial block 2 (by decide) tail hparts.1
        have htail3 :=
          quaternionBlockMomentProduct_monoMul_square_of_not_mem
            monomial block 3 (by decide) tail hparts.1
        change
          quaternionBlockMoment block
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 0)) *
              quaternionBlockMomentProduct
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 0)) tail +
            (quaternionBlockMoment block
                  (monoMul monomial
                    (quaternionBlockSquareMonomial block 1)) *
                quaternionBlockMomentProduct
                  (monoMul monomial
                    (quaternionBlockSquareMonomial block 1)) tail +
              (quaternionBlockMoment block
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 2)) *
                  quaternionBlockMomentProduct
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 2)) tail +
                quaternionBlockMoment block
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 3)) *
                  quaternionBlockMomentProduct
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 3)) tail)) ≈
            quaternionBlockMoment block monomial *
              quaternionBlockMomentProduct monomial tail
        rw [htail0, htail1, htail2, htail3]
        exact Q'.eqv_trans _
          ((quaternionBlockMoment block
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 0)) +
              (quaternionBlockMoment block
                  (monoMul monomial
                    (quaternionBlockSquareMonomial block 1)) +
                (quaternionBlockMoment block
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 2)) +
                  quaternionBlockMoment block
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 3))))) *
            quaternionBlockMomentProduct monomial tail) _
          (four_mul_factor _ _ _ _ _)
          (Q'.mul_eqv_congr_right _ _ _
            (quaternionBlockMoment_mul_blockRadius monomial block))
      · have htailMem : block ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left heq
        have ih := quaternionBlockMomentProduct_mul_blockRadius
          monomial block tail hparts.2 htailMem
        have hheadNe : head ≠ block := by
          intro hreverse
          exact heq hreverse.symm
        have hhead0 := quaternionBlockMoment_monoMul_square_of_ne
          monomial hheadNe (show 0 < 4 by decide)
        have hhead1 := quaternionBlockMoment_monoMul_square_of_ne
          monomial hheadNe (show 1 < 4 by decide)
        have hhead2 := quaternionBlockMoment_monoMul_square_of_ne
          monomial hheadNe (show 2 < 4 by decide)
        have hhead3 := quaternionBlockMoment_monoMul_square_of_ne
          monomial hheadNe (show 3 < 4 by decide)
        change
          quaternionBlockMoment head
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 0)) *
              quaternionBlockMomentProduct
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 0)) tail +
            (quaternionBlockMoment head
                  (monoMul monomial
                    (quaternionBlockSquareMonomial block 1)) *
                quaternionBlockMomentProduct
                  (monoMul monomial
                    (quaternionBlockSquareMonomial block 1)) tail +
              (quaternionBlockMoment head
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 2)) *
                  quaternionBlockMomentProduct
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 2)) tail +
                quaternionBlockMoment head
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 3)) *
                  quaternionBlockMomentProduct
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 3)) tail)) ≈
            quaternionBlockMoment head monomial *
              quaternionBlockMomentProduct monomial tail
        rw [hhead0, hhead1, hhead2, hhead3]
        exact Q'.eqv_trans _
          (quaternionBlockMoment head monomial *
            (quaternionBlockMomentProduct
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 0)) tail +
              (quaternionBlockMomentProduct
                  (monoMul monomial
                    (quaternionBlockSquareMonomial block 1)) tail +
                (quaternionBlockMomentProduct
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 2)) tail +
                  quaternionBlockMomentProduct
                    (monoMul monomial
                      (quaternionBlockSquareMonomial block 3)) tail)))) _
          (four_left_factor _ _ _ _ _)
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

/-! ## 4. Arbitrary-block finite-product monomial recurrence -/

/-- **Exact arbitrary-block sphere descent.**  For every selected block inside
the finite product carrier, multiplication of a monomial by the four
coordinate squares has the same finite-product moment as the original
monomial.  No support bound on the original monomial is needed. -/
theorem finiteProductHaarMono_mul_blockRadius
    (blockCount block : Nat) (hblock : block < blockCount)
    (monomial : List Nat) :
    finiteProductHaarMono blockCount
        (monoMul monomial (quaternionBlockSquareMonomial block 0)) +
      (finiteProductHaarMono blockCount
          (monoMul monomial (quaternionBlockSquareMonomial block 1)) +
        (finiteProductHaarMono blockCount
            (monoMul monomial (quaternionBlockSquareMonomial block 2)) +
          finiteProductHaarMono blockCount
            (monoMul monomial
              (quaternionBlockSquareMonomial block 3)))) ≈
      finiteProductHaarMono blockCount monomial := by
  have htail0 := allZero_drop_monoMul_quaternionBlockSquare
    monomial hblock (show 0 < 4 by decide)
  have htail1 := allZero_drop_monoMul_quaternionBlockSquare
    monomial hblock (show 1 < 4 by decide)
  have htail2 := allZero_drop_monoMul_quaternionBlockSquare
    monomial hblock (show 2 < 4 by decide)
  have htail3 := allZero_drop_monoMul_quaternionBlockSquare
    monomial hblock (show 3 < 4 by decide)
  unfold finiteProductHaarMono
  rw [htail0, htail1, htail2, htail3]
  by_cases htail : allZero (monomial.drop (4 * blockCount)) = true
  · simp only [htail, if_true]
    exact quaternionBlockMomentProduct_mul_blockRadius
      monomial block (List.range blockCount)
      (rangeNodupLocal blockCount) (List.mem_range.mpr hblock)
  · have hfalse :
        allZero (monomial.drop (4 * blockCount)) = false := by
      cases hvalue : allZero (monomial.drop (4 * blockCount)) with
      | false => rfl
      | true => exact (htail hvalue).elim
    simp only [hfalse, Bool.false_eq_true, if_false]
    change (0 : Q') + (0 + (0 + 0)) ≈ 0
    decide

/-! ## 5. Full polynomial ideal descent -/

private theorem scaled_four_radius (q a b c d z : Q')
    (hradius : a + (b + (c + d)) ≈ z) :
    (q * 1) * a + ((q * 1) * b + ((q * 1) * c + (q * 1) * d)) ≈
      q * z := by
  have hq : q * 1 ≈ q := Q'.mul_one_eqv q
  refine Q'.eqv_trans _
    (q * a + (q * b + (q * c + q * d))) _ ?_ ?_
  · exact q_add_congr
      (Q'.mul_eqv_congr_right _ _ _ hq)
      (q_add_congr
        (Q'.mul_eqv_congr_right _ _ _ hq)
        (q_add_congr
          (Q'.mul_eqv_congr_right _ _ _ hq)
          (Q'.mul_eqv_congr_right _ _ _ hq)))
  · exact Q'.eqv_trans _ (q * (a + (b + (c + d)))) _
      (four_left_factor _ _ _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ hradius)

private theorem finiteProductHaar_mul_blockRadius_single
    (blockCount block : Nat) (hblock : block < blockCount)
    (monomial : List Nat) (coefficient : Q') :
    finiteProductHaar blockCount
        (polyMul [(monomial, coefficient)]
          (quaternionBlockRadiusPolynomial block)) ≈
      finiteProductHaar blockCount [(monomial, coefficient)] := by
  change
    (coefficient * 1) *
          finiteProductHaarMono blockCount
            (monoMul monomial
              (quaternionBlockSquareMonomial block 0)) +
      ((coefficient * 1) *
          finiteProductHaarMono blockCount
            (monoMul monomial
              (quaternionBlockSquareMonomial block 1)) +
        ((coefficient * 1) *
            finiteProductHaarMono blockCount
              (monoMul monomial
                (quaternionBlockSquareMonomial block 2)) +
          ((coefficient * 1) *
              finiteProductHaarMono blockCount
                (monoMul monomial
                  (quaternionBlockSquareMonomial block 3)) + 0))) ≈
      coefficient * finiteProductHaarMono blockCount monomial + 0
  simp only [Q'.add_zero']
  exact scaled_four_radius _ _ _ _ _ _
    (finiteProductHaarMono_mul_blockRadius
      blockCount block hblock monomial)

/-- The complete finite-product moment functional descends through the sphere
equation in every carried quaternion block. -/
theorem finiteProductHaar_mul_blockRadius
    (blockCount block : Nat) (hblock : block < blockCount) :
    ∀ polynomial : RatPoly,
      finiteProductHaar blockCount
          (polyMul polynomial
            (quaternionBlockRadiusPolynomial block)) ≈
        finiteProductHaar blockCount polynomial
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      have hmul :
          polyMul (term :: polynomial)
              (quaternionBlockRadiusPolynomial block) =
            polyMul [term] (quaternionBlockRadiusPolynomial block) ++
              polyMul polynomial
                (quaternionBlockRadiusPolynomial block) := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount
            (polyMul [term]
              (quaternionBlockRadiusPolynomial block)) +
          finiteProductHaar blockCount
            (polyMul polynomial
              (quaternionBlockRadiusPolynomial block))) _
        (finiteProductHaar_append blockCount _ _) ?_
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount [term] +
          finiteProductHaar blockCount polynomial) _
        (q_add_congr
          (finiteProductHaar_mul_blockRadius_single
            blockCount block hblock term.1 term.2)
          (finiteProductHaar_mul_blockRadius
            blockCount block hblock polynomial)) ?_
      change
        finiteProductHaar blockCount [term] +
            finiteProductHaar blockCount polynomial ≈
          finiteProductHaar blockCount ([term] ++ polynomial)
      exact Q'.eqv_symm
        (finiteProductHaar_append blockCount [term] polynomial)

#print axioms coordinateSquareMonomial_length
#print axioms quaternionBlockSquareMonomial_length
#print axioms exponentAt_coordinateSquareMonomial
#print axioms exponentAt_monoMul
#print axioms monoMul_drop_of_right_length_le
#print axioms monoMul_drop_quaternionBlockSquare
#print axioms allZero_drop_monoMul_quaternionBlockSquare
#print axioms exponentAt_monoMul_quaternionBlockSquare
#print axioms quaternionBlockMoment_monoMul_square_of_ne
#print axioms quaternionBlockMoment_mul_blockRadius
#print axioms quaternionBlockMomentProduct_monoMul_square_of_not_mem
#print axioms quaternionBlockMomentProduct_mul_blockRadius
#print axioms finiteProductHaarMono_mul_blockRadius
#print axioms finiteProductHaar_mul_blockRadius

end YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
