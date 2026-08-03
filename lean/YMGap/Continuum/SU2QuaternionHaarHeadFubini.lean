/-
# Constructive one-block Fubini for arbitrary-product quaternion Haar

The exact product-Haar functional is defined recursively in four-coordinate
quaternion blocks.  This module exposes that recursion as a polynomial-valued
partial integral: integrate the head `S^3` block, delete its four exponents,
and retain a rational polynomial in the remaining blocks.

This is the analytic carrier needed for the BF4 exposed-link argument.  A
later block permutation moves the selected exposed link to the head; the
one-link Peter--Weyl calculation can then be performed before the remaining
115 Haar integrations.
-/

import YMGap.Continuum.BF4GeometricHaarMehlerProjection
import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

namespace YMGap.Continuum.SU2QuaternionHaarHeadFubini

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv

/-- Exact normalized `S^3` moment of the head quaternion block. -/
def headQuaternionMoment (monomial : List Nat) : Q' :=
  sphereMoment4
    (exponentAt monomial 0)
    (exponentAt monomial 1)
    (exponentAt monomial 2)
    (exponentAt monomial 3)

/-- Integrate one monomial in the head quaternion and shift the remaining
coordinate exponents down by four. -/
def partialHaarHeadTerm (term : RatTerm) : RatTerm :=
  (term.1.drop 4, term.2 * headQuaternionMoment term.1)

/-- Polynomial-valued conditional Haar integration over the head block. -/
def partialHaarHead (polynomial : RatPoly) : RatPoly :=
  polynomial.map partialHaarHeadTerm

/-- Total polynomial degree in the four coordinates of the head
quaternion. -/
def headQuaternionDegree (monomial : List Nat) : Nat :=
  exponentAt monomial 0 + exponentAt monomial 1 +
    exponentAt monomial 2 + exponentAt monomial 3

/-- Every monomial of the polynomial is odd in the head quaternion block. -/
def HeadQuaternionOdd (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → headQuaternionDegree term.1 % 2 = 1

theorem headQuaternionMoment_eq_zero_of_odd
    {monomial : List Nat}
    (hodd : headQuaternionDegree monomial % 2 = 1) :
    headQuaternionMoment monomial = 0 := by
  unfold headQuaternionMoment sphereMoment4
  split
  next heven =>
    unfold headQuaternionDegree at hodd
    omega
  next => rfl

/-- Odd head-block polynomials vanish after the selected `S^3` integral,
even after all remaining quaternion blocks are integrated. -/
theorem quaternionHaar_partialHaarHead_eq_zero_of_odd
    (blocks : Nat) : ∀ polynomial : RatPoly,
    HeadQuaternionOdd polynomial →
      quaternionHaar blocks (partialHaarHead polynomial) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | term :: rest, hodd => by
      change
        (term.2 * headQuaternionMoment term.1) *
              quaternionHaarMono blocks (term.1.drop 4) +
            quaternionHaar blocks (partialHaarHead rest) ≈
          0
      rw [headQuaternionMoment_eq_zero_of_odd
        (hodd term List.mem_cons_self)]
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _
            (term.2 *
              (0 * quaternionHaarMono blocks (term.1.drop 4))) _
            (Q'.mul_assoc_eqv term.2 0
              (quaternionHaarMono blocks (term.1.drop 4)))
            (Q'.eqv_trans _ (term.2 * 0) _
              (Q'.mul_eqv_congr_left term.2 _ _
                (Q'.zero_mul_eqv
                  (quaternionHaarMono blocks (term.1.drop 4))))
              (Q'.mul_zero_eqv term.2)))
          (quaternionHaar_partialHaarHead_eq_zero_of_odd blocks rest
            (fun other hother =>
              hodd other (List.mem_cons_of_mem term hother)))
      · decide

private theorem drop_four_then_blocks (monomial : List Nat) (blocks : Nat) :
    (monomial.drop 4).drop (4 * blocks) =
      monomial.drop (4 * (blocks + 1)) := by
  rw [List.drop_drop]
  congr 1
  omega

/-- Monomial Fubini: the head sphere moment times the remaining product
moment is the original product moment. -/
theorem headMoment_mul_tailHaarMono
    (blocks : Nat) (monomial : List Nat) :
    headQuaternionMoment monomial *
        quaternionHaarMono blocks (monomial.drop 4) ≈
      quaternionHaarMono (blocks + 1) monomial := by
  unfold quaternionHaarMono
  rw [drop_four_then_blocks]
  by_cases htail : allZero (monomial.drop (4 * (blocks + 1))) = true
  · rw [if_pos htail, if_pos htail]
    unfold quaternionHaarPrefix headQuaternionMoment
    cases blocks <;> exact Q'.eqv_refl _
  · have hfalse :
        allZero (monomial.drop (4 * (blocks + 1))) = false := by
      cases hvalue : allZero (monomial.drop (4 * (blocks + 1)))
      · rfl
      · exact False.elim (htail hvalue)
    rw [if_neg htail, if_neg htail]
    exact Q'.mul_zero_eqv _

/-- **Polynomial one-block Fubini.**  Integrating the remaining `blocks`
after `partialHaarHead` is exactly the original `(blocks+1)`-fold Haar
functional. -/
theorem quaternionHaar_partialHaarHead
    (blocks : Nat) : ∀ polynomial : RatPoly,
    quaternionHaar blocks (partialHaarHead polynomial) ≈
      quaternionHaar (blocks + 1) polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * headQuaternionMoment term.1) *
              quaternionHaarMono blocks (term.1.drop 4) +
            quaternionHaar blocks (partialHaarHead rest) ≈
          term.2 * quaternionHaarMono (blocks + 1) term.1 +
            quaternionHaar (blocks + 1) rest
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _
          (term.2 *
            (headQuaternionMoment term.1 *
              quaternionHaarMono blocks (term.1.drop 4))) _
          (Q'.mul_assoc_eqv term.2
            (headQuaternionMoment term.1)
            (quaternionHaarMono blocks (term.1.drop 4)))
          (Q'.mul_eqv_congr_left term.2 _ _
            (headMoment_mul_tailHaarMono blocks term.1)))
        (quaternionHaar_partialHaarHead blocks rest)

/-! ## Moving an arbitrary selected block to the Fubini head -/

/-- Swap block zero with `selected`, leaving every other block fixed. -/
def headSwapBlockMap (selected block : Nat) : Nat :=
  if block = 0 then selected
  else if block = selected then 0
  else block

/-- The head/selected transposition as an explicit constructive block
involution.  The definition also covers `selected = 0`, where it is the
identity. -/
def headSwapBlockInvolution
    (blocks selected : Nat) (hselected : selected < blocks) :
    QuaternionBlockInvolution blocks where
  map := headSwapBlockMap selected
  map_lt := by
    intro block hblock
    by_cases hblockZero : block = 0
    · simp only [headSwapBlockMap, if_pos hblockZero]
      exact hselected
    · simp only [headSwapBlockMap, if_neg hblockZero]
      by_cases hblockSelected : block = selected
      · rw [if_pos hblockSelected]
        omega
      · rw [if_neg hblockSelected]
        exact hblock
  involutive := by
    intro block hblock
    by_cases hblockZero : block = 0
    · subst block
      simp [headSwapBlockMap]
    · by_cases hblockSelected : block = selected
      · subst block
        simp [headSwapBlockMap, hblockZero]
      · simp [headSwapBlockMap, hblockZero, hblockSelected]

theorem headSwapBlockInvolution_map_zero
    (blocks selected : Nat) (hselected : selected < blocks) :
    (headSwapBlockInvolution blocks selected hselected).map 0 = selected := by
  simp [headSwapBlockInvolution, headSwapBlockMap]

theorem headSwapBlockInvolution_map_selected
    (blocks selected : Nat) (hselected : selected < blocks) :
    (headSwapBlockInvolution blocks selected hselected).map selected = 0 := by
  by_cases hselectedZero : selected = 0
  · subst selected
    simp [headSwapBlockInvolution, headSwapBlockMap]
  · simp [headSwapBlockInvolution, headSwapBlockMap, hselectedZero]

/-- **Selected-block Fubini.**  Reindex a supported polynomial so that an
arbitrary selected quaternion is first, integrate that head block, and then
integrate the remaining blocks.  This is exactly the original product-Haar
value. -/
theorem quaternionHaar_eq_partialHaar_selected
    (tailBlocks selected : Nat) (hselected : selected < tailBlocks + 1)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) polynomial) :
    quaternionHaar (tailBlocks + 1) polynomial ≈
      quaternionHaar tailBlocks
        (partialHaarHead
          (reindexQuaternionPolynomial
            (headSwapBlockInvolution
              (tailBlocks + 1) selected hselected)
            polynomial)) := by
  let permutation :=
    headSwapBlockInvolution (tailBlocks + 1) selected hselected
  exact Q'.eqv_trans _
    (quaternionHaar (tailBlocks + 1)
      (reindexQuaternionPolynomial permutation polynomial)) _
    (Q'.eqv_symm
      (quaternionHaar_reindex permutation polynomial hsupport))
    (Q'.eqv_symm
      (quaternionHaar_partialHaarHead tailBlocks
        (reindexQuaternionPolynomial permutation polynomial)))

end YMGap.Continuum.SU2QuaternionHaarHeadFubini

#print axioms YMGap.Continuum.SU2QuaternionHaarHeadFubini.headMoment_mul_tailHaarMono
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadFubini.quaternionHaar_partialHaarHead_eq_zero_of_odd
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadFubini.quaternionHaar_partialHaarHead
#print axioms YMGap.Continuum.SU2QuaternionHaarHeadFubini.quaternionHaar_eq_partialHaar_selected
