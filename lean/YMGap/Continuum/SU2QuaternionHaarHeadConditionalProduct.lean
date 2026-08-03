/-
# Conditional product law for one exposed quaternion Haar block

`partialHaarHead` retains all tail variables, but its useful multiplicative
law needs a side condition: the second factor must be independent of the
head quaternion.  This file proves that law at the level actually consumed by
the BF4 argument.  The remaining `blocks` Haar integrations are performed
after the selected head integration, and every tail monomial is retained.

No semantic independence or measure-theoretic Fubini theorem is assumed; the
proof is a finite calculation with the explicit `S^3` monomial moments.
-/

import YMGap.Continuum.SU2QuaternionHaarHeadFubini

namespace YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadFubini

local infix:50 " ≈ " => Q'.eqv

/-- Delete the four selected-head exponents without integrating them. -/
def dropHeadPolynomial (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun term => (term.1.drop 4, term.2)

/-- Syntactic independence of the selected head quaternion. -/
def HeadQuaternionIndependent (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → headQuaternionDegree term.1 = 0

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

private theorem monoMul_right_nil : ∀ monomial : List Nat,
    monoMul monomial [] = monomial
  | [] => rfl
  | _ :: _ => by simp only [monoMul]

private theorem drop_monoMul :
    ∀ (count : Nat) (left right : List Nat),
      (monoMul left right).drop count =
        monoMul (left.drop count) (right.drop count)
  | 0, left, right => by simp
  | count + 1, [], right => by simp [monoMul]
  | count + 1, left, [] => by
      rw [monoMul_right_nil, List.drop_nil, monoMul_right_nil]
  | count + 1, _ :: left, _ :: right => by
      simp only [monoMul, List.drop_succ_cons]
      exact drop_monoMul count left right

private theorem independent_coordinates_zero
    {monomial : List Nat}
    (hindependent : headQuaternionDegree monomial = 0) :
    exponentAt monomial 0 = 0 ∧
      exponentAt monomial 1 = 0 ∧
    exponentAt monomial 2 = 0 ∧
      exponentAt monomial 3 = 0 := by
  unfold headQuaternionDegree at hindependent
  have h012_3 := Nat.eq_zero_of_add_eq_zero hindependent
  have h01_2 := Nat.eq_zero_of_add_eq_zero h012_3.1
  have h0_1 := Nat.eq_zero_of_add_eq_zero h01_2.1
  exact ⟨h0_1.1, h0_1.2, h01_2.2, h012_3.2⟩

private theorem headQuaternionMoment_monoMul_independent_right
    (left right : List Nat)
    (hindependent : headQuaternionDegree right = 0) :
    headQuaternionMoment (monoMul left right) =
      headQuaternionMoment left := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    independent_coordinates_zero hindependent
  unfold headQuaternionMoment
  rw [exponentAt_monoMul, exponentAt_monoMul,
    exponentAt_monoMul, exponentAt_monoMul,
    h0, h1, h2, h3]
  simp only [Nat.add_zero]

private theorem conditional_pair
    (blocks : Nat) (left right : RatTerm)
    (hindependent : headQuaternionDegree right.1 = 0) :
    (left.2 * right.2) *
          quaternionHaarMono (blocks + 1)
            (monoMul left.1 right.1) ≈
      ((left.2 * headQuaternionMoment left.1) * right.2) *
        quaternionHaarMono blocks
          (monoMul (left.1.drop 4) (right.1.drop 4)) := by
  let tailMoment :=
    quaternionHaarMono blocks
      ((monoMul left.1 right.1).drop 4)
  have hfubini :=
    headMoment_mul_tailHaarMono blocks
      (monoMul left.1 right.1)
  have hhead :=
    headQuaternionMoment_monoMul_independent_right
      left.1 right.1 hindependent
  refine Q'.eqv_trans _
    ((left.2 * right.2) *
      (headQuaternionMoment (monoMul left.1 right.1) *
        tailMoment)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hfubini)) ?_
  dsimp only [tailMoment]
  rw [drop_monoMul 4 left.1 right.1]
  rw [hhead]
  exact Q'.eqv_trans _
    ((left.2 * right.2) *
      (headQuaternionMoment left.1 *
        quaternionHaarMono blocks
          (monoMul (left.1.drop 4) (right.1.drop 4)))) _
    (Q'.eqv_refl _) (by
      refine Q'.eqv_trans _
        (((left.2 * right.2) * headQuaternionMoment left.1) *
          quaternionHaarMono blocks
            (monoMul (left.1.drop 4) (right.1.drop 4))) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.mul_eqv_congr_right _ _ _ ?_
      refine Q'.eqv_trans _
        (left.2 *
          (right.2 * headQuaternionMoment left.1)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        (left.2 *
          (headQuaternionMoment left.1 * right.2)) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem conditional_row
    (blocks : Nat) (left : RatTerm) :
    ∀ right : RatPoly,
      HeadQuaternionIndependent right →
      quaternionHaarRow (blocks + 1) left right ≈
        quaternionHaarRow blocks
          (partialHaarHeadTerm left)
          (dropHeadPolynomial right)
  | [], _ => Q'.eqv_refl 0
  | right :: rest, hindependent => by
      change
        (left.2 * right.2) *
              quaternionHaarMono (blocks + 1)
                (monoMul left.1 right.1) +
            quaternionHaarRow (blocks + 1) left rest ≈
          ((left.2 * headQuaternionMoment left.1) * right.2) *
              quaternionHaarMono blocks
                (monoMul (left.1.drop 4) (right.1.drop 4)) +
            quaternionHaarRow blocks
              (partialHaarHeadTerm left)
              (dropHeadPolynomial rest)
      exact Q'.add_eqv_congr'
        (conditional_pair blocks left right
          (hindependent right List.mem_cons_self))
        (conditional_row blocks left rest
          (fun term hterm =>
            hindependent term
              (List.mem_cons_of_mem right hterm)))

private theorem conditional_bilinear
    (blocks : Nat) :
    ∀ (left right : RatPoly),
      HeadQuaternionIndependent right →
      quaternionHaarBilinear (blocks + 1) left right ≈
        quaternionHaarBilinear blocks
          (partialHaarHead left)
          (dropHeadPolynomial right)
  | [], right, _ => Q'.eqv_refl 0
  | left :: rest, right, hindependent => by
      change
        quaternionHaarRow (blocks + 1) left right +
              quaternionHaarBilinear (blocks + 1) rest right ≈
          quaternionHaarRow blocks
                (partialHaarHeadTerm left)
                (dropHeadPolynomial right) +
            quaternionHaarBilinear blocks
              (partialHaarHead rest)
              (dropHeadPolynomial right)
      exact Q'.add_eqv_congr'
        (conditional_row blocks left right hindependent)
        (conditional_bilinear blocks rest right hindependent)

/-- **Coefficient-retaining conditional product law.**  If `right` is
independent of the selected head quaternion, then integrating `left * right`
over all `blocks+1` factors is exactly the same as first integrating the head
of `left`, deleting the empty head coordinates of `right`, multiplying the
two tail polynomials, and integrating the remaining `blocks` factors. -/
theorem quaternionHaar_polyMul_headIndependent
    (blocks : Nat) (left right : RatPoly)
    (hindependent : HeadQuaternionIndependent right) :
    quaternionHaar (blocks + 1) (polyMul left right) ≈
      quaternionHaar blocks
        (polyMul
          (partialHaarHead left)
          (dropHeadPolynomial right)) := by
  exact Q'.eqv_trans _
    (quaternionHaarBilinear (blocks + 1) left right) _
    (quaternionHaar_polyMul (blocks + 1) left right)
    (Q'.eqv_trans _
      (quaternionHaarBilinear blocks
        (partialHaarHead left)
        (dropHeadPolynomial right)) _
      (conditional_bilinear blocks left right hindependent)
      (Q'.eqv_symm
        (quaternionHaar_polyMul blocks
          (partialHaarHead left)
          (dropHeadPolynomial right))))

end YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct

#print axioms YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct.quaternionHaar_polyMul_headIndependent
