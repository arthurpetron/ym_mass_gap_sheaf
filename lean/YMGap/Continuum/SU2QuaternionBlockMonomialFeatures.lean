/-
Finite blockwise monomial features for the original quaternion polynomial
carrier.  The masks preserve exponent-list length, including trailing-zero
aliases.  The resulting factorization is a coefficient equality; it makes no
finite-dimensional Hilbert-space or norm estimate.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.SU2QuaternionBlockMonomialFeatures

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

local infix:50 " ≈ " => Q'.eqv

/-- Keep exactly the exponents in block `b`, preserving the raw list length. -/
def keepBlockFrom (b start : Nat) : List Nat → List Nat
  | [] => []
  | exponent :: tail =>
      (if coordinateInQuaternionBlock b start then exponent else 0) ::
        keepBlockFrom b (start + 1) tail

/-- Keep one quaternion block while retaining trailing zero coordinates. -/
def keepBlock (b : Nat) (m : List Nat) : List Nat :=
  keepBlockFrom b 0 m

/-- The exterior monomial with its original rational coefficient. -/
def outsideFeature (b : Nat) (t : RatTerm) : RatPoly :=
  [(clearQuaternionBlock b t.1, t.2)]

/-- The selected-block monomial, with unit coefficient. -/
def insideFeature (b : Nat) (t : RatTerm) : RatPoly :=
  [(keepBlock b t.1, 1)]

private theorem monoMul_clear_keep_from (b start : Nat) :
    ∀ m : List Nat,
      monoMul (clearQuaternionBlockFrom b start m)
        (keepBlockFrom b start m) = m
  | [] => rfl
  | exponent :: tail => by
      simp only [clearQuaternionBlockFrom, keepBlockFrom, monoMul]
      by_cases h : coordinateInQuaternionBlock b start
      · simp only [h, if_true, Nat.zero_add]
        exact congrArg (List.cons exponent)
          (monoMul_clear_keep_from b (start + 1) tail)
      · simp only [h, if_false, Nat.add_zero]
        exact congrArg (List.cons exponent)
          (monoMul_clear_keep_from b (start + 1) tail)

private theorem monoMul_clear_keep (b : Nat) (m : List Nat) :
    monoMul (clearQuaternionBlock b m) (keepBlock b m) = m := by
  exact monoMul_clear_keep_from b 0 m

private theorem clear_keep_block_independent_from (a b start : Nat)
    (hne : a ≠ b) : ∀ m : List Nat,
      clearQuaternionBlockFrom a start (keepBlockFrom b start m) =
        keepBlockFrom b start m
  | [] => rfl
  | exponent :: tail => by
      simp only [clearQuaternionBlockFrom, keepBlockFrom]
      by_cases hb : coordinateInQuaternionBlock b start
      · have ha : ¬ coordinateInQuaternionBlock a start := by
          intro ha
          unfold coordinateInQuaternionBlock at ha hb
          omega
        simp only [hb, if_true, ha, if_false]
        exact congrArg (List.cons exponent)
          (clear_keep_block_independent_from a b (start + 1) hne tail)
      · simp only [hb, if_false]
        by_cases ha : coordinateInQuaternionBlock a start
        · simp only [ha, if_true]
          exact congrArg (List.cons 0)
            (clear_keep_block_independent_from a b (start + 1) hne tail)
        · simp only [ha, if_false]
          exact congrArg (List.cons 0)
            (clear_keep_block_independent_from a b (start + 1) hne tail)

theorem term_factorization (b : Nat) (t : RatTerm) :
    RatPolyCoeffEqv [t]
      (polyMul (outsideFeature b t) (insideFeature b t)) := by
  unfold outsideFeature insideFeature
  change RatPolyCoeffEqv [t]
    [(monoMul (clearQuaternionBlock b t.1) (keepBlock b t.1), t.2 * 1)]
  have hm := monoMul_clear_keep b t.1
  intro weight
  change t.2 * weight t.1 + 0 ≈
    (t.2 * 1) * weight (monoMul (clearQuaternionBlock b t.1)
      (keepBlock b t.1)) + 0
  rw [hm]
  exact Q'.add_eqv_congr' (Q'.eqv_symm
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv t.2))) (Q'.eqv_refl _)

theorem outside_independent (b : Nat) (t : RatTerm) :
    QuaternionBlockIndependent b (outsideFeature b t) := by
  intro term hterm
  simp only [outsideFeature, List.mem_singleton] at hterm
  subst term
  exact clearQuaternionBlock_idempotent b t.1

theorem inside_independent (a b : Nat) (hne : a ≠ b) (t : RatTerm) :
    QuaternionBlockIndependent a (insideFeature b t) := by
  intro term hterm
  simp only [insideFeature, List.mem_singleton] at hterm
  subst term
  exact clear_keep_block_independent_from a b 0 hne t.1

#print axioms keepBlockFrom
#print axioms keepBlock
#print axioms outsideFeature
#print axioms insideFeature
#print axioms term_factorization
#print axioms outside_independent
#print axioms inside_independent

end YMGap.Continuum.SU2QuaternionBlockMonomialFeatures
