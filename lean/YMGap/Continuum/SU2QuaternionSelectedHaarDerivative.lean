/-
# Derivatives through an in-place selected quaternion Haar projection

Lowering an exponent outside a selected quaternion block commutes with the
selected block mask and leaves its four-coordinate moment unchanged.  These
monomial identities give coefficientwise commutation of the corresponding
formal derivative with the concrete in-place Haar projection.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockProjection

namespace YMGap.Continuum.SU2QuaternionSelectedHaarDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (natList_eq_of_length_getD)

local infix:50 " ≈ " => Q'.eqv

private theorem lowerExponentAt_length (coordinate : Nat) : ∀ monomial : List Nat,
    (lowerExponentAt coordinate monomial).length = monomial.length
  | [] => by cases coordinate <;> rfl
  | _ :: rest => by
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          simp only [lowerExponentAt, List.length_cons,
            lowerExponentAt_length coordinate rest]

private theorem exponentAt_lowerExponentAt
    (coordinate target : Nat) (monomial : List Nat) :
    exponentAt (lowerExponentAt coordinate monomial) target =
      if coordinate = target then exponentAt monomial target - 1
      else exponentAt monomial target := by
  induction coordinate generalizing target monomial with
  | zero =>
      cases monomial with
      | nil => cases target <;> rfl
      | cons exponent rest => cases target <;> rfl
  | succ coordinate ih =>
      cases monomial with
      | nil => simp [lowerExponentAt, exponentAt]
      | cons exponent rest =>
          cases target with
          | zero => simp [lowerExponentAt, exponentAt]
          | succ target =>
              simpa [lowerExponentAt, exponentAt, Nat.succ.injEq] using
                ih target rest

/-- Clearing one quaternion block commutes with lowering an exponent in a
distinct quaternion block. -/
theorem lowerExponentAt_clearQuaternionBlock_of_ne
    {selected block component : Nat} (hne : block ≠ selected)
    (hcomponent : component < 4) (monomial : List Nat) :
    lowerExponentAt (4 * block + component)
        (clearQuaternionBlock selected monomial) =
      clearQuaternionBlock selected
        (lowerExponentAt (4 * block + component) monomial) := by
  apply natList_eq_of_length_getD
  · rw [lowerExponentAt_length, clearQuaternionBlock_length,
      clearQuaternionBlock_length, lowerExponentAt_length]
  · intro target htarget
    change exponentAt (lowerExponentAt (4 * block + component)
        (clearQuaternionBlock selected monomial)) target =
      exponentAt (clearQuaternionBlock selected
        (lowerExponentAt (4 * block + component) monomial)) target
    rw [exponentAt_lowerExponentAt, exponentAt_clearQuaternionBlock,
      exponentAt_clearQuaternionBlock, exponentAt_lowerExponentAt]
    have hout : ¬ coordinateInQuaternionBlock selected (4 * block + component) := by
      intro hin
      have hleft := hin.1
      have hright := hin.2
      have : selected = block := by omega
      exact hne this.symm
    by_cases heq : 4 * block + component = target
    · subst target
      simp only [hout, if_false]
    · simp only [if_neg heq]

/-- A selected quaternion moment is unchanged by lowering an exponent in a
distinct block. -/
theorem quaternionBlockMoment_lowerExponentAt_of_ne
    {selected block component : Nat} (hne : block ≠ selected)
    (hcomponent : component < 4) (monomial : List Nat) :
    quaternionBlockMoment selected
        (lowerExponentAt (4 * block + component) monomial) =
      quaternionBlockMoment selected monomial := by
  unfold quaternionBlockMoment
  have hcoord : ∀ k : Nat, k < 4 →
      4 * block + component ≠ 4 * selected + k := by
    intro k hk heq
    apply hne
    omega
  have hzero : 4 * block + component ≠ 4 * selected := by
    simpa only [Nat.add_zero] using hcoord 0 (by decide)
  rw [exponentAt_lowerExponentAt, if_neg hzero,
    exponentAt_lowerExponentAt, if_neg (hcoord 1 (by omega)),
    exponentAt_lowerExponentAt, if_neg (hcoord 2 (by omega)),
    exponentAt_lowerExponentAt, if_neg (hcoord 3 (by omega))]

private theorem map_coeff {A : Type} (left right : A → RatTerm)
    (h : ∀ a, (left a).1 = (right a).1 ∧ (left a).2 ≈ (right a).2) :
    ∀ xs : List A, RatPolyCoeffEqv (xs.map left) (xs.map right)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => by
      intro weight
      change (left a).2 * weight (left a).1 +
          ratWeightedSum weight (xs.map left) ≈
        (right a).2 * weight (right a).1 +
          ratWeightedSum weight (xs.map right)
      rw [(h a).1]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (h a).2)
        (map_coeff left right h xs weight)

/-- A coordinate derivative in one quaternion block commutes
coefficientwise with Haar projection in a distinct block. -/
theorem ratDerivative_project_of_ne
    {selected block component : Nat} (hne : block ≠ selected)
    (hcomponent : component < 4) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative (4 * block + component) (project selected polynomial))
      (project selected (ratDerivative (4 * block + component) polynomial)) := by
  simp only [ratDerivative, project, integrateQuaternionBlock, List.map_map]
  apply map_coeff
  intro term
  constructor
  · exact lowerExponentAt_clearQuaternionBlock_of_ne hne hcomponent term.1
  · change Q'.ofNat
        (exponentAt (clearQuaternionBlock selected term.1)
          (4 * block + component)) *
          (term.2 * quaternionBlockMoment selected term.1) ≈
        (Q'.ofNat (exponentAt term.1 (4 * block + component)) * term.2) *
          quaternionBlockMoment selected
            (lowerExponentAt (4 * block + component) term.1)
    rw [exponentAt_clearQuaternionBlock_of_ne term.1 hne hcomponent,
      quaternionBlockMoment_lowerExponentAt_of_ne hne hcomponent]
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

#print axioms lowerExponentAt_clearQuaternionBlock_of_ne
#print axioms quaternionBlockMoment_lowerExponentAt_of_ne
#print axioms ratDerivative_project_of_ne

end YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
