/-
# Head degree ceilings under differentiation in another block

A tangential derivative at a non-head quaternion block changes none of the
four head exponents. This statement includes literal zero-coefficient terms;
it is syntactic finite-polynomial bookkeeping, not a weighted estimate.
-/

import YMGap.Continuum.SU2QuaternionBlockDegreeBound
import YMGap.Continuum.QuaternionHaarMixedAngularDerivative

namespace YMGap.Continuum.QuaternionHaarMixedAngularDegreeBound

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionBlockDegreeBound

private theorem exponentAt_lower_other
    (coordinate target : Nat) (hne : coordinate ≠ target) :
    ∀ monomial : List Nat,
      exponentAt (lowerExponentAt coordinate monomial) target =
        exponentAt monomial target
  | [] => by cases coordinate <;> cases target <;> rfl
  | _ :: rest => by
      cases coordinate with
      | zero =>
          cases target with
          | zero => exact False.elim (hne rfl)
          | succ _ => rfl
      | succ coordinate =>
          cases target with
          | zero => rfl
          | succ target =>
              simp only [lowerExponentAt, exponentAt]
              exact exponentAt_lower_other coordinate target
                (fun h => hne (congrArg Nat.succ h)) rest

private theorem lower_other_preserves_head_degree
    (coordinate : Nat) (hcoord : 4 ≤ coordinate) (monomial : List Nat) :
    quaternionBlockDegree (lowerExponentAt coordinate monomial) 0 =
      quaternionBlockDegree monomial 0 := by
  have h0 : coordinate ≠ 0 := by omega
  have h1 : coordinate ≠ 1 := by omega
  have h2 : coordinate ≠ 2 := by omega
  have h3 : coordinate ≠ 3 := by omega
  simp only [quaternionBlockDegree, Nat.mul_zero, Nat.zero_add,
    exponentAt_lower_other coordinate 0 h0,
    exponentAt_lower_other coordinate 1 h1,
    exponentAt_lower_other coordinate 2 h2,
    exponentAt_lower_other coordinate 3 h3]

/-- A formal derivative in another block preserves every term's head-degree
ceiling, even when its coefficient is zero. -/
theorem ratDerivative_headDegreeLE_other {coordinate degree : Nat}
    (hcoordinate : 4 ≤ coordinate) {p : RatPoly}
    (hp : DegreeLE 0 degree p) :
    DegreeLE 0 degree (ratDerivative coordinate p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  rw [lower_other_preserves_head_degree coordinate hcoordinate source.1]
  exact hp source hs

/-- A tangential derivative in any non-head quaternion block preserves the
head-degree ceiling of the literal polynomial list. -/
theorem blockAngularDerivative_headDegreeLE_of_ne
    {block degree : Nat} (hblock : block ≠ 0) (i j : Nat)
    (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : DegreeLE 0 degree p) :
    DegreeLE 0 degree (blockAngularDerivative block i j p) := by
  have hcoord_i : 4 ≤ 4*block+i := by omega
  have hcoord_j : 4 ≤ 4*block+j := by omega
  have hvar_i : HasQuaternionBlockDegree 0 0 (polyVar (4*block+i)) := by
    simpa only [if_neg hblock.symm] using
      (hasQuaternionBlockDegree_coordinate block i 0 hi)
  have hvar_j : HasQuaternionBlockDegree 0 0 (polyVar (4*block+j)) := by
    simpa only [if_neg hblock.symm] using
      (hasQuaternionBlockDegree_coordinate block j 0 hj)
  have hvar_i_le : DegreeLE 0 0 (polyVar (4*block+i)) :=
    fun t ht => Nat.le_of_eq (hvar_i t ht)
  have hvar_j_le : DegreeLE 0 0 (polyVar (4*block+j)) :=
    fun t ht => Nat.le_of_eq (hvar_j t ht)
  unfold blockAngularDerivative angularDerivative
  have hleft : DegreeLE 0 degree
      (polyMul (polyVar (4*block+i)) (ratDerivative (4*block+j) p)) := by
    simpa only [Nat.zero_add] using
      (DegreeLE.mul hvar_i_le (ratDerivative_headDegreeLE_other hcoord_j hp))
  have hright : DegreeLE 0 degree
      (polyMul (polyVar (4*block+j)) (ratDerivative (4*block+i) p)) := by
    simpa only [Nat.zero_add] using
      (DegreeLE.mul hvar_j_le (ratDerivative_headDegreeLE_other hcoord_i hp))
  exact hleft.add (hright.smul (-1))

end YMGap.Continuum.QuaternionHaarMixedAngularDegreeBound

#print axioms YMGap.Continuum.QuaternionHaarMixedAngularDegreeBound.ratDerivative_headDegreeLE_other
#print axioms YMGap.Continuum.QuaternionHaarMixedAngularDegreeBound.blockAngularDerivative_headDegreeLE_of_ne
