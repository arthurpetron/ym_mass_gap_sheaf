/-
# Head degree under angular differentiation in a distinct quaternion block

The literal rational-polynomial derivative retains zero-coefficient terms.
Even these retain their head degree when the differentiated coordinate lies
outside the head block. This is syntactic algebra, not a Haar estimate.
-/

import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionDerivativeCommutation

namespace YMGap.Continuum.QuaternionHaarMixedAngularDerivative

set_option autoImplicit false

open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex

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

/-- A derivative outside coordinates 0--3 preserves literal head degree,
including terms with zero differentiation coefficient. -/
theorem ratDerivative_headDegree_other {coordinate degree : Nat}
    (hcoordinate : 4 ≤ coordinate) {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 degree p) :
    HasQuaternionBlockDegree 0 degree (ratDerivative coordinate p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact (lower_other_preserves_head_degree coordinate hcoordinate source.1).trans
    (hp source hs)

/-- An angular derivative in a non-head quaternion block preserves the
exact syntactic degree of every head monomial. -/
theorem blockAngularDerivative_headDegree_of_ne
    {block degree : Nat} (hblock : block ≠ 0) (i j : Nat)
    (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 degree p) :
    HasQuaternionBlockDegree 0 degree (blockAngularDerivative block i j p) := by
  have hcoord_i : 4 ≤ 4*block+i := by omega
  have hcoord_j : 4 ≤ 4*block+j := by omega
  have hvar_i : HasQuaternionBlockDegree 0 0 (polyVar (4*block+i)) := by
    simpa only [if_neg hblock.symm] using
      (hasQuaternionBlockDegree_coordinate block i 0 hi)
  have hvar_j : HasQuaternionBlockDegree 0 0 (polyVar (4*block+j)) := by
    simpa only [if_neg hblock.symm] using
      (hasQuaternionBlockDegree_coordinate block j 0 hj)
  unfold blockAngularDerivative angularDerivative
  have hleft := hvar_i.mul (ratDerivative_headDegree_other hcoord_j hp)
  have hright := hvar_j.mul (ratDerivative_headDegree_other hcoord_i hp)
  have hleft' : HasQuaternionBlockDegree 0 degree
      (polyMul (polyVar (4*block+i)) (ratDerivative (4*block+j) p)) := by
    simpa only [Nat.zero_add] using hleft
  have hright' : HasQuaternionBlockDegree 0 degree
      (polyMul (polyVar (4*block+j)) (ratDerivative (4*block+i) p)) := by
    simpa only [Nat.zero_add] using hright
  exact hleft'.add (hright'.smul (-1))

/-- The same distinct-block derivative remains in the declared finite
quaternion carrier. -/
theorem blockAngularDerivative_supported {blocks block : Nat}
    (hblock : block < blocks) (i j : Nat) (hi : i < 4) (hj : j < 4)
    {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (blockAngularDerivative block i j p) := by
  unfold blockAngularDerivative
  exact angularDerivative_supported_at (by omega) (by omega) hp

#print axioms ratDerivative_headDegree_other
#print axioms blockAngularDerivative_headDegree_of_ne
#print axioms blockAngularDerivative_supported

end YMGap.Continuum.QuaternionHaarMixedAngularDerivative
