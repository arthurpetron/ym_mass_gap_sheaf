/-
# Support bookkeeping for quaternion angular derivatives

Formal coordinate differentiation and head-block rotations do not introduce
coordinates outside the original finite quaternion carrier.  This file also
records scalar compatibility and the exact removal of a rational center.
These are algebraic support facts only; no Haar estimate or action bound is
asserted.
-/

import YMGap.Continuum.SU2QuaternionHaarAngularIBP
import YMGap.Continuum.BF4CompactActionCPOrder

namespace YMGap.Continuum.SU2QuaternionAngularSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarAngularIBP

private theorem lowerExponentAt_length (coordinate : Nat) : ∀ monomial : List Nat,
    (lowerExponentAt coordinate monomial).length = monomial.length
  | [] => by cases coordinate <;> rfl
  | _ :: rest => by
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          simp only [lowerExponentAt, List.length_cons]
          exact congrArg Nat.succ (lowerExponentAt_length coordinate rest)

/-- Formal differentiation preserves a supplied quaternion-block support. -/
theorem ratDerivative_supported {blocks coordinate : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (ratDerivative coordinate p) := by
  intro term ht
  unfold ratDerivative at ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  rw [lowerExponentAt_length]
  exact hp source hs

/-- Rational scalar multiplication preserves quaternion-block support. -/
theorem polySmul_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp ht
  exact hp source hs

/-- Polynomial addition preserves quaternion-block support. -/
theorem polyAdd_supported {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := by
  intro term ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp term ht
  · exact hq term ht

private theorem polyVar_supported {blocks coordinate : Nat}
    (hc : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro term ht
  simp only [polyVar, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst term
  simp [varMono]
  omega

/-- A head angular derivative preserves support in every nonempty block
carrier. -/
theorem angularDerivative_supported {blocks i j : Nat} {p : RatPoly}
    (hblocks : 0 < blocks) (hi : i < 4) (hj : j < 4)
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (angularDerivative i j p) := by
  have hi' : i < 4 * blocks := by omega
  have hj' : j < 4 * blocks := by omega
  unfold angularDerivative
  exact polyAdd_supported
    (supported_polyMul (polyVar_supported hi') (ratDerivative_supported hp))
    (polySmul_supported
      (supported_polyMul (polyVar_supported hj') (ratDerivative_supported hp)) (-1))

/-- Angular differentiation commutes with rational scalar multiplication. -/
theorem angularDerivative_smul (i j : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (polySmul c p))
      (polySmul c (angularDerivative i j p)) := by
  let left := polyMul (polyVar i) (ratDerivative j p)
  let right := polyMul (polyVar j) (ratDerivative i p)
  have hleft : RatPolyCoeffEqv
      (polyMul (polyVar i) (ratDerivative j (polySmul c p)))
      (polySmul c left) :=
    ((ratDerivative_smul j c p).mul_left (polyVar i)).trans
      (RatPolyCoeffEqv.polyMul_smul_right c (polyVar i) (ratDerivative j p))
  have hright : RatPolyCoeffEqv
      (polyMul (polyVar j) (ratDerivative i (polySmul c p)))
      (polySmul c right) :=
    ((ratDerivative_smul i c p).mul_left (polyVar j)).trans
      (RatPolyCoeffEqv.polyMul_smul_right c (polyVar j) (ratDerivative i p))
  have hnegative : RatPolyCoeffEqv
      (polySmul (-1) (polySmul c right))
      (polySmul c (polySmul (-1) right)) :=
    (RatPolyCoeffEqv.smul_assoc (-1) c right).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) c) right).trans
        (RatPolyCoeffEqv.smul_assoc c (-1) right).symm)
  unfold angularDerivative
  exact (hleft.add ((hright.smul (-1)).trans hnegative)).trans
    (RatPolyCoeffEqv.smul_add c left (polySmul (-1) right)).symm

/-- Subtracting an arbitrary rational constant does not change the angular
derivative. -/
theorem angularDerivative_centered {i j : Nat} (hi : i < 4) (hj : j < 4)
    (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j
        (polyAdd f (polySmul (-c) polyOne)))
      (angularDerivative i j f) := by
  have hone := angularDerivative_independent_zero hi hj polyOne
    (hasQuaternionBlockDegree_one 0)
  have hc : RatPolyCoeffEqv
      (angularDerivative i j (polySmul (-c) polyOne)) polyZero :=
    (angularDerivative_smul i j (-c) polyOne).trans
      ((hone.smul (-c)).trans (RatPolyCoeffEqv.smul_zero (-c)))
  refine (angularDerivative_add i j f (polySmul (-c) polyOne)).trans ?_
  exact ((RatPolyCoeffEqv.refl _).add hc).trans
    (RatPolyCoeffEqv.add_zero _)

end YMGap.Continuum.SU2QuaternionAngularSupport

#print axioms YMGap.Continuum.SU2QuaternionAngularSupport.ratDerivative_supported
#print axioms YMGap.Continuum.SU2QuaternionAngularSupport.polySmul_supported
#print axioms YMGap.Continuum.SU2QuaternionAngularSupport.polyAdd_supported
#print axioms YMGap.Continuum.SU2QuaternionAngularSupport.angularDerivative_supported
#print axioms YMGap.Continuum.SU2QuaternionAngularSupport.angularDerivative_smul
#print axioms YMGap.Continuum.SU2QuaternionAngularSupport.angularDerivative_centered
