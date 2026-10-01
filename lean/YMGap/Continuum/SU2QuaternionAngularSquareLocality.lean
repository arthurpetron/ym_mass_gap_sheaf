/-
# Block locality of the six-plane angular square

Differentiating in one quaternion block preserves syntactic independence
of every distinct block. If the polynomial is independent of the selected
block itself, its angular square vanishes coefficientwise.
-/

import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.SU2QuaternionAngularSquareLocality

set_option autoImplicit false

open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)

private theorem derivative_preserves_independent
    {selected block component : Nat} (hne : block ≠ selected)
    (hc : component < 4) {f : RatPoly}
    (hf : QuaternionBlockIndependent selected f) :
    QuaternionBlockIndependent selected (ratDerivative (4*block+component) f) := by
  intro term ht
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ht
  change clearQuaternionBlock selected
      (lowerExponentAt (4*block+component) source.1) =
    lowerExponentAt (4*block+component) source.1
  rw [← lowerExponentAt_clearQuaternionBlock_of_ne hne hc,
    hf source hsource]

private theorem angular_preserves_independent
    {selected block i j : Nat} (hne : block ≠ selected)
    (hi : i < 4) (hj : j < 4) {f : RatPoly}
    (hf : QuaternionBlockIndependent selected f) :
    QuaternionBlockIndependent selected (blockAngularDerivative block i j f) := by
  exact quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polyMul
      (quaternionBlockIndependent_polyVar_of_distinctBlock hne hi)
      (derivative_preserves_independent hne hj hf))
    (quaternionBlockIndependent_polySmul (-1)
      (quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyVar_of_distinctBlock hne hj)
        (derivative_preserves_independent hne hi hf)))

/-- The angular square at `block` introduces no dependence on a distinct
quaternion block, including all six signed cross terms inside its square. -/
theorem blockAngularSquare_independent_of_ne
    {selected block : Nat} (hne : block ≠ selected) {f : RatPoly}
    (hf : QuaternionBlockIndependent selected f) :
    QuaternionBlockIndependent selected (blockAngularSquare block f) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) :
      QuaternionBlockIndependent selected
        (polyMul (blockAngularDerivative block i j f)
          (blockAngularDerivative block i j f)) :=
    quaternionBlockIndependent_polyMul
      (angular_preserves_independent hne hi hj hf)
      (angular_preserves_independent hne hi hj hf)
  unfold blockAngularSquare six
  exact quaternionBlockIndependent_polyAdd (h 0 1 (by decide) (by decide))
    (quaternionBlockIndependent_polyAdd (h 0 2 (by decide) (by decide))
      (quaternionBlockIndependent_polyAdd (h 0 3 (by decide) (by decide))
        (quaternionBlockIndependent_polyAdd (h 1 2 (by decide) (by decide))
          (quaternionBlockIndependent_polyAdd (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

/-- Independence of the differentiated block makes every angular plane
zero coefficientwise, not merely after Haar integration. -/
theorem blockAngularSquare_zero {block : Nat} {f : RatPoly}
    (hf : QuaternionBlockIndependent block f) :
    RatPolyCoeffEqv (blockAngularSquare block f) polyZero := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) :
      RatPolyCoeffEqv
        (polyMul (blockAngularDerivative block i j f)
          (blockAngularDerivative block i j f)) polyZero :=
    let hz := angularDerivative_blockIndependent_zero hi hj hf
    (hz.mul hz).trans (RatPolyCoeffEqv.mul_zero_left polyZero)
  unfold blockAngularSquare six
  exact ((h 0 1 (by decide) (by decide)).add
    ((h 0 2 (by decide) (by decide)).add
      ((h 0 3 (by decide) (by decide)).add
        ((h 1 2 (by decide) (by decide)).add
          ((h 1 3 (by decide) (by decide)).add
            (h 2 3 (by decide) (by decide))))))).trans (by
              change RatPolyCoeffEqv polyZero polyZero
              exact RatPolyCoeffEqv.refl _)

end YMGap.Continuum.SU2QuaternionAngularSquareLocality

#print axioms YMGap.Continuum.SU2QuaternionAngularSquareLocality.blockAngularSquare_independent_of_ne
#print axioms YMGap.Continuum.SU2QuaternionAngularSquareLocality.blockAngularSquare_zero
