/-
# Exact product-heat image of the fundamental plaquette square

The Clebsch--Gordan identity `chi_1^2 = 1 + chi_2`, constant preservation,
and the literal four-link spin-two transmission give the complete square
image.  All equalities remain on the existing supported Haar quotient.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSpinTwoPlaquette
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatSpinTwoPlaquette

/-- The first character square is the vacuum plus the label-two character. -/
theorem first_character_square (p : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (characterPolynomial p 1) (characterPolynomial p 1))
      (polyAdd polyOne (characterPolynomial p 2)) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p 1)
  let b := characterPolynomial p 0
  have h : RatPolyCoeffEqv a
      (polyAdd (characterPolynomial p 2) polyOne) := by
    exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
      (fun i => if i = 0 then a else b)).trans
      (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add
        (RatPolyCoeffEqv.refl b))
  exact h.trans (RatPolyCoeffEqv.add_comm _ _)

/-- The actual selected product heat sends the fundamental plaquette square
to its vacuum channel plus the transmitted label-two channel. -/
theorem productMap_plaquetteSquare_of_perm
    (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest)) :
    let f := characterPolynomial (word a b c d false false true true).scalar 1
    let chi2 := characterPolynomial (word a b c d false false true true).scalar 2
    SupportedHaarEqv n (productMap n w K ids (polyMul f f))
      (polyAdd polyOne (polySmul (qpow w 32) chi2)) := by
  dsimp only
  let p := (word a b c d false false true true).scalar
  have hsquare : SupportedHaarEqv n
      (productMap n w K ids
        (polyMul (characterPolynomial p 1) (characterPolynomial p 1)))
      (productMap n w K ids (polyAdd polyOne (characterPolynomial p 2))) :=
    SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        (productMap_congr n w K ids (first_character_square p)))
  have hlinear : SupportedHaarEqv n
      (productMap n w K ids (polyAdd polyOne (characterPolynomial p 2)))
      (polyAdd (productMap n w K ids polyOne)
        (productMap n w K ids (characterPolynomial p 2))) :=
    SupportedHaarEqv.of_carrier
      (RatPolyCoeffEqv.haarCarrier
        (productMap_add n w K ids polyOne (characterPolynomial p 2)))
  have hone := productMap_one n w K ids hn hids
  have htwo := productMap_spinTwoPlaquette_of_perm n w K hK a b c d ids rest hn hids hp
  exact hsquare.trans (hlinear.trans (hone.add htwo))

end YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare

#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare.first_character_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare.productMap_plaquetteSquare_of_perm
