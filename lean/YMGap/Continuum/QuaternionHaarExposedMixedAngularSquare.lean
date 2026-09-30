/-
# Exact mixed angular square for the exposed four-link fundamental word

Both first-order angular-square identities belong to the SAME polynomial
character. The second is the cyclic presentation with block one first.
The resulting mixed square retains every Haar insertion, without an action,
positivity, or continuum assumption.
-/

import YMGap.Continuum.QuaternionHaarMixedAngularSquare
import YMGap.Continuum.QuaternionHaarMixedAngularDerivative
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare

namespace YMGap.Continuum.QuaternionHaarExposedMixedAngularSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
  (exposedFourWord exposedFourWord_scalar_blockDegree)
open YMGap.Continuum.SU2QuaternionOrientedWordSelection (word word_cyclic)
open YMGap.Continuum.SU2QuaternionFourBlockExposure (fourBlockExposure)
open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative angularDerivative_congr)
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative blockAngularSquare)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six angularSquare)
open YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy
  (exposedFundamental_angularSquare)
open YMGap.Continuum.QuaternionHaarMixedAngularDerivative
open YMGap.Continuum.QuaternionHaarMixedAngularSquare
  (mixed_square_of_linear_identities)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
  (oriented_fourWord_first_angularSquare_of_exposure)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem blockAngularSquare_congr (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularSquare block p) (blockAngularSquare block q) := by
  have hd (i j : Nat) := angularDerivative_congr (4*block+i) (4*block+j) h
  unfold blockAngularSquare six
  exact ((hd 0 1).mul (hd 0 1)).add
    (((hd 0 2).mul (hd 0 2)).add
      (((hd 0 3).mul (hd 0 3)).add
        (((hd 1 2).mul (hd 1 2)).add
          (((hd 1 3).mul (hd 1 3)).add
            ((hd 2 3).mul (hd 2 3))))))

/-- The block-one angular square is the same fundamental `4-f²` identity,
using only a cyclic re-expression of the exposed four-word. -/
theorem exposed_block_one_square {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) :
    let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
    HaarCarrierEqv blocks (blockAngularSquare 1 f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  dsimp only
  let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
  let rotated := characterPolynomial (word 1 2 3 0 r1 r2 r3 r0).scalar 1
  have hword : RatPolyCoeffEqv f rotated := by
    change RatPolyCoeffEqv
      (characterPolynomial (word 0 1 2 3 r0 r1 r2 r3).scalar 1)
      (characterPolynomial (word 1 2 3 0 r1 r2 r3 r0).scalar 1)
    exact characterPolynomial_coeffEqv (word_cyclic 0 1 2 3 r0 r1 r2 r3) 1
  let a : Fin blocks := ⟨1, by omega⟩
  let b : Fin blocks := ⟨2, by omega⟩
  let c : Fin blocks := ⟨3, hb⟩
  let d : Fin blocks := ⟨0, by omega⟩
  let exposure := fourBlockExposure hb a b c d
    (by change (1 : Nat) ≠ 2; decide) (by change (1 : Nat) ≠ 3; decide)
    (by change (1 : Nat) ≠ 0; decide) (by change (2 : Nat) ≠ 3; decide)
    (by change (2 : Nat) ≠ 0; decide) (by change (3 : Nat) ≠ 0; decide)
  have hrot : HaarCarrierEqv blocks (blockAngularSquare 1 rotated)
      (polyAdd (cap 4) (polyNeg (polyMul rotated rotated))) :=
    oriented_fourWord_first_angularSquare_of_exposure hb a b c d exposure r1 r2 r3 r0
  exact (RatPolyCoeffEqv.haarCarrier (blockAngularSquare_congr 1 hword)).trans
    (hrot.trans
      (RatPolyCoeffEqv.haarCarrier
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (RatPolyCoeffEqv.neg (hword.symm.mul hword.symm)))))

/-- Exact `S₂=8+f²`: the head angular energies of all six block-one
rotations of the SAME exposed fundamental character. -/
theorem exposed_mixed_angular_square {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) :
    let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
    HaarCarrierEqv blocks
      (six (fun i j => angularSquare (blockAngularDerivative 1 i j f)))
      (polyAdd (cap 8) (polyMul f f)) := by
  dsimp only
  let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
  have hf : HasQuaternionBlockDegree 0 1 f := by
    change HasQuaternionBlockDegree 0 1
      (polySmul 2 (exposedFourWord r0 r1 r2 r3).scalar)
    exact (exposedFourWord_scalar_blockDegree r0 r1 r2 r3 0 (by decide)).smul 2
  have hg : ∀ i j, i < 4 → j < 4 →
      HasQuaternionBlockDegree 0 1 (blockAngularDerivative 1 i j f) := by
    intro i j hi hj
    exact blockAngularDerivative_headDegree_of_ne (by decide : 1 ≠ 0) i j hi hj hf
  have hfSquare : HaarCarrierEqv blocks (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) :=
    exposedFundamental_angularSquare hb r0 r1 r2 r3
  have hgSquare : HaarCarrierEqv blocks
      (six (fun i j => polyMul (blockAngularDerivative 1 i j f)
        (blockAngularDerivative 1 i j f)))
      (polyAdd (cap 4) (polyNeg (polyMul f f))) :=
    exposed_block_one_square hb r0 r1 r2 r3
  exact mixed_square_of_linear_identities (by omega : 0 < blocks) f
    (fun i j => blockAngularDerivative 1 i j f) hf hg hfSquare hgSquare

/-- Every constructed nonnegative original polynomial weight keeps the
strict mixed-square floor eight times its own Haar mass. No lower bound on
the weight, and no normalization or replacement measure, is used. -/
theorem exposed_mixed_weighted_floor {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (W : RatPoly) (hW : Certificate blocks W) :
    let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
    8 * quaternionHaar blocks W ≤ quaternionHaar blocks
      (polyMul W (six (fun i j => angularSquare (blockAngularDerivative 1 i j f)))) := by
  dsimp only
  let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
  let E := six (fun i j => angularSquare (blockAngularDerivative 1 i j f))
  have hf : SupportedQuaternionBlocks blocks f :=
    SU2QuaternionOrientedWordSelection.word_supported
      (by omega : 0 < blocks) (by omega : 1 < blocks)
      (by omega : 2 < blocks) hb r0 r1 r2 r3 1
  have hs : (0 : Q') ≤ quaternionHaar blocks (polyMul W (polyMul f f)) :=
    Q'.le_trans' _ _ _ (hW.square_insertion_nonnegative f hf)
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul f f) W)))
  have hc : Q'.eqv (quaternionHaar blocks (polyMul W (cap 8)))
      (8 * quaternionHaar blocks W) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      ((RatPolyCoeffEqv.mul_comm W (cap 8)).trans
        (QuaternionHaarPolynomialSquareBound.cap_mul_left 8 W)))
      (quaternionHaar_polySmul blocks 8 W)
  have he : Q'.eqv (quaternionHaar blocks (polyMul W E))
      (8 * quaternionHaar blocks W + quaternionHaar blocks (polyMul W (polyMul f f))) := by
    have h := exposed_mixed_angular_square hb r0 r1 r2 r3 W
    exact Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W _ _))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' hc (Q'.eqv_refl _))))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hs)
    (Q'.le_of_eqv (Q'.eqv_symm he))

#print axioms exposed_block_one_square
#print axioms exposed_mixed_angular_square
#print axioms exposed_mixed_weighted_floor

end YMGap.Continuum.QuaternionHaarExposedMixedAngularSquare
