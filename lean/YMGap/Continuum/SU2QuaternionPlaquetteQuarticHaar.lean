/-
# Cubic and quartic Haar moments of a literal spatial SU(2) plaquette

The character recurrence and one actual selected physical link give the
third and fourth bare Haar moments on the original four-link face.  These
moments are the finite geometric inputs for a projected-source Ward-sign
diagnostic.  No terminal source, interacting marginal, or continuum claim is
made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
import YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare

namespace YMGap.Continuum.SU2QuaternionPlaquetteQuarticHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (character_haar_zero)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
  (first_character_square)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

/-- The already-used SU(2) fundamental-times-character recurrence, exposed
locally so neither the literal face nor its inverse orientations are changed. -/
private theorem first_mul_succ (p : RatPoly) (n : Nat) :
    RatPolyCoeffEqv
      (polyMul (characterPolynomial p 1) (characterPolynomial p (n+1)))
      (polyAdd (characterPolynomial p (n+2)) (characterPolynomial p n)) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p (n+1))
  let b := characterPolynomial p n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1))
    (by decide) (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (.refl b))

private theorem cube_character (p : RatPoly) :
    let f := characterPolynomial p 1
    RatPolyCoeffEqv (polyMul (polyMul f f) f)
      (polyAdd f (polyAdd (characterPolynomial p 3) f)) := by
  dsimp only
  let f := characterPolynomial p 1
  let chi2 := characterPolynomial p 2
  exact ((first_character_square p).mul_right f).trans
    ((RatPolyCoeffEqv.mul_comm (polyAdd polyOne chi2) f).trans
      ((RatPolyCoeffEqv.mul_add_right f polyOne chi2).trans
        ((RatPolyCoeffEqv.mul_one f).add (first_mul_succ p 1))))

private theorem square_mul_two (p : RatPoly) :
    let f := characterPolynomial p 1
    let chi2 := characterPolynomial p 2
    RatPolyCoeffEqv (polyMul (polyMul f f) chi2)
      (polyAdd
        (polyAdd (characterPolynomial p 4) chi2)
        (polyAdd chi2 polyOne)) := by
  dsimp only
  let f := characterPolynomial p 1
  let chi2 := characterPolynomial p 2
  exact (RatPolyCoeffEqv.mul_assoc f f chi2).trans
    (((first_mul_succ p 1).mul_left f).trans
      ((RatPolyCoeffEqv.mul_add_right f (characterPolynomial p 3) f).trans
        ((first_mul_succ p 2).add (first_mul_succ p 0))))

private theorem fourth_character (p : RatPoly) :
    let f := characterPolynomial p 1
    let chi2 := characterPolynomial p 2
    RatPolyCoeffEqv (polyMul (polyMul f f) (polyMul f f))
      (polyAdd (polyAdd polyOne chi2)
        (polyAdd (polyAdd (characterPolynomial p 4) chi2)
          (polyAdd chi2 polyOne))) := by
  dsimp only
  let f := characterPolynomial p 1
  let chi2 := characterPolynomial p 2
  let f2 := polyMul f f
  exact ((RatPolyCoeffEqv.refl f2).mul (first_character_square p)).trans
    ((RatPolyCoeffEqv.mul_add_right f2 polyOne chi2).trans
      (((RatPolyCoeffEqv.mul_one f2).add (square_mul_two p)).trans
        ((first_character_square p).add (RatPolyCoeffEqv.refl _))))

/-- Every positive-spin literal plaquette character has zero bare Haar mean.
The one chosen link remains an actual member of the original face. -/
private theorem spin_haar_zero (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (spin : Nat) (hs : 0 < spin) :
    H width (characterPolynomial (plaquette width face).scalar spin) ≈ 0 := by
  let l : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : l ∈ edgesOf face := by simp [l, edgesOf]
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff
      (RatPolyCoeffEqv.mul_one (characterPolynomial (plaquette width face).scalar spin))))
    (character_haar_zero hf l hl spin hs polyOne (supported_one _)
      (quaternionBlockIndependent_polyOne _))

/-- Third moment of the actual four-link fundamental Wilson plaquette. -/
theorem plaquette_cubic_zero (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    let f := characterPolynomial (plaquette width face).scalar 1
    H width (polyMul (polyMul f f) f) ≈ 0 := by
  dsimp only
  let p := (plaquette width face).scalar
  let f := characterPolynomial p 1
  have h := haar_of_coeff (blocks := N width) (cube_character p)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (spin_haar_zero width face hf 1 (by decide))
          (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
            (Q'.add_eqv_congr'
              (spin_haar_zero width face hf 3 (by decide))
              (spin_haar_zero width face hf 1 (by decide)))))
        (by decide)))

/-- Fourth moment of the same physical four-link fundamental character;
the two vacuum channels survive, while spins two and four vanish. -/
theorem plaquette_quartic_two (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    let f := characterPolynomial (plaquette width face).scalar 1
    H width (polyMul (polyMul f f) (polyMul f f)) ≈ 2 := by
  dsimp only
  let p := (plaquette width face).scalar
  have h := haar_of_coeff (blocks := N width) (fourth_character p)
  have hzero2 := spin_haar_zero width face hf 2 (by decide)
  have hzero4 := spin_haar_zero width face hf 4 (by decide)
  have hone : H width polyOne ≈ 1 :=
    QPolyHaarPositiveSubstitution.haar_one (N width)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
            (Q'.add_eqv_congr' hone hzero2))
          (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
            (Q'.add_eqv_congr'
              (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
                (Q'.add_eqv_congr' hzero4 hzero2))
              (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
                (Q'.add_eqv_congr' hzero2 hone)))))
        (by decide)))

#print axioms plaquette_cubic_zero
#print axioms plaquette_quartic_two

end YMGap.Continuum.SU2QuaternionPlaquetteQuarticHaar
