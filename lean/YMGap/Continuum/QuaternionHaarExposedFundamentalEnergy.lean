/-
# Exact angular energy of an exposed fundamental character

The carré-du-champ Leibniz identity, exposed-character Casimir, and
fundamental fusion rule give Gamma(chi_1)=4-chi_1^2 under arbitrary
insertion in every carrier containing the four exposed quaternion blocks.
-/

import YMGap.Continuum.QuaternionHaarExposedHeatCasimir
import YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy

set_option autoImplicit false

local infix:50 " ≈ " => YMGap.Constructive.Q'.eqv

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.QuaternionHaarExposedHeatCasimir
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonic
open YMGap.Continuum.SU2QuaternionAllCarrierExposedSelection
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

attribute [local irreducible] angularDerivative

private theorem secondAngular_square (i j : Nat) (f : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyMul f f)))
      (polyAdd
        (polySmul 2 (polyMul (angularDerivative i j f) (angularDerivative i j f)))
        (polySmul 2 (polyMul f
          (angularDerivative i j (angularDerivative i j f))))) := by
  let df := angularDerivative i j f
  let ddf := angularDerivative i j df
  have hfirst := angularDerivative_mul i j f f
  have hsecond := (angularDerivative_congr i j hfirst).trans
    (angularDerivative_add i j (polyMul df f) (polyMul f df))
  have hexpand := (angularDerivative_mul i j df f).add
    (angularDerivative_mul i j f df)
  exact hsecond.trans (hexpand.trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 2) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 2))))
      (.add (.mul (.const 2) (.mul (.var 1) (.var 1)))
        (.mul (.const 2) (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => f | 1 => df | _ => ddf)).trans
      ((cap_mul_left 2 (polyMul df df)).add
        (cap_mul_left 2 (polyMul f ddf)))))

private theorem six_add (a b : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyAdd (a i j) (b i j)))
      (polyAdd (six a) (six b)) := by
  unfold six
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | 5 => a 2 3
      | 6 => b 0 1 | 7 => b 0 2 | 8 => b 0 3
      | 9 => b 1 2 | 10 => b 1 3 | _ => b 2 3)

private theorem six_smul (c : Q') (a : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polySmul c (a i j))) (polySmul c (six a)) := by
  unfold six
  have h4 := (RatPolyCoeffEqv.smul_add c (a 1 3) (a 2 3)).symm
  have h3 := ((RatPolyCoeffEqv.refl _).add h4).trans
    (RatPolyCoeffEqv.smul_add c (a 1 2) (polyAdd (a 1 3) (a 2 3))).symm
  have h2 := ((RatPolyCoeffEqv.refl _).add h3).trans
    (RatPolyCoeffEqv.smul_add c (a 0 3)
      (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))).symm
  have h1 := ((RatPolyCoeffEqv.refl _).add h2).trans
    (RatPolyCoeffEqv.smul_add c (a 0 2)
      (polyAdd (a 0 3) (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3))))).symm
  exact ((RatPolyCoeffEqv.refl _).add h1).trans
    (RatPolyCoeffEqv.smul_add c (a 0 1)
      (polyAdd (a 0 2) (polyAdd (a 0 3)
        (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))))).symm

private theorem six_mul_left (f : RatPoly) (a : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyMul f (a i j))) (polyMul f (six a)) := by
  unfold six
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1))
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 0) (.var 3))
          (.add (.mul (.var 0) (.var 4))
            (.add (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 6)))))))
    (.mul (.var 0) (.add (.var 1) (.add (.var 2) (.add (.var 3)
      (.add (.var 4) (.add (.var 5) (.var 6)))))))
    (by decide) (fun
      | 0 => f | 1 => a 0 1 | 2 => a 0 2 | 3 => a 0 3
      | 4 => a 1 2 | 5 => a 1 3 | _ => a 2 3)

private theorem six_square_collect (f : RatPoly) :
    RatPolyCoeffEqv
      (six (fun i j => polyAdd
        (polySmul 2 (polyMul (angularDerivative i j f) (angularDerivative i j f)))
        (polySmul 2 (polyMul f
          (angularDerivative i j (angularDerivative i j f))))))
      (polyAdd (polySmul 2 (angularSquare f))
        (polySmul 2 (polyMul f (angularLaplacian f)))) := by
  unfold angularSquare angularLaplacian
  let a := fun i j => polyMul (angularDerivative i j f) (angularDerivative i j f)
  let b := fun i j => polyMul f (angularDerivative i j (angularDerivative i j f))
  exact (six_add (fun i j => polySmul 2 (a i j))
      (fun i j => polySmul 2 (b i j))).trans
    ((six_smul 2 a).add
      ((six_smul 2 b).trans
        (RatPolyCoeffEqv.smul 2 (six_mul_left f
          (fun i j => angularDerivative i j (angularDerivative i j f))))))

/-- Polynomial carré-du-champ identity, before any Haar integration. -/
theorem angularLaplacian_square (f : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyMul f f))
      (polyAdd (polySmul 2 (angularSquare f))
        (polySmul 2 (polyMul f (angularLaplacian f)))) := by
  unfold angularLaplacian
  exact ((secondAngular_square 0 1 f).add
    ((secondAngular_square 0 2 f).add
      ((secondAngular_square 0 3 f).add
        ((secondAngular_square 1 2 f).add
          ((secondAngular_square 1 3 f).add
            (secondAngular_square 2 3 f)))))).trans
    (six_square_collect f)

private theorem secondAngular_add (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyAdd p q)))
      (polyAdd (angularDerivative i j (angularDerivative i j p))
        (angularDerivative i j (angularDerivative i j q))) :=
  (angularDerivative_congr i j (angularDerivative_add i j p q)).trans
    (angularDerivative_add i j (angularDerivative i j p) (angularDerivative i j q))

private theorem angularLaplacian_add (p q : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyAdd p q))
      (polyAdd (angularLaplacian p) (angularLaplacian q)) := by
  unfold angularLaplacian
  exact ((secondAngular_add 0 1 p q).add
    ((secondAngular_add 0 2 p q).add
      ((secondAngular_add 0 3 p q).add
        ((secondAngular_add 1 2 p q).add
          ((secondAngular_add 1 3 p q).add
            (secondAngular_add 2 3 p q)))))).trans
    (six_add
      (fun i j => angularDerivative i j (angularDerivative i j p))
      (fun i j => angularDerivative i j (angularDerivative i j q)))

private theorem angularDerivative_zero_local (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans
      (RatPolyCoeffEqv.zero_smul _))

private theorem secondAngular_one (i j : Nat) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j polyOne)) polyZero :=
  (angularDerivative_congr i j (angularDerivative_one i j)).trans
    (angularDerivative_zero_local i j)

private theorem angularLaplacian_one :
    RatPolyCoeffEqv (angularLaplacian polyOne) polyZero := by
  unfold angularLaplacian
  have h := ((secondAngular_one 0 1).add
    ((secondAngular_one 0 2).add
      ((secondAngular_one 0 3).add
        ((secondAngular_one 1 2).add
          ((secondAngular_one 1 3).add (secondAngular_one 2 3))))))
  change RatPolyCoeffEqv _ polyZero at h
  exact h

private theorem angularLaplacian_add_one (g : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyAdd g polyOne)) (angularLaplacian g) :=
  (angularLaplacian_add g polyOne).trans
    (((RatPolyCoeffEqv.refl _).add angularLaplacian_one).trans
      (RatPolyCoeffEqv.add_zero _))

/-- The fundamental Clebsch--Gordan identity in the polynomial carrier. -/
theorem fundamental_square (x : RatPoly) :
    RatPolyCoeffEqv (polyMul (characterPolynomial x 1) (characterPolynomial x 1))
      (polyAdd (characterPolynomial x 2) polyOne) := by
  let a := polyMul (characterPolynomial x 1) (characterPolynomial x 1)
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1))
    (by decide) (fun i => if i = 0 then a else polyOne)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) polyOne)).add
      (RatPolyCoeffEqv.refl polyOne))

/-- Generic exposed-character Casimir on every carrier containing blocks 0--3. -/
theorem exposedCharacter_angularCasimir {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) (spin : Nat) :
    QuaternionHaarCarrierEqv blocks
      (angularLaplacian
        (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin))
      (polySmul (-(Q'.ofNat spin * (Q'.ofNat spin + 2)))
        (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin)) := by
  let solid := exposedSolidZonalCharacter r0 r1 r2 r3 spin
  let ordinary := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar spin
  let eigenvalue := -(Q'.ofNat spin * (Q'.ofNat spin + 2))
  have hc : QuaternionHaarCarrierEqv blocks solid ordinary :=
    exposedSolid_eq_character hb r0 r1 r2 r3 spin
  have hl := angularLaplacian_carrier (by omega : 0 < blocks) hc
  have hs : QuaternionHaarCarrierEqv blocks
      (angularLaplacian solid) (polySmul eigenvalue solid) :=
    harmonic_angularLaplacian (by omega) solid
      (exposedSolidZonalCharacter_blockDegree r0 r1 r2 r3 0 (by omega) spin)
      (laplacian_exposedSolidZonalCharacter_zero r0 r1 r2 r3 spin)
  exact QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.symm hl)
    (QuaternionHaarCarrierEqv.trans hs (QuaternionHaarCarrierEqv.smul eigenvalue hc))

/-- Exact exposed fundamental energy with every polynomial insertion retained. -/
theorem exposedFundamental_angularSquare {blocks : Nat} (hb : 3 < blocks)
    (r0 r1 r2 r3 : Bool) :
    let f := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
    QuaternionHaarCarrierEqv blocks (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
  let x := (exposedFourWord r0 r1 r2 r3).scalar
  let f := characterPolynomial x 1
  let g := characterPolynomial x 2
  have hfusion : QuaternionHaarCarrierEqv blocks (polyMul f f) (polyAdd g polyOne) :=
    RatPolyCoeffEqv.haarCarrier (fundamental_square x)
  have hLf := exposedCharacter_angularCasimir hb r0 r1 r2 r3 1
  have hLg := exposedCharacter_angularCasimir hb r0 r1 r2 r3 2
  have hLsquare : QuaternionHaarCarrierEqv blocks
      (angularLaplacian (polyMul f f)) (polySmul (-8) g) :=
    QuaternionHaarCarrierEqv.trans
      (angularLaplacian_carrier (by omega) hfusion)
      (QuaternionHaarCarrierEqv.trans
        (RatPolyCoeffEqv.haarCarrier (angularLaplacian_add_one g))
        (QuaternionHaarCarrierEqv.trans hLg
          (RatPolyCoeffEqv.haarCarrier
            (RatPolyCoeffEqv.smul_coefficient (by decide) g))))
  have hLeib : QuaternionHaarCarrierEqv blocks
      (angularLaplacian (polyMul f f))
      (polyAdd (polySmul 2 (angularSquare f))
        (polySmul 2 (polyMul f (angularLaplacian f)))) :=
    RatPolyCoeffEqv.haarCarrier (angularLaplacian_square f)
  have hright : QuaternionHaarCarrierEqv blocks
      (polyAdd (polySmul 2 (angularSquare f))
        (polySmul 2 (polyMul f (angularLaplacian f))))
      (polyAdd (polySmul 2 (angularSquare f)) (polySmul (-6) (polyMul f f))) := by
    exact QuaternionHaarCarrierEqv.add (QuaternionHaarCarrierEqv.refl _ _)
      (QuaternionHaarCarrierEqv.trans
        (QuaternionHaarCarrierEqv.smul 2 (QuaternionHaarCarrierEqv.mul_left f hLf))
        (RatPolyCoeffEqv.haarCarrier (((cap_mul_left 2 _).symm.trans
          ((RatPolyCoeffEqv.refl _).mul
            ((RatPolyCoeffEqv.refl f).mul (cap_mul_left (-3) f).symm))).trans
          ((coeffEvalExpr_eqv_of_normalize_eq
            (.mul (.const 2) (.mul (.var 0) (.mul (.const (-3)) (.var 0))))
            (.mul (.const (-6)) (.mul (.var 0) (.var 0)))
            (by decide) (fun _ => f)).trans
              (cap_mul_left (-6) (polyMul f f))))))
  have hmain : QuaternionHaarCarrierEqv blocks
      (polyAdd (polySmul 2 (angularSquare f)) (polySmul (-6) (polyMul f f)))
      (polySmul (-8) g) :=
    QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.symm hright)
      (QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.symm hLeib) hLsquare)
  let F := polyMul f f
  let G := angularSquare f
  have hadd := QuaternionHaarCarrierEqv.add hmain
    (QuaternionHaarCarrierEqv.refl blocks (polySmul 6 F))
  have htwice : QuaternionHaarCarrierEqv blocks (polySmul 2 G)
      (polyAdd (polySmul (-8) g) (polySmul 6 F)) :=
    QuaternionHaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier
        ((cap_mul_left 2 G).symm.trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.const 2) (.var 0))
          (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const (-6)) (.var 1)))
            (.mul (.const 6) (.var 1)))
          (by decide) (fun | 0 => G | _ => F)).trans
        (((cap_mul_left 2 G).add (cap_mul_left (-6) F)).add
          (cap_mul_left 6 F)))))
      (QuaternionHaarCarrierEqv.trans hadd
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.refl _)))
  have hhalf := QuaternionHaarCarrierEqv.smul HalfPow.half htwice
  have hhalf_left : RatPolyCoeffEqv (polySmul HalfPow.half (polySmul 2 G)) G :=
    ((RatPolyCoeffEqv.smul_assoc HalfPow.half 2 G).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half * 2 ≈ 1) G)).trans
      (RatPolyCoeffEqv.one_smul G)
  have hhalf_right : RatPolyCoeffEqv
      (polySmul HalfPow.half (polyAdd (polySmul (-8) g) (polySmul 6 F)))
      (polyAdd (polySmul (-4) g) (polySmul 3 F)) :=
    (RatPolyCoeffEqv.smul_add HalfPow.half (polySmul (-8) g) (polySmul 6 F)).trans
      (((RatPolyCoeffEqv.smul_assoc HalfPow.half (-8) g).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half * (-8) ≈ -4) g)).add
        ((RatPolyCoeffEqv.smul_assoc HalfPow.half 6 F).trans
          (RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half * 6 ≈ 3) F)))
  have hgamma : QuaternionHaarCarrierEqv blocks G
      (polyAdd (polySmul (-4) g) (polySmul 3 F)) :=
    QuaternionHaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier hhalf_left.symm)
      (QuaternionHaarCarrierEqv.trans hhalf (RatPolyCoeffEqv.haarCarrier hhalf_right))
  have hthree : QuaternionHaarCarrierEqv blocks (polySmul 3 F)
      (polySmul 3 (polyAdd g polyOne)) := QuaternionHaarCarrierEqv.smul 3 hfusion
  have hnormalize : RatPolyCoeffEqv
      (polyAdd (polySmul (-4) g) (polySmul 3 (polyAdd g polyOne)))
      (polyAdd (cap 4) (polyNeg (polyAdd g polyOne))) :=
    (((cap_mul_left (-4) g).symm.add
      (cap_mul_left 3 (polyAdd g polyOne)).symm).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.const (-4)) (.var 0))
          (.mul (.const 3) (.add (.var 0) (.const 1))))
        (.add (.const 4) (.neg (.add (.var 0) (.const 1))))
        (by decide) (fun _ => g)))
  have hneg : QuaternionHaarCarrierEqv blocks
      (polyNeg (polyAdd g polyOne)) (polyNeg F) :=
    QuaternionHaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier
        (QuaternionHaarAngularCarrier.neg_smul (polyAdd g polyOne)))
      (QuaternionHaarCarrierEqv.trans
        (QuaternionHaarCarrierEqv.smul (-1) (QuaternionHaarCarrierEqv.symm hfusion))
        (RatPolyCoeffEqv.haarCarrier (QuaternionHaarAngularCarrier.neg_smul F).symm))
  exact QuaternionHaarCarrierEqv.trans hgamma
    (QuaternionHaarCarrierEqv.trans
      (QuaternionHaarCarrierEqv.add (QuaternionHaarCarrierEqv.refl _ _) hthree)
      (QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier hnormalize)
        (QuaternionHaarCarrierEqv.add (QuaternionHaarCarrierEqv.refl _ _) hneg)))

end YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy

#print axioms YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy.angularLaplacian_square
#print axioms YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy.fundamental_square
#print axioms YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy.exposedCharacter_angularCasimir
#print axioms YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy.exposedFundamental_angularSquare
