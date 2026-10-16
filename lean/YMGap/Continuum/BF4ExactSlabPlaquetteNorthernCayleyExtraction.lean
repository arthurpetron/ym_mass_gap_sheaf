/-
# Northern-chart extraction for the ORIGINAL plaquette scalar

On the explicit event that the four actual link values in one corrected-slab
plaquette have nonnegative scalar coordinate, the constructive inverse Cayley
chart supplies the four chart pins required by the exact cleared plaquette
identity.  No independent-link replacement or new source law is introduced.

This is a pointwise finite identity.  It does not estimate the complementary
southern-chart event, integrate the rational chart coordinates, compare the
original Haar carrier with a Gaussian law, or prove any continuum statement.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a + c ≈ b + d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h

/-- Multiplication of a chart triple by the rational unit changes only its
stored rational representatives, not its semantic coordinates. -/
theorem scale3_one_equivalent (a : Triple) :
    ((scale3 1 a).x ≈ a.x) ∧
      ((scale3 1 a).y ≈ a.y) ∧
      ((scale3 1 a).z ≈ a.z) :=
  ⟨Q'.one_mul_eqv a.x, Q'.one_mul_eqv a.y, Q'.one_mul_eqv a.z⟩

/-- Exact stereographic coordinates respect the semantic scale-by-one change
of rational representatives. -/
theorem stereographic_scale3_one (a : Triple) :
    (stereographic (scale3 1 a)).Equivalent (stereographic a) := by
  have hcoord := scale3_one_equivalent a
  have hnorm : norm3 (scale3 1 a) ≈ norm3 a := by
    unfold norm3
    exact ac (ac (mc hcoord.1 hcoord.1) (mc hcoord.2.1 hcoord.2.1))
      (mc hcoord.2.2 hcoord.2.2)
  have hden : denominator (scale3 1 a) ≈ denominator a :=
    ac (Q'.eqv_refl 1) hnorm
  have hrecip :
      Q'.recipPos (denominator (scale3 1 a)) (denominator_positive (scale3 1 a)) ≈
        Q'.recipPos (denominator a) (denominator_positive a) :=
    Q'.recipPos_eqv_congr _ _ _ _ hden
  have hrawScalar : 1 + -norm3 (scale3 1 a) ≈ 1 + -norm3 a :=
    ac (Q'.eqv_refl 1) (nc hnorm)
  change
    (Q'.recipPos (denominator (scale3 1 a)) (denominator_positive (scale3 1 a)) *
          (1 + -norm3 (scale3 1 a)) ≈
        Q'.recipPos (denominator a) (denominator_positive a) * (1 + -norm3 a)) ∧
      (Q'.recipPos (denominator (scale3 1 a)) (denominator_positive (scale3 1 a)) *
          (2 * (scale3 1 a).x) ≈
        Q'.recipPos (denominator a) (denominator_positive a) * (2 * a.x)) ∧
      (Q'.recipPos (denominator (scale3 1 a)) (denominator_positive (scale3 1 a)) *
          (2 * (scale3 1 a).y) ≈
        Q'.recipPos (denominator a) (denominator_positive a) * (2 * a.y)) ∧
      (Q'.recipPos (denominator (scale3 1 a)) (denominator_positive (scale3 1 a)) *
          (2 * (scale3 1 a).z) ≈
        Q'.recipPos (denominator a) (denominator_positive a) * (2 * a.z))
  exact ⟨mc hrecip hrawScalar,
    mc hrecip (mc (Q'.eqv_refl 2) hcoord.1),
    mc hrecip (mc (Q'.eqv_refl 2) hcoord.2.1),
    mc hrecip (mc (Q'.eqv_refl 2) hcoord.2.2)⟩

private theorem northernChartPin (x : UnitNorm) (hx : (0 : Q') ≤ x.val.r) :
    x.Equivalent (stereographic (scale3 1 (inverseChart x hx))) := by
  exact UnitNorm.semanticSetoid.iseqv.trans
    (UnitNorm.semanticSetoid.iseqv.symm (stereographic_inverse x hx))
    (UnitNorm.semanticSetoid.iseqv.symm
      (stereographic_scale3_one (inverseChart x hx)))

/-- On the explicit northern-chart event for all four actual link values, the
ORIGINAL corrected-slab plaquette scalar has the exact denominator-cleared
Cayley polynomial.  The four inverse coordinates are constructive witnesses;
the earlier supplied chart-pin premises have disappeared. -/
theorem original_plaquette_northern_cayley_cleared
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq)
    (ha : (0 : Q') ≤
      (linkValue extent qs (face.1, (dirsOf face.2).1)).val.r)
    (hb : (0 : Q') ≤
      (linkValue extent qs
        (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)).val.r)
    (hc : (0 : Q') ≤
      (linkValue extent qs
        (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)).val.r)
    (hd : (0 : Q') ≤
      (linkValue extent qs (face.1, (dirsOf face.2).2)).val.r) :
    let a := inverseChart
      (linkValue extent qs (face.1, (dirsOf face.2).1)) ha
    let b := inverseChart
      (linkValue extent qs
        (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)) hb
    let c := inverseChart
      (linkValue extent qs
        (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)) hc
    let d := inverseChart
      (linkValue extent qs (face.1, (dirsOf face.2).2)) hd
    cayleyDenominator 1 a b (neg3 c) (neg3 d) *
        (2 + -(2 * evalRatPoly (environment qs)
          (correctedSlabPlaquettePolynomial extent face).scalar)) ≈
      cayleyDeficit 1 a b (neg3 c) (neg3 d) := by
  dsimp only
  exact original_plaquette_cayley_cleared extent qs face 1 _ _ _ _
    (northernChartPin _ ha) (northernChartPin _ hb)
    (northernChartPin _ hc) (northernChartPin _ hd)

end YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction.scale3_one_equivalent
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction.stereographic_scale3_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNorthernCayleyExtraction.original_plaquette_northern_cayley_cleared
