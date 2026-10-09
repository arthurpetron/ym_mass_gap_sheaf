/-
# Ordered finite bilinear folds on the original angular polynomials

These coefficient identities expand the literal active Gamma of two finite
RatPoly sums into their ordered occurrence pairs. Repeated indices and signed
rational scalars are retained. The original Casimir and product folds are
expanded on the same carrier; no raw derivative of a Haar equivalence occurs.

The consumer is signed original spatial-family curvature assembly. These
identities supply no sign for its channel-weighted cross moments, no warmed
source response estimate, and no scaling retention or physical gap.
-/

import YMGap.Continuum.SU2QuaternionActiveCasimirProduct
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.QuaternionHaarGammaFiniteSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyZero)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_add six_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (activeCasimir_add)

private theorem six_congr {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (a i j) (b i j)) :
    RatPolyCoeffEqv (six a) (six b) := by
  unfold six
  exact (h 0 1).add ((h 0 2).add ((h 0 3).add
    ((h 1 2).add ((h 1 3).add (h 2 3)))))

/-- Coefficient equivalence in both original Gamma arguments. -/
theorem activeGamma_congr (active : List Nat) {p p' q q' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') :
    RatPolyCoeffEqv (activeGamma active p q) (activeGamma active p' q') := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b rest ih =>
      exact (six_congr (fun i j =>
        (angularDerivative_congr (4*b+i) (4*b+j) hp).mul
          (angularDerivative_congr (4*b+i) (4*b+j) hq))).add ih

private theorem blockGamma_add_right (b : Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (blockGamma b p (polyAdd q r))
      (polyAdd (blockGamma b p q) (blockGamma b p r)) := by
  unfold blockGamma
  refine (six_congr (fun i j => ?_)).trans (six_add _ _)
  exact ((angularDerivative_add (4*b+i) (4*b+j) q r).mul_left _).trans
    (RatPolyCoeffEqv.mul_add_right _ _ _)

/-- Bilinearity in the right argument on exactly the listed original blocks. -/
theorem activeGamma_add_right (active : List Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (activeGamma active p (polyAdd q r))
      (polyAdd (activeGamma active p q) (activeGamma active p r)) := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b rest ih =>
      exact ((blockGamma_add_right b p q r).add ih).trans
        (RatPolyCoeffEqv.four_add_swap _ _ _ _)

/-- Bilinearity in the left argument, without a support or degree premise. -/
theorem activeGamma_add_left (active : List Nat) (p q r : RatPoly) :
    RatPolyCoeffEqv (activeGamma active (polyAdd p q) r)
      (polyAdd (activeGamma active p r) (activeGamma active q r)) :=
  (activeGamma_symm active _ r).trans ((activeGamma_add_right active r p q).trans
    ((activeGamma_symm active r p).add (activeGamma_symm active r q)))

/-- Independent rational scales multiply, retaining their signs. -/
theorem activeGamma_smul_pair (active : List Nat) (c d : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (activeGamma active (polySmul c p) (polySmul d q))
      (polySmul (c*d) (activeGamma active p q)) := by
  have hb (b : Nat) :
      RatPolyCoeffEqv (blockGamma b (polySmul c p) (polySmul d q))
        (polySmul (c*d) (blockGamma b p q)) := by
    unfold blockGamma
    refine (six_congr (fun i j => ?_)).trans (six_smul _ _)
    exact ((angularDerivative_smul (4*b+i) (4*b+j) c p).mul
      (angularDerivative_smul (4*b+i) (4*b+j) d q)).trans
      ((RatPolyCoeffEqv.polyMul_smul_left c _ _).trans
        (((RatPolyCoeffEqv.polyMul_smul_right d _ _).smul c).trans
          (RatPolyCoeffEqv.smul_assoc c d _)))
  induction active with
  | nil => exact (RatPolyCoeffEqv.smul_zero (c*d)).symm
  | cons b rest ih =>
      exact ((hb b).add ih).trans (RatPolyCoeffEqv.smul_add (c*d) _ _).symm

private theorem angular_zero (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans (RatPolyCoeffEqv.zero_smul _))

private theorem gamma_zero_right (active : List Nat) (p : RatPoly) :
    RatPolyCoeffEqv (activeGamma active p polyZero) polyZero := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b rest ih =>
      have hb : RatPolyCoeffEqv (blockGamma b p polyZero) polyZero := by
        unfold blockGamma
        exact six_congr (b := fun _ _ => polyZero) (fun i j =>
          ((angular_zero (4*b+i) (4*b+j)).mul_left _).trans
            (RatPolyCoeffEqv.mul_zero_right _))
      exact (hb.add ih).trans (RatPolyCoeffEqv.add_zero _)

/-- Pointwise coefficient transport through an ordered finite fold. -/
theorem finitePolySum_coeff_congr {I : Type} (f g : I → RatPoly)
    (h : ∀ i, RatPolyCoeffEqv (f i) (g i)) : ∀ xs : List I,
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => RatPolyCoeffEqv.refl _
  | i::xs => (h i).add (finitePolySum_coeff_congr f g h xs)

/-- The fold of pointwise sums splits without deduplicating either fold. -/
theorem finitePolySum_add {I : Type} (f g : I → RatPoly) : ∀ xs : List I,
    RatPolyCoeffEqv (finitePolySum (fun i => polyAdd (f i) (g i)) xs)
      (polyAdd (finitePolySum f xs) (finitePolySum g xs))
  | [] => RatPolyCoeffEqv.refl _
  | _::xs => ((RatPolyCoeffEqv.refl _).add (finitePolySum_add f g xs)).trans
      (RatPolyCoeffEqv.four_add_swap _ _ _ _)

/-- A signed rational scale commutes with the literal ordered fold. -/
theorem finitePolySum_smul {I : Type} (c : Q') (f : I → RatPoly) : ∀ xs : List I,
    RatPolyCoeffEqv (finitePolySum (fun i => polySmul c (f i)) xs)
      (polySmul c (finitePolySum f xs))
  | [] => (RatPolyCoeffEqv.smul_zero c).symm
  | _::xs => ((RatPolyCoeffEqv.refl _).add (finitePolySum_smul c f xs)).trans
      (RatPolyCoeffEqv.smul_add c _ _).symm

/-- Gamma expands the ordered fold in its right argument. -/
theorem activeGamma_finitePolySum_right {J : Type}
    (active : List Nat) (p : RatPoly) (g : J → RatPoly) : ∀ ys : List J,
    RatPolyCoeffEqv (activeGamma active p (finitePolySum g ys))
      (finitePolySum (fun j => activeGamma active p (g j)) ys)
  | [] => gamma_zero_right active p
  | j::ys => (activeGamma_add_right active p (g j) _).trans
      ((RatPolyCoeffEqv.refl _).add (activeGamma_finitePolySum_right active p g ys))

/-- Gamma expands the ordered fold in its left argument. -/
theorem activeGamma_finitePolySum_left {I : Type}
    (active : List Nat) (f : I → RatPoly) (xs : List I) (q : RatPoly) :
    RatPolyCoeffEqv (activeGamma active (finitePolySum f xs) q)
      (finitePolySum (fun i => activeGamma active (f i) q) xs) :=
  (activeGamma_symm active _ q).trans
    ((activeGamma_finitePolySum_right active q f xs).trans
      (finitePolySum_coeff_congr _ _ (fun i => activeGamma_symm active q (f i)) xs))

/-- Exact ordered occurrence-pair expansion, including repeated indices. -/
theorem activeGamma_finitePolySum_pair {I J : Type} (active : List Nat)
    (f : I → RatPoly) (g : J → RatPoly) (xs : List I) (ys : List J) :
    RatPolyCoeffEqv (activeGamma active (finitePolySum f xs) (finitePolySum g ys))
      (finitePolySum (fun i =>
        finitePolySum (fun j => activeGamma active (f i) (g j)) ys) xs) :=
  (activeGamma_finitePolySum_left active f xs _).trans
    (finitePolySum_coeff_congr _ _
      (fun i => activeGamma_finitePolySum_right active (f i) g ys) xs)

private theorem mul_fold_right {J : Type} (p : RatPoly) (g : J → RatPoly) :
    ∀ ys : List J,
    RatPolyCoeffEqv (polyMul p (finitePolySum g ys))
      (finitePolySum (fun j => polyMul p (g j)) ys)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | j::ys => (RatPolyCoeffEqv.mul_add_right p (g j) _).trans
      ((RatPolyCoeffEqv.refl _).add (mul_fold_right p g ys))

private theorem mul_fold_left {I : Type} (f : I → RatPoly) (xs : List I) (q : RatPoly) :
    RatPolyCoeffEqv (polyMul (finitePolySum f xs) q)
      (finitePolySum (fun i => polyMul (f i) q) xs) :=
  (RatPolyCoeffEqv.mul_comm _ q).trans ((mul_fold_right q f xs).trans
    (finitePolySum_coeff_congr _ _ (fun i => RatPolyCoeffEqv.mul_comm q (f i)) xs))

/-- Multiplication has the SAME ordered pair-fold convention as Gamma. -/
theorem finitePolySum_mul_pair {I J : Type}
    (f : I → RatPoly) (g : J → RatPoly) (xs : List I) (ys : List J) :
    RatPolyCoeffEqv (polyMul (finitePolySum f xs) (finitePolySum g ys))
      (finitePolySum (fun i => finitePolySum (fun j => polyMul (f i) (g j)) ys) xs) :=
  (mul_fold_left f xs _).trans (finitePolySum_coeff_congr _ _
    (fun i => mul_fold_right (f i) g ys) xs)

private theorem casimir_zero (active : List Nat) :
    RatPolyCoeffEqv (activeCasimirPolynomial active polyZero) polyZero := by
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b rest ih =>
      exact ((RatPolyCoeffEqv.neg
        (blockAngularLaplacian_independent_zero b polyZero
          (quaternionBlockIndependent_polyZero b))).add ih).trans
        (RatPolyCoeffEqv.add_zero polyZero)

/-- The original active Casimir commutes with every ordered finite fold. -/
theorem activeCasimir_finitePolySum {I : Type}
    (active : List Nat) (f : I → RatPoly) : ∀ xs : List I,
    RatPolyCoeffEqv (activeCasimirPolynomial active (finitePolySum f xs))
      (finitePolySum (fun i => activeCasimirPolynomial active (f i)) xs)
  | [] => casimir_zero active
  | i::xs => (activeCasimir_add active (f i) _).trans
      ((RatPolyCoeffEqv.refl _).add (activeCasimir_finitePolySum active f xs))

end YMGap.Continuum.QuaternionHaarGammaFiniteSum

#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_congr
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_add_right
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_add_left
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_smul_pair
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.finitePolySum_coeff_congr
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.finitePolySum_add
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.finitePolySum_smul
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_finitePolySum_right
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_finitePolySum_left
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeGamma_finitePolySum_pair
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.finitePolySum_mul_pair
#print axioms YMGap.Continuum.QuaternionHaarGammaFiniteSum.activeCasimir_finitePolySum
