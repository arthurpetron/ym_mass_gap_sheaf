/-
# Polynomial spectral moments equal ACTUAL original probe-vector norms

The original time composition/symmetry and bilinearity identify
<p(T2)v,q(T2)v> with the constructed functional on pq. Its sup-norm
bound therefore controls the ACTUAL cyclic polynomial vectors, not
coordinates of a supplied diagonal model. All nome/spacing parameters
remain fixed. No full spectral calculus or continuum conclusion.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)

local notation "B" => completedInner
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem combineRC_product (f : Nat → RC) (p q : QPoly.Poly) (r : Nat) :
    combineRC f (QPoly.pmul p q) r=combineRC (fun j => combineRC f q j) p r := by
  induction p generalizing r with
  | nil => rfl
  | cons c p ih =>
      rw [QPoly.pmul,combineRC_add,combineRC_scale]
      simp only [combineRC,scale_zero,rc_zero_add,ih]

theorem inner_vector_left (x y : Completion) (p : QPoly.Poly) (r : Nat) :
    B (polynomialVector x p r) y=combineRC (fun j => B (completedTime (j+j) x) y) p r := by
  induction p generalizing r with
  | nil => exact completedInner_zero_left y
  | cons c p ih =>
      rw [polynomialVector,completedInner_add_left,completedInner_smul_left,ih]
      rfl

theorem inner_orbit_vector (x : Completion) (r : Nat) (q : QPoly.Poly) (s : Nat) :
    B (completedTime (r+r) x) (polynomialVector x q s)=
      combineRC (fun j => B x (completedTime (j+j) x)) q (r+s) := by
  induction q generalizing s with
  | nil => exact completedInner_zero_right _
  | cons c q ih =>
      rw [polynomialVector,completedInner_add_right,completedInner_smul_right,
        completedTime_symmetric,completedTime_comp,ih]
      rw [show (s+s)+(r+r)=(r+s)+(r+s) by omega,
        show r+(s+1)=(r+s)+1 by omega]
      rfl

theorem inner_vector_product (x : Completion) (p q : QPoly.Poly) :
    B (polynomialVector x p 0) (polynomialVector x q 0)=
      combineRC (fun j => B x (completedTime (j+j) x)) (QPoly.pmul p q) 0 := by
  rw [inner_vector_left]
  simp only [inner_orbit_vector,Nat.add_zero]
  exact (combineRC_product _ p q 0).symm

/-- The scalar functional and both vectors refer to the SAME original T2. -/
theorem probe_inner_product (p q : QPoly.Poly) :
    B (polynomialVector unitProbe.val p 0) (polynomialVector unitProbe.val q 0)=
      momentFunctional (QPoly.pmul p q) := by
  rw [inner_vector_product]
  unfold momentFunctional limitAt
  rw [combine_pin]
  have h : (fun j => B unitProbe.val (completedTime (j+j) unitProbe.val))=
      (fun j => Quotient.mk crealSetoid (limitRepresentative j)) := by
    funext j
    exact (limitMoment_pin j).symm
  rw [h]

theorem probe_norm_square (p : QPoly.Poly) :
    B (polynomialVector unitProbe.val p 0) (polynomialVector unitProbe.val p 0)=
      momentFunctional (QPoly.pmul p p) := probe_inner_product p p

/-- Uniform in polynomial degree: the actual cyclic vector has norm <= M. -/
theorem probe_norm_bound (p : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (B (polynomialVector unitProbe.val p 0) (polynomialVector unitProbe.val p 0)) (rat (M*M)) := by
  rw [probe_norm_square]
  apply functional_upper
  intro t ht h1
  have hu := Q'.le_trans' _ _ _ (Q'.le_abs_self _) (h t ht h1)
  have hl := Q'.le_trans' _ _ _ (Q'.neg_le_neg (h t ht h1)) (ExpNeg.neg_abs_le _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.eval_pmul p p t))
    (Q'.mul_le_of_bounds hM hM hl hu hl hu)

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.combineRC_product
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.inner_vector_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.inner_orbit_vector
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.inner_vector_product
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.probe_inner_product
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.probe_norm_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm.probe_norm_bound
