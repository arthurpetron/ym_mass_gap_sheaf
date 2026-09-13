/-
# A strict ORIGINAL shared-link Haar floor for finite Jacobi approximants

Substitute each actual ordered plaquette scalar into the nonnegative
coefficient Jacobi derivative in t=1+x. Its four-square certificate is
valid with arbitrary insertions, so all face factors may share links.
Retaining each constant coefficient gives c(w)^F below the original
normalized quaternion Haar integral, uniformly in N>=1 at fixed w and F.

These are finite Jacobi approximants, NOT the original unweighted heat
cutoffs. Their coefficient-level identification and quantified convergence
to the original interacting action remain open. No action-limit floor,
physical vacuum, spectral gap, or volume/spacing-uniform bound is claimed.
-/

import YMGap.Continuum.JacobiShiftedPositiveCoefficients
import YMGap.Continuum.QuaternionHaarUnitScalarSquare
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

namespace YMGap.Continuum.BF4ExactSlabJacobiHaarFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The actual plaquette word is retained, with all original link variables. -/
def faceApprox (w : Q') (N extent id : Nat) : RatPoly :=
  QPolyHaarPositiveSubstitution.subst
    (oneAddScalar (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)))
    (JacobiShiftedPositiveCoefficients.heat w N)

private theorem eval_arg {x y : Q'} (h : x ≈ y) : ∀ p : QPoly.Poly,
    QPoly.eval p x ≈ QPoly.eval p y
  | [] => Q'.eqv_refl 0
  | c :: p => Q'.add_eqv_congr_left c _ _
      (Cheb.mul_eqv_congr _ _ _ _ h (eval_arg h p))

/-- Evaluation is pinned to the existing normalized full Jacobi derivative. -/
theorem eval_faceApprox (w : Q') (N extent id : Nat) (rho : Nat → Q') :
    evalRatPoly rho (faceApprox w N extent id)
      ≈ SU2PointwiseHeatPositiveCompletion.inverseNome w *
        (HalfPow.half * JTPFullProductDerivativeNormalization.fullProdDx w
          (evalRatPoly rho (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar) N) := by
  have hshift : evalRatPoly rho
      (oneAddScalar (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)))
      ≈ 1 + evalRatPoly rho (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar :=
    Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr_right _ _ _ (evalRatPoly_one rho))
  exact Q'.eqv_trans _ _ _ (QPolyHaarPositiveSubstitution.eval_subst rho _ _)
    (Q'.eqv_trans _ _ _ (eval_arg hshift _)
      (JacobiShiftedPositiveCoefficients.eval_heat w _ N))

/-- Every physical face has a constructed ordinary Haar square certificate. -/
def face_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    Certificate (boundaryCompleteSlabLinks extent).length (faceApprox w N extent id) :=
  QPolyHaarPositiveSubstitution.certificate
    (slab_oneAddScalar_certificate (slabPlaquetteAt_mem hid)) _
    (JacobiShiftedPositiveCoefficients.heat_nonnegative hw0 hw1 N)

/-- Multiplication is within one Haar carrier; no independence premise. -/
def product_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) : (ids : List Nat) →
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    Certificate (boundaryCompleteSlabLinks extent).length
      (polynomialProduct (faceApprox w N extent) ids)
  | [], _ => .one _
  | id :: ids, hids => (face_certificate hw0 hw1 N (hids id List.mem_cons_self)).mul
      (product_certificate hw0 hw1 N extent ids (fun j hj => hids j (List.mem_cons_of_mem id hj)))

/-- Explicit nome- and face-count-dependent lower bound. -/
def productFloor (w : Q') (ids : List Nat) : Q' := SU2PointwiseHeatStrictFloor.floor w ^ ids.length

theorem productFloor_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (ids : List Nat) :
    (0 : Q') < productFloor w ids := HKPos.pow_pos (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1) _

/-- Strict integrated floor with every overlapping face retained. The
uniformity is only over N>=1; w, extent, and the face list remain explicit. -/
theorem productFloor_le_haar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) (hN : 1 ≤ N) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    productFloor w ids ≤ quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polynomialProduct (faceApprox w N extent) ids)
  | [], _ => Q'.ge_of_eqv (QPolyHaarPositiveSubstitution.haar_one _)
  | id :: ids, hids => by
      have htailIds := fun j hj => hids j (List.mem_cons_of_mem id hj)
      have Z := product_certificate hw0 hw1 N extent ids htailIds
      have htail := productFloor_le_haar hw0 hw1 N extent hN ids htailIds
      have hc := JacobiShiftedPositiveCoefficients.floor_le_heat_constant hw0 hw1 N hN
      have hretain := QPolyHaarPositiveSubstitution.eval_zero_mul_haar_le
        (slab_oneAddScalar_certificate (slabPlaquetteAt_mem (hids id List.mem_cons_self))) Z
        (JacobiShiftedPositiveCoefficients.heat w N)
        (JacobiShiftedPositiveCoefficients.heat_nonnegative hw0 hw1 N)
      exact Q'.le_trans' _ _ _
        (HKConv.mul_le_mul' (Q'.le_of_lt (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1))
          Z.haar_nonnegative hc htail)
        (Q'.le_trans' _ _ _ hretain
          (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- The complete finite slab's approximant has strictly positive Haar value. -/
theorem full_haar_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N extent : Nat) (hN : 1 ≤ N) :
    (0 : Q') < quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polynomialProduct (faceApprox w N extent) (slabPhysicalFaceEdges extent)) :=
  Q'.pos_of_lt_of_le (productFloor_pos hw0 hw1 _)
    (productFloor_le_haar hw0 hw1 N extent hN _ (fun _ h => h))

end YMGap.Continuum.BF4ExactSlabJacobiHaarFloor

#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.faceApprox
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.eval_faceApprox
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.face_certificate
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.product_certificate
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.productFloor
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.productFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.productFloor_le_haar
#print axioms YMGap.Continuum.BF4ExactSlabJacobiHaarFloor.full_haar_positive
