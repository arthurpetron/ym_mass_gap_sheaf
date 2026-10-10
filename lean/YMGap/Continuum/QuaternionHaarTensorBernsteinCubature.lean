/-
Finite tensor Bernstein data on the ACTUAL one-quaternion polynomial Haar carrier.
All four coordinates remain in the same Haar functional; no product of
independent marginals is used.  The grid is a polynomial cubature input, not
an extension to continuous functions or a sphere-supremum assertion.
-/

import YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
import YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.BinomialTheorem

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinCubature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinRationalPositiveRow
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarBernsteinRowCertificate
open YMGap.Continuum.BinomialTheorem

local infix:50 " ≈ " => Q'.eqv

/-- A positive Bernstein degree, `N=n+1`. -/
def degree (n : Nat) : Nat := n+1

/-- Actual shifted quaternion coordinate `(1+x_i)/2`. -/
def shiftedCoordinate (i : Fin 4) : RatPoly := unitArgument (polyVar i.val)

private def shiftedCertificate (i : Fin 4) :
    Certificate 1 (shiftedCoordinate i) :=
  unitArgument_certificate (coordinateSquareBound 1 i.val (by omega))

private def complementaryCertificate (i : Fin 4) :
    Certificate 1 (subst (shiftedCoordinate i) oneMinusVar) :=
  oneMinusUnitArgument_certificate (coordinateSquareBound 1 i.val (by omega))

private abbrev anchorPpow :=
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.ppow
private abbrev anchorPvar :=
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar

private theorem subst_pvar (y : RatPoly) :
    RatPolyCoeffEqv (subst y anchorPvar) y := by
  unfold anchorPvar YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pvar
  exact (subst_zero_cons y [1]).trans
    (((subst_singleton y 1).mul_left y).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 1 y polyOne).trans
        ((RatPolyCoeffEqv.one_smul (polyMul y polyOne)).trans
          (RatPolyCoeffEqv.mul_one y))))

private def powerCertificate {p : Poly} {y : RatPoly}
    (P : Certificate 1 (subst y p)) :
    (k : Nat) → Certificate 1 (subst y (anchorPpow p k))
  | 0 => by
      change Certificate 1 (subst y [1])
      exact .ofCoeff ((subst_singleton y 1).trans
        (RatPolyCoeffEqv.one_smul polyOne)) (.one 1)
  | k+1 => by
      change Certificate 1 (subst y (pmul p (anchorPpow p k)))
      exact .ofCoeff (subst_pmul y p (anchorPpow p k))
        (.mul P (powerCertificate P k))

private def basisCertificate (n : Nat) (i : Fin 4) (k : Nat) :
    Certificate 1 (subst (shiftedCoordinate i)
      (bernsteinBasisPoly (degree n) k)) := by
  let y := shiftedCoordinate i
  let left : Certificate 1 (subst y (anchorPpow anchorPvar k)) :=
    powerCertificate (.ofCoeff (subst_pvar y) (shiftedCertificate i)) k
  let right : Certificate 1
      (subst y (anchorPpow oneMinusVar (degree n-k))) :=
    powerCertificate (complementaryCertificate i) (degree n-k)
  exact .ofCoeff
    (subst_pmul y (anchorPpow anchorPvar k)
      (anchorPpow oneMinusVar (degree n-k))) (.mul left right)

/-- One actual binomial-weighted polynomial Bernstein factor. -/
def coordinateBasis (n : Nat) (i : Fin 4) (k : Nat) : RatPoly :=
  subst (shiftedCoordinate i)
    (pscale (Q'.ofNat (YMGap.RG.binom (degree n) k))
      (bernsteinBasisPoly (degree n) k))

/-- Positive on the original, single-block Haar carrier, not on a surrogate law. -/
def coordinateBasisCertificate (n : Nat) (i : Fin 4) (k : Nat) :
    Certificate 1 (coordinateBasis n i k) := by
  unfold coordinateBasis
  exact .ofCoeff
    (subst_pscale (shiftedCoordinate i)
      (Q'.ofNat (YMGap.RG.binom (degree n) k))
      (bernsteinBasisPoly (degree n) k))
    (.smul _ (YMGap.RG.ofNat_nonneg _)
      (basisCertificate n i k))

/-- Four explicit grid indices, each in `0,...,N`, where `N=n+1`. -/
structure GridIndex (n : Nat) : Type where
  k0 : Fin (n+2)
  k1 : Fin (n+2)
  k2 : Fin (n+2)
  k3 : Fin (n+2)

/-- The same joint term with raw indices, useful under four explicit sums. -/
def jointBasisRaw (n k0 k1 k2 k3 : Nat) : RatPoly :=
  polyMul (coordinateBasis n ⟨0, by decide⟩ k0)
    (polyMul (coordinateBasis n ⟨1, by decide⟩ k1)
      (polyMul (coordinateBasis n ⟨2, by decide⟩ k2)
        (coordinateBasis n ⟨3, by decide⟩ k3)))

/-- Joint basis term on the same four-coordinate quaternion block. -/
def jointBasis (n : Nat) (k : GridIndex n) : RatPoly :=
  jointBasisRaw n k.k0.val k.k1.val k.k2.val k.k3.val

def jointBasisCertificate (n : Nat) (k : GridIndex n) :
    Certificate 1 (jointBasis n k) :=
  .mul (coordinateBasisCertificate n ⟨0, by decide⟩ k.k0.val)
    (.mul (coordinateBasisCertificate n ⟨1, by decide⟩ k.k1.val)
      (.mul (coordinateBasisCertificate n ⟨2, by decide⟩ k.k2.val)
        (coordinateBasisCertificate n ⟨3, by decide⟩ k.k3.val)))

/-- A computable rational joint weight, with all four factors under ONE Haar. -/
def jointWeight (n : Nat) (k : GridIndex n) : Q' :=
  quaternionHaar 1 (jointBasis n k)

def jointWeightRaw (n k0 k1 k2 k3 : Nat) : Q' :=
  quaternionHaar 1 (jointBasisRaw n k0 k1 k2 k3)

theorem jointWeight_nonnegative (n : Nat) (k : GridIndex n) :
    (0 : Q') ≤ jointWeight n k :=
  (jointBasisCertificate n k).haar_nonnegative

theorem jointWeightRaw_nonnegative (n k0 k1 k2 k3 : Nat) :
    (0 : Q') ≤ jointWeightRaw n k0 k1 k2 k3 := by
  unfold jointWeightRaw jointBasisRaw
  exact (Certificate.mul (coordinateBasisCertificate n ⟨0, by decide⟩ k0)
    (Certificate.mul (coordinateBasisCertificate n ⟨1, by decide⟩ k1)
      (Certificate.mul (coordinateBasisCertificate n ⟨2, by decide⟩ k2)
        (coordinateBasisCertificate n ⟨3, by decide⟩ k3)))).haar_nonnegative

/-- Finite polynomial sum, intentionally retaining the literal summands. -/
def ratFinSum (f : Nat → RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | m+1 => polyAdd (ratFinSum f m) (f m)

private theorem ratFinSum_congr (f g : Nat → RatPoly)
    (h : ∀ k, RatPolyCoeffEqv (f k) (g k)) :
    ∀ count, RatPolyCoeffEqv (ratFinSum f count) (ratFinSum g count)
  | 0 => RatPolyCoeffEqv.refl polyZero
  | count+1 => (ratFinSum_congr f g h count).add (h count)

private theorem ratFinSum_mul_left (factor : RatPoly) (f : Nat → RatPoly) :
    ∀ count, RatPolyCoeffEqv
      (polyMul factor (ratFinSum f count))
      (ratFinSum (fun k => polyMul factor (f k)) count)
  | 0 => RatPolyCoeffEqv.mul_zero_right factor
  | count+1 => by
      change RatPolyCoeffEqv
        (polyMul factor (polyAdd (ratFinSum f count) (f count)))
        (polyAdd (ratFinSum (fun k => polyMul factor (f k)) count)
          (polyMul factor (f count)))
      exact (RatPolyCoeffEqv.mul_add_right factor _ _).trans
        ((ratFinSum_mul_left factor f count).add (RatPolyCoeffEqv.refl _))

private theorem ratFinSum_mul_right (f : Nat → RatPoly) (factor : RatPoly) :
    ∀ count, RatPolyCoeffEqv
      (polyMul (ratFinSum f count) factor)
      (ratFinSum (fun k => polyMul (f k) factor) count)
  | 0 => RatPolyCoeffEqv.mul_zero_left factor
  | count+1 => by
      change RatPolyCoeffEqv
        (polyMul (polyAdd (ratFinSum f count) (f count)) factor)
        (polyAdd (ratFinSum (fun k => polyMul (f k) factor) count)
          (polyMul (f count) factor))
      rw [polyMul_add_left_exact]
      exact (ratFinSum_mul_right f factor count).add (RatPolyCoeffEqv.refl _)

private theorem ratFinSum_haar (f : Nat → RatPoly) : ∀ count,
    quaternionHaar 1 (ratFinSum f count) ≈
      finSum (fun k => quaternionHaar 1 (f k)) count
  | 0 => Q'.eqv_refl 0
  | count+1 => by
      change quaternionHaar 1 (polyAdd (ratFinSum f count) (f count)) ≈
        finSum (fun k => quaternionHaar 1 (f k)) count +
          quaternionHaar 1 (f count)
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (Q'.add_eqv_congr_right _ _ _ (ratFinSum_haar f count))

private theorem subst_polyFinSum (y : RatPoly) (f : Nat → Poly) :
    ∀ count, RatPolyCoeffEqv
      (subst y (QuaternionHaarBernsteinRowCertificate.polyFinSum f count))
      (ratFinSum (fun k => subst y (f k)) count)
  | 0 => RatPolyCoeffEqv.refl polyZero
  | count+1 => (subst_padd y _ _).trans
      ((subst_polyFinSum y f count).add (RatPolyCoeffEqv.refl _))

/-- The full one-coordinate binomial row on the actual Haar carrier. -/
def coordinatePartition (n : Nat) (i : Fin 4) : RatPoly :=
  subst (shiftedCoordinate i)
    (bernsteinRowPoly (degree n)
      (fun k => Q'.ofNat (YMGap.RG.binom (degree n) k)))

private theorem coordinatePartition_eq_sum (n : Nat) (i : Fin 4) :
    RatPolyCoeffEqv (coordinatePartition n i)
      (ratFinSum (fun k => coordinateBasis n i k) (n+2)) := by
  unfold coordinatePartition bernsteinRowPoly coordinateBasis
  exact subst_polyFinSum (shiftedCoordinate i)
    (fun k => pscale (Q'.ofNat (YMGap.RG.binom (degree n) k))
      (bernsteinBasisPoly (degree n) k)) (n+2)

theorem coordinatePartition_one (n : Nat) (i : Fin 4) :
    RatPolyCoeffEqv (coordinatePartition n i) polyOne := by
  have hpoly : PolyEqv
      (bernsteinRowPoly (degree n)
        (fun k => Q'.ofNat (YMGap.RG.binom (degree n) k))) [1] := by
    intro x
    exact Q'.eqv_trans _ _ _
      (bernsteinRowPoly_eval (degree n)
        (fun k => Q'.ofNat (YMGap.RG.binom (degree n) k)) x)
      (Q'.eqv_trans _ _ _
        (partition_of_unity (degree n) x)
        (by
          change (1 : Q') ≈ 1 + x * 0
          exact Q'.eqv_symm (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_zero_eqv x))
            (QPoly.q_add_zero_eqv 1))))
  unfold coordinatePartition
  exact (subst_polyEqv (shiftedCoordinate i) hpoly).trans
    ((subst_singleton (shiftedCoordinate i) 1).trans
      (RatPolyCoeffEqv.one_smul polyOne))

private def basis0 (n k : Nat) : RatPoly :=
  coordinateBasis n ⟨0, by decide⟩ k
private def basis1 (n k : Nat) : RatPoly :=
  coordinateBasis n ⟨1, by decide⟩ k
private def basis2 (n k : Nat) : RatPoly :=
  coordinateBasis n ⟨2, by decide⟩ k
private def basis3 (n k : Nat) : RatPoly :=
  coordinateBasis n ⟨3, by decide⟩ k

private def tail2 (n : Nat) : RatPoly :=
  ratFinSum (fun k2 =>
    ratFinSum (fun k3 => polyMul (basis2 n k2) (basis3 n k3)) (n+2)) (n+2)

private def tail1 (n : Nat) : RatPoly :=
  ratFinSum (fun k1 =>
    ratFinSum (fun k2 =>
      ratFinSum (fun k3 =>
        polyMul (basis1 n k1)
          (polyMul (basis2 n k2) (basis3 n k3))) (n+2)) (n+2)) (n+2)

/-- The literal four-fold finite polynomial sum of the joint basis. -/
def jointPolynomial (n : Nat) : RatPoly :=
  ratFinSum (fun k0 =>
    ratFinSum (fun k1 =>
      ratFinSum (fun k2 =>
        ratFinSum (fun k3 => jointBasisRaw n k0 k1 k2 k3)
          (n+2)) (n+2)) (n+2)) (n+2)

private theorem tail2_eq_partitions (n : Nat) :
    RatPolyCoeffEqv
      (polyMul (coordinatePartition n ⟨2, by decide⟩)
        (coordinatePartition n ⟨3, by decide⟩))
      (tail2 n) := by
  have h2 := coordinatePartition_eq_sum n ⟨2, by decide⟩
  have h3 := coordinatePartition_eq_sum n ⟨3, by decide⟩
  exact (h2.mul h3).trans
    ((ratFinSum_mul_right (basis2 n)
      (ratFinSum (basis3 n) (n+2)) (n+2)).trans
      (ratFinSum_congr _ _ (fun k2 =>
        ratFinSum_mul_left (basis2 n k2) (basis3 n) (n+2)) (n+2)))

private theorem tail1_eq_partitions (n : Nat) :
    RatPolyCoeffEqv
      (polyMul (coordinatePartition n ⟨1, by decide⟩)
        (polyMul (coordinatePartition n ⟨2, by decide⟩)
          (coordinatePartition n ⟨3, by decide⟩)))
      (tail1 n) := by
  have h1 := coordinatePartition_eq_sum n ⟨1, by decide⟩
  have ht := tail2_eq_partitions n
  have hexpand (k1 : Nat) :
      RatPolyCoeffEqv (polyMul (basis1 n k1) (tail2 n))
        (ratFinSum (fun k2 => ratFinSum (fun k3 =>
          polyMul (basis1 n k1)
            (polyMul (basis2 n k2) (basis3 n k3))) (n+2)) (n+2)) := by
    unfold tail2
    exact (ratFinSum_mul_left (basis1 n k1) _ (n+2)).trans
      (ratFinSum_congr _ _ (fun k2 =>
        ratFinSum_mul_left (basis1 n k1) _ (n+2)) (n+2))
  exact ((h1.mul ht).trans
    (ratFinSum_mul_right (basis1 n) (tail2 n) (n+2))).trans
    (ratFinSum_congr _ _ hexpand (n+2))

theorem jointPolynomial_eq_partitions (n : Nat) :
    RatPolyCoeffEqv
      (polyMul (coordinatePartition n ⟨0, by decide⟩)
        (polyMul (coordinatePartition n ⟨1, by decide⟩)
          (polyMul (coordinatePartition n ⟨2, by decide⟩)
            (coordinatePartition n ⟨3, by decide⟩))))
      (jointPolynomial n) := by
  have h0 := coordinatePartition_eq_sum n ⟨0, by decide⟩
  have ht := tail1_eq_partitions n
  have hexpand (k0 : Nat) :
      RatPolyCoeffEqv (polyMul (basis0 n k0) (tail1 n))
        (ratFinSum (fun k1 =>
          ratFinSum (fun k2 =>
            ratFinSum (fun k3 => jointBasisRaw n k0 k1 k2 k3)
              (n+2)) (n+2)) (n+2)) := by
    unfold tail1 jointBasisRaw
    exact (ratFinSum_mul_left (basis0 n k0) _ (n+2)).trans
      (ratFinSum_congr _ _ (fun k1 =>
        (ratFinSum_mul_left (basis0 n k0) _ (n+2)).trans
          (ratFinSum_congr _ _ (fun k2 =>
            ratFinSum_mul_left (basis0 n k0) _ (n+2)) (n+2))) (n+2))
  exact ((h0.mul ht).trans
    (ratFinSum_mul_right (basis0 n) (tail1 n) (n+2))).trans
    (ratFinSum_congr _ _ hexpand (n+2))

/-- The literal sum of all `(N+1)^4` joint weights. -/
def jointMass (n : Nat) : Q' :=
  finSum (fun k0 => finSum (fun k1 => finSum (fun k2 =>
    finSum (fun k3 => jointWeightRaw n k0 k1 k2 k3) (n+2))
    (n+2)) (n+2)) (n+2)

theorem jointPolynomial_haar_eq_mass (n : Nat) :
    quaternionHaar 1 (jointPolynomial n) ≈ jointMass n := by
  unfold jointPolynomial jointMass
  exact Q'.eqv_trans _ _ _ (ratFinSum_haar _ (n+2))
    (finSum_eqv_congr _ _ (fun k0 =>
      Q'.eqv_trans _ _ _ (ratFinSum_haar _ (n+2))
        (finSum_eqv_congr _ _ (fun k1 =>
          Q'.eqv_trans _ _ _ (ratFinSum_haar _ (n+2))
            (finSum_eqv_congr _ _ (fun k2 =>
              ratFinSum_haar _ (n+2)) (n+2))) (n+2))) (n+2))

/-- The actual joint cubature weights have unit total mass. -/
theorem jointMass_one (n : Nat) : jointMass n ≈ 1 := by
  have hrow := jointPolynomial_eq_partitions n
  have hones : RatPolyCoeffEqv
      (polyMul (coordinatePartition n ⟨0, by decide⟩)
        (polyMul (coordinatePartition n ⟨1, by decide⟩)
          (polyMul (coordinatePartition n ⟨2, by decide⟩)
            (coordinatePartition n ⟨3, by decide⟩)))) polyOne := by
    exact ((coordinatePartition_one n ⟨0, by decide⟩).mul
      ((coordinatePartition_one n ⟨1, by decide⟩).mul
        ((coordinatePartition_one n ⟨2, by decide⟩).mul
          (coordinatePartition_one n ⟨3, by decide⟩)))).trans
      ((RatPolyCoeffEqv.one_mul _).trans
        ((RatPolyCoeffEqv.one_mul _).trans
          (RatPolyCoeffEqv.one_mul _)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (jointPolynomial_haar_eq_mass n))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hrow.symm.trans hones))
      (by decide +kernel : quaternionHaar 1 polyOne ≈ 1))

/-- The elevated coefficient row for an actual univariate `QPoly`. -/
def elevatedRow (n : Nat) (p : Poly) (i : Fin 4) : RatPoly :=
  subst (shiftedCoordinate i)
    (bernsteinRowPoly (degree n) (unnormalizedRow p n))

/-- Exact rational reconstruction of each elevated row, with a guard computed
from the actual coefficient list rather than supplied as analytic input. -/
theorem elevatedRow_reconstruction (n : Nat) (p : Poly) (i : Fin 4)
    (hdegree : p.length ≤ n+1) :
    RatPolyCoeffEqv (elevatedRow n p i) (subst (shiftedCoordinate i) p) := by
  unfold elevatedRow
  apply subst_polyEqv (shiftedCoordinate i)
  intro x
  exact Q'.eqv_trans _ _ _
    (bernsteinRowPoly_eval (degree n) (unnormalizedRow p n) x)
    (unnormalizedRow_reconstruction p n hdegree x)

/-- Four actual `QPoly` factors, all at the same finite Bernstein degree. -/
def jointElevatedRow (n : Nat) (p0 p1 p2 p3 : Poly) : RatPoly :=
  polyMul (elevatedRow n p0 ⟨0, by decide⟩)
    (polyMul (elevatedRow n p1 ⟨1, by decide⟩)
      (polyMul (elevatedRow n p2 ⟨2, by decide⟩)
        (elevatedRow n p3 ⟨3, by decide⟩)))

/-- Exact four-factor reconstruction, with no factorization of Haar. -/
theorem jointElevatedRow_reconstruction (n : Nat) (p0 p1 p2 p3 : Poly)
    (h0 : p0.length ≤ n+1) (h1 : p1.length ≤ n+1)
    (h2 : p2.length ≤ n+1) (h3 : p3.length ≤ n+1) :
    RatPolyCoeffEqv (jointElevatedRow n p0 p1 p2 p3)
      (polyMul (subst (shiftedCoordinate ⟨0, by decide⟩) p0)
        (polyMul (subst (shiftedCoordinate ⟨1, by decide⟩) p1)
          (polyMul (subst (shiftedCoordinate ⟨2, by decide⟩) p2)
            (subst (shiftedCoordinate ⟨3, by decide⟩) p3)))) :=
  (elevatedRow_reconstruction n p0 ⟨0, by decide⟩ h0).mul
    ((elevatedRow_reconstruction n p1 ⟨1, by decide⟩ h1).mul
      ((elevatedRow_reconstruction n p2 ⟨2, by decide⟩ h2).mul
        (elevatedRow_reconstruction n p3 ⟨3, by decide⟩ h3)))

/-- A single computable cutoff that accommodates all four actual lists. -/
def jointCutoff (p0 p1 p2 p3 : Poly) : Nat :=
  max (max p0.length p1.length) (max p2.length p3.length)

theorem jointElevatedRow_reconstruction_auto (p0 p1 p2 p3 : Poly) :
    RatPolyCoeffEqv
      (jointElevatedRow (jointCutoff p0 p1 p2 p3) p0 p1 p2 p3)
      (polyMul (subst (shiftedCoordinate ⟨0, by decide⟩) p0)
        (polyMul (subst (shiftedCoordinate ⟨1, by decide⟩) p1)
          (polyMul (subst (shiftedCoordinate ⟨2, by decide⟩) p2)
            (subst (shiftedCoordinate ⟨3, by decide⟩) p3)))) := by
  apply jointElevatedRow_reconstruction
  all_goals unfold jointCutoff; omega

end YMGap.Continuum.QuaternionHaarTensorBernsteinCubature

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.degree
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.shiftedCoordinate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.coordinateBasis
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.coordinateBasisCertificate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.GridIndex
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointBasisRaw
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointBasis
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointBasisCertificate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointWeight
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointWeightRaw
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointWeight_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointWeightRaw_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.ratFinSum
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.coordinatePartition
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.coordinatePartition_one
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointPolynomial
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointPolynomial_eq_partitions
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointMass
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointPolynomial_haar_eq_mass
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointMass_one
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.elevatedRow
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.elevatedRow_reconstruction
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointElevatedRow
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointElevatedRow_reconstruction
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointCutoff
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinCubature.jointElevatedRow_reconstruction_auto
