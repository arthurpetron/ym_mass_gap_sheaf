/-
# The actual inserted SU(2) heat retains one explicit activity factor

The constant character cancels from the ORIGINAL partition-cleared
covariance response. Strip w^3 from every positive-spin heat term using
natural subtraction of its Casimir exponent, without division by w.
The actual response and every positional Mobius coefficient then retain
this same factor. The signed cofactor keeps both its linear third-moment
term and its quadratic correction; neither is discarded.

These are finite identities for arbitrary rational w, including zero.
No bound on the cofactor, spatial decay, or physical gap is asserted.
The original old/new partition denominator is not changed.
-/

import YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
import YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
import YMGap.Continuum.SU2FiniteHeatPowerFactorization
import YMGap.Continuum.FiniteSelectionMobiusFactorization
import YMGap.Continuum.RationalConnectedResponsePerturbation

namespace YMGap.Continuum.BF4ExactSlabResponseInsertionActivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionMobiusFactorization
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- Explicit residual heat polynomial; there is no inverse nome. -/
def strippedHeat (w : Q') (K extent id : Nat) : RatPoly :=
  finitePolySum (fun i => polySmul
    (dimQ (1+i) * qpow w (c4 (1+i)-3))
    (characterPolynomial (faceScalar extent id) (1+i))) (List.range K)

private theorem sum_factor {A : Type} (f g : A → RatPoly) (t : Q')
    (h : ∀ a, RatPolyCoeffEqv (f a) (polySmul t (g a))) : ∀ xs : List A,
    RatPolyCoeffEqv (finitePolySum f xs) (polySmul t (finitePolySum g xs))
  | [] => (RatPolyCoeffEqv.smul_zero t).symm
  | a::xs => ((h a).add (sum_factor f g t h xs)).trans
      (RatPolyCoeffEqv.smul_add t (g a) (finitePolySum g xs)).symm

/-- The actual heat prefix is one plus w^3 times the displayed polynomial. -/
theorem faceHeat_affine (w : Q') (K extent id : Nat) :
    RatPolyCoeffEqv (faceHeatPolynomial w K extent id)
      (polyAdd polyOne (polySmul (qpow w 3) (strippedHeat w K extent id))) := by
  refine (faceHeat_eq_one_add w extent id K).trans ((RatPolyCoeffEqv.refl _).add ?_)
  apply sum_factor
  intro i
  exact (RatPolyCoeffEqv.smul_coefficient
    (extract_floor w (dimQ (1+i)) 3 (c4 (1+i)) (positive_casimir (by omega))) _).trans
      (RatPolyCoeffEqv.smul_assoc (qpow w 3) (dimQ (1+i)*qpow w (c4 (1+i)-3)) _).symm

private theorem numerator_add (w : Q') (K extent : Nat) (ids : List Nat) (p q : RatPoly) :
    numerator w (blocks extent) extent ids (polyAdd p q) K ≈
      numerator w (blocks extent) extent ids p K + numerator w (blocks extent) extent ids q K := by
  unfold numerator
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append _ _ _

private theorem numerator_smul (w : Q') (K extent : Nat) (ids : List Nat) (t : Q') (p : RatPoly) :
    numerator w (blocks extent) extent ids (polySmul t p) K ≈
      t * numerator w (blocks extent) extent ids p K :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right _ t _ p)
      (Q'.mul_eqv_congr_left t _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

private theorem numerator_affine (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (p r : RatPoly) (t : Q')
    (h : RatPolyCoeffEqv (faceHeatPolynomial w K extent id) (polyAdd polyOne (polySmul t r))) :
    numerator w (blocks extent) extent ids (polyMul p (faceHeatPolynomial w K extent id)) K ≈
      numerator w (blocks extent) extent ids p K +
        t*numerator w (blocks extent) extent ids (polyMul p r) K := by
  have hp := ((h.mul_left p).trans (RatPolyCoeffEqv.mul_add_right p _ _)).trans
    ((RatPolyCoeffEqv.mul_one p).add (RatPolyCoeffEqv.polyMul_smul_right t p r))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_right _))
    (Q'.eqv_trans _ _ _ (numerator_add w K extent ids p (polySmul t (polyMul p r)))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (numerator_smul w K extent ids t (polyMul p r))))

private theorem partition_affine (w : Q') (K extent : Nat) (ids : List Nat)
    (id : Nat) (r : RatPoly) (t : Q')
    (h : RatPolyCoeffEqv (faceHeatPolynomial w K extent id) (polyAdd polyOne (polySmul t r))) :
    numerator w (blocks extent) extent ids (faceHeatPolynomial w K extent id) K ≈
      heatProductHaar w (blocks extent) extent ids K +
        t*numerator w (blocks extent) extent ids r K :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (h.mul_right _))
    (Q'.eqv_trans _ _ _ (numerator_add w K extent ids polyOne (polySmul t r))
      (Q'.add_eqv_congr' (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
        (numerator_smul w K extent ids t r)))

/-- Signed cofactor using only moments of the SAME original old action. -/
def responseCofactor (w : Q') (K extent : Nat) (ids : List Nat)
    (p q r : RatPoly) (t : Q') : Q' :=
  let M := fun f => numerator w (blocks extent) extent ids f K
  RationalConnectedResponsePerturbation.cofactor
    (heatProductHaar w (blocks extent) extent ids K) (M p) (M q) (M r)
    (M (polyMul p q)) (M (polyMul p r)) (M (polyMul q r))
    (M (polyMul (polyMul p q) r)) t

/-- An affine pin for the actual inserted face gives its exact activity. -/
theorem response_affine (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat)
    (p q r : RatPoly) (t : Q')
    (h : RatPolyCoeffEqv (faceHeatPolynomial w K extent id) (polyAdd polyOne (polySmul t r))) :
    response w K extent ids id p q ≈ t*responseCofactor w K extent ids p q r t := by
  let M := fun f => numerator w (blocks extent) extent ids f K
  let Z := heatProductHaar w (blocks extent) extent ids K
  have hR := partition_affine w K extent ids id r t h
  have hnew : connectedNumerator w K extent (ids++[id]) p q ≈
      (M (polyMul p q)+t*M (polyMul (polyMul p q) r))*(Z+t*M r) +
        -((M p+t*M (polyMul p r))*(M q+t*M (polyMul q r))) :=
    Q'.eqv_trans _ _ _ (connected_append_face w K extent ids id p q)
      (Q'.add_eqv_congr'
        (qmul (numerator_affine w K extent ids id (polyMul p q) r t h) hR)
        (Q'.neg_eqv_congr _ _ (qmul (numerator_affine w K extent ids id p r t h)
          (numerator_affine w K extent ids id q r t h))))
  have hpartition := Q'.eqv_trans _ _ _ (partition_append_face w K extent ids id) hR
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_identity w K extent ids id p q)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul hnew (Q'.eqv_refl _))
    (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _) (qmul hpartition hpartition)))) ?_
  exact RationalConnectedResponsePerturbation.affine_response Z (M p) (M q) (M r)
    (M (polyMul p q)) (M (polyMul p r)) (M (polyMul q r))
    (M (polyMul (polyMul p q) r)) t

/-- Explicit cofactor after extracting the minimum positive SU(2) Casimir. -/
def insertionCofactor (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : RatPoly) : Q' :=
  responseCofactor w K extent ids p q (strippedHeat w K extent id) (qpow w 3)

theorem response_activity (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : RatPoly) :
    response w K extent ids id p q ≈ (qpow w 3)*insertionCofactor w K extent ids id p q :=
  response_affine w K extent ids id p q _ _ (faceHeat_affine w K extent id)

def insertionCoefficient (w : Q') (K extent id : Nat) (p q : RatPoly) (ids : List Nat) : Q' :=
  coefficient (fun ys => insertionCofactor w K extent ys id p q) ids

/-- Finite differences in OLD selected faces preserve the insertion activity. -/
theorem responseCoefficient_activity (w : Q') (K extent id : Nat) (p q : RatPoly) (ids : List Nat) :
    responseCoefficient w K extent id p q ids ≈
      (qpow w 3)*insertionCoefficient w K extent id p q ids :=
  Q'.eqv_trans _ _ _ (coefficient_congr _ _ ids (fun ys _ => response_activity w K extent ys id p q))
    (coefficient_mul_left (qpow w 3) (fun ys => insertionCofactor w K extent ys id p q) ids)

end YMGap.Continuum.BF4ExactSlabResponseInsertionActivity

#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.strippedHeat
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.faceHeat_affine
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.responseCofactor
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.response_affine
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.insertionCofactor
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.response_activity
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.insertionCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionActivity.responseCoefficient_activity
