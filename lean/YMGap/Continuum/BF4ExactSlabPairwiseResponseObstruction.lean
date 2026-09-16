/-
# Vanishing pair responses do not remove an ORIGINAL third response

On any physical plaquette take the original cutoff-one heat factor at
w=1/8, and the same-plaquette character probes chi_2 and chi_3. Under the
empty selected action both probe/heat covariance numerators vanish.
Nevertheless the third connected numerator is 1/256, and inserting that
single original heat factor changes their covariance from zero to 1/256.
Both partitions are exactly one. The heat factor has an existing positive
square certificate, so this is not an example based on a signed fake law.

These are original gauge-invariant character polynomials, not auxiliary
quaternion coordinates. Their labels need not lie in a cutoff-one boundary
code carrier: the original moment API accepts arbitrary supported polynomial
observables. They occupy the SAME plaquette. No separated-probe, full-slab,
spatial-decay, OS-gap or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction
import YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels

namespace YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction (face_character_haar_zero tail_one)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

def nome : Q' := Q'.mkPos 1 8 (by decide)
def signal : Q' := Q'.mkPos 1 256 (by decide)

theorem signal_positive : (0 : Q') < signal := by decide

def leftProbe (extent id : Nat) : RatPoly := characterPolynomial (faceScalar extent id) 2
def rightProbe (extent id : Nat) : RatPoly := characterPolynomial (faceScalar extent id) 3
def insertion (extent id : Nat) : RatPoly := faceHeatPolynomial nome 1 extent id

theorem leftProbe_supported (extent id : Nat) :
    SupportedQuaternionBlocks (blocks extent) (leftProbe extent id) :=
  BF4ExactSlabAllExtentTemporalHaarForm.original_character_support extent (slabPlaquetteAt extent id) 2

theorem rightProbe_supported (extent id : Nat) :
    SupportedQuaternionBlocks (blocks extent) (rightProbe extent id) :=
  BF4ExactSlabAllExtentTemporalHaarForm.original_character_support extent (slabPlaquetteAt extent id) 3

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_one (n : Nat) : quaternionHaar n polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private def chiExpr : Nat → PolyExpr
  | 0 => .const 1
  | 1 => .mul (.const 2) (.var 0)
  | n+2 => .add (.mul (.mul (.const 2) (.var 0)) (chiExpr (n+1)))
      (.mul (.const (-1)) (chiExpr n))

private theorem chiExpr_pin (x : RatPoly) : ∀ n,
    RatPolyCoeffEqv (coeffEvalExpr (fun _ => x) (chiExpr n)) (characterPolynomial x n)
  | 0 => RatPolyCoeffEqv.one_smul _
  | 1 => cap_mul_left 2 x
  | n+2 => ((cap_mul_left 2 x).mul (chiExpr_pin x (n+1))).add
      (((chiExpr_pin x n).mul_left (cap (-1))).trans (cap_mul_left (-1) _))

private theorem probe_product_pin (x : RatPoly) :
    RatPolyCoeffEqv (polyMul (characterPolynomial x 2) (characterPolynomial x 3))
      (polyAdd (characterPolynomial x 5) (polyAdd (characterPolynomial x 3) (characterPolynomial x 1))) :=
  ((chiExpr_pin x 2).mul (chiExpr_pin x 3)).symm.trans
    ((coeffEvalExpr_eqv_of_normalize_eq (.mul (chiExpr 2) (chiExpr 3))
      (.add (chiExpr 5) (.add (chiExpr 3) (chiExpr 1))) (by decide) (fun _ => x)).trans
      ((chiExpr_pin x 5).add ((chiExpr_pin x 3).add (chiExpr_pin x 1))))

private theorem first_mul_succ (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul (characterPolynomial x 1) (characterPolynomial x (n+1)))
      (polyAdd (characterPolynomial x (n+2)) (characterPolynomial x n)) := by
  let a := polyMul (characterPolynomial x 1) (characterPolynomial x (n+1))
  let b := characterPolynomial x n
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i=0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (RatPolyCoeffEqv.refl b))

private theorem first_pair {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) (n : Nat) :
    quaternionHaar (blocks extent)
      (polyMul (characterPolynomial (faceScalar extent id) 1)
        (characterPolynomial (faceScalar extent id) (n+1))) ≈ (if n=0 then 1 else 0) := by
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (first_mul_succ (faceScalar extent id) n)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  cases n with
  | zero =>
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (face_character_haar_zero hi 2 (by decide)) (haar_one _)) (by decide)
  | succ n =>
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (face_character_haar_zero hi (n+1+2) (by omega))
        (face_character_haar_zero hi (n+1) (by omega)))
      (by simp only [Nat.succ_ne_zero, ↓reduceIte]; decide)

/-- The literal full cutoff-one factor, not a selected-spin replacement. -/
theorem insertion_pin (extent id : Nat) :
    RatPolyCoeffEqv (insertion extent id)
      (polyAdd polyOne (polySmul signal (characterPolynomial (faceScalar extent id) 1))) := by
  have h := faceHeat_eq_one_add nome extent id 1
  rw [tail_one] at h
  exact h.trans ((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.smul_coefficient (by decide : coeffW nome 1 ≈ signal) _))

/-- Existing constructive positivity applies to this actual original heat. -/
def insertionCertificate {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    Certificate (blocks extent) (insertion extent id) :=
  BF4ExactSlabSmallNomeHaarComparison.faceCertificate (w := nome)
    (by decide) (by decide) (by decide) (by decide) extent id hi 1

private theorem heat_moment (extent id : Nat) (p : RatPoly) :
    quaternionHaar (blocks extent) (polyMul p (insertion extent id)) ≈
      quaternionHaar (blocks extent) p + signal * quaternionHaar (blocks extent)
        (polyMul p (characterPolynomial (faceScalar extent id) 1)) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (((insertion_pin extent id).mul_left p).trans
      ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
        ((RatPolyCoeffEqv.mul_one p).add (RatPolyCoeffEqv.polyMul_smul_right _ _ _)))))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polySmul _ _ _)))

variable {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent)

local notation "H" => quaternionHaar (blocks extent)
local notation "p" => leftProbe extent id
local notation "q" => rightProbe extent id
local notation "r" => insertion extent id

include hi

theorem left_mean_zero : H p ≈ 0 := face_character_haar_zero hi 2 (by decide)
theorem right_mean_zero : H q ≈ 0 := face_character_haar_zero hi 3 (by decide)

theorem probe_pair_mean_zero : H (polyMul p q) ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (probe_product_pin (faceScalar extent id)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (face_character_haar_zero hi 5 (by decide))
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (right_mean_zero hi) (face_character_haar_zero hi 1 (by decide))))) (by decide)))

theorem insertion_mean_one : H r ≈ 1 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (insertion_pin extent id))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_one _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
          (Q'.mul_eqv_congr_left _ _ _ (face_character_haar_zero hi 1 (by decide))))) (by decide)))

theorem left_insertion_mean_zero : H (polyMul p r) ≈ 0 :=
  Q'.eqv_trans _ _ _ (heat_moment extent id p)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (left_mean_zero hi)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) (first_pair hi 1)))) (by decide))

theorem right_insertion_mean_zero : H (polyMul q r) ≈ 0 :=
  Q'.eqv_trans _ _ _ (heat_moment extent id q)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (right_mean_zero hi)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)) (first_pair hi 2)))) (by decide))

private theorem triple_character_mean_one :
    H (polyMul (polyMul p q) (characterPolynomial (faceScalar extent id) 1)) ≈ 1 := by
  let x := faceScalar extent id
  let c := characterPolynomial x 1
  have hc := (RatPolyCoeffEqv.mul_comm (polyMul p q) c).trans
    (((probe_product_pin x).mul_left c).trans
      ((RatPolyCoeffEqv.mul_add_right c (characterPolynomial x 5)
        (polyAdd (characterPolynomial x 3) c)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.mul_add_right c (characterPolynomial x 3) c))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (first_pair hi 4)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (first_pair hi 2) (first_pair hi 0)))) (by decide)))

theorem triple_insertion_mean : H (polyMul (polyMul p q) r) ≈ signal :=
  Q'.eqv_trans _ _ _ (heat_moment extent id (polyMul p q))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (probe_pair_mean_zero hi)
      (Q'.mul_eqv_congr_left _ _ _ (triple_character_mean_one hi))) (by decide))

omit hi

private theorem empty_moment (s : RatPoly) : numerator nome (blocks extent) extent [] s 1 ≈ H s :=
  haar_of_coeff (RatPolyCoeffEqv.mul_one s)

private theorem empty_partition : heatProductHaar nome (blocks extent) extent [] 1 ≈ 1 := haar_one _

include hi

theorem left_pair_response_zero : connectedNumerator nome 1 extent [] p r ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul (Q'.eqv_trans _ _ _ (empty_moment _) (left_insertion_mean_zero hi)) empty_partition)
    (Q'.neg_eqv_congr _ _ (qmul
      (Q'.eqv_trans _ _ _ (empty_moment _) (left_mean_zero hi))
      (Q'.eqv_trans _ _ _ (empty_moment _) (insertion_mean_one hi))))) (by decide)

theorem right_pair_response_zero : connectedNumerator nome 1 extent [] q r ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul (Q'.eqv_trans _ _ _ (empty_moment _) (right_insertion_mean_zero hi)) empty_partition)
    (Q'.neg_eqv_congr _ _ (qmul
      (Q'.eqv_trans _ _ _ (empty_moment _) (right_mean_zero hi))
      (Q'.eqv_trans _ _ _ (empty_moment _) (insertion_mean_one hi))))) (by decide)

theorem old_connected_zero : connectedNumerator nome 1 extent [] p q ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul (Q'.eqv_trans _ _ _ (empty_moment _) (probe_pair_mean_zero hi)) empty_partition)
    (Q'.neg_eqv_congr _ _ (qmul
      (Q'.eqv_trans _ _ _ (empty_moment _) (left_mean_zero hi))
      (Q'.eqv_trans _ _ _ (empty_moment _) (right_mean_zero hi))))) (by decide)

theorem singleton_partition : heatProductHaar nome (blocks extent) extent [id] 1 ≈ 1 :=
  Q'.eqv_trans _ _ _ (partition_append_face nome 1 extent [] id)
    (Q'.eqv_trans _ _ _ (empty_moment _) (insertion_mean_one hi))

theorem singleton_connected : connectedNumerator nome 1 extent [id] p q ≈ signal :=
  Q'.eqv_trans _ _ _ (connected_append_face nome 1 extent [] id p q)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (qmul (Q'.eqv_trans _ _ _ (empty_moment _) (triple_insertion_mean hi))
        (Q'.eqv_trans _ _ _ (empty_moment _) (insertion_mean_one hi)))
      (Q'.neg_eqv_congr _ _ (qmul
        (Q'.eqv_trans _ _ _ (empty_moment _) (left_insertion_mean_zero hi))
        (Q'.eqv_trans _ _ _ (empty_moment _) (right_insertion_mean_zero hi))))) (by decide))

theorem thirdNumerator_eq : thirdNumerator nome 1 extent [] p q r ≈ signal := by
  have hZ := @empty_partition extent
  have hp := Q'.eqv_trans _ _ _ (empty_moment p) (left_mean_zero hi)
  have hq := Q'.eqv_trans _ _ _ (empty_moment q) (right_mean_zero hi)
  have hr := Q'.eqv_trans _ _ _ (empty_moment r) (insertion_mean_one hi)
  have hpq := Q'.eqv_trans _ _ _ (empty_moment (polyMul p q)) (probe_pair_mean_zero hi)
  have hpr := Q'.eqv_trans _ _ _ (empty_moment (polyMul p r)) (left_insertion_mean_zero hi)
  have hqr := Q'.eqv_trans _ _ _ (empty_moment (polyMul q r)) (right_insertion_mean_zero hi)
  have hpqr := Q'.eqv_trans _ _ _ (empty_moment (polyMul (polyMul p q) r)) (triple_insertion_mean hi)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (qmul hpqr (qmul hZ hZ))
            (Q'.neg_eqv_congr _ _ (qmul (qmul hpq hr) hZ)))
          (Q'.neg_eqv_congr _ _ (qmul (qmul hpr hq) hZ)))
        (Q'.neg_eqv_congr _ _ (qmul (qmul hqr hp) hZ)))
      (qmul (qmul (qmul (Q'.eqv_refl 2) hp) hq) hr)) (by decide)

theorem response_eq : response nome 1 extent [] id p q ≈ signal :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul (Q'.eqv_trans _ _ _ (empty_moment r) (insertion_mean_one hi)) (thirdNumerator_eq hi))
    (Q'.neg_eqv_congr _ _ (qmul (left_pair_response_zero hi) (right_pair_response_zero hi)))) (by decide)

theorem response_ne_zero : ¬ response nome 1 extent [] id p q ≈ 0 := by
  intro hz
  exact (by decide : ¬ signal ≈ 0) (Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_eq hi)) hz)

theorem singleton_connected_ne_zero : ¬ connectedNumerator nome 1 extent [id] p q ≈ 0 := by
  intro hz
  exact (by decide : ¬ signal ≈ 0) (Q'.eqv_trans _ _ _ (Q'.eqv_symm (singleton_connected hi)) hz)

omit hi

/-- Reuse the existing literal physical plaquette; no large finite search. -/
theorem concrete_face_physical : 0 ∈ slabPhysicalFaceEdges 1 :=
  (mem_centralLowerFaceIds.mp BF4ExactSlabPlaquetteCoordinateChannels.probeId_lower).1

theorem concrete_response_ne_zero :
    ¬ response nome 1 1 [] 0 (leftProbe 1 0) (rightProbe 1 0) ≈ 0 :=
  response_ne_zero concrete_face_physical

end YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction

#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.nome
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.signal
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.signal_positive
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.leftProbe
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.rightProbe
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.insertion
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.leftProbe_supported
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.rightProbe_supported
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.insertion_pin
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.insertionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.left_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.right_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.probe_pair_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.insertion_mean_one
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.left_insertion_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.right_insertion_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.triple_insertion_mean
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.left_pair_response_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.right_pair_response_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.old_connected_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.singleton_partition
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.singleton_connected
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.thirdNumerator_eq
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.response_eq
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.response_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.singleton_connected_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.concrete_face_physical
#print axioms YMGap.Continuum.BF4ExactSlabPairwiseResponseObstruction.concrete_response_ne_zero
