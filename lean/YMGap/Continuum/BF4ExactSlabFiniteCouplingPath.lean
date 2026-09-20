/-
# A constructed two-nome path through original positive heat products

Change the actual factors one at a time. Every intermediate shared-link
background is certified positive, and both endpoint partitions are retained.
The normalized change costs at most the number of changed factors times
the proved one-face cap. There is no exponential partition-floor penalty.

The face-count factor is explicit: this is finite-volume control, not a
thermodynamic Lipschitz theorem. Its consumer is comparison of the EXISTING
cutoff-removed expectations at two nomes and finite-window localization.
-/
import YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability
import YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence

namespace YMGap.Continuum.BF4ExactSlabFiniteCouplingPath

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability (relativeVariation)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

theorem weightedMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hi : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent)
    {B : RatPoly} (HB : Certificate (blocks extent) B) (hB : (0 : Q') < quaternionHaar (blocks extent) B) :
    (0 : Q') < quaternionHaar (blocks extent) (polyMul B (polynomialProduct (faceHeatPolynomial w K extent) ids)) :=
  Q'.pos_of_lt_of_le (Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) ids.length) hB)
    (headProduct_weighted_floor hw0 hw1 K extent hK HB ids hi)

/-- An actual normalized moment, not an abstract expectation with new laws. -/
def weightedValue {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hi : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent)
    {B : RatPoly} (HB : Certificate (blocks extent) B) (hB : (0 : Q') < quaternionHaar (blocks extent) B)
    (p : RatPoly) : Q' :=
  normalizedMoment (blocks extent) (polyMul B (polynomialProduct (faceHeatPolynomial w K extent) ids)) p
    (weightedMass_positive hw0 hw1 K extent hK ids hi HB hB)

private theorem normalized_face_pin (w : Q') (K extent id : Nat) (B p : RatPoly)
    (h : (0 : Q') < faceMass w K extent id B) :
    normalizedMoment (blocks extent) (polyMul B (faceHeatPolynomial w K extent id)) p h ≈
      faceMoment w K extent id B p * Q'.recipPos (faceMass w K extent id B) h :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ p).trans (RatPolyCoeffEqv.mul_assoc p B _).symm))

private theorem shuffle (A B C : RatPoly) : RatPolyCoeffEqv
    (polyMul A (polyMul B C)) (polyMul (polyMul A C) B) :=
  coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide) (fun | 0 => A | 1 => B | _ => C)

private theorem weighted_nil {u v : Q'} (hu0 : (0 : Q') < u) (hu1 : u < (1 : Q'))
    (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) (K extent : Nat)
    (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    {B : RatPoly} (HB : Certificate (blocks extent) B) (hB : (0 : Q') < quaternionHaar (blocks extent) B)
    (p : RatPoly) :
    weightedValue hv0 hv1 K extent hKv [] (fun _ h => False.elim (List.not_mem_nil h)) HB hB p ≈
      weightedValue hu0 hu1 K extent hKu [] (fun _ h => False.elim (List.not_mem_nil h)) HB hB p :=
  Q'.eqv_refl _

private theorem abs_chain {a b c x y : Q'} (hab : Q'.abs (a + -b) ≤ x) (hbc : Q'.abs (b + -c) ≤ y) :
    Q'.abs (a + -c) ≤ x+y := by
  have ht : a + -c ≈ (a + -b)+(b + -c) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2)))) (by decide)
      (fun | 0 => a | 1 => b | _ => c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr ht))
    (Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _) (Q'.add_le_add hab hbc))

private theorem count_step (n : Nat) (b : Q') : b + Q'.ofNat n*b ≈ Q'.ofNat (n+1)*b := by
  have hs : Q'.ofNat (n+1) ≈ Q'.ofNat n+1 := Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
    (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.ofNat 1 ≈ (1 : Q')))
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1) (.var 0))) (.mul (.add (.var 1) (.const 1)) (.var 0))
    (by decide) (fun | 0 => b | _ => Q'.ofNat n)) (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hs))

/-- The finite path constructs all its intermediate densities. Only the
number of changed faces is lost; an arbitrary positive spectator remains. -/
theorem weighted_difference_bound {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v)
    (hvW : v ≤ W) (hW1 : W < (1 : Q')) (K extent : Nat)
    (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
    (ids : List Nat) (hi : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent)
    {B : RatPoly} (HB : Certificate (blocks extent) B) (hB : (0 : Q') < quaternionHaar (blocks extent) B)
    {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c) :
    let hv0 := Q'.pos_of_lt_of_le hu0 huv
    let hv1 := Q'.lt_of_le_of_lt hvW hW1
    let hu1 := Q'.lt_of_le_of_lt huv hv1
    Q'.abs (weightedValue hv0 hv1 K extent hKv ids hi HB hB p +
      -(weightedValue hu0 hu1 K extent hKu ids hi HB hB p)) ≤
      Q'.ofNat ids.length*(2*c*relativeVariation W u v) := by
  dsimp only
  let hv0 := Q'.pos_of_lt_of_le hu0 huv
  let hv1 := Q'.lt_of_le_of_lt hvW hW1
  let hu1 := Q'.lt_of_le_of_lt huv hv1
  induction ids generalizing B with
  | nil =>
      have hz := Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (weighted_nil hu0 hu1 hv0 hv1 K extent hKu hKv HB hB p))
        (Q'.add_neg_self_eqv _)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hz))
        (Q'.ge_of_eqv (Q'.zero_mul_eqv _))
  | cons id ids ih =>
      have hid := hi id List.mem_cons_self
      have ht : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent :=
        fun i hi' => hi i (List.mem_cons_of_mem id hi')
      let C := polyMul B (polynomialProduct (faceHeatPolynomial v K extent) ids)
      let HC := HB.mul (headProduct_certificate hv0 hv1 K extent hKv ids ht)
      have hC : (0 : Q') < quaternionHaar (blocks extent) C :=
        weightedMass_positive hv0 hv1 K extent hKv ids ht HB hB
      let A := polyMul B (faceHeatPolynomial u K extent id)
      let HA := HB.mul (faceHead_certificate hu0 hu1 K extent id hid hKu)
      have hA : (0 : Q') < quaternionHaar (blocks extent) A :=
        faceMass_positive hu0 hu1 extent id hid HB K hKu hB
      let z := weightedValue hv0 hv1 K extent hKv ids ht HA hA p
      have hvpin : weightedValue hv0 hv1 K extent hKv (id::ids) hi HB hB p ≈
          faceMoment v K extent id C p * Q'.recipPos (faceMass v K extent id C)
            (faceMass_positive hv0 hv1 extent id hid HC K hKv hC) :=
        Q'.eqv_trans _ _ _
          (normalizedMoment_congr _ _ (shuffle B (faceHeatPolynomial v K extent id) _) (RatPolyCoeffEqv.refl p))
          (normalized_face_pin v K extent id C p _)
      have hzpin : z ≈ faceMoment u K extent id C p * Q'.recipPos (faceMass u K extent id C)
          (faceMass_positive hu0 hu1 extent id hid HC K hKu hC) := by
        apply Q'.eqv_trans _ _ _ _ (normalized_face_pin u K extent id C p _)
        apply normalizedMoment_congr _ _ _ (RatPolyCoeffEqv.refl p)
        exact (RatPolyCoeffEqv.mul_assoc B (faceHeatPolynomial u K extent id) _).trans
          (shuffle B (faceHeatPolynomial u K extent id) _)
      have hstep : Q'.abs (weightedValue hv0 hv1 K extent hKv (id::ids) hi HB hB p + -z) ≤
          2*c*relativeVariation W u v :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
          (Q'.add_eqv_congr' hvpin (Q'.neg_eqv_congr _ _ hzpin))))
          (BF4ExactSlabOneFaceCouplingStability.normalized_difference_bound
            hu0 huv hvW hW1 K extent id hid hKu hKv HC P hC)
      have hupin : weightedValue hu0 hu1 K extent hKu (id::ids) hi HB hB p ≈
          weightedValue hu0 hu1 K extent hKu ids ht HA hA p :=
        normalizedMoment_congr _ _ (RatPolyCoeffEqv.mul_assoc B (faceHeatPolynomial u K extent id) _).symm
          (RatPolyCoeffEqv.refl p)
      have hrest : Q'.abs (z + -(weightedValue hu0 hu1 K extent hKu (id::ids) hi HB hB p)) ≤
          Q'.ofNat ids.length*(2*c*relativeVariation W u v) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hupin)))) (ih ht HA hA)
      exact Q'.le_trans' _ _ _ (abs_chain hstep hrest) (Q'.le_of_eqv (count_step ids.length _))

end YMGap.Continuum.BF4ExactSlabFiniteCouplingPath

#print axioms YMGap.Continuum.BF4ExactSlabFiniteCouplingPath.weightedMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCouplingPath.weightedValue
#print axioms YMGap.Continuum.BF4ExactSlabFiniteCouplingPath.weighted_difference_bound
