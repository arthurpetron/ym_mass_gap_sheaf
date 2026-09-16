/-
# Norm-relative variance stability under ONE original heat-cutoff change

All shared variables and every positive background factor are retained.
The same high-spin estimate is applied under arbitrary polynomial squares,
not under a supplied observable sup cap. Both endpoint partitions remain.
Normalized squared norms, and then variances centered at their OWN computed
means, compare in both directions by (1+eta)^2. No eta<1 guard is used.

These are ordinary original-action covariance norms, NOT reflected OS norms.
The cutoff depends on w and eta. Changing arbitrarily many faces, spatial
decay, a physical transfer identification and a continuum gap remain open.
-/

import YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.RationalPositiveRatioComparison
import YMGap.Continuum.RationalVarianceComparison

namespace YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly, quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | _ :: p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv _ _) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem difference_pin (w : Q') (K L extent id : Nat) (B : RatPoly) :
    faceMass w (K+L) extent id B + -(faceMass w K extent id B) ≈
      quaternionHaar (blocks extent) (polyMul B
        (polyAdd (faceHeatPolynomial w (K+L) extent id) (polyNeg (faceHeatPolynomial w K extent id)))) :=
  Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide)
      (fun | 0 => B | 1 => faceHeatPolynomial w (K+L) extent id | _ => faceHeatPolynomial w K extent id)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg _ _))))

private theorem le_factor {a b eta : Q'} (h : Q'.abs (a + -b) ≤ eta*b) : a ≤ (1+eta)*b :=
  Q'.le_trans' _ _ _ (ExpNeg.le_add_of_abs_sub_le h)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.var 1) (.var 0))) (.mul (.add (.const 1) (.var 1)) (.var 0))
      (by decide) (fun | 0 => b | _ => eta)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (eta : Q') (he : (0 : Q') < eta) (K L extent id : Nat)
  (hi : id ∈ slabPhysicalFaceEdges extent) (hK : relativeCutoff w eta ≤ K)
  {B : RatPoly} (H : Certificate (blocks extent) B)

include hw0 hw1 he hi hK H in
theorem mass_new_le_old :
    faceMass w (K+L) extent id B ≤ (1+eta)*faceMass w K extent id B :=
  le_factor (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (difference_pin w K L extent id B)))
    (relativePrefix_weighted_bound hw0 hw1 eta he K L extent id hi hK H))

include hw0 hw1 he hi hK H in
theorem mass_old_le_new :
    faceMass w K extent id B ≤ (1+eta)*faceMass w (K+L) extent id B :=
  le_factor (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _))
    (mass_difference_bound hw0 hw1 eta he K L extent id hi hK H))

def normalizedSquare (w : Q') (J extent id : Nat) (B p : RatPoly)
    (hZ : (0 : Q') < faceMass w J extent id B) : Q' :=
  faceMoment w J extent id B (polyMul p p) * Q'.recipPos (faceMass w J extent id B) hZ

def normalizedVariance (w : Q') (J extent id : Nat) (B p : RatPoly)
    (hZ : (0 : Q') < faceMass w J extent id B) : Q' :=
  RationalVarianceComparison.variance (faceMoment w J extent id B p)
    (faceMoment w J extent id B (polyMul p p)) (Q'.recipPos (faceMass w J extent id B) hZ)

include hw0 hw1 hi H in
private theorem moment_nonnegative (J : Nat) (hJ : headCutoff w ≤ J) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    (0 : Q') ≤ faceMoment w J extent id B (polyMul p p) :=
  ((H.multiplySquare p hp).mul (faceHead_certificate hw0 hw1 J extent id hi hJ)).haar_nonnegative

include hw0 hw1 he hi hK H in
theorem square_comparison (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hz : (0 : Q') < faceMass w K extent id B)
    (hZ : (0 : Q') < faceMass w (K+L) extent id B) :
    normalizedSquare w (K+L) extent id B p hZ ≤
      ((1+eta)*(1+eta))*normalizedSquare w K extent id B p hz :=
  RationalPositiveRatioComparison.ratio_comparison _ _ _ _ _ hz hZ
    (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt he))
    (moment_nonnegative hw0 hw1 extent id hi H K (Nat.le_trans (Nat.le_max_left _ _) hK) p hp)
    (mass_new_le_old hw0 hw1 eta he K L extent id hi hK (H.multiplySquare p hp))
    (mass_old_le_new hw0 hw1 eta he K L extent id hi hK H)

include hw0 hw1 he hi hK H in
theorem square_comparison_reverse (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hz : (0 : Q') < faceMass w K extent id B)
    (hZ : (0 : Q') < faceMass w (K+L) extent id B) :
    normalizedSquare w K extent id B p hz ≤
      ((1+eta)*(1+eta))*normalizedSquare w (K+L) extent id B p hZ :=
  RationalPositiveRatioComparison.ratio_comparison _ _ _ _ _ hZ hz
    (Q'.zero_le_add _ _ Q'.zero_le_one (Q'.le_of_lt he))
    (moment_nonnegative hw0 hw1 extent id hi H (K+L)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_add_right _ _)) p hp)
    (mass_old_le_new hw0 hw1 eta he K L extent id hi hK (H.multiplySquare p hp))
    (mass_new_le_old hw0 hw1 eta he K L extent id hi hK H)

/-- Literal p-c, written in the scalar/addition operations of weighted GNS. -/
def shifted (p : RatPoly) (c : Q') : RatPoly := polyAdd (polySmul 1 p) (polySmul (-c) polyOne)

private theorem supported_smul {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem shifted_supported {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (shifted p c) :=
  supported_add (supported_smul hp 1) (supported_smul (supported_one n) (-c))

include hw0 hw1 hi H in
private theorem square_pin (J : Nat) (hJ : headCutoff w ≤ J) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (c : Q')
    (hZ : (0 : Q') < faceMass w J extent id B) :
    normalizedSquare w J extent id B (shifted p c) hZ ≈
      RationalVarianceComparison.quadratic (faceMass w J extent id B) (faceMoment w J extent id B p)
        (faceMoment w J extent id B (polyMul p p)) (Q'.recipPos (faceMass w J extent id B) hZ) c := by
  let W := polyMul B (faceHeatPolynomial w J extent id)
  let D := weightedGNSData (blocks extent) W (H.mul (faceHead_certificate hw0 hw1 J extent id hi hJ))
  have h := D.diag_expand 1 (-c) ⟨p,hp⟩ ⟨polyOne,supported_one _⟩
  have hb : weightedPair (blocks extent) W p p ≈ faceMoment w J extent id B (polyMul p p) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  have ha : weightedPair (blocks extent) W p polyOne ≈ faceMoment w J extent id B p :=
    haar_of_coeff (((RatPolyCoeffEqv.mul_one p).mul_right W).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  have hz : weightedPair (blocks extent) W polyOne polyOne ≈ faceMass w J extent id B :=
    haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right W).trans (RatPolyCoeffEqv.one_mul W))
  have ht := Q'.eqv_trans _ _ _ h (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl 1) hb))
      (qmul (Q'.eqv_refl 1) (qmul (Q'.eqv_refl (-c)) ha)))
    (Q'.add_eqv_congr' (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl 1) ha))
      (qmul (Q'.eqv_refl (-c)) (qmul (Q'.eqv_refl (-c)) hz))))
  have hpw : faceMoment w J extent id B (polyMul (shifted p c) (shifted p c)) ≈
      weightedPair (blocks extent) W (shifted p c) (shifted p c) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)
  exact Q'.eqv_trans _ _ _ (qmul (Q'.eqv_trans _ _ _ hpw ht) (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.mul (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
        (.mul (.const 1) (.mul (.neg (.var 3)) (.var 1))))
        (.add (.mul (.neg (.var 3)) (.mul (.const 1) (.var 1)))
          (.mul (.neg (.var 3)) (.mul (.neg (.var 3)) (.var 2))))) (.var 4))
      (.mul (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 3)) (.var 1))))
        (.mul (.mul (.var 3) (.var 3)) (.var 2))) (.var 4)) (by decide)
      (fun
        | 0 => faceMoment w J extent id B (polyMul p p)
        | 1 => faceMoment w J extent id B p
        | 2 => faceMass w J extent id B
        | 3 => c
        | _ => Q'.recipPos (faceMass w J extent id B) hZ))

include hw0 hw1 hi H in
theorem variance_nonnegative (J : Nat) (hJ : headCutoff w ≤ J) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (hZ : (0 : Q') < faceMass w J extent id B) :
    (0 : Q') ≤ normalizedVariance w J extent id B p hZ := by
  let mean := faceMoment w J extent id B p * Q'.recipPos (faceMass w J extent id B) hZ
  have hc := shifted_supported hp mean
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (moment_nonnegative hw0 hw1 extent id hi H J hJ (shifted p mean) hc)
      (Q'.le_of_lt (Q'.recipPos_pos _ hZ)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (square_pin hw0 hw1 extent id hi H J hJ p hp mean hZ)
      (RationalVarianceComparison.quadratic_minimizer _ _ _ _ (Q'.mul_recipPos_eqv _ hZ))))

include hw0 hw1 he hi hK H in
theorem variance_comparison (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hz : (0 : Q') < faceMass w K extent id B)
    (hZ : (0 : Q') < faceMass w (K+L) extent id B) :
    normalizedVariance w (K+L) extent id B p hZ ≤
      ((1+eta)*(1+eta))*normalizedVariance w K extent id B p hz := by
  apply RationalVarianceComparison.variance_transport _ _ _ _ _ _ _ _ _
    (Q'.mul_recipPos_eqv _ hz) (Q'.mul_recipPos_eqv _ hZ)
  intro c
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (square_pin hw0 hw1 extent id hi H (K+L)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_add_right _ _)) p hp c hZ))
    (Q'.le_trans' _ _ _ (square_comparison hw0 hw1 eta he K L extent id hi hK H
      (shifted p c) (shifted_supported hp c) hz hZ)
      (Q'.le_of_eqv (qmul (Q'.eqv_refl _)
        (square_pin hw0 hw1 extent id hi H K (Nat.le_trans (Nat.le_max_left _ _) hK) p hp c hz))))

include hw0 hw1 he hi hK H in
theorem variance_comparison_reverse (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hz : (0 : Q') < faceMass w K extent id B)
    (hZ : (0 : Q') < faceMass w (K+L) extent id B) :
    normalizedVariance w K extent id B p hz ≤
      ((1+eta)*(1+eta))*normalizedVariance w (K+L) extent id B p hZ := by
  apply RationalVarianceComparison.variance_transport _ _ _ _ _ _ _ _ _
    (Q'.mul_recipPos_eqv _ hZ) (Q'.mul_recipPos_eqv _ hz)
  intro c
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (square_pin hw0 hw1 extent id hi H K (Nat.le_trans (Nat.le_max_left _ _) hK) p hp c hz))
    (Q'.le_trans' _ _ _ (square_comparison_reverse hw0 hw1 eta he K L extent id hi hK H
      (shifted p c) (shifted_supported hp c) hz hZ)
      (Q'.le_of_eqv (qmul (Q'.eqv_refl _)
        (square_pin hw0 hw1 extent id hi H (K+L)
          (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_add_right _ _)) p hp c hZ))))

include hw0 hw1 he hi hK H in
/-- The two ordinary centered seminorms have the SAME null observables.
This is not a statement about the reflected OS null space. -/
theorem variance_null_iff (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hz : (0 : Q') < faceMass w K extent id B)
    (hZ : (0 : Q') < faceMass w (K+L) extent id B) :
    normalizedVariance w (K+L) extent id B p hZ ≈ 0 ↔ normalizedVariance w K extent id B p hz ≈ 0 := by
  constructor
  · intro hn
    exact ExpNeg.eqv_of_le_le
      (Q'.le_trans' _ _ _ (variance_comparison_reverse hw0 hw1 eta he K L extent id hi hK H p hp hz hZ)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hn) (Q'.mul_zero_eqv _))))
      (variance_nonnegative hw0 hw1 extent id hi H K (Nat.le_trans (Nat.le_max_left _ _) hK) p hp hz)
  · intro ho
    exact ExpNeg.eqv_of_le_le
      (Q'.le_trans' _ _ _ (variance_comparison hw0 hw1 eta he K L extent id hi hK H p hp hz hZ)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ho) (Q'.mul_zero_eqv _))))
      (variance_nonnegative hw0 hw1 extent id hi H (K+L)
        (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_add_right _ _)) p hp hZ)

include he in
/-- Actual spectator heat product, with its positivity and BOTH positive
partitions constructed. Uniform over every supported observable, not its cap. -/
theorem original_variance_comparison (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p) :
    let B := polynomialProduct (faceHeatPolynomial w J extent) ids
    let HB := headProduct_certificate hw0 hw1 J extent hJ ids hids
    let hB : (0 : Q') < quaternionHaar (blocks extent) B :=
      Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids) (partition_floor hw0 hw1 extent ids hids J hJ)
    let hz := faceMass_positive hw0 hw1 extent id hi HB K (Nat.le_trans (Nat.le_max_left _ _) hK) hB
    let hZ := faceMass_positive hw0 hw1 extent id hi HB (K+L)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_add_right _ _)) hB
    normalizedVariance w (K+L) extent id B p hZ ≤ ((1+eta)*(1+eta))*normalizedVariance w K extent id B p hz ∧
      normalizedVariance w K extent id B p hz ≤ ((1+eta)*(1+eta))*normalizedVariance w (K+L) extent id B p hZ :=
  ⟨variance_comparison hw0 hw1 eta he K L extent id hi hK
      (headProduct_certificate hw0 hw1 J extent hJ ids hids) p hp _ _,
    variance_comparison_reverse hw0 hw1 eta he K L extent id hi hK
      (headProduct_certificate hw0 hw1 J extent hJ ids hids) p hp _ _⟩

end YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison

#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.mass_new_le_old
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.mass_old_le_new
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.normalizedSquare
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.normalizedVariance
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.square_comparison
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.square_comparison_reverse
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.shifted
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.shifted_supported
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.variance_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.variance_comparison
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.variance_comparison_reverse
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.variance_null_iff
#print axioms YMGap.Continuum.BF4ExactSlabOneFaceVarianceComparison.original_variance_comparison
