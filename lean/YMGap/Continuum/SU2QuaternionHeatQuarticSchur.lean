/-
# Signed Schur domination of the ORIGINAL quartic one-link kernel

Both computed Haar marginals are the original exceptional coefficient.
Positivity of the kernel times an endpoint-difference square gives the
signed bound, without positive definiteness of the quartic operator or
division. The source consumer costs its RAW Haar square, not OWN variance.
No interacting, completed, or scaling estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticMoment
import YMGap.Continuum.SU2HeatQuarticLowCoefficients
import YMGap.Continuum.SU2QuaternionRelativeHeatContraction
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.SU2QuaternionProductHeatMomentDefect

namespace YMGap.Continuum.SU2QuaternionHeatQuarticSchur

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTwoSliceSwap
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatVacuum
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion (lifted_independent)
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup
open YMGap.Continuum.SU2HeatQuarticLowCoefficients (zeroCoeff zeroCoeff_le_sixty)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect (rawSourceMoment)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (haar_liftBoundary)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The squared trace deficit times the complete original inclusive prefix. -/
def quarticKernel (q : Q') (K : Nat) : RatPoly :=
  polyMul (polyMul (defect relativeScalar) (defect relativeScalar)) (relativeHeat q K)

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_smul {n : Nat} {p : RatPoly}
    (c : Q') (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem defect_supported : SupportedQuaternionBlocks 2 (defect relativeScalar) :=
  supported_add (support_smul _ (supported_one 2))
    (support_neg (character_supported (scalar_supported (by decide) (by decide)) 1))

theorem quarticKernel_supported (q : Q') (K : Nat) :
    SupportedQuaternionBlocks 2 (quarticKernel q K) :=
  supported_polyMul (supported_polyMul defect_supported defect_supported)
    (relativeHeat_supported q K)

/-- A constructed square certificate, not an operator-PSD hypothesis. -/
def quarticKernel_certificate {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K : Nat) (hK : headCutoff q ≤ K) : Certificate 2 (quarticKernel q K) :=
  Certificate.multiplySquare _ defect_supported (relativeHeat_certificate hq0 hq1 K hK)

private def L (r p : RatPoly) : Q' := H 2 (polyMul p r)

private theorem Ladd (r p s : RatPoly) : L r (polyAdd p s) ≈ L r p+L r s := by
  unfold L
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append 2 _ _

private theorem Lscale (r p : RatPoly) (c : Q') : L r (polyMul (cap c) p) ≈ c*L r p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((cap_mul_left c p).mul_right r))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
      (quaternionHaar_polySmul 2 c _))

private theorem Lneg (r p : RatPoly) : L r (polyNeg p) ≈ -(L r p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((QuaternionHaarAngularCarrier.neg_smul p).mul_right r))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left (-1) p r))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 2 (-1) _)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => L r p))))

private theorem add_value (r : RatPoly) {p s : RatPoly} {u v : Q'}
    (hp : L r p ≈ u) (hs : L r s ≈ v) : L r (polyAdd p s) ≈ u+v :=
  Q'.eqv_trans _ _ _ (Ladd r p s) (Q'.add_eqv_congr' hp hs)

private theorem scale_value (r : RatPoly) {p : RatPoly} {v : Q'}
    (c : Q') (hp : L r p ≈ v) : L r (polyMul (cap c) p) ≈ c*v :=
  Q'.eqv_trans _ _ _ (Lscale r p c) (Q'.mul_eqv_congr_left _ _ _ hp)

private theorem neg_value (r : RatPoly) {p : RatPoly} {v : Q'}
    (hp : L r p ≈ v) : L r (polyNeg p) ≈ -v :=
  Q'.eqv_trans _ _ _ (Lneg r p) (Q'.neg_eqv_congr _ _ hp)

private theorem basis_value (r x : RatPoly) : ∀ j,
    L r (quarticBasis x j) ≈ quarticResponse (fun s => L r (characterPolynomial x s)) j
  | 0 => add_value r
      (add_value r (scale_value r 5 (Q'.eqv_refl _))
        (neg_value r (scale_value r 4 (Q'.eqv_refl _)))) (Q'.eqv_refl _)
  | 1 => add_value r
      (add_value r (scale_value r 6 (Q'.eqv_refl _))
        (neg_value r (scale_value r 4 (add_value r (Q'.eqv_refl _) (Q'.eqv_refl _)))))
      (Q'.eqv_refl _)
  | _k+2 => Q'.eqv_trans _ _ _ (add_value r
      (add_value r (scale_value r 6 (Q'.eqv_refl _))
        (neg_value r (scale_value r 4 (add_value r (Q'.eqv_refl _) (Q'.eqv_refl _)))))
      (add_value r (Q'.eqv_refl _) (Q'.eqv_refl _)))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem sum_value (r : RatPoly) (f : Nat → RatPoly) : ∀ M,
    L r (finitePolySum f (List.range M)) ≈ finSum (fun j => L r (f j)) M
  | 0 => haar_of_coeff (RatPolyCoeffEqv.mul_zero_left _)
  | M+1 => by
      rw [List.range_succ, PolynomialWeightedSumBounds.sum_append, RationalTail.finSum_succ]
      exact add_value r (sum_value r f M)
        (Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.add_zero _).mul_right r))
          (Q'.eqv_refl _))

private theorem Lsmul (r p : RatPoly) (c : Q') : L r (polySmul c p) ≈ c*L r p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul 2 c _)

private theorem quartic_value (r : RatPoly) (q : Q') (K : Nat) :
    L r (quarticKernel q K) ≈
      finSum (fun j => quarticCoeff (cutCoeff q K) j * L r (relativeCharacter j)) (K+3) := by
  unfold quarticKernel
  rw [relativeHeat_eq_prefix]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff ((heat_quartic_expansion q K relativeScalar).mul_right r))
    (Q'.eqv_trans _ _ _ (sum_value r _ (K+1))
      (Q'.eqv_trans _ _ _
        (finSum_eqv_congr _ _ (fun j => Q'.eqv_trans _ _ _ (Lsmul r _ _)
          (Q'.mul_eqv_congr_left _ _ _ (basis_value r relativeScalar j))) (K+1))
        (finite_regroup q K (fun j => L r (relativeCharacter j)))))

private theorem sum_zero_slot (v : Q') : ∀ M,
    finSum (fun j => if j = 0 then v else 0) (M+1) ≈ v
  | 0 => Q'.eqv_of_eq (Q'.zero_add' v)
  | M+1 => by
      change finSum (fun j => if j = 0 then v else 0) (M+1)+0 ≈ v
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (sum_zero_slot v M)

/-- The actual upper-endpoint marginal; K>=2 retains all three vacuum coefficients. -/
theorem quarticKernel_upper_marginal (q : Q') (K : Nat) (hK2 : 2 ≤ K)
    (f : RatPoly) (_hf : SupportedQuaternionBlocks 1 f) :
    H 2 (polyMul (quarticKernel q K) (liftBoundary 1 f)) ≈ zeroCoeff q*H 1 f := by
  let r := liftBoundary 1 f
  have hc (j : Nat) : L r (relativeCharacter j) ≈
      (if j = 0 then H 2 r else 0) := character_vacuum 1 (by decide) j r (lifted_independent f)
  have hs : finSum (fun j => quarticCoeff (cutCoeff q K) j*L r (relativeCharacter j)) (K+3) ≈
      quarticCoeff (cutCoeff q K) 0*H 2 r := by
    refine Q'.eqv_trans _ _ _ (finSum_eqv_congr _ _ (fun j => ?_) (K+3))
      (sum_zero_slot _ (K+2))
    by_cases hj : j = 0
    · subst j
      exact Q'.mul_eqv_congr_left _ _ _ (hc 0)
    · rw [if_neg hj]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (hc j))
        (by rw [if_neg hj]; exact Q'.mul_zero_eqv _)
  have hz : quarticCoeff (cutCoeff q K) 0 = zeroCoeff q := by
    simp only [quarticCoeff, cutCoeff, if_pos (show 0 ≤ K by omega),
      if_pos (show 1 ≤ K by omega), if_pos hK2, zeroCoeff]
  exact Q'.eqv_trans _ _ _ (quartic_value r q K)
    (Q'.eqv_trans _ _ _ hs (by rw [hz]; exact Q'.mul_eqv_congr_left _ _ _ (haar_liftBoundary 1 1 f)))

private theorem padded_neg {p s : RatPoly} (h : PaddedPolynomialCoeffEqv 2 p s) :
    PaddedPolynomialCoeffEqv 2 (polyNeg p) (polyNeg s) :=
  (PaddedPolynomialCoeffEqv.of_coeff (QuaternionHaarAngularCarrier.neg_smul p)).trans
    ((h.smul (-1)).trans (PaddedPolynomialCoeffEqv.of_coeff
      (QuaternionHaarAngularCarrier.neg_smul s).symm))

private theorem scalar_swap : PaddedPolynomialCoeffEqv 2
    (reindexQuaternionPolynomial (swap 1) relativeScalar) relativeScalar := by
  unfold PaddedPolynomialCoeffEqv
  exact RatPolyCoeffEqv.of_canon_termwise (by decide +kernel)

private theorem kernel_swap (q : Q') (K : Nat) : PaddedPolynomialCoeffEqv 2
    (reindexQuaternionPolynomial (swap 1) (quarticKernel q K)) (quarticKernel q K) := by
  have hc (j : Nat) : PaddedPolynomialCoeffEqv 2
      (reindexQuaternionPolynomial (swap 1) (characterPolynomial relativeScalar j))
      (characterPolynomial relativeScalar j) :=
    (PaddedPolynomialCoeffEqv.of_prefix (reindexQuaternionPolynomial_character_prefix _ _ _)).trans
      (scalar_swap.character j)
  have hd : PaddedPolynomialCoeffEqv 2
      (reindexQuaternionPolynomial (swap 1) (defect relativeScalar)) (defect relativeScalar) := by
    unfold defect cap
    rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_smul]
    exact ((PaddedPolynomialCoeffEqv.of_prefix (reindex_polyOne_prefix _)).smul 2).add
      (padded_neg (hc 1))
  have hh : PaddedPolynomialCoeffEqv 2
      (reindexQuaternionPolynomial (swap 1) (relativeHeat q K)) (relativeHeat q K) := by
    rw [relativeHeat_eq_prefix]
    unfold heatPrefix
    induction List.range (K+1) with
    | nil => exact PaddedPolynomialCoeffEqv.of_coeff (.refl _)
    | cons j js ih =>
        simp only [finitePolySum, reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_smul]
        exact ((hc j).smul _).add ih
  unfold quarticKernel
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]
  exact (hd.mul hd).mul hh

/-- The actual lower-endpoint marginal, obtained by complete carrier exchange. -/
theorem quarticKernel_lower_marginal (q : Q') (K : Nat) (hK2 : 2 ≤ K)
    (f : RatPoly) (hf : SupportedQuaternionBlocks 1 f) :
    H 2 (polyMul (quarticKernel q K) f) ≈ zeroCoeff q*H 1 f := by
  have hf2 : SupportedQuaternionBlocks 2 f := fun t ht => Nat.le_trans (hf t ht) (by decide)
  have hp := supported_polyMul (quarticKernel_supported q K) hf2
  have hpin : PaddedPolynomialCoeffEqv 2
      (reindexQuaternionPolynomial (swap 1) (polyMul (quarticKernel q K) f))
      (polyMul (quarticKernel q K) (liftBoundary 1 f)) := by
    rw [reindexQuaternionPolynomial_mul]
    exact (kernel_swap q K).mul (PaddedPolynomialCoeffEqv.of_prefix (lower_prefix 1 f hf))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (SU2QuaternionTwoSliceSwap.haar 1 _ hp))
    (Q'.eqv_trans _ _ _ (hpin.haar (polynomial_supported 1 _) 
      (supported_polyMul (quarticKernel_supported q K) (lift_supported hf 1)))
      (quarticKernel_upper_marginal q K hK2 f hf))

private theorem young_expansion (q : Q') (K : Nat) (a : RatPoly) :
    H 2 (polyMul (polyMul (jump 1 a) (jump 1 a)) (quarticKernel q K)) ≈
      weightedPair 2 (quarticKernel q K) a a+
        (-(weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a))+
          (-(weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a))+
            weightedPair 2 (quarticKernel q K) (liftBoundary 1 a) (liftBoundary 1 a))) := by
  let b := liftBoundary 1 a
  let W := quarticKernel q K
  have hn (p : RatPoly) : H 2 (polyNeg p) ≈ -(H 2 p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 2 (-1) p)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => H 2 p)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1)))) (.var 2))
    (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
      (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))
          (.mul (.mul (.var 1) (.var 1)) (.var 2))))) (by decide)
    (fun
      | 0 => a
      | 1 => b
      | _ => W)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append 2 _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append 2 _ _)
          (Q'.add_eqv_congr' (hn _)
            (Q'.eqv_trans _ _ _ (quaternionHaar_append 2 _ _)
              (Q'.add_eqv_congr' (hn _) (Q'.eqv_refl _)))))))

/-- Signed original bilateral insertion is dominated by the identity Haar form. -/
theorem quartic_signed_schur {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K : Nat) (hK : headCutoff q ≤ K) (hK2 : 2 ≤ K)
    (a : RatPoly) (ha : SupportedQuaternionBlocks 1 a) :
    weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a) ≤ zeroCoeff q*H 1 (polyMul a a) := by
  have hpos := (quarticKernel_certificate hq0 hq1 K hK).square_insertion_nonnegative
    (jump 1 a) (jump_supported ha)
  have hl : weightedPair 2 (quarticKernel q K) a a ≈ zeroCoeff q*H 1 (polyMul a a) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (quarticKernel_lower_marginal q K hK2 _ (supported_polyMul ha ha))
  have hu : weightedPair 2 (quarticKernel q K) (liftBoundary 1 a) (liftBoundary 1 a) ≈
      zeroCoeff q*H 1 (polyMul a a) := by
    unfold weightedPair
    rw [← lift_product]
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (quarticKernel_upper_marginal q K hK2 _ (supported_polyMul ha ha))
  have h := Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (young_expansion q K a)
    (Q'.add_eqv_congr' hl (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _ hu)))))
  have he : zeroCoeff q*H 1 (polyMul a a)+
      (-(weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a))+
        (-(weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a))+zeroCoeff q*H 1 (polyMul a a))) ≈
      2*(zeroCoeff q*H 1 (polyMul a a)-weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a)) :=
    poly_identity_of_normal_eq (.add (.var 0) (.add (.neg (.var 1)) (.add (.neg (.var 1)) (.var 0))))
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => zeroCoeff q*H 1 (polyMul a a) | _ => weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a))
  have hd : (0 : Q') ≤ zeroCoeff q*H 1 (polyMul a a)-weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a) :=
    Q'.le_of_mul_le_mul_left (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv 2))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))) (by decide)
  exact Q'.le_of_sub_nonneg hd

/-- Explicit second-order budget, independent of the degree of the signed endpoint. -/
theorem quartic_signed_budget {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K : Nat) (hK : headCutoff q ≤ K) (hK2 : 2 ≤ K)
    (a : RatPoly) (ha : SupportedQuaternionBlocks 1 a) :
    weightedPair 2 (quarticKernel q K) a (liftBoundary 1 a) ≤
      (60*RingNormaliser.qpow (1-q) 2)*H 1 (polyMul a a) :=
  Q'.le_trans' _ _ _ (quartic_signed_schur hq0 hq1 K hK hK2 a ha)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (zeroCoeff_le_sixty (Q'.le_of_lt hq0) (Q'.le_of_lt hq1))
      (Certificate.square a ha).haar_nonnegative)

/-- Substituting an actual signed source costs its RAW source-square moment. -/
theorem source_quartic_signed_budget {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K : Nat) (hK : headCutoff q ≤ K) (hK2 : 2 ≤ K)
    (source f : RatPoly) (hs : SupportedQuaternionBlocks 1 source) (hf : SupportedQuaternionBlocks 1 f) :
    weightedPair 2 (quarticKernel q K) (polyMul source f) (liftBoundary 1 (polyMul source f)) ≤
      (60*RingNormaliser.qpow (1-q) 2)*rawSourceMoment 1 source (polyMul f f) :=
  Q'.le_trans' _ _ _ (quartic_signed_budget hq0 hq1 K hK hK2 _ (supported_polyMul hs hf))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff
      (RatPolyCoeffEqv.mul_four_swap source f source f))))

#print axioms quarticKernel
#print axioms quarticKernel_supported
#print axioms quarticKernel_certificate
#print axioms quarticKernel_upper_marginal
#print axioms quarticKernel_lower_marginal
#print axioms quartic_signed_schur
#print axioms quartic_signed_budget
#print axioms source_quartic_signed_budget

end YMGap.Continuum.SU2QuaternionHeatQuarticSchur
