/-
# Even mean-square Haar perturbation smallness fails for the original face heat

For every actual physical plaquette and every K>=1, its full positive-spin
remainder R_K has H[R_K]=0 and H[chi_1*R_K]=2*w^3. Since H[chi_1^2]=1,
ordinary Haar Cauchy--Schwarz gives H[R_K^2]>=4*w^6. Thus at w>=7/8 even
the weaker Haar-relative variance cap one fails, at every later cutoff.

This is distinct from failure of a pointwise/certificate Interval bound:
that earlier result alone did not exclude small L2 variation. The original
face prefix has mean one and equals 1+R_K. No small-nome or positivity guard
is required for the algebra and Haar norm bound. Interpreting the prefix as
a positive probability density still requires its original positivity
certificate, e.g. the existing late-cutoff guard; that guard is not weakened.

Scope: one literal original face under bare Haar, not the full V*T^n1,
not its conditional determinant, and not a shared-heat reference law.
This rules out an individual-face small-Haar-perturbation avenue near w=1;
it does NOT rule out a signed full-action estimate or a Yang--Mills gap.
-/

import YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (original_character_support)
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder (faceHeat_eq_one_add)
open YMGap.Continuum.BF4ExactSlabHeatHaarGuardObstruction
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (remainderFace_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one _)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

/-- The remainder is centered for the ACTUAL original Haar functional. -/
theorem remainder_mean_zero (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) :
    quaternionHaar (N extent) (faceHeatTail w extent id 1 K) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul _))) ?_
  apply inserted_sum_zero
  intro i _
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (face_character_haar_zero hi (1+i) (by omega))) (Q'.mul_zero_eqv _)))

theorem prefix_mean_one (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) :
    quaternionHaar (N extent) (faceHeatPolynomial w K extent id) ≈ 1 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (faceHeat_eq_one_add w extent id K))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_one _) (remainder_mean_zero w hi K))
        (by decide)))

private theorem fundamental_term_high (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (i : Nat) :
    quaternionHaar (N extent)
      (polyMul (characterPolynomial (faceScalar extent id) 1)
        (faceHeatTerm w extent id (1+(1+i)))) ≈ 0 := by
  have hpair := first_character_pair hi (i+1)
  simp only [Nat.succ_ne_zero, ↓reduceIte] at hpair
  have he : 1+(1+i) = (i+1)+1 := by omega
  rw [he]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hpair) (Q'.mul_zero_eqv _)))

/-- Every later cutoff retains this exact fundamental-character coefficient. -/
theorem fundamental_remainder_pairing (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar (N extent)
      (polyMul (characterPolynomial (faceScalar extent id) 1)
        (faceHeatTail w extent id 1 K)) ≈ 2*qpow w 3 := by
  have hsplit := PolynomialWeightedSumBounds.sum_range_add
    (fun i => faceHeatTerm w extent id (1+i)) 1 (K-1)
  rw [Nat.add_sub_of_le hK] at hsplit
  unfold faceHeatTail
  rw [hsplit]
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _) ?_
  have htail : quaternionHaar (N extent)
      (polyMul (characterPolynomial (faceScalar extent id) 1)
        (finitePolySum (fun i => faceHeatTerm w extent id (1+(1+i))) (List.range (K-1)))) ≈ 0 :=
    inserted_sum_zero _ _ _ _ (fun i _ => fundamental_term_high w hi i)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ?_ htail) (Q'.eqv_of_eq (Q'.add_zero' _))
  simp only [show List.range 1 = [0] from rfl, finitePolySum, Nat.reduceAdd,
    polyAdd, polyZero, List.append_nil]
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (first_character_pair hi 0))
        (Q'.mul_one_eqv _)))

/-- Since H(h_K)=1, this is its Haar-relative variance, not a new law. -/
def remainderVariance (w : Q') (K extent id : Nat) : Q' :=
  quaternionHaar (N extent)
    (polyMul (faceHeatTail w extent id 1 K) (faceHeatTail w extent id 1 K))

private theorem unit_weight_pair (blocks : Nat) (p q : RatPoly) :
    weightedPair blocks polyOne p q ≈ quaternionHaar blocks (polyMul p q) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_one _)

/-- Projection onto the normalized fundamental character alone forces this
lower bound. No upper-label cancellation or positivity of h_K is assumed. -/
theorem remainderVariance_lower (w : Q') {extent id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) (hK : 1 ≤ K) :
    4*qpow w 6 ≤ remainderVariance w K extent id := by
  let c := characterPolynomial (faceScalar extent id) 1
  let r := faceHeatTail w extent id 1 K
  have hc : SupportedQuaternionBlocks (N extent) c := original_character_support _ _ _
  have h := weighted_cauchySchwarz (N extent) polyOne c r (Certificate.one _) hc
    (remainderFace_supported w K extent id)
  have hcross := Q'.eqv_trans _ _ _ (unit_weight_pair (N extent) c r)
    (fundamental_remainder_pairing w hi K hK)
  have hdiag := Q'.eqv_trans _ _ _ (unit_weight_pair (N extent) c c) (first_character_pair hi 0)
  have hleft : weightedPair (N extent) polyOne c r * weightedPair (N extent) polyOne c r ≈
      4*qpow w 6 :=
    Q'.eqv_trans _ _ _ (qmul hcross hcross)
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.pow (.var 0) 3)) (.mul (.const 2) (.pow (.var 0) 3)))
        (.mul (.const 4) (.pow (.var 0) 6)) (by decide) (fun _ => w))
  have hright : weightedPair (N extent) polyOne c c * weightedPair (N extent) polyOne r r ≈
      remainderVariance w K extent id :=
    Q'.eqv_trans _ _ _ (qmul hdiag (unit_weight_pair (N extent) r r))
      (Q'.one_mul_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- Smallness fails even in bare-Haar L2, a weaker requirement than the old
two-sided Interval cap. The fixed threshold is explicit, not beta-uniform. -/
theorem remainderVariance_gt_one {w : Q'} (hw : nomeThreshold ≤ w)
    {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) (K : Nat) (hK : 1 ≤ K) :
    (1 : Q') < remainderVariance w K extent id :=
  HeatKernelRGStep.lt_of_lt_of_le
    (HeatKernelRGStep.lt_of_lt_of_le (by decide : (1 : Q') < 4*qpow nomeThreshold 6)
      (Q'.mul_le_mul_of_nonneg_left _ _ 4
        (FusedAmplitudeDerivation.qpow_mono_base (by decide : (0 : Q') ≤ nomeThreshold) hw 6)
        (by decide)))
    (remainderVariance_lower w hi K hK)

/-- Choosing a later cutoff, even depending on w, cannot restore cap one. -/
theorem no_eventual_small_variance {w : Q'} (hw : nomeThreshold ≤ w)
    {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) (K0 : Nat)
    (h : ∀ K, K0 ≤ K → remainderVariance w K extent id ≤ (1 : Q')) : False :=
  Int.not_lt_of_ge (h (max K0 1) (Nat.le_max_left _ _))
    (remainderVariance_gt_one hw hi (max K0 1) (Nat.le_max_right _ _))

end YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction

#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.remainder_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.prefix_mean_one
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.fundamental_remainder_pairing
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.remainderVariance
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.remainderVariance_lower
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.remainderVariance_gt_one
#print axioms YMGap.Continuum.BF4ExactSlabHeatHaarVarianceObstruction.no_eventual_small_variance
