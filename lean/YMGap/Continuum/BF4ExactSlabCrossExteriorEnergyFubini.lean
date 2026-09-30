/-
# Literal cross-exterior energy integrand on the original doubled carrier

The original full weight splits into its incident and complementary
products. Only the selected head is exchanged. The resulting integrand
contains a same-exterior conditional replica energy and a full second
exterior marginal B*D. The latter has the ORIGINAL full partition mass.
-/

import YMGap.Continuum.BF4ExactSlabCrossExteriorReplacement
import YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
import YMGap.Continuum.SU2QuaternionConditionalReplicaMarginal
import YMGap.Continuum.BF4ExactSlabInPlaceVarianceEnergy

namespace YMGap.Continuum.BF4ExactSlabCrossExteriorEnergyFubini

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabConditionalStarComparison
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.BF4ExactSlabCrossExteriorReplacement
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
open YMGap.Continuum.BF4ExactSlabInPlaceVarianceEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPartialSliceSwap (reindex_fixed_of_selected_independent)
open YMGap.Continuum.SU2QuaternionReplicaPathIncrement
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.SU2QuaternionConditionalReplicaMarginal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "B" => complementHeat w K extent link
local notation "D" => inPlaceNormalizer w K extent link
local notation "A" => incidentHeat w K extent link
local notation "G" k => reciprocal D (starUpper w extent link)
  (starUpper_positive hw0 hw1 extent link) k

private theorem support_double {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))

include hl

private theorem exchanged_weight :
    HaarCarrierEqv (blocks extent + blocks extent)
      (reindexQuaternionPolynomial (headExchange extent link) (fullWeight w K extent))
      (polyMul (reindexQuaternionPolynomial (headExchange extent link) A) B) := by
  have h := reindex_carrier (headExchange extent link)
    (support_double (fullWeight_supported w K extent))
    (support_double (supported_polyMul (incidentHeat_supported w K extent link)
      (complementHeat_supported w K extent link)))
    (carrier_extend (blocks extent) (fullWeight_supported w K extent)
      (supported_polyMul (incidentHeat_supported w K extent link)
        (complementHeat_supported w K extent link))
      (RatPolyCoeffEqv.haarCarrier (heatProduct_partition w K extent link)))
  rw [reindexQuaternionPolynomial_mul] at h
  exact h.trans (HaarCarrierEqv.mul (.refl _ _)
    (reindex_fixed_of_selected_independent (blocks extent) [slot extent link] B
      (complementHeat_supported w K extent link) (by
        intro j hj
        have he := List.mem_singleton.mp hj
        subst j
        exact degree_zero_independent (complementHeat_degree_zero w K extent link hl))))

/-- Exact polynomial identity under every doubled Haar insertion. The
opposite signs of the two difference conventions cancel in their square. -/
theorem comparison_integrand_pin (f : RatPoly) (k : Nat) :
    HaarCarrierEqv (blocks extent + blocks extent)
      (polyMul (polyMul (firstKernel hw0 hw1 K extent link k)
        (otherNormalizer w K extent link)) (replacementInsertion w K extent link f))
      (polyMul
        (polyMul (polyMul B (G k))
          (mixedEnergy (blocks extent) [slot extent link] A f f))
        (liftBoundary (blocks extent) (polyMul B D))) := by
  have hE := otherNormalizer_lift_pin w K extent hl
  have hW := exchanged_weight (w := w) K extent link hl
  have htransport := HaarCarrierEqv.mul
    (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ (firstKernel hw0 hw1 K extent link k)) hE)
    (HaarCarrierEqv.mul hW
      (HaarCarrierEqv.refl _ (polyMul (liftBoundary (blocks extent) B)
        (replacementSquare extent link f))))
  refine htransport.trans ?_
  rw [lift_product]
  exact RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 3) (.var 4))
        (.mul (.var 5) (.mul (.add (.var 7) (.neg (.var 6)))
          (.add (.var 7) (.neg (.var 6)))))))
    (.mul (.mul (.mul (.var 4) (.var 1))
      (.mul (.mul (.var 0) (.var 3))
        (.mul (.add (.var 6) (.neg (.var 7))) (.add (.var 6) (.neg (.var 7))))))
      (.mul (.var 5) (.var 2)))
    (by decide)
    (fun | 0 => A | 1 => G k | 2 => liftBoundary (blocks extent) D
         | 3 => reindexQuaternionPolynomial (headExchange extent link) A
         | 4 => B | 5 => liftBoundary (blocks extent) B | 6 => f
         | _ => reindexQuaternionPolynomial (headExchange extent link) f))

/-- The second exterior marginal integrates to the original partition,
not the mass of the incident star or the complementary action alone. -/
theorem second_exterior_partition_pin :
    quaternionHaar (blocks extent) (polyMul B D) ≈
      quaternionHaar (blocks extent) (fullWeight w K extent) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (full_marginal_pin w K extent hl).symm)
      (project_mean (blocks extent) (slot extent link)
        (List.idxOf_lt_length_of_mem hl) (fullWeight w K extent)))

/-- Exact removal of the unused second exterior. The first exterior stays
inside the reciprocal-weighted conditional determinant. -/
theorem comparison_integral_marginal (f : RatPoly)
    (hf : SupportedQuaternionBlocks (blocks extent) f) (k : Nat) :
    comparisonIntegral hw0 hw1 K extent link f k ≈
      quaternionHaar (blocks extent)
        (polyMul (polyMul B (G k))
          (polyAdd (covarianceNumerator [slot extent link] A f f)
            (covarianceNumerator [slot extent link] A f f))) *
      quaternionHaar (blocks extent) (fullWeight w K extent) := by
  have hB := complementHeat_supported w K extent link
  have hD := inPlaceNormalizer_supported w K extent link
  have hG := reciprocal_supported hD _ (starUpper_positive hw0 hw1 extent link) k
  have hiB := degree_zero_independent (complementHeat_degree_zero w K extent link hl)
  have hiD := inPlaceNormalizer_independent w K extent link
  have hiG := reciprocal_independent (slot extent link) D hiD _
    (starUpper_positive hw0 hw1 extent link) k
  have h := singleton_conditional_replica_marginal (blocks extent) (slot extent link)
    (List.idxOf_lt_length_of_mem hl) A f (polyMul B (G k)) (polyMul B D)
    (incidentHeat_supported w K extent link) hf
    (supported_polyMul hB hG) (supported_polyMul hB hD)
    (quaternionBlockIndependent_polyMul hiB hiG)
    (quaternionBlockIndependent_polyMul hiB hiD)
  exact Q'.eqv_trans _ _ _
    (haar_of_carrier (comparison_integrand_pin hw0 hw1 K extent link hl f k))
    (Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left _ _ _ (second_exterior_partition_pin (w := w) K extent link hl)))

/-- The literal cross-exterior comparison integral is the original full
partition times the EXISTING two-head finite reciprocal energy integral. -/
theorem comparison_integral_energy_pin (hK : headCutoff w ≤ K)
    (p : (fullData hw0 hw1 K extent hK).V) (k : Nat) :
    comparisonIntegral hw0 hw1 K extent link p.val k ≈
      quaternionHaar (blocks extent) (fullWeight w K extent) *
        replicaIntegral hw0 hw1 K extent hK link hl p k := by
  have he := inPlaceCovariance_energy_pin hw0 hw1 K extent hK link hl p k
  have hd := Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_add_right (blocks extent) (polyMul B (G k))
      (inPlaceCovariance hw0 hw1 K extent hK link p)
      (inPlaceCovariance hw0 hw1 K extent hK link p))
    (Q'.add_eqv_congr' he he)
  have hr := replicaIntegral_pin hw0 hw1 K extent hK link hl p k
  exact Q'.eqv_trans _ _ _
    (comparison_integral_marginal hw0 hw1 K extent link hl p.val p.property k)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ hd (Q'.eqv_symm hr)))
      (Q'.mul_comm_eqv _ _))

/-- Fully pinned finite comparison: independent-full-replica replacement
versus the actual same-exterior reciprocal energy and ORIGINAL partition. -/
theorem original_replacement_finite_energy_bound (hK : headCutoff w ≤ K)
    (p : (fullData hw0 hw1 K extent hK).V) (k : Nat) :
    (starLower w extent link * starLower w extent link *
      (1 + -((starRadius hw0 hw1 extent link)^k))) *
      replacementIntegral w K extent link p.val ≤
    ((starUpper w extent link * starUpper w extent link) *
      quaternionHaar (blocks extent) (fullWeight w K extent)) *
      replicaIntegral hw0 hw1 K extent hK link hl p k :=
  Q'.le_trans' _ _ _
    (original_replacement_comparison hw0 hw1 K extent hK link hl p.val p.property k)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (comparison_integral_energy_pin hw0 hw1 K extent link hl hK p k))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

#print axioms comparison_integrand_pin
#print axioms second_exterior_partition_pin
#print axioms comparison_integral_marginal
#print axioms comparison_integral_energy_pin
#print axioms original_replacement_finite_energy_bound

end YMGap.Continuum.BF4ExactSlabCrossExteriorEnergyFubini
