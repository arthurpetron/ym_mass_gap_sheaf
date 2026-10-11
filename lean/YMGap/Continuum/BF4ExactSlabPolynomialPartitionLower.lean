/-
# Computed polynomial floor for the SAME ORIGINAL finite partition

The complete original action dominates a separable test on its literal
distinct link carrier. Every selected physical face remains, and the
original six-occurrence cap pays overlapping links without independent
face integration. Original product-Haar computes the test's moment exactly.

For F selected faces and L original links the identity-normalized partition
is at least 2^(-F) * kernelMoment(6*M)^L, hence at least
2^(-F) * (1/(6*M+1)^2)^L. M is the produced localization degree, explicitly
dependent on coupling and cutoff. This is a GLOBAL finite partition floor,
not a boundary-conditioned floor, a volume/cutoff-uniform bound, an entropy
identification, a signed late-response estimate, or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabKernelProductRecoding
import YMGap.Continuum.BF4ExactSlabKernelIncidence
import YMGap.Continuum.FiniteProductMultiplicityBound
import YMGap.Continuum.QuaternionHaarTensorLocalization

namespace YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct (base base_bounds)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_smul)
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_polySmul)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment haar_mono)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit (linkValue)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization (localizationDegree)
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization
open YMGap.Continuum.BF4ExactSlabKernelProductRecoding
open YMGap.Continuum.BF4ExactSlabKernelIncidence (faceLinks_count_le_six)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (faceLinks)
open YMGap.Continuum.FiniteProductMultiplicityBound (scalarProduct_multiplicity_bound)
open YMGap.Continuum.QuaternionHaarTensorLocalization
open YMGap.Continuum.SU2QuaternionPolynomialKernelConcentration (kernelMoment)
open YMGap.Continuum.SU2QuaternionKernelMomentLower (localizationFloor localizationFloor_positive)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit (heatProductHaar)
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep (qpow_qpow)

local infix:50 " ≈ " => Q'.eqv

private theorem scalar_congr {A : Type} {f g : A → Q'} : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → scalarProduct f xs ≈ scalarProduct g xs
  | [], _ => Q'.eqv_refl 1
  | a::xs, h => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (h a List.mem_cons_self))
      (Q'.mul_eqv_congr_left _ _ _ (scalar_congr xs (fun b hb => h b (List.mem_cons_of_mem a hb))))

private theorem power_bounds (x : Q') (hx : (0 : Q') ≤ x ∧ x ≤ 1) : ∀ m,
    (0 : Q') ≤ qpow x m ∧ qpow x m ≤ 1
  | 0 => ⟨by change (0 : Q') ≤ 1; decide, Q'.le_refl' _⟩
  | m+1 => ⟨qpow_nonneg x hx.1 (m+1),
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg (power_bounds x hx m).2 hx.2 (by decide) hx.1)
        (Q'.le_of_eqv (by decide : (1 : Q')*1 ≈ 1))⟩

/-- The separable original-carrier test is below the ACTUAL occurrence
product. Physicality and no repeated face IDs are essential for the cap six. -/
theorem original_tensor_le_occurrences (extent M : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hn : ids.Nodup) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs)
      (tensorKernel (boundaryCompleteSlabLinks extent).length (6*M)) ≤
        linkPowerProduct extent qs M (faceLinks extent ids) := by
  have hm := scalarProduct_multiplicity_bound
    (fun link => qpow (base (linkValue extent qs link)) M) 6
    (boundaryCompleteSlabLinks extent) (faceLinks extent ids)
    (boundaryCompleteSlabLinks_nodup extent) (faceLinks_physical extent ids hids)
    (fun link _ => faceLinks_count_le_six extent ids hids hn link)
    (fun link _ => power_bounds _ (base_bounds _) M)
  have hp : scalarProduct
      (fun link => qpow (qpow (base (linkValue extent qs link)) M) 6)
      (boundaryCompleteSlabLinks extent) ≈
        linkPowerProduct extent qs (6*M) (boundaryCompleteSlabLinks extent) := by
    apply scalar_congr
    intro link _
    simpa only [Nat.mul_comm] using qpow_qpow (base (linkValue extent qs link)) M 6
  have he := Q'.eqv_trans _ _ _
    (tensorKernel_eval (boundaryCompleteSlabLinks extent).length (6*M) qs)
    (Q'.eqv_symm (carrierProduct_index_pin extent qs (6*M)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp) hm)

/-- The polynomial test is dominated by the COMPLETE identity-normalized
original density on every SAME original unit assignment. -/
theorem original_test_le_density {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hn : ids.Nodup) (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs)
      (polySmul (half^ids.length)
        (tensorKernel (boundaryCompleteSlabLinks extent).length (6*localizationDegree w hw0 hw1 K))) ≤
      evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) := by
  have h0 : (0 : Q') ≤ half^ids.length := Q'.pow_nonneg half (by decide) ids.length
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (evalRatPoly_smul _ _ _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (original_tensor_le_occurrences extent _ ids hids hn qs) h0)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (localizedProduct_recoding hw0 hw1 K extent qs ids))
        (original_product_localization hw0 hw1 K extent ids qs hK)))

/-- Exact test moment below the SAME ORIGINAL finite Haar partition.
Neither the original action nor its integration carrier has been replaced. -/
theorem normalized_partition_moment_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hn : ids.Nodup) (hK : finiteCutoff w ≤ K+1) :
    half^ids.length * (kernelMoment (6*localizationDegree w hw0 hw1 K))^(boundaryCompleteSlabLinks extent).length ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length
        (normalizedHeatProduct w hw0 K extent ids) := by
  have hs : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (polySmul (half^ids.length)
        (tensorKernel (boundaryCompleteSlabLinks extent).length (6*localizationDegree w hw0 hw1 K))) := by
    intro term ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    exact tensorKernel_supported _ _ s hs
  have hm := haar_mono _ _ _ hs (normalizedHeatProduct_supported w hw0 K extent ids)
    (original_test_le_density hw0 hw1 K extent ids hids hn hK)
  have he : quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polySmul (half^ids.length)
        (tensorKernel (boundaryCompleteSlabLinks extent).length (6*localizationDegree w hw0 hw1 K))) ≈
      half^ids.length * (kernelMoment (6*localizationDegree w hw0 hw1 K))^(boundaryCompleteSlabLinks extent).length :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
    (Q'.mul_eqv_congr_left _ _ _ (tensorKernel_haar _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hm

/-- Computed rational floor; its volume and coupling/cutoff dependence
are retained as DATA, not concealed in a purported uniform constant. -/
def partitionFloor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) : Q' :=
  half^ids.length * (localizationFloor (6*localizationDegree w hw0 hw1 K))^(boundaryCompleteSlabLinks extent).length

theorem partitionFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) : (0 : Q') < partitionFloor w hw0 hw1 K extent ids :=
  Q'.mul_pos (HKPos.pow_pos (by decide) ids.length)
    (HKPos.pow_pos (localizationFloor_positive _) _)

/-- Computed floor below the literal identity-normalized original partition. -/
theorem normalized_partition_lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hn : ids.Nodup) (hK : finiteCutoff w ≤ K+1) :
    partitionFloor w hw0 hw1 K extent ids ≤
      quaternionHaar (boundaryCompleteSlabLinks extent).length
        (normalizedHeatProduct w hw0 K extent ids) := by
  have hs := tensorKernel_haar_lower (boundaryCompleteSlabLinks extent).length
    (6*localizationDegree w hw0 hw1 K)
  have hf := Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (tensorKernel_haar _ _))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hf (Q'.pow_nonneg half (by decide) ids.length))
    (normalized_partition_moment_lower hw0 hw1 K extent ids hids hn hK)

/-- Pin the lower bound to the EXISTING unnormalized original partition.
The reciprocal factor is identity normalization, NEVER a supplied partition. -/
theorem original_partition_normalized_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hn : ids.Nodup) (hK : finiteCutoff w ≤ K+1) :
    partitionFloor w hw0 hw1 K extent ids ≤
      normalizingFactor w hw0 K ids *
        heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K :=
  Q'.le_trans' _ _ _ (normalized_partition_lower hw0 hw1 K extent ids hids hn hK)
    (Q'.le_of_eqv (normalizedHeatProductHaar_pin w hw0 K extent ids))

/-- Undo identity normalization and bound the ACTUAL original partition.
The original heat factors, inclusive cutoff and product-Haar are unchanged. -/
theorem original_partition_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hn : ids.Nodup) (hK : finiteCutoff w ≤ K+1) :
    productCeiling w K ids * partitionFloor w hw0 hw1 K extent ids ≤
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K := by
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ _
    (original_partition_normalized_lower hw0 hw1 K extent ids hids hn hK)
    (Q'.le_of_lt (productCeiling_positive (Q'.le_of_lt hw0) K ids))
  have he : productCeiling w K ids *
      (normalizingFactor w hw0 K ids *
        heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K) ≈
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv _ _))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv he)

/-- Specialization to the COMPLETE original physical face list, not merely
an assumed nodup subaction. Every original physical action factor remains. -/
theorem complete_original_partition_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K extent : Nat)
    (hK : finiteCutoff w ≤ K+1) :
    productCeiling w K (slabPhysicalFaceEdges extent) *
        partitionFloor w hw0 hw1 K extent (slabPhysicalFaceEdges extent) ≤
      heatProductHaar w (boundaryCompleteSlabLinks extent).length extent
        (slabPhysicalFaceEdges extent) K :=
  original_partition_lower hw0 hw1 K extent (slabPhysicalFaceEdges extent)
    (fun _ h => h) (CayleyParentInj.range_nodup _) hK

end YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.original_tensor_le_occurrences
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.original_test_le_density
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.normalized_partition_moment_lower
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.partitionFloor
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.partitionFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.normalized_partition_lower
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.original_partition_normalized_lower
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.original_partition_lower
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialPartitionLower.complete_original_partition_lower
