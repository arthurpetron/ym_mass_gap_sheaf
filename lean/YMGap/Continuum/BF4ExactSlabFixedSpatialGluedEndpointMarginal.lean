/-
# Exact endpoint marginal of the original two-layer middle integral

The actual K01*V1*K12 middle action is placed on three chronological
copies of the original slice carrier. Ordered Haar Fubini, the exact
kinetic marginal, and kinetic symmetry identify its lower endpoint test
with the original transferStep applied to one. V1 is retained ONCE;
the outside endpoint factors V0 and V2 are not part of gluedMiddle.

This is an unnormalized finite polynomial/Haar identity at every nome and
cutoff. It constructs neither a normalized fine/coarse comparison nor a
changing-scale gap. The compressed boundary carrier keeps its existing
order; no identification with two consecutive canonical slices is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
import YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryCarrier
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection (correctedSlabLinkAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported spatialWeight_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (kineticWeight_lower_marginal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry (kineticWeight_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction
  (kineticMap kineticMap_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (kernel_pairing_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors (EndpointLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

private theorem exponent_zero : ∀ (m : List Nat) (c : Nat),
    m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero m c (by simp only [List.length_cons] at h; omega)

/-- An injectively placed supported polynomial uses only its original image. -/
theorem placed_image_local {source target : Nat} (E : BlockEmbedding source target)
    {p : RatPoly} (hp : SupportedQuaternionBlocks source p) :
    BlockLocal target (fun b => b ∈ E.image) (E.polynomial p) := by
  intro term hm b hb hn c hc
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
  rw [E.exponent_pin original.1 (by omega),
    show (4*b+c)/4 = b by omega, show (4*b+c)%4 = c by omega,
    E.index_not_mem hn]
  exact exponent_zero original.1 _ (Nat.le_trans (hp original ho) (by omega))

/-- Endpoint-local tests can be pulled through the actual middle integral,
without introducing or cancelling either endpoint spatial factor. -/
theorem endpoint_test_gluing (w : Q') (K extent width start : Nat) (p : RatPoly)
    (hp : BlockLocal (B extent)
      (fun b => EndpointLink start (correctedSlabLinkAt extent b)) p) :
    quaternionHaar (B extent) (polyMul p (middleIntegrand w K extent width start)) ≈
      quaternionHaar (B extent) (polyMul p (gluedMiddle w K extent width start)) := by
  apply quaternionHaar_polyMul_eq_after_integratingBlocks_of_local hp
  intro b hb
  have hm := List.mem_filter.mp hb
  have ht := (of_decide_eq_true hm.2).2
  refine ⟨List.mem_range.mp hm.1, ?_⟩
  intro he
  rcases he.2 with he | he <;> omega

/-- Three canonical slices retain the complete K01*V1*K12 factor. -/
theorem chronological_middle_pairing (w : Q') (K width : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar ((N width+N width)+N width)
      (polyMul p (polyMul (kineticWeight w K width)
        (liftBoundary (N width)
          (polyMul (spatialWeight w K width) (kineticWeight w K width))))) ≈
      quaternionHaar (N width) (polyMul p (transferStep w K width polyOne)) := by
  let k := kineticWeight w K width
  let v := spatialWeight w K width
  let f := kineticMap w K width p
  have hv := spatialWeight_supported w K width
  have hf := kineticMap_supported w K width hp
  have hfirst := haar_of_coeff (blocks := (N width+N width)+N width)
    ((RatPolyCoeffEqv.mul_assoc p k (liftBoundary (N width) (polyMul v k))).symm.trans
      ((RatPolyCoeffEqv.mul_comm p k).mul_right (liftBoundary (N width) (polyMul v k))))
  have hhead := head_pairing (N width+N width) (N width) (polyMul k p) (polyMul v k)
  have hreorder := haar_of_coeff (blocks := N width+N width)
    ((RatPolyCoeffEqv.mul_assoc f v k).symm.trans
      ((RatPolyCoeffEqv.mul_comm (polyMul f v) k).trans
        ((RatPolyCoeffEqv.mul_comm f v).mul_left k)))
  have hpeel := kineticWeight_lower_marginal w K width (polyMul v f)
    (supported_polyMul hv hf)
  have hcomm := haar_of_coeff (blocks := N width) (RatPolyCoeffEqv.mul_comm v f)
  have hback := Q'.eqv_symm
    (head_pairing (N width) (N width) (polyMul k p) v)
  have hswap := kernel_pairing_swap (kineticWeight_supported w K width) hp hv
    (kineticWeight_swap w K width)
  have hunit := haar_of_coeff (blocks := N width+N width)
    (((RatPolyCoeffEqv.mul_one v).symm.mul_left k).mul_right (liftBoundary (N width) p))
  have hstep := step_pairing (N width) (N width) k v polyOne p
  have hlast := haar_of_coeff (blocks := N width)
    (RatPolyCoeffEqv.mul_comm (transferStep w K width polyOne) p)
  exact Q'.eqv_trans _ _ _ hfirst (Q'.eqv_trans _ _ _ hhead
    (Q'.eqv_trans _ _ _ hreorder (Q'.eqv_trans _ _ _ hpeel
      (Q'.eqv_trans _ _ _ hcomm (Q'.eqv_trans _ _ _ hback
        (Q'.eqv_trans _ _ _ hswap (Q'.eqv_trans _ _ _ hunit
          (Q'.eqv_trans _ _ _ hstep hlast))))))))

/-- The chronological three-slice polynomial is the actual ambient middle
integrand, with the original geometric containment guards. -/
theorem chronological_middle_pin {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+2 ≤ extent) (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv (B extent)
      ((BF4ExactSlabFixedSpatialChainCarrier.embedding 2 hw ht).polynomial
        (polyMul (kineticWeight w K width)
          (liftBoundary (N width)
            (polyMul (spatialWeight w K width) (kineticWeight w K width)))))
      (middleIntegrand w K extent width start) := by
  have hv := spatialWeight_supported w K width
  have hk := kineticWeight_supported w K width
  have hvk := supported_polyMul (support_mono hv (by omega)) hk
  rw [BlockEmbedding.polynomial_mul, pair_polynomial_pin hw ht _ hk,
    tail_polynomial_pin hw ht _ (show SupportedQuaternionBlocks (2*(N width))
      (polyMul (spatialWeight w K width) (kineticWeight w K width)) by
        simpa only [Nat.succ_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_add] using hvk),
    BlockEmbedding.polynomial_mul, head_polynomial_pin hw
      (show start+1+1 ≤ extent by omega) _ hv,
    pair_polynomial_pin hw (show start+1+(0+1) ≤ extent by omega) _ hk]
  exact (kineticWeight_pin hw (show start+1 ≤ extent by omega) w K).mul
    ((spatialWeight_pin hw (show start+1 ≤ extent by omega) w K).mul
      (kineticWeight_pin hw (show start+1+1 ≤ extent by omega) w K))

/-- The ORIGINAL ambient glued middle, tested at its lower endpoint, is
exactly the first original transfer message. Outside V0 and V2 remain outside. -/
theorem glued_lower_endpoint_pairing {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+2 ≤ extent) (w : Q') (K : Nat)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar (B extent)
      (polyMul
        ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
          (show start ≤ extent by omega)).polynomial p)
        (gluedMiddle w K extent width start)) ≈
      quaternionHaar (N width) (polyMul p (transferStep w K width polyOne)) := by
  let E := BF4ExactSlabFixedSpatialChainCarrier.embedding 2 hw ht
  let L := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)
  let c := polyMul (kineticWeight w K width)
    (liftBoundary (N width) (polyMul (spatialWeight w K width) (kineticWeight w K width)))
  have hlocal : BlockLocal (B extent)
      (fun b => EndpointLink start (correctedSlabLinkAt extent b)) (L.polynomial p) := by
    intro term hm b hb hn
    apply placed_image_local L hp term hm b hb
    intro hi
    have hs := (BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff hw
      (show start ≤ extent by omega) hb).mp hi
    exact hn ⟨hs.1, Or.inl hs.2.2.2.2⟩
  have hglue := Q'.eqv_symm (endpoint_test_gluing w K extent width start _ hlocal)
  have hpin : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (polyMul p c))
      (polyMul (L.polynomial p) (middleIntegrand w K extent width start)) := by
    rw [BlockEmbedding.polynomial_mul, head_polynomial_pin hw ht p hp]
    exact (PaddedPolynomialCoeffEqv.refl _ _).mul (chronological_middle_pin hw ht w K)
  have hc : SupportedQuaternionBlocks (3*(N width)) c := by
    apply supported_polyMul
    · exact support_mono (kineticWeight_supported w K width) (by omega)
    · have h := lift_supported (supported_polyMul
        (support_mono (spatialWeight_supported w K width) (by omega))
        (kineticWeight_supported w K width)) (N width)
      simpa only [Nat.succ_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_assoc] using h
  have hsource := supported_polyMul (support_mono hp (show N width ≤ 3*(N width) by omega)) hc
  have hambient := supported_polyMul (L.polynomial_supported p)
    (middleIntegrand_supported w K extent width start)
  have hfinite : quaternionHaar (3*(N width)) (polyMul p c) ≈
      quaternionHaar (N width) (polyMul p (transferStep w K width polyOne)) := by
    simpa only [Nat.succ_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_assoc] using
      chronological_middle_pairing w K width hp
  have hhaar := E.haar _ hsource
  exact Q'.eqv_trans _ _ _ hglue (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (hpin.haar (E.polynomial_supported _) hambient))
      (Q'.eqv_trans _ _ _ hhaar hfinite))

/-- The SAME endpoint test on the already computed compressed kernel.
Compression reads the original ambient coordinates; the boundary list is
not assumed to be ordered lower-then-upper. -/
theorem compressed_lower_endpoint_pairing {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+2 ≤ extent) (w : Q') (K : Nat)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar (BF4ExactSlabFixedSpatialBoundaryCarrier.baseLinks width).length
      (polyMul
        ((BF4ExactSlabFixedSpatialBoundaryCarrier.embedding hw ht).compress
          ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
            (show start ≤ extent by omega)).polynomial p))
        (BF4ExactSlabFixedSpatialBoundaryCarrier.kernel hw ht w K)) ≈
      quaternionHaar (N width) (polyMul p (transferStep w K width polyOne)) := by
  let E := BF4ExactSlabFixedSpatialBoundaryCarrier.embedding hw ht
  let L := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)
  let q := E.compress (L.polynomial p)
  let k := BF4ExactSlabFixedSpatialBoundaryCarrier.kernel hw ht w K
  have hlocal : BlockLocal (B extent) (fun b => b ∈ E.image) (L.polynomial p) := by
    intro term hm b hb hn
    apply placed_image_local L hp term hm b hb
    intro hi
    have hs := (BF4ExactSlabFixedSpatialSliceCarrier.embedding_mem_iff hw
      (show start ≤ extent by omega) hb).mp hi
    exact hn ((BF4ExactSlabFixedSpatialBoundaryCarrier.embedding_mem_iff hw ht hb).mpr
      (Or.inl hs))
  have htest := E.polynomial_compress_prefix (L.polynomial p) hlocal
  have hkernel := BF4ExactSlabFixedSpatialBoundaryCarrier.kernel_reconstructs hw ht w K
  have hpin : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (polyMul q k))
      (polyMul (L.polynomial p) (gluedMiddle w K extent width start)) := by
    rw [BlockEmbedding.polynomial_mul]
    exact .of_prefix (htest.mul hkernel)
  have hsource := supported_polyMul (E.compress_supported (L.polynomial p))
    (BF4ExactSlabFixedSpatialBoundaryCarrier.kernel_supported hw ht w K)
  have hambient := supported_polyMul (L.polynomial_supported p)
    (gluedMiddle_supported w K extent width start)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (E.haar (polyMul q k) hsource))
    (Q'.eqv_trans _ _ _ (hpin.haar (E.polynomial_supported _) hambient)
      (glued_lower_endpoint_pairing hw ht w K hp))

end YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal.placed_image_local
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal.endpoint_test_gluing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal.chronological_middle_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal.chronological_middle_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal.glued_lower_endpoint_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGluedEndpointMarginal.compressed_lower_endpoint_pairing
