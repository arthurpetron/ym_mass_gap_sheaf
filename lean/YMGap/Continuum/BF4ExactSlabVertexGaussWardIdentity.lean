/-
# Finite Ward identity for the full ORIGINAL slab action

The literal all-link vertex generator has zero finite product-Haar integral.
Raw Leibniz is applied to the full action times an arbitrary supported signed
test, before the produced common-padded action derivative is replaced by zero.
There is no action inverse, positivity/nome assumption or assumed invariance.
This is finite gauge symmetry, not horizontal energy, signed-cost control,
completed transfer transport or a continuum/QFT closure theorem.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction
import YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt

namespace YMGap.Continuum.BF4ExactSlabVertexGaussWardIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity (fullHeatProduct_supported)
open YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord
open YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter
open YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.SU2QuaternionLeftRightAngularAction
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "SlabB" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] boundaryCompleteSlabLinks
local infix:50 " ≈ " => Q'.eqv

private theorem haar_add_zero {blocks : Nat} {p q : RatPoly}
    (hp : quaternionHaar blocks p ≈ 0) (hq : quaternionHaar blocks q ≈ 0) :
    quaternionHaar blocks (polyAdd p q) ≈ 0 :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append blocks p q)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hp hq) (by decide))

private theorem haar_neg_zero {blocks : Nat} {p : RatPoly}
    (hp : quaternionHaar blocks p ≈ 0) : quaternionHaar blocks (polyNeg p) ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp) (by decide)))

private theorem directions (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem plane_zero {blocks block : Nat} (hb : block < blocks)
    (i j : Nat) (hi : i < 4) (hj : j < 4) (p : RatPoly) :
    quaternionHaar blocks (blockAngularDerivative block i j p) ≈ 0 :=
  quaternionHaar_angularDerivative_at hb hi hj p

private theorem left_zero {blocks block : Nat} (hb : block < blocks)
    (i : Fin 3) (p : RatPoly) :
    quaternionHaar blocks (pairedDerivativeAt block i p) ≈ 0 := by
  rcases directions i with rfl | rfl | rfl
  · exact haar_add_zero (plane_zero hb 0 1 (by decide) (by decide) p)
      (plane_zero hb 2 3 (by decide) (by decide) p)
  · exact haar_add_zero (plane_zero hb 0 2 (by decide) (by decide) p)
      (haar_neg_zero (plane_zero hb 1 3 (by decide) (by decide) p))
  · exact haar_add_zero (plane_zero hb 0 3 (by decide) (by decide) p)
      (plane_zero hb 1 2 (by decide) (by decide) p)

private theorem right_zero {blocks block : Nat} (hb : block < blocks)
    (i : Fin 3) (p : RatPoly) :
    quaternionHaar blocks (rightDerivativeAt block i p) ≈ 0 := by
  rcases directions i with rfl | rfl | rfl
  · exact haar_add_zero (plane_zero hb 0 1 (by decide) (by decide) p)
      (haar_neg_zero (plane_zero hb 2 3 (by decide) (by decide) p))
  · exact haar_add_zero (plane_zero hb 0 2 (by decide) (by decide) p)
      (plane_zero hb 1 3 (by decide) (by decide) p)
  · exact haar_add_zero (plane_zero hb 0 3 (by decide) (by decide) p)
      (haar_neg_zero (plane_zero hb 1 2 (by decide) (by decide) p))

private theorem frame_zero {blocks block : Nat} (hb : block < blocks)
    (right : Bool) (i : Fin 3) (p : RatPoly) :
    quaternionHaar blocks (frameDerivativeAt right block i p) ≈ 0 := by
  cases right
  · exact left_zero hb i p
  · exact right_zero hb i p

private theorem link_zero (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p : RatPoly)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) :
    quaternionHaar (SlabB extent) (linkGauss extent v i link p) ≈ 0 := by
  have hb := List.idxOf_lt_length_of_mem hl
  unfold linkGauss
  apply haar_add_zero
  · split
    · exact haar_neg_zero (frame_zero hb false i p)
    · exact Q'.eqv_refl 0
  · split
    · exact frame_zero hb true i p
    · exact Q'.eqv_refl 0

private theorem sum_zero (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p : RatPoly) :
    ∀ links : List Z4Link, (∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) →
      quaternionHaar (SlabB extent)
        (finitePolySum (fun link => linkGauss extent v i link p) links) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | link :: links, h => haar_add_zero
      (link_zero extent v i p link (h link List.mem_cons_self))
      (sum_zero extent v i p links (fun e he => h e (List.mem_cons_of_mem link he)))

/-- The actual finite Gauss derivation has zero Haar integral for every
signed polynomial, with no source support or action assumption. -/
theorem vertexGauss_haar_zero (extent : Nat) (v : Z4Vertex) (i : Fin 3) (p : RatPoly) :
    quaternionHaar (SlabB extent) (vertexGauss extent v i p) ≈ 0 :=
  sum_zero extent v i p (boundaryCompleteSlabLinks extent) (fun _ h => h)

/-- Exact finite Ward cancellation under the FULL original chronological
heat action. The source is arbitrary signed and supported on the SAME slab. -/
theorem original_action_ward_zero (w : Q') (K half : Nat) (v : Z4Vertex) (i : Fin 3)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (SlabB (centralExtent half)) p) :
    quaternionHaar (SlabB (centralExtent half))
      (polyMul (fullHeatProduct w K half) (vertexGauss (centralExtent half) v i p)) ≈ 0 := by
  let extent := centralExtent half
  let V := fullHeatProduct w K half
  have hV := fullHeatProduct_supported w K half
  have hkill : quaternionHaar (SlabB extent)
      (polyMul (vertexGauss extent v i V) p) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ p))
      (Q'.eqv_trans _ _ _
        ((fullHeatProduct_gauss_zero w K half v i).haar_insert
          (vertexGauss_supported extent v i hV) (by intro term ht; cases ht) p hp)
        (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right p)))
  have hsum : quaternionHaar (SlabB extent) (polyMul (vertexGauss extent v i V) p) +
      quaternionHaar (SlabB extent) (polyMul V (vertexGauss extent v i p)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (SlabB extent) _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (vertexGauss_mul extent v i V p).symm)
        (vertexGauss_haar_zero extent v i (polyMul V p)))
  have hz : (0 : Q') +
      quaternionHaar (SlabB extent) (polyMul V (vertexGauss extent v i p)) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_eqv_congr' hkill (Q'.eqv_refl _))) hsum
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_zero_add_eqv _)) hz

end YMGap.Continuum.BF4ExactSlabVertexGaussWardIdentity

#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWardIdentity.vertexGauss_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussWardIdentity.original_action_ward_zero
