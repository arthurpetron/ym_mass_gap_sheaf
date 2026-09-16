/-
# Original finite time-chain moments are iterates of the same weighted step

The chronological carrier places every spatial and kinetic factor of the
selected original action, including the joining and endpoint spatial weights.
Signed original spatial-face probes on both endpoints are pinned through
the same common temporal sweep, not reinterpreted as arbitrary messages.
Their unnormalized Haar moment is exactly a pairing with the finite iterate
of the previously constructed K/V step on one fixed spatial carrier.

This is finite signed polynomial integration. It proves no stationary vacuum,
positive normalization, completed OS operator, contraction or spectral gap.
The action is the stated selected spatial window, not a marginal of a larger
interacting action with surrounding plaquettes silently removed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier
import YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
import YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_pin spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabConnectedTemporalSweep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

/-- The first slice of the full carrier has its original placement. -/
theorem head_polynomial_pin {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p) :
    (embedding steps hw ht).polynomial p =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
        (show start ≤ extent by omega)).polynomial p := by
  apply BlockEmbedding.polynomial_head_placement
  · rw [Nat.succ_mul]; omega
  · exact fun _ hi => head_block hw ht hi
  · exact hp

/-- The first kinetic pair has its original ordered lower/upper placement. -/
theorem pair_polynomial_pin {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+(steps+1) ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width+N width) p) :
    (embedding (steps+1) hw ht).polynomial p =
      (BF4ExactSlabFixedSpatialPairCarrier.embedding hw
        (show start+1 ≤ extent by omega)).polynomial p := by
  apply BlockEmbedding.polynomial_head_placement
  · simp only [Nat.succ_mul]; omega
  · exact fun _ hi => pair_block hw ht hi
  · exact hp

/-- Removing one chronological slice gives the original tail-chain placement. -/
theorem tail_polynomial_pin {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+(steps+1) ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks ((steps+1)*N width) p) :
    (embedding (steps+1) hw ht).polynomial (liftBoundary (N width) p) =
      (embedding steps (start := start+1) hw
        (show start+1+steps ≤ extent by omega)).polynomial p := by
  apply BlockEmbedding.polynomial_liftBoundary
  · simp only [Nat.succ_mul]; omega
  · exact fun i _ => tail_block hw ht i
  · exact hp

private theorem chain_reorder (k v a g : RatPoly) :
    RatPolyCoeffEqv (polyMul k (polyMul v (polyMul a g)))
      (polyMul (polyMul v (polyMul k a)) g) :=
  (RatPolyCoeffEqv.mul_assoc k v (polyMul a g)).symm.trans
    (((RatPolyCoeffEqv.mul_comm k v).mul_right (polyMul a g)).trans
      ((RatPolyCoeffEqv.mul_assoc (polyMul v k) a g).symm.trans
        ((RatPolyCoeffEqv.mul_assoc v k a).mul_right g)))

/-- Every factor and the final insertion in the compact chain have the
same original ambient realization, coefficient-sensitively up to padding. -/
theorem chain_pin {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+steps ≤ extent) (w : Q') (K : Nat)
    (g : RatPoly) (hg : SupportedQuaternionBlocks (N width) g) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding steps hw ht).polynomial
        (chain (N width) (kineticWeight w K width) (spatialWeight w K width) steps g))
      (polyMul (ambientChain w K extent width start steps)
        ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).polynomial g)) := by
  induction steps generalizing start with
  | zero =>
      rw [chain, BlockEmbedding.polynomial_mul,
        head_polynomial_pin hw ht _ (spatialWeight_supported w K width),
        head_polynomial_pin hw ht g hg]
      exact (spatialWeight_pin hw ht w K).mul (.refl _ _)
  | succ steps ih =>
      rw [chain, BlockEmbedding.polynomial_mul, BlockEmbedding.polynomial_mul,
        pair_polynomial_pin hw ht _ (kineticWeight_supported w K width),
        head_polynomial_pin hw ht _ (spatialWeight_supported w K width),
        tail_polynomial_pin hw ht _ (chain_supported
          (kineticWeight_supported w K width) (spatialWeight_supported w K width) steps hg)]
      have htail := ih (start := start+1) (show start+1+steps ≤ extent by omega)
      have htime : start+1+steps = start+(steps+1) := by omega
      simp only [htime] at htail
      exact ((kineticWeight_pin hw (show start+1 ≤ extent by omega) w K).mul
        ((spatialWeight_pin hw (show start ≤ extent by omega) w K).mul htail)).trans
          (.of_coeff (chain_reorder _ _ _ _))

theorem ambientChain_supported (w : Q') (K extent width start steps : Nat) :
    SupportedQuaternionBlocks (B extent) (ambientChain w K extent width start steps) := by
  induction steps generalizing start with
  | zero => exact heatProduct_supported w K extent (spatialIds extent width start)
  | succ steps ih =>
      exact supported_polyMul (heatProduct_supported w K extent (spatialIds extent width start))
        (supported_polyMul (kineticHeat_supported w K extent width start) (ih (start+1)))

/-- Full finite swept-action pairing with any two supported source insertions.
The iterate uses the same K and V at every time, with no normalization. -/
theorem swept_chain_iteration {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+steps ≤ extent) (w : Q') (K : Nat)
    (f g : RatPoly) (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    quaternionHaar (B extent)
      (polyMul
        ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw
          (show start ≤ extent by omega)).polynomial f)
        (polyMul (ambientChain w K extent width start steps)
          ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).polynomial g))) ≈
      quaternionHaar (N width)
        (polyMul (iterateStep (N width) (kineticWeight w K width)
          (spatialWeight w K width) steps f) (polyMul (spatialWeight w K width) g)) := by
  let E := embedding steps hw ht
  let L := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)
  let U := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht
  let c := chain (N width) (kineticWeight w K width) (spatialWeight w K width) steps g
  have hpin : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (polyMul f c))
      (polyMul (L.polynomial f)
        (polyMul (ambientChain w K extent width start steps) (U.polynomial g))) := by
    rw [BlockEmbedding.polynomial_mul, head_polynomial_pin hw ht f hf]
    exact (PaddedPolynomialCoeffEqv.refl _ _).mul (chain_pin hw ht w K g hg)
  have hsource : SupportedQuaternionBlocks ((steps+1)*N width) (polyMul f c) :=
    supported_polyMul (support_mono hf (by rw [Nat.succ_mul]; omega))
      (chain_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) steps hg)
  have hambient := supported_polyMul (L.polynomial_supported f)
    (supported_polyMul (ambientChain_supported w K extent width start steps) (U.polynomial_supported g))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hpin.haar (E.polynomial_supported _) hambient))
    (Q'.eqv_trans _ _ _ (E.haar _ hsource)
      (chain_pairing (N width) (kineticWeight w K width) (spatialWeight w K width) steps f g))

/-- Original selected-action endpoint moments are exact iterates of the
original weighted step. Spatiality justifies the SAME temporal sweep;
the endpoint pins are constructed, not supplied as new hypotheses. -/
theorem original_chain_iteration {width start steps extent : Nat}
    (hw : width ≤ extent) (ht : start+steps ≤ extent) (w : Q') (K : Nat)
    (low high : List FaceFactor)
    (hlow : ∀ f, f ∈ low → f.1 ∈ spatialFaces width)
    (hhigh : ∀ f, f ∈ high → f.1 ∈ spatialFaces width) :
    quaternionHaar (B extent)
      (polyMul (sweptProduct extent 0
        (placeProbes start low ++ placeProbes (start+steps) high))
        (originalChainAction w K extent width start steps)) ≈
      quaternionHaar (N width)
        (polyMul (iterateStep (N width) (kineticWeight w K width)
          (spatialWeight w K width) steps (sourceProbe width low))
          (polyMul (spatialWeight w K width) (sourceProbe width high))) := by
  have hs : start ≤ extent := by omega
  let L := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw hs
  let U := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht
  let f := sourceProbe width low
  let g := sourceProbe width high
  let probes := placeProbes start low ++ placeProbes (start+steps) high
  have hp : PaddedPolynomialCoeffEqv (B extent)
      (polyMul (L.polynomial f) (U.polynomial g)) (sweptProduct extent 0 probes) :=
    ((sourceProbe_pin hw hs low hlow).mul (sourceProbe_pin hw ht high hhigh)).trans
      (.of_coeff (swept_append extent 0 _ _).symm)
  have ha := ambientChain_supported w K extent width start steps
  have hplaced := supported_polyMul (L.polynomial_supported f) (U.polynomial_supported g)
  have hprobes := product_supported (sweptCharacter extent 0)
    (swept_character_supported extent 0) probes
  have hreplace := (hp.symm.mul (.refl _ (ambientChain w K extent width start steps))).haar
    (supported_polyMul hprobes ha) (supported_polyMul hplaced ha)
  have hreorder : RatPolyCoeffEqv
      (polyMul (polyMul (L.polynomial f) (U.polynomial g)) (ambientChain w K extent width start steps))
      (polyMul (L.polynomial f) (polyMul (ambientChain w K extent width start steps) (U.polynomial g))) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).trans ((RatPolyCoeffEqv.mul_comm _ _).mul_left _)
  have horiginal := original_chain_pairing w K extent width start steps probes
    (fun p hp => (List.mem_append.mp hp).elim
      (placeProbes_physical hw hs low hlow p) (placeProbes_physical hw ht high hhigh p))
    (fun p hp => (List.mem_append.mp hp).elim
      (placeProbes_spatial start low hlow p) (placeProbes_spatial (start+steps) high hhigh p))
  exact Q'.eqv_trans _ _ _ horiginal (Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ (haar_of_coeff hreorder)
      (swept_chain_iteration hw ht w K f g
        (sourceProbe_supported width low) (sourceProbe_supported width high))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.head_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.pair_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.tail_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.chain_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.ambientChain_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.swept_chain_iteration
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration.original_chain_iteration
