/-
# Ordered Hessian expectation of the ACTUAL growing Wilson square

Two Haar integrations move all nine ordered jets off the SAME complete
weight. The selected-link source is transported through its explicit head
swap, moving the weight and source together, not identifying the weights.
The resulting signed expectation is 48*H[W]-16*H[W*Gamma_s(f)].
This is finite algebra, not a variance floor, retention or continuum theorem.
-/

import YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP
import YMGap.Continuum.BF4DyadicWilsonSquareDoubleIBP
import YMGap.Continuum.BF4ExactSlabFixedSpatialFisherVector
import YMGap.Continuum.SU2QuaternionReplicaPairBounds

namespace YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative threeSum)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP
  (gradient gradientSquare doubleIBPSource)
open YMGap.Continuum.QPolyHaarPairedAtOrderedDoubleIBP
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
  (observableBlocks observableBlocks_lt)
open YMGap.Continuum.BF4DyadicWilsonSquareDoubleIBP (paddedSquare_doubleIBPSource_48)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks marginalWeight pairedDerivativeAt

private theorem three_carrier {blocks : Nat} {p q : Fin 3 → RatPoly}
    (h : ∀ i, HaarCarrierEqv blocks (p i) (q i)) :
    HaarCarrierEqv blocks (threeSum p) (threeSum q) :=
  HaarCarrierEqv.add (h 0) (HaarCarrierEqv.add (h 1) (h 2))

private theorem three_supported {blocks : Nat} (p : Fin 3 → RatPoly)
    (hp : ∀ i, SupportedQuaternionBlocks blocks (p i)) :
    SupportedQuaternionBlocks blocks (threeSum p) :=
  supported_add (hp 0) (supported_add (hp 1) (hp 2))

private theorem reindex_three {blocks : Nat} (swap : QuaternionBlockInvolution blocks)
    (p : Fin 3 → RatPoly) :
    reindexQuaternionPolynomial swap (threeSum p) =
      threeSum (fun i => reindexQuaternionPolynomial swap (p i)) := by
  simp only [threeSum, reindexQuaternionPolynomial_add]

private theorem paired_reindex {blocks s : Nat} (hs : s < blocks)
    (i : Fin 3) (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    let swap := headSwapBlockInvolution blocks s hs
    HaarCarrierEqv blocks (pairedDerivativeAt 0 i (reindexQuaternionPolynomial swap p))
      (reindexQuaternionPolynomial swap (pairedDerivativeAt s i p)) := by
  have h0 : 0 < blocks := Nat.lt_of_le_of_lt (Nat.zero_le s) hs
  have h := chain_pairedDerivativeAt [headSwapBlockInvolution blocks s hs] h0 i p hp
  simpa only [applyQuaternionBlockSwapChain, quaternionBlockSwapChainSource,
    headSwapBlockInvolution_map_zero] using h

private theorem source_supported {blocks s : Nat} (hs : s < blocks)
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    SupportedQuaternionBlocks blocks (orderedSourceAt s u) :=
  three_supported _ (fun j => pairedDerivativeAt_supported hs j
    (three_supported _ (fun i => pairedDerivativeAt_supported hs i
      (supported_polyMul (hu i) (hu j)))))

/-- The full ordered source travels with all its polynomial coefficients.
The transport is a supported Haar-carrier identity, not raw coefficient
equality and not equality of the original and swapped integration weights. -/
theorem ordered_source_head_transport {blocks s : Nat} (hs : s < blocks)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    let swap := headSwapBlockInvolution blocks s hs
    HaarCarrierEqv blocks
      (doubleIBPSource (reindexQuaternionPolynomial swap f))
      (reindexQuaternionPolynomial swap
        (orderedSourceAt s (fun i => pairedDerivativeAt s i f))) := by
  let swap := headSwapBlockInvolution blocks s hs
  let g := fun i => pairedDerivativeAt s i f
  let head := reindexQuaternionPolynomial swap f
  let gh := fun i => pairedDerivativeAt 0 i head
  let inner := fun j => threeSum (fun i => pairedDerivativeAt s i (polyMul (g i) (g j)))
  let innerH := fun j => threeSum (fun i => pairedDerivativeAt 0 i (polyMul (gh i) (gh j)))
  have h0 : 0 < blocks := Nat.lt_of_le_of_lt (Nat.zero_le s) hs
  have hg (i : Fin 3) := pairedDerivativeAt_supported hs i hf
  have hgh (i : Fin 3) := pairedDerivativeAt_supported h0 i (reindex_supported swap f)
  have hd (i : Fin 3) : HaarCarrierEqv blocks (gh i)
      (reindexQuaternionPolynomial swap (g i)) := paired_reindex hs i f hf
  have hinner (j : Fin 3) : HaarCarrierEqv blocks (innerH j)
      (reindexQuaternionPolynomial swap (inner j)) := by
    rw [reindex_three]
    apply three_carrier
    intro i
    have hp : HaarCarrierEqv blocks (polyMul (gh i) (gh j))
        (reindexQuaternionPolynomial swap (polyMul (g i) (g j))) := by
      rw [reindexQuaternionPolynomial_mul]
      exact HaarCarrierEqv.mul (hd i) (hd j)
    exact (pairedDerivativeAt_carrier h0 i (supported_polyMul (hgh i) (hgh j))
      (reindex_supported swap _) hp).trans
      (paired_reindex hs i (polyMul (g i) (g j)) (supported_polyMul (hg i) (hg j)))
  have hi (j : Fin 3) : SupportedQuaternionBlocks blocks (inner j) :=
    three_supported _ (fun i => pairedDerivativeAt_supported hs i
      (supported_polyMul (hg i) (hg j)))
  have hih (j : Fin 3) : SupportedQuaternionBlocks blocks (innerH j) :=
    three_supported _ (fun i => pairedDerivativeAt_supported h0 i
      (supported_polyMul (hgh i) (hgh j)))
  have hsource : HaarCarrierEqv blocks (orderedSourceAt 0 gh)
      (reindexQuaternionPolynomial swap (orderedSourceAt s g)) := by
    change HaarCarrierEqv blocks (threeSum (fun j => pairedDerivativeAt 0 j (innerH j)))
      (reindexQuaternionPolynomial swap (threeSum (fun j => pairedDerivativeAt s j (inner j))))
    rw [reindex_three]
    exact three_carrier (fun j =>
      (pairedDerivativeAt_carrier h0 j (hih j) (reindex_supported swap _) (hinner j)).trans
        (paired_reindex hs j (inner j) (hi j)))
  simpa only [gh, pairedDerivativeAt_zero, orderedSourceAt_head] using hsource

private theorem gradient_head_transport {blocks s : Nat} (hs : s < blocks)
    (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
    let swap := headSwapBlockInvolution blocks s hs
    HaarCarrierEqv blocks (gradientSquare (reindexQuaternionPolynomial swap f))
      (reindexQuaternionPolynomial swap
        (threeSquare (fun i => pairedDerivativeAt s i f))) := by
  dsimp only
  let swap := headSwapBlockInvolution blocks s hs
  have hd (i : Fin 3) : HaarCarrierEqv blocks
      (pairedDerivative i (reindexQuaternionPolynomial swap f))
      (reindexQuaternionPolynomial swap (pairedDerivativeAt s i f)) := by
    simpa only [pairedDerivativeAt_zero] using paired_reindex hs i f hf
  change HaarCarrierEqv blocks (threeSum (fun i => polyMul
      (pairedDerivative i (reindexQuaternionPolynomial swap f))
      (pairedDerivative i (reindexQuaternionPolynomial swap f))))
    (reindexQuaternionPolynomial swap (threeSum (fun i => polyMul
      (pairedDerivativeAt s i f) (pairedDerivativeAt s i f))))
  rw [reindex_three]
  apply three_carrier
  intro i
  rw [reindexQuaternionPolynomial_mul]
  exact HaarCarrierEqv.mul (hd i) (hd i)

private theorem weighted_cap (blocks : Nat) (W : RatPoly) (c : Q') :
    quaternionHaar blocks (polyMul W (cap c)) ≈ c*quaternionHaar blocks W :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm W (cap c)).trans
    (cap_mul_left c W))) (quaternionHaar_polySmul blocks c W)

/-- The actual selected-link Hessian expectation for ANY supported original
weight; both W and the source move through the same head swap in the proof. -/
theorem paddedSquare_frozen_hessian_haar (scale width : Nat)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth)
    (W : RatPoly) (hW : SupportedQuaternionBlocks (N width) W) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let u := fun i => pairedDerivativeAt block i f
    quaternionHaar (N width) (frozenSecondAt block u W) ≈
      48*quaternionHaar (N width) W +
        (-16)*quaternionHaar (N width) (polyMul W (threeSquare u)) := by
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let hs := observableBlocks_lt scale width hwidth block hb
  let swap := headSwapBlockInvolution (N width) block hs
  let u := fun i => pairedDerivativeAt block i f
  let source := orderedSourceAt block u
  let energy := threeSquare u
  let W' := reindexQuaternionPolynomial swap W
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hu (i : Fin 3) := pairedDerivativeAt_supported hs i hf
  have hsource := source_supported hs u hu
  have henergy : SupportedQuaternionBlocks (N width) energy :=
    three_supported _ (fun i => supported_polyMul (hu i) (hu i))
  have htransport := ordered_source_head_transport hs f hf
  have hpin := paddedSquare_doubleIBPSource_48 scale width hwidth block hb
  have hsigned := htransport.symm.trans hpin
  have hswap : quaternionHaar (N width) (polyMul W source) ≈
      quaternionHaar (N width) (polyMul W' (reindexQuaternionPolynomial swap source)) := by
    have h := quaternionHaar_reindex swap (polyMul W source) (supported_polyMul hW hsource)
    rw [reindexQuaternionPolynomial_mul] at h
    exact Q'.eqv_symm h
  have hsplit : quaternionHaar (N width) (polyMul W'
      (polyAdd (cap 48) (polySmul (-16) (gradientSquare (reindexQuaternionPolynomial swap f))))) ≈
      48*quaternionHaar (N width) W' +
        (-16)*quaternionHaar (N width)
          (polyMul W' (gradientSquare (reindexQuaternionPolynomial swap f))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W' _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
        (Q'.add_eqv_congr' (weighted_cap (N width) W' 48)
          (quaternionHaar_polyMul_smul_right (N width) (-16) W' _)))
  have hg : quaternionHaar (N width)
      (polyMul W' (gradientSquare (reindexQuaternionPolynomial swap f))) ≈
      quaternionHaar (N width) (polyMul W energy) := by
    have h := quaternionHaar_reindex swap (polyMul W energy) (supported_polyMul hW henergy)
    rw [reindexQuaternionPolynomial_mul] at h
    exact Q'.eqv_trans _ _ _ ((gradient_head_transport hs f hf) W') h
  exact Q'.eqv_trans _ _ _ (frozenSecondAt_haar_ordered_source hs W u)
    (Q'.eqv_trans _ _ _ hswap (Q'.eqv_trans _ _ _ (hsigned W')
      (Q'.eqv_trans _ _ _ hsplit (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left 48 _ _ (quaternionHaar_reindex swap W hW))
        (Q'.mul_eqv_congr_left (-16) _ _ hg)))))

/-- Specialization to the literal complete original odd marginal, preserving
all spatial factors and both chronological messages, including depth zero. -/
theorem paddedSquare_original_frozen_hessian_haar (w : Q') (K width n scale : Nat)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let W := marginalWeight w K width n
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let u := fun i => pairedDerivativeAt block i f
    quaternionHaar (N width) (frozenSecondAt block u W) ≈
      48*quaternionHaar (N width) W +
        (-16)*quaternionHaar (N width) (polyMul W (threeSquare u)) :=
  paddedSquare_frozen_hessian_haar scale width hwidth block hb
    (marginalWeight w K width n) (marginalWeight_supported w K width n)

end YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian.ordered_source_head_transport
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian.paddedSquare_frozen_hessian_haar
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareFisherHessian.paddedSquare_original_frozen_hessian_haar
