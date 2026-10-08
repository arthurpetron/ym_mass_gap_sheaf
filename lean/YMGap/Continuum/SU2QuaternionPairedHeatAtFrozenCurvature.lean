/-
# Produced frozen curvature at the ORIGINAL selected heat pair

The entire polynomial direction and all nine ordered jets travel through
the explicit pair chart. The reverse chart returns a certificate for the
literal heatAt a b at its FIRST endpoint, which may be a surviving OUTPUT
block. The same fixed-nome cost/onset is retained; there is no volume or
inverse-floor loss. Frozen coefficients are never differentiated.

This removes the arbitrary-block recoding input of the local original
conditional-score route. Retaining the full interacting spectator action,
identifying its marginal jets, OS and scaling are separate joins.
-/

import YMGap.Continuum.SU2QuaternionPairedFrameAt
import YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData

namespace YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionFourBlockSelection (chain_mul)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarMixedAngularTransport (chain_carrier)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative threeSum)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (firstJet jetCurvature)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (reindex_cap_carrier)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData (relativeHeat_eq_prefix)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit (pairedPrefix)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature

/-- Direct actual first and all ordered second jets at this original block. -/
def frozenCurvatureAt (block : Nat) (C : Q') (p : RatPoly)
    (u : Fin 3 → RatPoly) : RatPoly :=
  jetCurvature C p (fun i => pairedDerivativeAt block i p)
    (fun i j => pairedDerivativeAt block i (pairedDerivativeAt block j p)) u

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem three_supported {blocks : Nat} {f : Fin 3 → RatPoly}
    (hf : ∀ i, SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (threeSum f) :=
  supported_add (hf 0) (supported_add (hf 1) (hf 2))

theorem frozenCurvatureAt_supported {blocks block : Nat} (hb : block < blocks)
    (C : Q') {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p)
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    SupportedQuaternionBlocks blocks (frozenCurvatureAt block C p u) := by
  have hd := fun i => pairedDerivativeAt_supported hb i hp
  have hdd := fun i j => pairedDerivativeAt_supported hb i (hd j)
  have hfirst := three_supported (fun i => supported_polyMul (hu i) (hd i))
  have hsecond := three_supported (fun i => three_supported (fun j =>
    supported_polyMul (supported_polyMul (hu i) (hu j)) (hdd i j)))
  have hnorm := three_supported (fun i => supported_polyMul (hu i) (hu i))
  exact supported_add
    (supported_polyMul (polySmul_supported (supported_one blocks) C)
      (supported_polyMul hnorm (supported_polyMul hp hp)))
    (supported_add (supported_polyMul hp hsecond)
      (support_neg (supported_polyMul hfirst hfirst)))

private theorem three_carrier {blocks : Nat} {f g : Fin 3 → RatPoly}
    (h : ∀ i, HaarCarrierEqv blocks (f i) (g i)) :
    HaarCarrierEqv blocks (threeSum f) (threeSum g) :=
  HaarCarrierEqv.add (h 0) (HaarCarrierEqv.add (h 1) (h 2))

private theorem chain_three {blocks : Nat} (ss : List (QuaternionBlockInvolution blocks))
    (f : Fin 3 → RatPoly) :
    applyQuaternionBlockSwapChain ss (threeSum f) =
      threeSum (fun i => applyQuaternionBlockSwapChain ss (f i)) := by
  simp only [threeSum, chain_add]

private theorem chain_cap {blocks : Nat} (ss : List (QuaternionBlockInvolution blocks))
    (C : Q') : HaarCarrierEqv blocks (applyQuaternionBlockSwapChain ss (cap C)) (cap C) := by
  have hc : SupportedQuaternionBlocks blocks (cap C) := polySmul_supported (supported_one blocks) C
  induction ss with
  | nil => exact HaarCarrierEqv.refl _ _
  | cons s rest ih =>
      exact (chain_carrier rest (reindex_supported s _) hc (reindex_cap_carrier s C)).trans ih

private def chain_certificate {blocks : Nat} :
    (ss : List (QuaternionBlockInvolution blocks)) → {p : RatPoly} →
    SupportedQuaternionBlocks blocks p → Certificate blocks p →
    Certificate blocks (applyQuaternionBlockSwapChain ss p)
  | [], _, _, P => P
  | s::ss, p, hp, P =>
      chain_certificate ss (reindex_supported s p) (reindex_certificate s hp P)

/-- Charting the literal curvature charts coefficients only AFTER jets. -/
theorem chain_frozenCurvatureAt {blocks block : Nat}
    (ss : List (QuaternionBlockInvolution blocks)) (hb : block < blocks)
    (C : Q') (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (u : Fin 3 → RatPoly) :
    HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain ss
        (frozenCurvatureAt (quaternionBlockSwapChainSource ss block) C p u))
      (frozenCurvatureAt block C (applyQuaternionBlockSwapChain ss p)
        (fun i => applyQuaternionBlockSwapChain ss (u i))) := by
  have hfirst : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain ss
        (firstJet u (fun i => pairedDerivativeAt (quaternionBlockSwapChainSource ss block) i p)))
      (firstJet (fun i => applyQuaternionBlockSwapChain ss (u i))
        (fun i => pairedDerivativeAt block i (applyQuaternionBlockSwapChain ss p))) := by
    simp only [firstJet, chain_three, chain_mul]
    exact three_carrier (fun i => HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
      (chain_pairedDerivativeAt ss hb i p hp).symm)
  have hsecond : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain ss
        (quadraticForm u (fun i j => pairedDerivativeAt (quaternionBlockSwapChainSource ss block) i
          (pairedDerivativeAt (quaternionBlockSwapChainSource ss block) j p))))
      (quadraticForm (fun i => applyQuaternionBlockSwapChain ss (u i))
        (fun i j => pairedDerivativeAt block i
          (pairedDerivativeAt block j (applyQuaternionBlockSwapChain ss p)))) := by
    simp only [quadraticForm, chain_three, chain_mul]
    exact three_carrier (fun i => three_carrier (fun j =>
      HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) (chain_pairedSecondAt ss hb i j p hp).symm))
  have hnorm : applyQuaternionBlockSwapChain ss (threeSquare u) =
      threeSquare (fun i => applyQuaternionBlockSwapChain ss (u i)) := by
    simp only [threeSquare, chain_add, chain_mul]
  unfold frozenCurvatureAt jetCurvature
  simp only [chain_add, chain_mul, chain_neg, hnorm]
  exact HaarCarrierEqv.add
    (HaarCarrierEqv.mul (chain_cap ss C) (HaarCarrierEqv.refl _ _))
    (HaarCarrierEqv.add (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) hsecond)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hfirst hfirst)))

private theorem curvature_jet_carrier {blocks : Nat} (C : Q')
    {p q : RatPoly} {dp dq : Fin 3 → RatPoly} {ddp ddq : Fin 3 → Fin 3 → RatPoly}
    (u : Fin 3 → RatPoly) (h : HaarCarrierEqv blocks p q)
    (hd : ∀ i, HaarCarrierEqv blocks (dp i) (dq i))
    (hdd : ∀ i j, HaarCarrierEqv blocks (ddp i j) (ddq i j)) :
    HaarCarrierEqv blocks (jetCurvature C p dp ddp u) (jetCurvature C q dq ddq u) := by
  have hf := three_carrier (fun i => HaarCarrierEqv.mul (HaarCarrierEqv.refl blocks (u i)) (hd i))
  exact HaarCarrierEqv.add
    (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) (HaarCarrierEqv.mul h h)))
    (HaarCarrierEqv.add
      (HaarCarrierEqv.mul h (three_carrier (fun i => three_carrier (fun j =>
        HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) (hdd i j)))))
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hf hf)))

/-- Produced SAME original-packet curvature at ANY distinct selected pair,
with the FIRST endpoint differentiated and the original onset/cost intact. -/
def heatAt_frozen_curvature_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (a b : Fin blocks) (hab : a.val ≠ b.val)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixFrozenCurvatureCutoff w ≤ K)
    (u : Fin 3 → RatPoly) (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (frozenCurvatureAt a.val (prefixCurvatureCost w)
      (heatAt a.val b.val w K) u) := by
  let ss := pairSteps hb a b
  let p := heatAt a.val b.val w K
  let g := applyQuaternionBlockSwapChain ss p
  let v := fun i => applyQuaternionBlockSwapChain ss (u i)
  have hp := heat_supported a.isLt b.isLt w K
  have hg := applyQuaternionBlockSwapChain_supported ss p hp
  have hprefix : SupportedQuaternionBlocks blocks (pairedPrefix w K) :=
    (SU2QuaternionPairedHeatPrefixDeficit.prefix_value_interval hb hw0 hw1 K).support
  have hheat : HaarCarrierEqv blocks g (pairedPrefix w K) := by
    apply carrier_of_supported hg hprefix
    intro r hr
    simpa only [relativeHeat_eq_prefix, pairedPrefix] using
      (heat_exposed hb a b hab w K).haar_insert hg
        (heat_supported (by omega : 0 < blocks) hb w K) r hr
  have hfirst (i : Fin 3) : HaarCarrierEqv blocks
      (pairedDerivativeAt 0 i g) (pairedDerivative i (pairedPrefix w K)) := by
    rw [← pairedDerivativeAt_zero i (pairedPrefix w K)]
    exact pairedDerivativeAt_carrier (by omega) i hg hprefix hheat
  have hsecond (i j : Fin 3) : HaarCarrierEqv blocks
      (pairedDerivativeAt 0 i (pairedDerivativeAt 0 j g))
      (pairedDerivative i (pairedDerivative j (pairedPrefix w K))) := by
    rw [← pairedDerivativeAt_zero j (pairedPrefix w K),
      ← pairedDerivativeAt_zero i (pairedDerivativeAt 0 j (pairedPrefix w K))]
    exact pairedDerivativeAt_carrier (by omega) i
      (pairedDerivativeAt_supported (by omega) j hg)
      (pairedDerivativeAt_supported (by omega) j hprefix) (by
        simpa only [pairedDerivativeAt_zero] using hfirst j)
  have hchart := chain_frozenCurvatureAt ss (by omega : 0 < blocks)
    (prefixCurvatureCost w) p hp u
  rw [pair_zero hb a b hab] at hchart
  have hcanon := curvature_jet_carrier (prefixCurvatureCost w) v hheat hfirst hsecond
  let Q := prefix_frozen_curvature_certificate hb hw0 hw1 K hK v
    (fun i => applyQuaternionBlockSwapChain_supported ss (u i) (hu i))
  let chartCert := Certificate.transport (hchart.trans hcanon) Q
  have hcurv := frozenCurvatureAt_supported a.isLt (prefixCurvatureCost w) hp u hu
  have hchartSup := applyQuaternionBlockSwapChain_supported ss _ hcurv
  have hinv : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain ss.reverse (applyQuaternionBlockSwapChain ss
        (frozenCurvatureAt a.val (prefixCurvatureCost w) p u)))
      (frozenCurvatureAt a.val (prefixCurvatureCost w) p u) :=
    carrierOfPrefix (applyQuaternionBlockSwapChain_supported ss.reverse _ hchartSup)
      hcurv (reverse_apply_inverse_prefix ss _)
  exact Certificate.transport hinv.symm (chain_certificate ss.reverse hchartSup chartCert)

end YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature

#print axioms YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature.frozenCurvatureAt_supported
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature.chain_frozenCurvatureAt
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatAtFrozenCurvature.heatAt_frozen_curvature_certificate
