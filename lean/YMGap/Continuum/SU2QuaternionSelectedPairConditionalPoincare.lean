/-
# Conditional angular Poincare at an ORIGINAL distinct selected pair

The actual two-swap pair chart acts on the entire source and output weight.
Projection commutes coefficientwise with that chart; angular squares commute
in the supported prefix relation. The exposed heat packet is transported
only through its proved supported Haar-carrier equality. Thus the checked
slot-0/1 inequality applies without a universal headMap identification or
discarding an existing output/spectator variable.

The onset is computed from the charted ORIGINAL signed source. This is a
finite selected-link reference bound, not an interacting relative-rate or
changing-family/scaling/QFT claim.
-/

import YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionHaarCarrierProjection
import YMGap.Continuum.SU2QuaternionAngularReindex

namespace YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord (QuaternionPrefixPolynomialEqv.reindex)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarCarrierProjection
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionConditionalAngularPoincare (poincareCutoff)
open YMGap.Continuum.SU2QuaternionSelectedConditionalPoincare

local infix:50 " ≈ " => Q'.eqv

def pairChart (tail : Nat) (ht : 0 < tail) (i j : Fin (tail+1))
    (p : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain (pairSteps (Nat.succ_lt_succ ht) i j) p

def selectedPairMean (i j : Nat) (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  project i (polyMul (heatAt i j w K) p)

def selectedPairVariance (i j : Nat) (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (selectedPairMean i j w K (polyMul p p))
    (polyNeg (polyMul (selectedPairMean i j w K p) (selectedPairMean i j w K p)))

def selectedPairCutoff (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (p : RatPoly) : Nat :=
  poincareCutoff tail (pairChart tail ht i j p)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem chain_add {blocks : Nat} (ss : List (QuaternionBlockInvolution blocks))
    (p q : RatPoly) : applyQuaternionBlockSwapChain ss (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain ss p) (applyQuaternionBlockSwapChain ss q) := by
  induction ss generalizing p q with
  | nil => rfl
  | cons s ss ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_add, ih]

private theorem chain_neg {blocks : Nat} (ss : List (QuaternionBlockInvolution blocks))
    (p : RatPoly) : applyQuaternionBlockSwapChain ss (polyNeg p) =
      polyNeg (applyQuaternionBlockSwapChain ss p) := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
      simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_neg, ih]

private theorem chain_prefix {blocks : Nat} (ss : List (QuaternionBlockInvolution blocks))
    {p q : RatPoly} (h : QuaternionPrefixPolynomialEqv blocks p q) :
    QuaternionPrefixPolynomialEqv blocks (applyQuaternionBlockSwapChain ss p)
      (applyQuaternionBlockSwapChain ss q) := by
  induction ss generalizing p q with
  | nil => exact h
  | cons s ss ih => exact ih (QuaternionPrefixPolynomialEqv.reindex s h)

/-- Literal conditional projection transport; unlike angular recoding this
is coefficient-strength, even before supported Haar pairing. -/
theorem chain_project {blocks target : Nat} (ss : List (QuaternionBlockInvolution blocks))
    (ht : target < blocks) (p : RatPoly) :
    RatPolyCoeffEqv
      (applyQuaternionBlockSwapChain ss
        (project (quaternionBlockSwapChainSource ss target) p))
      (project target (applyQuaternionBlockSwapChain ss p)) := by
  induction ss generalizing p with
  | nil => exact .refl _
  | cons s ss ih =>
      let k := quaternionBlockSwapChainSource ss target
      have hk : k < blocks := quaternionBlockSwapChainSource_lt ss ht
      have hf := reindex_integrateQuaternionBlock s (s.map k) (s.map_lt k hk) p
      rw [s.involutive k hk] at hf
      change RatPolyCoeffEqv
        (applyQuaternionBlockSwapChain ss
          (reindexQuaternionPolynomial s (project (s.map k) p)))
        (project target (applyQuaternionBlockSwapChain ss (reindexQuaternionPolynomial s p)))
      exact (chain_coeff ss hf).trans (ih (reindexQuaternionPolynomial s p))

private theorem six_prefix {blocks : Nat} {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → QuaternionPrefixPolynomialEqv blocks (f i j) (g i j)) :
    QuaternionPrefixPolynomialEqv blocks (six f) (six g) :=
  (h 0 1 (by decide) (by decide)).append
    ((h 0 2 (by decide) (by decide)).append
      ((h 0 3 (by decide) (by decide)).append
        ((h 1 2 (by decide) (by decide)).append
          ((h 1 3 (by decide) (by decide)).append (h 2 3 (by decide) (by decide))))))

private theorem reindex_square_prefix {blocks block : Nat}
    (s : QuaternionBlockInvolution blocks) (hb : block < blocks) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial s (blockAngularSquare (s.map block) p))
      (blockAngularSquare block (reindexQuaternionPolynomial s p)) := by
  simpa only [blockAngularSquare, six, reindexQuaternionPolynomial_add,
    reindexQuaternionPolynomial_mul] using
    (six_prefix (fun i j hi hj =>
      (reindex_blockAngularDerivative_prefix s hb hi hj p).mul
        (reindex_blockAngularDerivative_prefix s hb hi hj p)))

theorem chain_blockAngularSquare_prefix {blocks target : Nat}
    (ss : List (QuaternionBlockInvolution blocks)) (ht : target < blocks) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain ss
        (blockAngularSquare (quaternionBlockSwapChainSource ss target) p))
      (blockAngularSquare target (applyQuaternionBlockSwapChain ss p)) := by
  induction ss generalizing p with
  | nil => exact .refl _ _
  | cons s ss ih =>
      exact (chain_prefix ss (reindex_square_prefix s
        (quaternionBlockSwapChainSource_lt ss ht) p)).trans
        (ih (reindexQuaternionPolynomial s p))

private def chain_certificate {blocks : Nat} :
    (ss : List (QuaternionBlockInvolution blocks)) → {p : RatPoly} →
    SupportedQuaternionBlocks blocks p → Certificate blocks p →
    Certificate blocks (applyQuaternionBlockSwapChain ss p)
  | [], _, _, P => P
  | s::ss, p, hp, P =>
      chain_certificate ss (reindex_supported s p) (reindex_certificate s hp P)

private theorem padded_carrier {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : PaddedPolynomialCoeffEqv blocks p q) : HaarCarrierEqv blocks p q := by
  apply carrier_of_supported hp hq
  intro r hr
  exact h.haar_insert hp hq r hr

private theorem mean_chart_pin (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q') (K : Nat)
    (p : RatPoly) (_hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (pairChart tail ht i j (selectedPairMean i.val j.val w K p))
      (selectedMean w K (pairChart tail ht i j p)) := by
  let ss := pairSteps (Nat.succ_lt_succ ht) i j
  have hc := chain_project ss (Nat.zero_lt_succ tail) (polyMul (heatAt i.val j.val w K) p)
  rw [pair_zero (Nat.succ_lt_succ ht) i j hij, chain_mul] at hc
  have hheat := padded_carrier
    (applyQuaternionBlockSwapChain_supported ss _ (heat_supported i.isLt j.isLt w K))
    (heat_supported (a := 0) (b := 1) (Nat.zero_lt_succ tail) (Nat.succ_lt_succ ht) w K)
    (heat_exposed (Nat.succ_lt_succ ht) i j hij w K)
  exact (RatPolyCoeffEqv.haarCarrier hc).trans
    (project_preserves_haarCarrierEqv (tail+1) 0 (Nat.zero_lt_succ tail)
      (HaarCarrierEqv.mul_right (pairChart tail ht i j p) hheat))

theorem selectedPairVariance_chart_pin (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q') (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hW : SupportedQuaternionBlocks (tail+1) W) :
    quaternionHaar (tail+1) (polyMul W (selectedPairVariance i.val j.val w K p)) ≈
      quaternionHaar (tail+1) (polyMul (pairChart tail ht i j W)
        (selectedVariance w K (pairChart tail ht i j p))) := by
  let ss := pairSteps (Nat.succ_lt_succ ht) i j
  have hm := mean_chart_pin tail ht i j hij w K p hp
  have hsq := mean_chart_pin tail ht i j hij w K (polyMul p p) (supported_polyMul hp hp)
  have hv := HaarCarrierEqv.add hsq (HaarCarrierEqv.neg (HaarCarrierEqv.mul hm hm))
  have hpMean : SupportedQuaternionBlocks (tail+1) (selectedPairMean i.val j.val w K p) :=
    project_supported i.val (supported_polyMul (heat_supported i.isLt j.isLt w K) hp)
  have hpSq : SupportedQuaternionBlocks (tail+1)
      (selectedPairMean i.val j.val w K (polyMul p p)) :=
    project_supported i.val (supported_polyMul (heat_supported i.isLt j.isLt w K)
      (supported_polyMul hp hp))
  have hpVar := supported_add hpSq (support_neg (supported_polyMul hpMean hpMean))
  have hchange := Q'.eqv_symm (quaternionHaar_applyQuaternionBlockSwapChain ss
    (polyMul W (selectedPairVariance i.val j.val w K p)) (supported_polyMul hW hpVar))
  rw [chain_mul] at hchange
  have hpin : HaarCarrierEqv (tail+1)
      (pairChart tail ht i j (selectedPairVariance i.val j.val w K p))
      (selectedVariance w K (pairChart tail ht i j p)) := by
    simpa only [selectedPairVariance, selectedVariance, pairChart, chain_add, chain_neg,
      chain_mul] using hv
  exact Q'.eqv_trans _ _ _ hchange (hpin (pairChart tail ht i j W))

theorem selectedPairAngular_chart_pin (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q') (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hW : SupportedQuaternionBlocks (tail+1) W) :
    quaternionHaar (tail+1)
      (polyMul W (polyMul (heatAt i.val j.val w K) (blockAngularSquare i.val p))) ≈
      quaternionHaar (tail+1) (polyMul (pairChart tail ht i j W)
        (polyMul (heatAt 0 1 w K) (angularSquare (pairChart tail ht i j p)))) := by
  let ss := pairSteps (Nat.succ_lt_succ ht) i j
  have hprefix := chain_blockAngularSquare_prefix ss (Nat.zero_lt_succ tail) p
  rw [pair_zero (Nat.succ_lt_succ ht) i j hij] at hprefix
  have henergy : HaarCarrierEqv (tail+1)
      (applyQuaternionBlockSwapChain ss (blockAngularSquare i.val p))
      (angularSquare (pairChart tail ht i j p)) := by
    apply carrier_of_supported
      (applyQuaternionBlockSwapChain_supported ss _ (blockAngularSquare_supported i.isLt hp))
      (blockAngularSquare_supported (block := 0) (Nat.zero_lt_succ tail)
        (applyQuaternionBlockSwapChain_supported ss p hp))
    intro r hr
    exact quaternionHaar_prefixPolynomialEqv (tail+1)
      ((QuaternionPrefixPolynomialEqv.refl (tail+1) r).mul hprefix)
      (supported_polyMul hr
        (applyQuaternionBlockSwapChain_supported ss _ (blockAngularSquare_supported i.isLt hp)))
      (supported_polyMul hr (blockAngularSquare_supported (block := 0)
        (Nat.zero_lt_succ tail) (applyQuaternionBlockSwapChain_supported ss p hp)))
  have hheat := padded_carrier
    (applyQuaternionBlockSwapChain_supported ss _ (heat_supported i.isLt j.isLt w K))
    (heat_supported (a := 0) (b := 1) (Nat.zero_lt_succ tail) (Nat.succ_lt_succ ht) w K)
    (heat_exposed (Nat.succ_lt_succ ht) i j hij w K)
  have hchange := Q'.eqv_symm (quaternionHaar_applyQuaternionBlockSwapChain ss _
    (supported_polyMul hW (supported_polyMul (heat_supported i.isLt j.isLt w K)
      (blockAngularSquare_supported i.isLt hp))))
  rw [chain_mul, chain_mul] at hchange
  exact Q'.eqv_trans _ _ _ hchange
    ((HaarCarrierEqv.mul hheat henergy) (pairChart tail ht i j W))

/-- Arbitrary distinct selected input/output, with the SAME original weight
and actual angular square. No output-independence is required on the source. -/
theorem selectedPair_weighted_angular_variance (tail : Nat) (ht : 0 < tail)
    (i j : Fin (tail+1)) (hij : i.val ≠ j.val) (w : Q')
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hW : SupportedQuaternionBlocks (tail+1) W) (P : Certificate (tail+1) W)
    (hiW : QuaternionBlockIndependent i.val W)
    (hK : selectedPairCutoff tail ht i j p ≤ K) :
    quaternionHaar (tail+1) (polyMul W (selectedPairVariance i.val j.val w K p)) ≤
      (1-w*w)*quaternionHaar (tail+1)
        (polyMul W (polyMul (heatAt i.val j.val w K) (blockAngularSquare i.val p))) := by
  let ss := pairSteps (Nat.succ_lt_succ ht) i j
  have hi : QuaternionBlockIndependent 0 (pairChart tail ht i j W) := by
    apply degree_zero_independent
    apply chain_degree ss (Nat.zero_lt_succ tail)
    rw [pair_zero (Nat.succ_lt_succ ht) i j hij]
    exact independent_has_degree_zero hiW
  have hb := selectedConditional_weighted_angular_variance tail ht w hw0 hw1 K
    (pairChart tail ht i j p) (pairChart tail ht i j W)
    (applyQuaternionBlockSwapChain_supported ss p hp) hK
    (chain_certificate ss hW P) hi
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (selectedPairVariance_chart_pin tail ht i j hij w K p W hp hW))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (1-w*w) _ _
        (Q'.eqv_symm (selectedPairAngular_chart_pin tail ht i j hij w K p W hp hW)))))

end YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare

#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.pairChart
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.selectedPairMean
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.selectedPairVariance
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.selectedPairCutoff
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.chain_project
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.chain_blockAngularSquare_prefix
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.selectedPairVariance_chart_pin
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.selectedPairAngular_chart_pin
#print axioms YMGap.Continuum.SU2QuaternionSelectedPairConditionalPoincare.selectedPair_weighted_angular_variance
