/-
# Two-edge angular energy through the same explicit block exposure

The two derivative directions are transported together, retaining prefix
padding and every original Haar insertion. The exposed identity becomes
an identity for the original oriented four-word; no surrogate action or
spectral assumption is used.
-/

import YMGap.Continuum.QuaternionHaarBlockAngularCarrier
import YMGap.Continuum.QuaternionHaarExposedMixedAngularSquare

namespace YMGap.Continuum.QuaternionHaarMixedAngularTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionFourBlockSelection (chain_mul)
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (exposedFourWord)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_carrier)
open YMGap.Continuum.QuaternionHaarMixedAngularDerivative
open YMGap.Continuum.QuaternionHaarBlockAngularCarrier
  (blockAngularDerivative_carrier reindex_blockAngularDerivative_carrier)
open YMGap.Continuum.QuaternionHaarExposedMixedAngularSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (reindex_cap_carrier)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteAngularSquare
  (chain_blockAngularSquare_carrier)

/-- Outer first-block energy of the six second-block derivatives. -/
def mixedSquare (first second : Nat) (p : RatPoly) : RatPoly :=
  six (fun i j => blockAngularSquare first (blockAngularDerivative second i j p))

private theorem six_supported {blocks : Nat} {f : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → SupportedQuaternionBlocks blocks (f i j)) :
    SupportedQuaternionBlocks blocks (six f) := by
  unfold six
  exact supported_add (h 0 1 (by decide) (by decide))
    (supported_add (h 0 2 (by decide) (by decide))
      (supported_add (h 0 3 (by decide) (by decide))
        (supported_add (h 1 2 (by decide) (by decide))
          (supported_add (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

theorem mixedSquare_supported {blocks first second : Nat}
    (ha : first < blocks) (hb : second < blocks) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (mixedSquare first second p) :=
  six_supported (fun i j hi hj => blockAngularSquare_supported ha
    (blockAngularDerivative_supported hb i j hi hj hp))

private theorem blockSquare_carrier {blocks block : Nat} (hb : block < blocks)
    {p q : RatPoly} (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (blockAngularSquare block p) (blockAngularSquare block q) := by
  apply six_carrier
  intro i j hi hj
  have hd := blockAngularDerivative_carrier hb hi hj hp hq h
  exact HaarCarrierEqv.mul hd hd

theorem mixedSquare_carrier {blocks first second : Nat}
    (ha : first < blocks) (hb : second < blocks) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (mixedSquare first second p) (mixedSquare first second q) := by
  apply six_carrier
  intro i j hi hj
  exact blockSquare_carrier ha
    (blockAngularDerivative_supported hb i j hi hj hp)
    (blockAngularDerivative_supported hb i j hi hj hq)
    (blockAngularDerivative_carrier hb hi hj hp hq h)

theorem chain_carrier {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly},
      SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks q →
      HaarCarrierEqv blocks p q →
      HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q)
  | [], _, _, _, _, h => h
  | s::steps, p, q, hp, hq, h =>
      chain_carrier steps (reindex_supported s p) (reindex_supported s q)
        (reindex_carrier s hp hq h)

private theorem reflect_chain {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps p)
      (applyQuaternionBlockSwapChain steps q)) : HaarCarrierEqv blocks p q := by
  have hr := chain_carrier steps.reverse
    (applyQuaternionBlockSwapChain_supported steps p hp)
    (applyQuaternionBlockSwapChain_supported steps q hq) h
  have inv (f : RatPoly) (hf : SupportedQuaternionBlocks blocks f) :
      HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps.reverse
        (applyQuaternionBlockSwapChain steps f)) f :=
    carrierOfPrefix (applyQuaternionBlockSwapChain_supported steps.reverse _
      (applyQuaternionBlockSwapChain_supported steps f hf)) hf
      (reverse_apply_inverse_prefix steps f)
  exact (inv p hp).symm.trans (hr.trans (inv q hq))

theorem chain_blockDerivative {blocks : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution blocks)) (block i j : Nat),
      block < blocks → i < 4 → j < 4 →
      ∀ (p : RatPoly), SupportedQuaternionBlocks blocks p →
      HaarCarrierEqv blocks
        (blockAngularDerivative block i j (applyQuaternionBlockSwapChain steps p))
        (applyQuaternionBlockSwapChain steps
          (blockAngularDerivative (quaternionBlockSwapChainSource steps block) i j p))
  | [], _, _, _, _, _, _, _, _ => HaarCarrierEqv.refl blocks _
  | s::rest, block, i, j, hb, hi, hj, p, hp => by
      let q := reindexQuaternionPolynomial s p
      have hs := quaternionBlockSwapChainSource_lt rest hb
      have hq := reindex_supported s p
      have hr := chain_blockDerivative rest block i j hb hi hj q hq
      have ht := (reindex_blockAngularDerivative_carrier s hs hi hj p hp).symm
      exact hr.trans (chain_carrier rest
        (blockAngularDerivative_supported hs i j hi hj hq)
        (reindex_supported s _) ht)

private theorem chain_six {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (f : Nat → Nat → RatPoly) :
    applyQuaternionBlockSwapChain steps (six f) =
      six (fun i j => applyQuaternionBlockSwapChain steps (f i j)) := by
  induction steps generalizing f with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain, six, reindexQuaternionPolynomial_add]
      exact ih (fun i j => reindexQuaternionPolynomial s (f i j))

/-- Both selected directions pass through the same finite coordinate change. -/
theorem chain_mixedSquare {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (first second : Nat)
    (ha : first < blocks) (hb : second < blocks)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks (mixedSquare first second (applyQuaternionBlockSwapChain steps p))
      (applyQuaternionBlockSwapChain steps
        (mixedSquare (quaternionBlockSwapChainSource steps first)
          (quaternionBlockSwapChainSource steps second) p)) := by
  unfold mixedSquare
  rw [chain_six]
  apply six_carrier
  intro i j hi hj
  have hsource := quaternionBlockSwapChainSource_lt steps hb
  have hd := chain_blockDerivative steps second i j hb hi hj p hp
  have hdp := blockAngularDerivative_supported hsource i j hi hj hp
  exact (blockSquare_carrier ha
    (blockAngularDerivative_supported hb i j hi hj
      (applyQuaternionBlockSwapChain_supported steps p hp))
    (applyQuaternionBlockSwapChain_supported steps _ hdp) hd).trans
    (chain_blockAngularSquare_carrier steps first ha _ hdp)

private theorem chain_cap {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (c : Q') :
    HaarCarrierEqv blocks (applyQuaternionBlockSwapChain steps (cap c)) (cap c) := by
  have hc : SupportedQuaternionBlocks blocks (cap c) := polySmul_supported (supported_one blocks) c
  induction steps with
  | nil => exact HaarCarrierEqv.refl _ _
  | cons s rest ih =>
      exact (chain_carrier rest (reindex_supported s _) hc (reindex_cap_carrier s c)).trans ih

private theorem chain_add {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p) (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s rest ih => simp only [applyQuaternionBlockSwapChain, reindexQuaternionPolynomial_add, ih]

private theorem mixedSquare_zero (second : Nat) (p : RatPoly) :
    mixedSquare 0 second p = six (fun i j => angularSquare (blockAngularDerivative second i j p)) := rfl

attribute [local irreducible] mixedSquare blockAngularSquare blockAngularDerivative
  SU2QuaternionAngularDerivative.angularDerivative angularSquare

/-- The original oriented word, at its first two distinct exposed blocks,
has the exact mixed square with every spectator and weight retained. -/
theorem oriented_word_mixedSquare_of_exposure {blocks : Nat} (hb : 3 < blocks)
    (a b c d : Fin blocks) (e : FourBlockExposure a b c d)
    (r0 r1 r2 r3 : Bool) :
    let f := characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar 1
    HaarCarrierEqv blocks (mixedSquare a.val b.val f) (polyAdd (cap 8) (polyMul f f)) := by
  dsimp only
  let f := characterPolynomial (word a.val b.val c.val d.val r0 r1 r2 r3).scalar 1
  let g := applyQuaternionBlockSwapChain e.steps f
  let canonical := characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 1
  have hf := word_supported a.isLt b.isLt c.isLt d.isLt r0 r1 r2 r3 1
  have hg := applyQuaternionBlockSwapChain_supported e.steps f hf
  have hc : SupportedQuaternionBlocks blocks canonical :=
    word_supported (by omega : 0 < blocks) (by omega : 1 < blocks)
      (by omega : 2 < blocks) hb r0 r1 r2 r3 1
  have hgc : HaarCarrierEqv blocks g canonical :=
    carrierOfPrefix hg hc (character_prefix hb e r0 r1 r2 r3 1)
  have hcanonical : HaarCarrierEqv blocks (mixedSquare 0 1 canonical)
      (polyAdd (cap 8) (polyMul canonical canonical)) := by
    rw [mixedSquare_zero]
    exact exposed_mixed_angular_square hb r0 r1 r2 r3
  have hidentity : HaarCarrierEqv blocks (mixedSquare 0 1 g)
      (polyAdd (cap 8) (polyMul g g)) := (mixedSquare_carrier (by omega : 0 < blocks)
    (by omega : 1 < blocks) hg hc hgc).trans
      (hcanonical.trans (HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
        (HaarCarrierEqv.mul hgc.symm hgc.symm)))
  have htransport := chain_mixedSquare e.steps 0 1 (by omega) (by omega) f hf
  rw [e.source_zero, e.source_one] at htransport
  have hgap : HaarCarrierEqv blocks
      (applyQuaternionBlockSwapChain e.steps (polyAdd (cap 8) (polyMul f f)))
      (polyAdd (cap 8) (polyMul g g)) := by
    rw [chain_add, chain_mul]
    exact HaarCarrierEqv.add (chain_cap e.steps 8) (HaarCarrierEqv.refl _ _)
  exact reflect_chain e.steps (mixedSquare_supported a.isLt b.isLt hf)
    (supported_add (polySmul_supported (supported_one blocks) 8) (supported_polyMul hf hf))
    (htransport.symm.trans (hidentity.trans hgap.symm))

#print axioms mixedSquare
#print axioms mixedSquare_supported
#print axioms mixedSquare_carrier
#print axioms chain_carrier
#print axioms chain_blockDerivative
#print axioms chain_mixedSquare
#print axioms oriented_word_mixedSquare_of_exposure

end YMGap.Continuum.QuaternionHaarMixedAngularTransport
