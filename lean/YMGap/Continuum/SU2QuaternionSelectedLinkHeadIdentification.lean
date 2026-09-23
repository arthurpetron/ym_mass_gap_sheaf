/-
# Minimal selected-link/operator identification certificate

The finite recoding and inverse-chain defect estimate are proved, but the
repository does not yet identify the independently defined selected-link
heat/projection update with that recoded operator.  This module factors that
missing bridge into one explicit Type-level certificate and proves its exact
finite consequence.  The certificate is substantive: it quantifies over
every supported state/test pairing on the same carrier.
-/

import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain

namespace YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The independently defined selected lower-link heat/projection update on
the original doubled carrier. -/
def selectedHeatProjection
    (tailBlocks selected multiplier : Nat)
    (_hblocks : 0 < tailBlocks)
    (_hselected : selected < tailBlocks + 1)
    (_hmultiplier : multiplier < tailBlocks + 1)
    (w : Q') (K : Nat) (polynomial : RatPoly) : RatPoly :=
  project selected
    (polyMul (heatAt selected multiplier w K) polynomial)

/-- The explicit swap chain used by the selected-pair exposure. -/
def selectedPairSteps
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1) :
    List (QuaternionBlockInvolution (tailBlocks + 1)) :=
  pairSteps (by omega) ⟨selected, hselected⟩ ⟨multiplier, hmultiplier⟩

/-- **Named open input.**  This is the exact same-carrier pairing bridge from
the original selected heat/projection update to the inverse-chain conjugate
of `headMap`.  No implementation is supplied here: any inhabitant must prove
all supported state/test pairings, so this cannot be filled by `Unit` or a
surrogate carrier. -/
structure SelectedLinkHeadIdentification
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat) : Type where
  pairing : ∀ (polynomial test : RatPoly),
    SupportedQuaternionBlocks (tailBlocks + 1) polynomial →
    SupportedQuaternionBlocks (tailBlocks + 1) test →
    quaternionHaar (tailBlocks + 1)
        (polyMul
          (selectedHeatProjection tailBlocks selected multiplier
            hblocks hselected hmultiplier w K polynomial) test) ≈
      quaternionHaar (tailBlocks + 1)
        (polyMul polynomial
          (chainConjugatedHeadMap
            (selectedPairSteps tailBlocks selected multiplier
              hblocks hselected hmultiplier) w K test))

/-- Conditional consequence of the named identification: the actual selected
heat/projection update inherits the checked finite `(1-w)` defect bound in the
original selected-block angular energy. -/
theorem selectedHeatProjection_defect_le_selected_block_energy
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks (tailBlocks + 1) polynomial)
    (identification : SelectedLinkHeadIdentification
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K) :
    quaternionHaar (tailBlocks + 1) (polyMul polynomial polynomial) -
        quaternionHaar (tailBlocks + 1)
          (polyMul polynomial
            (selectedHeatProjection tailBlocks selected multiplier
              hblocks hselected hmultiplier w K polynomial)) ≤
      ((1 : Q') - w) *
        quaternionHaar (tailBlocks + 1)
          (blockAngularSquare selected polynomial) := by
  let steps := selectedPairSteps tailBlocks selected multiplier
    hblocks hselected hmultiplier
  have hchain := translationPair_chain_defect_le_selected_block_energy
    tailBlocks selected multiplier hblocks hselected hmultiplier hdistinct
    hw0 hw1 K hK polynomial hpolynomial
  have hpair := identification.pairing polynomial polynomial
    hpolynomial hpolynomial
  have hpair_steps :
      quaternionHaar (tailBlocks + 1)
          (polyMul
            (selectedHeatProjection tailBlocks selected multiplier
              hblocks hselected hmultiplier w K polynomial) polynomial) ≈
        quaternionHaar (tailBlocks + 1)
          (polyMul polynomial
            (chainConjugatedHeadMap steps w K polynomial)) := by
    simpa [steps] using hpair
  have hpair' :
      quaternionHaar (tailBlocks + 1)
          (polyMul polynomial
            (selectedHeatProjection tailBlocks selected multiplier
              hblocks hselected hmultiplier w K polynomial)) ≈
        quaternionHaar (tailBlocks + 1)
          (polyMul polynomial
            (chainConjugatedHeadMap steps w K polynomial)) := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm polynomial
        (selectedHeatProjection tailBlocks selected multiplier
          hblocks hselected hmultiplier w K polynomial)))
      hpair_steps
  have hleft :
      quaternionHaar (tailBlocks + 1) (polyMul polynomial polynomial) -
          quaternionHaar (tailBlocks + 1)
            (polyMul polynomial
              (selectedHeatProjection tailBlocks selected multiplier
                hblocks hselected hmultiplier w K polynomial)) ≈
        quaternionHaar (tailBlocks + 1) (polyMul polynomial polynomial) -
          quaternionHaar (tailBlocks + 1)
            (polyMul polynomial
              (chainConjugatedHeadMap steps w K polynomial)) := by
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hpair')
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hchain

private theorem sum_le_sum {A : Type} (xs : List A) (f g : A → Q') :
    (∀ x, x ∈ xs → f x ≤ g x) →
      qListSum (xs.map f) ≤ qListSum (xs.map g) := by
  induction xs with
  | nil => intro _; exact Q'.le_refl' 0
  | cons x xs ih =>
      intro h
      change f x + qListSum (xs.map f) ≤ g x + qListSum (xs.map g)
      exact Q'.add_le_add (h x List.mem_cons_self)
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem sum_scale {A : Type} (xs : List A) (f : A → Q') (c : Q') :
    qListSum (xs.map (fun x => c * f x)) ≈ c * qListSum (xs.map f) := by
  induction xs with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | cons x xs ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (Q'.eqv_symm (Q'.mul_add_eqv c (f x) (qListSum (xs.map f))))

/-- A finite state-family budget obtained by summing the proved selected-link
defect.  The states are explicit data and each state carries its own
same-carrier identification certificate.  This is not yet the ordered hybrid
sweep: no relation between successive states, no inactive-projection removal,
and no continuum or OS conclusion is asserted here. -/
theorem selectedFiniteDefect_sum_le_selectedBlockEnergy
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : sufficientCutoff w ≤ K)
    (states : List RatPoly)
    (hstates : ∀ p, p ∈ states →
      SupportedQuaternionBlocks (tailBlocks + 1) p)
    (identifications : ∀ p, p ∈ states →
      SelectedLinkHeadIdentification
        tailBlocks selected multiplier hblocks hselected hmultiplier
          hdistinct w K) :
    qListSum (states.map (fun p =>
      quaternionHaar (tailBlocks + 1) (polyMul p p) -
        quaternionHaar (tailBlocks + 1)
          (polyMul p
            (selectedHeatProjection tailBlocks selected multiplier
              hblocks hselected hmultiplier w K p)))) ≤
      ((1 : Q') - w) *
        qListSum (states.map (fun p =>
          quaternionHaar (tailBlocks + 1)
            (blockAngularSquare selected p))) := by
  let defect : RatPoly → Q' := fun p =>
    quaternionHaar (tailBlocks + 1) (polyMul p p) -
      quaternionHaar (tailBlocks + 1)
        (polyMul p
          (selectedHeatProjection tailBlocks selected multiplier
            hblocks hselected hmultiplier w K p))
  let energy : RatPoly → Q' := fun p =>
    quaternionHaar (tailBlocks + 1) (blockAngularSquare selected p)
  have hpoint : ∀ p, p ∈ states → defect p ≤ ((1 : Q') - w) * energy p := by
    intro p hp
    exact selectedHeatProjection_defect_le_selected_block_energy
      tailBlocks selected multiplier hblocks hselected hmultiplier hdistinct
      hw0 hw1 K hK p (hstates p hp) (identifications p hp)
  have hsum := sum_le_sum states defect (fun p => ((1 : Q') - w) * energy p) hpoint
  have hscale := sum_scale states energy ((1 : Q') - w)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hscale)

end YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification

#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedHeatProjection
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedPairSteps
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.SelectedLinkHeadIdentification
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedHeatProjection_defect_le_selected_block_energy
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedFiniteDefect_sum_le_selectedBlockEnergy
