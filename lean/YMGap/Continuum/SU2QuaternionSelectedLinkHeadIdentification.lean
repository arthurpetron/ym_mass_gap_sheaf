/-
# Refuted universal selected-link/operator identification certificate

STATUS CORRECTION (2026-09-23): `SU2QuaternionSelectedLinkHeadObstruction`
refutes the universal identification, exposed-head, projection-pairing and
relative-pairing inputs below at `tailBlocks=3`, pair `0,2`, `w=1/2`, every
`K>=1`, including the computed cutoff guard. Existing-neighbor integration
is not fresh-head heat with the neighbor held as a spectator. The conditional
implications are retained unchanged, not advertised as an available proof
route. The separate `SelectedLinkExposedHeatHeadPairing` constructor is valid.
No frontier field is weakened. See the obstruction audit for the precise scope.

The finite recoding and inverse-chain defect estimate are proved, but the
repository does not yet identify the independently defined selected-link
heat/projection update with that recoded operator.  This module factors that
missing bridge into one explicit Type-level certificate and proves its exact
finite consequence.  The certificate is substantive: it quantifies over
every supported state/test pairing on the same carrier.
-/

import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain
import YMGap.Continuum.SU2QuaternionPaddedProjectionPairing

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
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionPaddedProjectionPairing
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
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

/-- **Refuted as a universal route; statement retained.** This is the proposed same-carrier pairing bridge from
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

/-- Refuted reduced input in the exposed chart; statement retained. This asks for the pairing
of the literal head projection of the exposed selected heat factor with the
recoded test, against the literal exposed `headMap` pairing.  The preceding
finite recoding and bilinear inverse-chain theorem reconstruct the original
selected-link identification from this field. -/
structure SelectedLinkExposedHeadPairing
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
          (project 0
            (exposeTranslationPairPolynomial (tailBlocks + 1)
              selected multiplier (by omega) hselected hmultiplier
              (polyMul (heatAt selected multiplier w K) polynomial)))
          (reindexQuaternionPolynomial
            (translationPairTailPermutation (tailBlocks + 1)
              selected multiplier (by omega) hselected hmultiplier)
            (reindexQuaternionPolynomial
              (translationPairHeadPermutation (tailBlocks + 1) selected hselected)
              test))) ≈
      quaternionHaar (tailBlocks + 1)
        (polyMul
          (headMap w K
            (applyQuaternionBlockSwapChain
              (selectedPairSteps tailBlocks selected multiplier
                hblocks hselected hmultiplier) test))
          (applyQuaternionBlockSwapChain
              (selectedPairSteps tailBlocks selected multiplier
                hblocks hselected hmultiplier) polynomial))

/-! The two genuinely separate obligations hidden by the reduced certificate.

`SelectedLinkExposedProjectionPairing` is the place where a future
projection-compatible use of `PaddedPolynomialCoeffEqv` must be supplied.
`SelectedLinkExposedHeatHeadPairing` is the independent exposed-chart
heat/head-map comparison.  Neither structure asserts that such a comparison
has already been constructed. -/

def selectedLinkExposedHeatPair
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (w : Q') (K : Nat) (polynomial test : RatPoly) : Q' :=
  heatPair tailBlocks w K
    (applyQuaternionBlockSwapChain
      (selectedPairSteps tailBlocks selected multiplier
        hblocks hselected hmultiplier) test)
    (applyQuaternionBlockSwapChain
      (selectedPairSteps tailBlocks selected multiplier
        hblocks hselected hmultiplier) polynomial)

structure SelectedLinkExposedProjectionPairing
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat) : Type where
  /-- The kernel-level padded equivalence that this certificate must consume. -/
  heat_kernel : PaddedPolynomialCoeffEqv (tailBlocks + 1)
    (exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier (heatAt selected multiplier w K))
    (relativeHeat w K)
  pairing : ∀ (polynomial test : RatPoly),
    SupportedQuaternionBlocks (tailBlocks + 1) polynomial →
    SupportedQuaternionBlocks (tailBlocks + 1) test →
    quaternionHaar (tailBlocks + 1)
        (polyMul
          (project 0
            (exposeTranslationPairPolynomial (tailBlocks + 1)
              selected multiplier (by omega) hselected hmultiplier
              (polyMul (heatAt selected multiplier w K) polynomial)))
          (reindexQuaternionPolynomial
            (translationPairTailPermutation (tailBlocks + 1)
              selected multiplier (by omega) hselected hmultiplier)
            (reindexQuaternionPolynomial
              (translationPairHeadPermutation (tailBlocks + 1) selected hselected)
              test))) ≈
      selectedLinkExposedHeatPair tailBlocks selected multiplier
        hblocks hselected hmultiplier w K polynomial test

/-! Refuted remaining input after the proved exposure and padded transport.
This witness speaks only about the relative heat form on the exposed carrier;
it does not repeat the heat-kernel recoding or the head-map symmetry. The
obstruction module proves that this requested pairing is false at admissible
parameters; it is not an outstanding analytic theorem. -/
structure SelectedLinkExposedRelativePairing
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
          (project 0
            (polyMul (relativeHeat w K)
              (exposeTranslationPairPolynomial (tailBlocks + 1)
                selected multiplier (by omega) hselected hmultiplier
                polynomial)))
          (exposeTranslationPairPolynomial (tailBlocks + 1)
            selected multiplier (by omega) hselected hmultiplier test)) ≈
      selectedLinkExposedHeatPair tailBlocks selected multiplier
        hblocks hselected hmultiplier w K polynomial test

def selectedLinkExposedProjectionPairing_of_pairing
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (pairing : ∀ (polynomial test : RatPoly),
      SupportedQuaternionBlocks (tailBlocks + 1) polynomial →
      SupportedQuaternionBlocks (tailBlocks + 1) test →
      quaternionHaar (tailBlocks + 1)
          (polyMul
            (project 0
              (exposeTranslationPairPolynomial (tailBlocks + 1)
                selected multiplier (by omega) hselected hmultiplier
                (polyMul (heatAt selected multiplier w K) polynomial)))
            (reindexQuaternionPolynomial
              (translationPairTailPermutation (tailBlocks + 1)
                selected multiplier (by omega) hselected hmultiplier)
              (reindexQuaternionPolynomial
                (translationPairHeadPermutation (tailBlocks + 1) selected hselected)
                test))) ≈
        selectedLinkExposedHeatPair tailBlocks selected multiplier
          hblocks hselected hmultiplier w K polynomial test) :
    SelectedLinkExposedProjectionPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K := by
  exact
    { heat_kernel := exposeTranslationPair_heat
        (tailBlocks + 1) selected multiplier (by omega)
          hselected hmultiplier hdistinct w K
      pairing := pairing }

/-! A fully proved finite variant is available when the input equivalence is
the ordinary coefficient equivalence.  This is the exact operation that is
missing for `PaddedPolynomialCoeffEqv`: the latter is an equivalence only
after a common identity reindex, and no theorem currently removes that
reindex before applying `project`. -/
theorem project_coeff_pairing
    {blocks index : Nat} {p q insertion : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    quaternionHaar blocks
        (polyMul (project index p) insertion) ≈
      quaternionHaar blocks
        (polyMul (project index q) insertion) := by
  exact haar_of_coeff ((project_congr index h).mul_right insertion)

structure SelectedLinkExposedHeatHeadPairing
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat) : Type where
  pairing : ∀ (polynomial test : RatPoly),
    SupportedQuaternionBlocks (tailBlocks + 1) polynomial →
    SupportedQuaternionBlocks (tailBlocks + 1) test →
    selectedLinkExposedHeatPair tailBlocks selected multiplier
        hblocks hselected hmultiplier w K polynomial test ≈
      quaternionHaar (tailBlocks + 1)
        (polyMul
          (headMap w K
            (applyQuaternionBlockSwapChain
              (selectedPairSteps tailBlocks selected multiplier
                hblocks hselected hmultiplier) test))
          (applyQuaternionBlockSwapChain
            (selectedPairSteps tailBlocks selected multiplier
              hblocks hselected hmultiplier) polynomial))

def selectedLinkExposedHeadPairing_of_bridges
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (projection : SelectedLinkExposedProjectionPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K)
    (heatHead : SelectedLinkExposedHeatHeadPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K) :
    SelectedLinkExposedHeadPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
      hdistinct w K := by
  refine ⟨?_⟩
  intro polynomial test hpolynomial htest
  exact Q'.eqv_trans _ _ _
    (projection.pairing polynomial test hpolynomial htest)
    (heatHead.pairing polynomial test hpolynomial htest)

/-! The exposed heat/head-map bridge is not an additional analytic input:
`headMap_pairing` already states the same equality in the opposite direction
for the recoded test and polynomial. -/
def selectedLinkExposedHeatHeadPairing_of_headMap
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat) :
    SelectedLinkExposedHeatHeadPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K := by
  refine ⟨?_⟩
  intro polynomial test hpolynomial htest
  exact Q'.eqv_symm (headMap_pairing tailBlocks w K
    (applyQuaternionBlockSwapChain
      (selectedPairSteps tailBlocks selected multiplier
        hblocks hselected hmultiplier) test)
    (applyQuaternionBlockSwapChain
      (selectedPairSteps tailBlocks selected multiplier
        hblocks hselected hmultiplier) polynomial))

def selectedLinkExposedHeadPairing_of_projection
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (projection : SelectedLinkExposedProjectionPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K) :
    SelectedLinkExposedHeadPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K :=
  selectedLinkExposedHeadPairing_of_bridges
    tailBlocks selected multiplier hblocks hselected hmultiplier
      hdistinct w K projection
    (selectedLinkExposedHeatHeadPairing_of_headMap
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K)

def selectedLinkExposedProjectionPairing_of_relative
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (relative : SelectedLinkExposedRelativePairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K) :
    SelectedLinkExposedProjectionPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K := by
  refine
    { heat_kernel := exposeTranslationPair_heat
        (tailBlocks + 1) selected multiplier (by omega)
          hselected hmultiplier hdistinct w K
      pairing := ?_ }
  intro polynomial test hpolynomial htest
  have hreduce := exposed_heat_product_projected_pairing
    tailBlocks selected multiplier hblocks hselected hmultiplier
      hdistinct w K polynomial test
  exact Q'.eqv_trans _ _ _ hreduce
    (relative.pairing polynomial test hpolynomial htest)

def selectedLinkExposedHeadPairing_of_relative
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (relative : SelectedLinkExposedRelativePairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K) :
    SelectedLinkExposedHeadPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K :=
  selectedLinkExposedHeadPairing_of_projection
    tailBlocks selected multiplier hblocks hselected hmultiplier
      hdistinct w K
    (selectedLinkExposedProjectionPairing_of_relative
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K relative)

/-- The reduced exposed-chart certificate is sufficient for the original
same-carrier selected-link identification. -/
def selectedLinkHeadIdentification_of_exposed
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (exposed : SelectedLinkExposedHeadPairing
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K) :
    SelectedLinkHeadIdentification
      tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct w K := by
  refine ⟨?_⟩
  intro polynomial test hpolynomial htest
  let steps := selectedPairSteps tailBlocks selected multiplier
    hblocks hselected hmultiplier
  have hheat : SupportedQuaternionBlocks (tailBlocks + 1)
      (heatAt selected multiplier w K) :=
    heat_supported hselected hmultiplier w K
  have hheatPolynomial : SupportedQuaternionBlocks (tailBlocks + 1)
      (polyMul (heatAt selected multiplier w K) polynomial) :=
    supported_polyMul hheat hpolynomial
  have hprojection := exposeTranslationPair_project_pairing
    (tailBlocks + 1) selected multiplier (by omega) hselected hmultiplier
      hdistinct (polyMul (heatAt selected multiplier w K) polynomial) test
      hheatPolynomial htest
  have hprojection' :
      quaternionHaar (tailBlocks + 1)
          (polyMul
            (project 0
              (exposeTranslationPairPolynomial (tailBlocks + 1)
                selected multiplier (by omega) hselected hmultiplier
                (polyMul (heatAt selected multiplier w K) polynomial)))
            (reindexQuaternionPolynomial
              (translationPairTailPermutation (tailBlocks + 1)
                selected multiplier (by omega) hselected hmultiplier)
              (reindexQuaternionPolynomial
                (translationPairHeadPermutation (tailBlocks + 1) selected hselected)
                test))) ≈
        quaternionHaar (tailBlocks + 1)
          (polyMul
            (selectedHeatProjection tailBlocks selected multiplier
              hblocks hselected hmultiplier w K polynomial) test) := by
    simpa [selectedHeatProjection] using hprojection
  have hexposed := exposed.pairing polynomial test hpolynomial htest
  have hbilinear := chainConjugatedHeadMap_pairing_bilinear
    tailBlocks w K steps polynomial test hpolynomial htest
  have horder :
      quaternionHaar (tailBlocks + 1)
          (polyMul
            (headMap w K
              (applyQuaternionBlockSwapChain steps test))
            (applyQuaternionBlockSwapChain steps polynomial)) ≈
        quaternionHaar (tailBlocks + 1)
          (polyMul
            (applyQuaternionBlockSwapChain steps polynomial)
            (headMap w K
              (applyQuaternionBlockSwapChain steps test))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm
      (headMap w K (applyQuaternionBlockSwapChain steps test))
      (applyQuaternionBlockSwapChain steps polynomial))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hprojection')
    (Q'.eqv_trans _ _ _ (by simpa [steps] using hexposed)
      (Q'.eqv_trans _ _ _ horder (Q'.eqv_symm hbilinear)))

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
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.SelectedLinkExposedHeadPairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedHeatPair
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.project_coeff_pairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.SelectedLinkExposedProjectionPairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.SelectedLinkExposedRelativePairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedProjectionPairing_of_pairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.SelectedLinkExposedHeatHeadPairing
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedHeadPairing_of_bridges
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedHeatHeadPairing_of_headMap
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedHeadPairing_of_projection
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedProjectionPairing_of_relative
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkExposedHeadPairing_of_relative
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedLinkHeadIdentification_of_exposed
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedHeatProjection_defect_le_selected_block_energy
#print axioms YMGap.Continuum.SU2QuaternionSelectedLinkHeadIdentification.selectedFiniteDefect_sum_le_selectedBlockEnergy
