/-
# Whole-slab recoupling bridge to exact projective certificates

This module connects the actual globally link-glued corrected-slab carrier to
the exact rational cross-ratio certificate used by the proposed
Birkhoff--Hopf route.

The certificate is placed on an explicitly selected unbranched sector of the
unnormalized whole-slab kernel.  The globally glued coarse-link multiplicity
is a target-column factor, so it cancels exactly from every projective
cross-ratio.  Positive row normalization also preserves the spread exactly,
and pointwise setoid transports identify both rescalings with the actual
normalized conditional kernel.  A regulator family then carries one common
spread through every cutoff/volume index without any factor involving the
sizes of the finite state lists.

What remains open is sharply isolated: construct the common raw certificate
for the face kernel from fusion-rule geometry and heat-kernel decay on a
local activity cone.  The full Cartesian Gibbs cone contains fusion-zero
holes and is not asserted to have finite uniform diameter.

## Axiom gate

Exact rational algebra only.  No `Classical.*`, `sorry`, `native_decide`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
import YMGap.Continuum.RationalCrossRatioDiameter

namespace YMGap.Continuum.CompactDualWholeSlabProjectiveBridge

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.RationalCrossRatioDiameter.FiniteCrossRatioDiameterCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right left left' right hleft)
    (Q'.mul_eqv_congr_left left' right right' hright)

/-! ## 1. Pointwise setoid transport of a finite certificate -/

def transportKernelEqv
    {Source Target : Type}
    {left right : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate left sources targets)
    (hkernel :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          left source target ≈ right source target) :
    FiniteCrossRatioDiameterCertificate right sources targets where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := by
    intro source hsource target htarget
    exact Q'.pos_of_lt_of_le
      (certificate.strictlyPositive source hsource target htarget)
      (Q'.le_of_eqv (hkernel source hsource target htarget))
  crossRatioBound := by
    intro first hfirst second hsecond leftTarget hleft
      rightTarget hright
    have hleftProduct :
        right first leftTarget * right second rightTarget ≈
          left first leftTarget * left second rightTarget :=
      mul_eqv_congr_local
        (Q'.eqv_symm
          (hkernel first hfirst leftTarget hleft))
        (Q'.eqv_symm
          (hkernel second hsecond rightTarget hright))
    have hrightProduct :
        (certificate.spread * certificate.spread) *
            (left first rightTarget * left second leftTarget) ≈
          (certificate.spread * certificate.spread) *
            (right first rightTarget * right second leftTarget) := by
      apply Q'.mul_eqv_congr_left
      exact mul_eqv_congr_local
        (hkernel first hfirst rightTarget hright)
        (hkernel second hsecond leftTarget hleft)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hleftProduct)
      (Q'.le_trans' _ _ _
        (certificate.crossRatioBound
          first hfirst second hsecond
          leftTarget hleft rightTarget hright)
        (Q'.le_of_eqv hrightProduct))

theorem transportKernelEqv_candidateRate_eqv
    {Source Target : Type}
    {left right : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate left sources targets)
    (hkernel :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          left source target ≈ right source target) :
    (transportKernelEqv certificate hkernel).candidateRate ≈
      certificate.candidateRate :=
  Q'.eqv_refl _

/-! ## 2. One physical corrected-slab projective sector -/

structure WholeSlabProjectiveRegulator : Type where
  scalePair : SlabScalePair
  fineCutoff : scalePair.fine.cutoff = 1
  coarseCouplingPositive :
    (0 : Q') < scalePair.coarse.coupling
  sources : List (CoherentSlabRecouplingSource scalePair)
  targets : List EdgeLabelling
  targetsPhysical :
    ∀ target, target ∈ targets →
      target ∈ scalePair.coarse.physicalLabellings

namespace WholeSlabProjectiveRegulator

def rawKernel
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) : Q' :=
  wholeSlabRecouplingRawWeight regulator.scalePair
    source.fineState target

/-- The source-dependent part of the raw whole-slab kernel.  All nontrivial
coarse shared-link dimensions have been omitted here. -/
def faceKernel
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) : Q' :=
  wholeSlabFaceRawProduct regulator.scalePair source.fineState target

/-- One geometric coarse-face fiber, viewed as a local kernel on the selected
source and target sectors. -/
def localFaceKernel
    (regulator : WholeSlabProjectiveRegulator)
    (coarseFaceId : Nat)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) : Q' :=
  wholeSlabFaceRawWeight regulator.scalePair
    source.fineState target coarseFaceId

/-- The remaining source-dependent slab weight is definitionally the finite
pointwise product of its geometric coarse-face kernels. -/
theorem faceKernel_eqv_factorized
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) :
    regulator.faceKernel source target ≈
      factorizedKernel regulator.localFaceKernel
        regulator.scalePair.coarse.faceEdges source target := by
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct
      (wholeSlabFaceRawWeight regulator.scalePair
        source.fineState target)
      regulator.scalePair.coarse.faceEdges) _ ?_ ?_
  · exact wholeSlabFaceRawProduct_eqv_finiteQProduct
      regulator.scalePair source.fineState target
  · generalize regulator.scalePair.coarse.faceEdges = faces
    induction faces with
    | nil =>
        unfold wholeSlabFiniteQProduct factorizedKernel
        exact Q'.eqv_refl 1
    | cons head tail ih =>
        unfold wholeSlabFiniteQProduct factorizedKernel
        apply Q'.mul_eqv_congr_left
        exact ih

/-- Assemble one exact certificate per geometric coarse face and transport
their finite product to the literal whole-slab face kernel.  The resulting
spread ledger contains only the local face spreads. -/
def faceCertificateOfLocalCertificates
    (regulator : WholeSlabProjectiveRegulator)
    (localCertificate :
      ∀ coarseFaceId,
        coarseFaceId ∈ regulator.scalePair.coarse.faceEdges →
          FiniteCrossRatioDiameterCertificate
            (regulator.localFaceKernel coarseFaceId)
            regulator.sources regulator.targets) :
    FiniteCrossRatioDiameterCertificate
      regulator.faceKernel regulator.sources regulator.targets :=
  transportKernelEqv
    (factorizedCertificate
      regulator.localFaceKernel regulator.sources regulator.targets
      regulator.scalePair.coarse.faceEdges localCertificate)
    (fun source _ target _ =>
      Q'.eqv_symm
        (regulator.faceKernel_eqv_factorized source target))

/-- Certificate-shaped local geometry sufficient for a volume-independent
face-kernel diameter.  Inactive faces have unit spread; the active filter
has a regulator-independent cardinality budget. -/
structure LocalFaceProjectiveCover
    (regulator : WholeSlabProjectiveRegulator)
    (localSpread : Q') (activeBudget : Nat) : Type where
  one_le_localSpread : (1 : Q') ≤ localSpread
  active : Nat → Bool
  active_count_le :
    (regulator.scalePair.coarse.faceEdges.filter active).length ≤
      activeBudget
  localCertificate :
    ∀ coarseFaceId,
      coarseFaceId ∈ regulator.scalePair.coarse.faceEdges →
        FiniteCrossRatioDiameterCertificate
          (regulator.localFaceKernel coarseFaceId)
          regulator.sources regulator.targets
  local_spread_ledger :
    ∀ coarseFaceId hface,
      (localCertificate coarseFaceId hface).spread ≈
        if active coarseFaceId then localSpread else 1

namespace LocalFaceProjectiveCover

def assembledFaceCertificate
    {regulator : WholeSlabProjectiveRegulator}
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    FiniteCrossRatioDiameterCertificate
      regulator.faceKernel regulator.sources regulator.targets :=
  regulator.faceCertificateOfLocalCertificates
    cover.localCertificate

theorem assembledFaceCertificate_spread_eqv_activePower
    {regulator : WholeSlabProjectiveRegulator}
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    cover.assembledFaceCertificate.spread ≈
      spreadPower localSpread
        (regulator.scalePair.coarse.faceEdges.filter
          cover.active).length := by
  refine Q'.eqv_trans _
    (factorSpreadProduct (fun _ => localSpread)
      (regulator.scalePair.coarse.faceEdges.filter
        cover.active)) _ ?_ ?_
  · exact factorizedCertificate_spread_eqv_activeProduct
      regulator.localFaceKernel regulator.sources regulator.targets
      cover.active (fun _ => localSpread)
      regulator.scalePair.coarse.faceEdges
      cover.localCertificate cover.local_spread_ledger
  · exact Q'.eqv_of_eq
      (factorSpreadProduct_const_eq_spreadPower
        localSpread
        (regulator.scalePair.coarse.faceEdges.filter
          cover.active))

theorem assembledFaceCertificate_spread_le_budget
    {regulator : WholeSlabProjectiveRegulator}
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    cover.assembledFaceCertificate.spread ≤
      spreadPower localSpread activeBudget := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv cover.assembledFaceCertificate_spread_eqv_activePower)
    (spreadPower_mono localSpread cover.one_le_localSpread
      cover.active_count_le)

/-- Replace the regulator-dependent active count by the common exact budget
spread. -/
def uniformFaceCertificate
    {regulator : WholeSlabProjectiveRegulator}
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    FiniteCrossRatioDiameterCertificate
      regulator.faceKernel regulator.sources regulator.targets :=
  cover.assembledFaceCertificate.widen
    (spreadPower localSpread activeBudget)
    cover.assembledFaceCertificate_spread_le_budget

theorem uniformFaceCertificate_spread_eq
    {regulator : WholeSlabProjectiveRegulator}
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    cover.uniformFaceCertificate.spread =
      spreadPower localSpread activeBudget :=
  rfl

end LocalFaceProjectiveCover

/-- The complete higher-valent coarse-link multiplicity is a function of the
retained target alone.  It is therefore a projective column gauge. -/
def linkColumnScale
    (regulator : WholeSlabProjectiveRegulator)
    (target : EdgeLabelling) : Q' :=
  Q'.ofNat
    (slabExplicitLinkMultiplicityProduct
      regulator.scalePair.coarse.cutoff
      regulator.scalePair.coarse.extent target)

theorem rawKernel_eqv_columnRescaledFaceKernel
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) :
    regulator.rawKernel source target ≈
      columnRescaledKernel regulator.linkColumnScale
        regulator.faceKernel source target :=
  Q'.eqv_refl _

def normalizedKernel
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) : Q' :=
  wholeSlabRecouplingConditionalKernel source target

def rowScale
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair) : Q' :=
  Q'.recipPos
    (wholeSlabRecouplingPartition source)
    (wholeSlabRecouplingPartition_pos source)

theorem rowScale_pos
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair) :
    (0 : Q') < regulator.rowScale source :=
  Q'.recipPos_pos _ _

theorem rowRescaledRaw_eqv_normalized
    (regulator : WholeSlabProjectiveRegulator)
    (source : CoherentSlabRecouplingSource regulator.scalePair)
    (target : EdgeLabelling) :
    rowRescaledKernel regulator.rowScale regulator.rawKernel
        source target ≈
      regulator.normalizedKernel source target := by
  unfold rowRescaledKernel rowScale rawKernel normalizedKernel
    wholeSlabRecouplingConditionalKernel Q'.divPos
  exact Q'.mul_comm_eqv _ _

/-! ## 3. Exact cancellation of target-only link multiplicities -/

/-- The retained unbranched target sector must avoid link-multiplicity zeros.
This condition is weaker than a diameter bound: it merely says that the
target-only projective gauge can be removed. -/
structure PositiveLinkColumnSector
    (regulator : WholeSlabProjectiveRegulator) : Prop where
  strictlyPositive :
    ∀ target, target ∈ regulator.targets →
      (0 : Q') < regulator.linkColumnScale target

/-- A face-only cross-ratio certificate lifts to the full raw whole-slab
kernel with exactly the same spread.  Hence the potentially high-valence
coarse shared-link factor contributes no projective diameter at all. -/
def rawCertificateOfFaceCertificate
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (faceCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.faceKernel regulator.sources regulator.targets) :
    FiniteCrossRatioDiameterCertificate
      regulator.rawKernel regulator.sources regulator.targets :=
  transportKernelEqv
    (faceCertificate.columnRescale
      regulator.linkColumnScale sector.strictlyPositive)
    (fun source _ target _ =>
      Q'.eqv_symm
        (regulator.rawKernel_eqv_columnRescaledFaceKernel source target))

theorem rawCertificateOfFaceCertificate_spread_eq
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (faceCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.faceKernel regulator.sources regulator.targets) :
    (regulator.rawCertificateOfFaceCertificate
      sector faceCertificate).spread =
        faceCertificate.spread :=
  rfl

theorem rawCertificateOfFaceCertificate_candidateRate_eqv
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (faceCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.faceKernel regulator.sources regulator.targets) :
    (regulator.rawCertificateOfFaceCertificate
      sector faceCertificate).candidateRate ≈
        faceCertificate.candidateRate :=
  Q'.eqv_refl _

/-- Normalize a raw unbranched-sector certificate without changing its
recorded spread or candidate contraction rate. -/
def normalizeCertificate
    (regulator : WholeSlabProjectiveRegulator)
    (rawCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.rawKernel regulator.sources regulator.targets) :
    FiniteCrossRatioDiameterCertificate
      regulator.normalizedKernel regulator.sources regulator.targets :=
  transportKernelEqv
    (rawCertificate.rowRescale regulator.rowScale
      (fun source _ => regulator.rowScale_pos source))
    (fun source _ target _ =>
      regulator.rowRescaledRaw_eqv_normalized source target)

/-- The complete face-to-physical-kernel bridge.  Target-column link factors
and source-row Gibbs normalizers both cancel without altering the certified
spread. -/
def normalizeFaceCertificate
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (faceCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.faceKernel regulator.sources regulator.targets) :
    FiniteCrossRatioDiameterCertificate
      regulator.normalizedKernel regulator.sources regulator.targets :=
  regulator.normalizeCertificate
    (regulator.rawCertificateOfFaceCertificate sector faceCertificate)

/-- The actual normalized kernel certificate obtained from a bounded
active-face cover.  Its spread is exactly the common budget power. -/
def normalizeCoveredFaceCertificate
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    FiniteCrossRatioDiameterCertificate
      regulator.normalizedKernel regulator.sources regulator.targets :=
  regulator.normalizeFaceCertificate sector
    cover.uniformFaceCertificate

theorem normalizeCoveredFaceCertificate_spread_eq
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    (regulator.normalizeCoveredFaceCertificate
      sector cover).spread =
        spreadPower localSpread activeBudget :=
  rfl

theorem normalizeCoveredFaceCertificate_rate_lt_one
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    {localSpread : Q'} {activeBudget : Nat}
    (cover :
      LocalFaceProjectiveCover regulator localSpread activeBudget) :
    (regulator.normalizeCoveredFaceCertificate
      sector cover).candidateRate < 1 :=
  (regulator.normalizeCoveredFaceCertificate
    sector cover).candidateRate_lt_one

/-- End-to-end local-factor constructor for the actual normalized physical
kernel: local face certificates are multiplied, target-only link factors
are removed, and source-row Gibbs normalizers are removed. -/
def normalizeLocalFaceCertificates
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (localCertificate :
      ∀ coarseFaceId,
        coarseFaceId ∈ regulator.scalePair.coarse.faceEdges →
          FiniteCrossRatioDiameterCertificate
            (regulator.localFaceKernel coarseFaceId)
            regulator.sources regulator.targets) :
    FiniteCrossRatioDiameterCertificate
      regulator.normalizedKernel regulator.sources regulator.targets :=
  regulator.normalizeFaceCertificate sector
    (regulator.faceCertificateOfLocalCertificates localCertificate)

theorem normalizeLocalFaceCertificates_rate_lt_one
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (localCertificate :
      ∀ coarseFaceId,
        coarseFaceId ∈ regulator.scalePair.coarse.faceEdges →
          FiniteCrossRatioDiameterCertificate
            (regulator.localFaceKernel coarseFaceId)
            regulator.sources regulator.targets) :
    (regulator.normalizeLocalFaceCertificates
      sector localCertificate).candidateRate < 1 :=
  (regulator.normalizeLocalFaceCertificates
    sector localCertificate).candidateRate_lt_one

theorem normalizeFaceCertificate_spread_eq
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (faceCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.faceKernel regulator.sources regulator.targets) :
    (regulator.normalizeFaceCertificate
      sector faceCertificate).spread =
        faceCertificate.spread :=
  rfl

theorem normalizeFaceCertificate_candidateRate_eqv
    (regulator : WholeSlabProjectiveRegulator)
    (sector : PositiveLinkColumnSector regulator)
    (faceCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.faceKernel regulator.sources regulator.targets) :
    (regulator.normalizeFaceCertificate
      sector faceCertificate).candidateRate ≈
        faceCertificate.candidateRate :=
  Q'.eqv_refl _

theorem normalizeCertificate_spread_eq
    (regulator : WholeSlabProjectiveRegulator)
    (rawCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.rawKernel regulator.sources regulator.targets) :
    (regulator.normalizeCertificate rawCertificate).spread =
      rawCertificate.spread :=
  rfl

theorem normalizeCertificate_candidateRate_eqv
    (regulator : WholeSlabProjectiveRegulator)
    (rawCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.rawKernel regulator.sources regulator.targets) :
    (regulator.normalizeCertificate rawCertificate).candidateRate ≈
      rawCertificate.candidateRate :=
  Q'.eqv_refl _

theorem normalizedKernel_projectiveSpread
    (regulator : WholeSlabProjectiveRegulator)
    (rawCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.rawKernel regulator.sources regulator.targets)
    (firstActivity secondActivity :
      CoherentSlabRecouplingSource regulator.scalePair → Q')
    (hfirst :
      ∀ source, source ∈ regulator.sources →
        (0 : Q') ≤ firstActivity source)
    (hsecond :
      ∀ source, source ∈ regulator.sources →
        (0 : Q') ≤ secondActivity source) :
    ProjectiveSpreadBound rawCertificate.spread regulator.targets
      (finiteKernelAction regulator.normalizedKernel
        regulator.sources firstActivity)
      (finiteKernelAction regulator.normalizedKernel
        regulator.sources secondActivity) := by
  exact
    (regulator.normalizeCertificate rawCertificate
    ).finiteKernelAction_projectiveSpread
      firstActivity secondActivity hfirst hsecond

theorem normalizedCandidateRate_lt_one
    (regulator : WholeSlabProjectiveRegulator)
    (rawCertificate :
      FiniteCrossRatioDiameterCertificate
        regulator.rawKernel regulator.sources regulator.targets) :
    (regulator.normalizeCertificate rawCertificate).candidateRate < 1 :=
  (regulator.normalizeCertificate rawCertificate).candidateRate_lt_one

end WholeSlabProjectiveRegulator

/-! ## 4. A common local active-face cover across regulator indices -/

/-- The finite, certificate-shaped target for the fusion/heat-kernel
geometry.  Every regulator shares one local spread and one active-face
budget; therefore every actual normalized kernel receives the same exact
projective spread. -/
structure UniformWholeSlabLocalFaceCover
    (Index : Type)
    (regulator : Index → WholeSlabProjectiveRegulator) : Type where
  localSpread : Q'
  activeBudget : Nat
  positiveLinkSector :
    ∀ index, WholeSlabProjectiveRegulator.PositiveLinkColumnSector
      (regulator index)
  cover :
    ∀ index,
      WholeSlabProjectiveRegulator.LocalFaceProjectiveCover
        (regulator index) localSpread activeBudget

def UniformWholeSlabLocalFaceCover.normalizedAtIndex
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (uniformCover :
      UniformWholeSlabLocalFaceCover Index regulator)
    (index : Index) :
    FiniteCrossRatioDiameterCertificate
      (regulator index).normalizedKernel
      (regulator index).sources
      (regulator index).targets :=
  (regulator index).normalizeCoveredFaceCertificate
    (uniformCover.positiveLinkSector index)
    (uniformCover.cover index)

theorem UniformWholeSlabLocalFaceCover.normalized_spread_eq
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (uniformCover :
      UniformWholeSlabLocalFaceCover Index regulator)
    (index : Index) :
    (uniformCover.normalizedAtIndex index).spread =
      spreadPower uniformCover.localSpread
        uniformCover.activeBudget :=
  rfl

theorem UniformWholeSlabLocalFaceCover.uniform_rate_eqv
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (uniformCover :
      UniformWholeSlabLocalFaceCover Index regulator)
    (first second : Index) :
    (uniformCover.normalizedAtIndex first).candidateRate ≈
      (uniformCover.normalizedAtIndex second).candidateRate :=
  Q'.eqv_refl _

theorem UniformWholeSlabLocalFaceCover.uniform_rate_lt_one
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (uniformCover :
      UniformWholeSlabLocalFaceCover Index regulator)
    (index : Index) :
    (uniformCover.normalizedAtIndex index).candidateRate < 1 :=
  (uniformCover.normalizedAtIndex index).candidateRate_lt_one

/-! ## 5. One common raw spread across regulator indices -/

structure UniformWholeSlabRawProjectiveCertificate
    (Index : Type)
    (regulator : Index → WholeSlabProjectiveRegulator) : Type where
  spread : Q'
  one_le_spread : (1 : Q') ≤ spread
  strictlyPositive :
    ∀ index source, source ∈ (regulator index).sources →
      ∀ target, target ∈ (regulator index).targets →
        (0 : Q') < (regulator index).rawKernel source target
  crossRatioBound :
    ∀ index first, first ∈ (regulator index).sources →
      ∀ second, second ∈ (regulator index).sources →
        ∀ left, left ∈ (regulator index).targets →
          ∀ right, right ∈ (regulator index).targets →
            (regulator index).rawKernel first left *
                (regulator index).rawKernel second right ≤
              (spread * spread) *
                ((regulator index).rawKernel first right *
                  (regulator index).rawKernel second left)

def UniformWholeSlabRawProjectiveCertificate.atIndex
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (certificate :
      UniformWholeSlabRawProjectiveCertificate Index regulator)
    (index : Index) :
    FiniteCrossRatioDiameterCertificate
      (regulator index).rawKernel
      (regulator index).sources
      (regulator index).targets where
  spread := certificate.spread
  one_le_spread := certificate.one_le_spread
  strictlyPositive := certificate.strictlyPositive index
  crossRatioBound := certificate.crossRatioBound index

def UniformWholeSlabRawProjectiveCertificate.normalizedAtIndex
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (certificate :
      UniformWholeSlabRawProjectiveCertificate Index regulator)
    (index : Index) :
    FiniteCrossRatioDiameterCertificate
      (regulator index).normalizedKernel
      (regulator index).sources
      (regulator index).targets :=
  (regulator index).normalizeCertificate
    (certificate.atIndex index)

theorem UniformWholeSlabRawProjectiveCertificate.normalized_spread_eq
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (certificate :
      UniformWholeSlabRawProjectiveCertificate Index regulator)
    (index : Index) :
    (certificate.normalizedAtIndex index).spread =
      certificate.spread :=
  rfl

theorem UniformWholeSlabRawProjectiveCertificate.uniform_rate_eqv
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (certificate :
      UniformWholeSlabRawProjectiveCertificate Index regulator)
    (first second : Index) :
    (certificate.normalizedAtIndex first).candidateRate ≈
      (certificate.normalizedAtIndex second).candidateRate :=
  Q'.eqv_refl _

theorem UniformWholeSlabRawProjectiveCertificate.uniform_rate_lt_one
    {Index : Type}
    {regulator : Index → WholeSlabProjectiveRegulator}
    (certificate :
      UniformWholeSlabRawProjectiveCertificate Index regulator)
    (index : Index) :
    (certificate.normalizedAtIndex index).candidateRate < 1 :=
  (certificate.normalizedAtIndex index).candidateRate_lt_one

#print axioms transportKernelEqv
#print axioms WholeSlabProjectiveRegulator.rawCertificateOfFaceCertificate
#print axioms WholeSlabProjectiveRegulator.faceCertificateOfLocalCertificates
#print axioms WholeSlabProjectiveRegulator.LocalFaceProjectiveCover.uniformFaceCertificate
#print axioms WholeSlabProjectiveRegulator.normalizeFaceCertificate
#print axioms WholeSlabProjectiveRegulator.normalizeLocalFaceCertificates
#print axioms WholeSlabProjectiveRegulator.normalizeCoveredFaceCertificate
#print axioms WholeSlabProjectiveRegulator.normalizeCertificate
#print axioms WholeSlabProjectiveRegulator.normalizedKernel_projectiveSpread
#print axioms UniformWholeSlabLocalFaceCover.normalizedAtIndex
#print axioms UniformWholeSlabLocalFaceCover.uniform_rate_lt_one
#print axioms UniformWholeSlabRawProjectiveCertificate.normalizedAtIndex
#print axioms UniformWholeSlabRawProjectiveCertificate.uniform_rate_lt_one

end YMGap.Continuum.CompactDualWholeSlabProjectiveBridge
