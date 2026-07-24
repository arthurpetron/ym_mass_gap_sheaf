/-
# Whole-slab recoupling bridge to exact projective certificates

This module connects the actual globally link-glued corrected-slab carrier to
the exact rational cross-ratio certificate used by the proposed
Birkhoff--Hopf route.

The certificate is placed on an explicitly selected unbranched sector of the
unnormalized whole-slab kernel.  Positive row normalization preserves its
spread exactly, and a pointwise setoid transport identifies the rescaled raw
kernel with the actual normalized conditional kernel.  A regulator family
then carries one common spread through every cutoff/volume index without any
factor involving the sizes of the finite state lists.

What remains open is sharply isolated: construct the common raw certificate
from fusion-rule geometry and heat-kernel decay on a local activity cone.
The full Cartesian Gibbs cone contains fusion-zero holes and is not asserted
to have finite uniform diameter.

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
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

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
      (Q'.ge_of_eqv (hkernel source hsource target htarget))
  crossRatioBound := by
    intro first hfirst second hsecond leftTarget hleft
      rightTarget hright
    have hleftProduct :
        right first leftTarget * right second rightTarget ≈
          left first leftTarget * left second rightTarget :=
      Q'.mul_eqv_congr'
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
      exact Q'.mul_eqv_congr'
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

/-! ## 3. One common physical spread across regulator indices -/

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
#print axioms WholeSlabProjectiveRegulator.normalizeCertificate
#print axioms WholeSlabProjectiveRegulator.normalizedKernel_projectiveSpread
#print axioms UniformWholeSlabRawProjectiveCertificate.normalizedAtIndex
#print axioms UniformWholeSlabRawProjectiveCertificate.uniform_rate_lt_one

end YMGap.Continuum.CompactDualWholeSlabProjectiveBridge
