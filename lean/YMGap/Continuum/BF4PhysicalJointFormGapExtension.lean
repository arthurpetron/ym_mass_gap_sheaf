/-
# Conditional extension of the physical reflected-joint form gap

The reflected-joint bridge proves the strict form estimate on the canonical
comparison image.  This module records the exact constructive interface
needed to pass that estimate to an arbitrary completed joint vector: an
explicit Cauchy representative, a `CauchyNull` closure witness, and exact
vacuum-orthogonality at every representative stage.  The density/range
witness is a `Type`-level input; it is not manufactured here.
-/

import YMGap.Continuum.BF4PhysicalJointFormGapBridge
import YMGap.Continuum.GNSJointPairingContinuity

namespace YMGap.Continuum.BF4PhysicalJointFormGapExtension

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveContractionOneStepForm
open YMGap.Continuum.PositiveContractionOneStepCompletion
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointFormGapBridge
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

/-! ## 1. The explicit exact-kernel replacement interface -/

/-- A Cauchy representative of a completed vector whose stages lie in a
specified kernel.  `close` pins the representative to the original quotient
class, so no representative is selected from a bare proposition. -/
structure ExactKernelCauchyReplacement
    (D : GNSData) (kernel : D.V → Prop)
    (original : CauchyGNS D) : Type where
  representative : CauchyGNS D
  close : CauchyNull D original representative
  stageInKernel : ∀ n : Nat, kernel (representative.seq n)

/-- Exact stagewise vacuum-complement data for the reflected-joint completion. -/
abbrev ExactPhysicalJointVacuumComplementReplacement
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData) : Type :=
  ExactKernelCauchyReplacement
    (physicalJointSmulGNS w hw K half).toGNSData
    (fun stage =>
      PhysicalJointVacuumOrthogonal w hw K half
        (embedV (physicalJointSmulGNS w hw K half).toGNSData stage))
    original

/-- The missing range/density witness, exposed as constructive data. -/
def ExactPhysicalJointVacuumComplementDensity
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) : Type :=
  ∀ original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData,
    PhysicalJointVacuumOrthogonal w hw K half
      (Quotient.mk
        (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
        original) →
      ExactPhysicalJointVacuumComplementReplacement hw K half original

/-! ## 2. The dense stage estimate on the genuine physical carrier -/

/-- The reflected-joint bridge specializes to a literal physical cylinder.
This is the finite-stage inequality used by the completion limit passage. -/
theorem physicalJoint_embed_form_gap_of_central_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (a : EdgeLabelling → Q')
    (horthogonal :
      PhysicalJointVacuumOrthogonal w hw K half
        (embedV (physicalJointSmulGNS w hw K half).toGNSData a)) :
    CReal.RCle
      ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointTransfer w hw K half
          (embedV (physicalJointSmulGNS w hw K half).toGNSData a))
        (embedV (physicalJointSmulGNS w hw K half).toGNSData a))
      (CReal.RCscale rate
        ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (embedV (physicalJointSmulGNS w hw K half).toGNSData a)
          (embedV (physicalJointSmulGNS w hw K half).toGNSData a))) := by
  have hcomparison :
      PhysicalJointVacuumOrthogonal w hw K half
        (physicalJointComparison w hw K half
          (embedV (centralPhysicalSmulGNS w hw K half).toGNSData a)) := by
    rw [physicalJointComparison_embed]
    exact horthogonal
  have hcentral :
      CentralPhysicalCompletedVacuumOrthogonal w hw K half
        (embedV (centralPhysicalSmulGNS w hw K half).toGNSData a) :=
    (physicalJointComparison_vacuumOrthogonal_iff w hw K half _).mp hcomparison
  have hbridge := physicalJointComparison_form_gap_of_central_form_gap
    hw K half gap
    (embedV (centralPhysicalSmulGNS w hw K half).toGNSData a) hcentral
  rw [physicalJointComparison_embed, physicalJointTransfer_embed] at hbridge
  exact hbridge

/-- The producer rate is available at every matched finite scale on literal
joint cylinders; this is still a finite statement, not a completed range
claim. -/
theorem producer_physicalJoint_embed_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (a : EdgeLabelling → Q')
    (horthogonal :
      PhysicalJointVacuumOrthogonal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (embedV
          (physicalJointSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData a)) :
    CReal.RCle
      ((physicalJointSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        (physicalJointTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (embedV
            (physicalJointSmulGNS
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0).toGNSData a))
        (embedV
          (physicalJointSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData a))
      (CReal.RCscale
        (Q'.mkPos 1 16 (by decide))
        ((physicalJointSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          (embedV
            (physicalJointSmulGNS
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0).toGNSData a)
          (embedV
            (physicalJointSmulGNS
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0).toGNSData a))) :=
  physicalJoint_embed_form_gap_of_central_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (producer_completed_vacuum_form_gap_data producer scale) a horthogonal

/-! ## 3. The representative-level completion passage -/

/-- Stagewise exact-kernel estimates pass through the genuine CReal pairing
limits. -/
theorem physicalJoint_cinnerRep_form_gap_of_stagewise_replacement
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (X : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData)
    (horthogonal : ∀ n : Nat,
      PhysicalJointVacuumOrthogonal w hw K half
        (embedV (physicalJointSmulGNS w hw K half).toGNSData (X.seq n))) :
    CReal.leEv
      ((physicalJointSmulGNS w hw K half).toGNSData.cinnerRep
        ((physicalJointSymbol w hw K half).cDiagCauchy X) X)
      (CReal.mul (CReal.ofQ' rate)
        ((physicalJointSmulGNS w hw K half).toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_ofQ'CauchySeq _ _)
    (CReal.convergesTo_constMul rate
      (CReal.convergesTo_ofQ'CauchySeq _ _))
  intro n
  have hn := physicalJoint_embed_form_gap_of_central_form_gap
    hw K half gap (X.seq n) (horthogonal n)
  change CReal.RCle
    (Quotient.mk CReal.crealSetoid
      (CReal.ofQ'
        ((physicalJointSmulGNS w hw K half).toGNSData.B
          (centralPhysicalMarkovApply w hw K half (X.seq n)) (X.seq n))))
    (CReal.RCscale rate
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          ((physicalJointSmulGNS w hw K half).toGNSData.B
            (X.seq n) (X.seq n))))) at hn
  rw [CReal.RCscale_mk, CReal.RCle_mk] at hn
  simpa only [GNSData.cInnerSeq, DiagonalTransferSymbol.cDiagCauchy] using hn

/-- One explicit exact-kernel replacement suffices for the completed joint
form bound on its quotient class. -/
theorem physicalJoint_completed_form_gap_of_replacement
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (original : CauchyGNS
      (physicalJointSmulGNS w hw K half).toGNSData)
    (replacement :
      ExactPhysicalJointVacuumComplementReplacement hw K half original) :
    CReal.RCle
      ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointTransfer w hw K half
          (Quotient.mk
            (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
            original))
        (Quotient.mk
          (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
          original))
      (CReal.RCscale rate
        ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (Quotient.mk
            (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
            original)
          (Quotient.mk
            (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
            original))) := by
  have hsame :
      Quotient.mk
          (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
          original =
        Quotient.mk
          (cauchySetoid (physicalJointSmulGNS w hw K half).toGNSData)
          replacement.representative :=
    Quotient.sound replacement.close
  rw [hsame]
  exact physicalJoint_cinnerRep_form_gap_of_stagewise_replacement
    hw K half gap replacement.representative replacement.stageInKernel

/-! ## 4. Contraction to the explicit conditional completion certificate -/

/-- If the exact range/density witness is supplied, the reflected-joint
completion has the strict form gap.  The witness remains an explicit input. -/
def PhysicalJointCompletedVacuumFormGap
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (rate : Q') : Prop :=
  (0 : Q') ≤ rate ∧ rate < 1 ∧
    ∀ vector : PhysicalJointCompletion w hw K half,
      PhysicalJointVacuumOrthogonal w hw K half vector →
        CReal.RCle
          ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
            (physicalJointTransfer w hw K half vector) vector)
          (CReal.RCscale rate
            ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
              vector vector))

def physicalJointCompletedVacuumFormGapOfDensity
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (density : ExactPhysicalJointVacuumComplementDensity hw K half) :
    PhysicalJointCompletedVacuumFormGap w hw K half rate := by
  refine ⟨gap.1, gap.2.1, ?_⟩
  intro vector horthogonal
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro original horthogonal
  exact physicalJoint_completed_form_gap_of_replacement
    hw K half gap original (density original horthogonal)

#print axioms ExactKernelCauchyReplacement
#print axioms ExactPhysicalJointVacuumComplementReplacement
#print axioms ExactPhysicalJointVacuumComplementDensity
#print axioms physicalJoint_embed_form_gap_of_central_form_gap
#print axioms producer_physicalJoint_embed_form_gap_sixteenth
#print axioms physicalJoint_cinnerRep_form_gap_of_stagewise_replacement
#print axioms physicalJoint_completed_form_gap_of_replacement
#print axioms physicalJointCompletedVacuumFormGapOfDensity

end YMGap.Continuum.BF4PhysicalJointFormGapExtension
