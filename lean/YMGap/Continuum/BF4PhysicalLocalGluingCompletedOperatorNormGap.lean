/-
# Local BF4 gluing alone gives the completed physical operator gap

The completed physical form/operator-gap stack was previously exposed through
`BF4QuarterPhysicalSeparatorProducer`.  That producer also carries a physical
separator, a same-object correlation pin, a bounded physical length, and an
open rate-sharpness witness.  None of those fields is needed to prove the
finite matched-scale gap of the concrete completed BF4 transfer.

This file extracts the actual dependency.  A
`PhysicalLocalGluingAFCertificate` supplies the finite mean-zero `1/16` form
bound.  Exact stagewise centering and constructive completion extend it to the
whole completed vacuum complement.  The existing positive-form
Cauchy--Schwarz argument then gives the genuine squared-norm estimate

  ||T v||^2 <= (1/16)^2 ||v||^2.

The physical-separator same-object and rate-sharpness obligations remain
necessary for the separate dimensionful correlation/mass interpretation, but
not for this concrete completed finite-stage operator gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Local gluing extends through exact centering -/

/-- Local gluing controls the corrected arbitrary-stage Markov form without
any physical-separator or rate-sharpness data. -/
theorem localGluing_centeredCorrection_form_le_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalLocalGluingAFCertificate
      family law spacing coupling)
    (scale : Nat) (observable : EdgeLabelling → Q') :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
    let E := (centralPhysicalMarkovFormGNS w hw K 0).toGNSData
    let mean := centralPhysicalStationaryMean w hw K 0 observable
    E.B observable observable + -(mean * mean) ≤
      Q'.mkPos 1 16 (by decide) *
        (D.B observable observable + -(mean * mean)) := by
  exact centralPhysical_centeredCorrection_form_le_of_abs_gap
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (Q'.mkPos 1 16 (by decide))
    (fun centered hcentered =>
      certificate.physical_joint_quadratic_abs_le_sixteenth_at
        scale centered hcentered)
    observable

/-- The corrected termwise form inequality, now parametrized only by the
local-gluing certificate. -/
theorem localGluing_cauchyCenteredFormSeq_le_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalLocalGluingAFCertificate
      family law spacing coupling)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData)
    (stage : Nat) :
    CReal.leEv
      (centralPhysicalCauchyCenteredMarkovFormSeq
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 X stage)
      (CReal.mul (CReal.ofQ' (Q'.mkPos 1 16 (by decide)))
        (centralPhysicalCauchyCenteredNormSeq
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 X stage)) := by
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw K 0).toGNSData
  let mean := centralPhysicalStationaryMean w hw K 0 (X.seq stage)
  let normCorrection := D.B (X.seq stage) (X.seq stage) + -(mean * mean)
  let formCorrection := E.B (X.seq stage) (X.seq stage) + -(mean * mean)
  have hfinite : formCorrection ≤
      Q'.mkPos 1 16 (by decide) * normCorrection :=
    localGluing_centeredCorrection_form_le_sixteenth
      certificate scale (X.seq stage)
  refine CReal.leEv_trans
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hfinite)) ?_
  exact CReal.leEv_of_equiv
    (CRealAlg.ofQ'_mul (Q'.mkPos 1 16 (by decide)) normCorrection)

/-! ## 2. Passage to the completed vacuum complement -/

/-- Representative-level completed form gap from local gluing alone. -/
theorem localGluing_cinnerRep_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalLocalGluingAFCertificate
      family law spacing coupling)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData) X)) :
    CReal.leEv
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).cDiagCauchy X) X)
      (CReal.mul (CReal.ofQ' (Q'.mkPos 1 16 (by decide)))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerRep
            X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 X horthogonal)
    (CReal.convergesTo_constMul (Q'.mkPos 1 16 (by decide))
      (centralPhysicalCauchyCenteredNormSeq_converges_self
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 X horthogonal))
  exact localGluing_cauchyCenteredFormSeq_le_sixteenth
    certificate scale X

/-- The concrete completed physical BF4 transfer has the `1/16` form gap on
its entire vacuum complement from local gluing alone. -/
theorem localGluing_completed_vacuum_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalLocalGluingAFCertificate
      family law spacing coupling)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector) vector)
      (CReal.RCscale (Q'.mkPos 1 16 (by decide))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
            vector vector)) := by
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact localGluing_cinnerRep_form_gap_sixteenth
    certificate scale X horthogonal

/-- Package the direct local-gluing result as the reusable completed form-gap
contract. -/
def localGluing_completed_vacuum_form_gap_data
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalLocalGluingAFCertificate
      family law spacing coupling)
    (scale : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (Q'.mkPos 1 16 (by decide)) :=
  ⟨by decide, by decide,
    localGluing_completed_vacuum_form_gap_sixteenth certificate scale⟩

/-! ## 3. Direct completed operator-norm gap -/

/-- At every matched scale, local gluing alone gives the genuine completed
operator estimate `||T v||^2 <= (1/16)^2 ||v||^2` on the vacuum complement. -/
theorem localGluing_completed_vacuum_operator_norm_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate : PhysicalLocalGluingAFCertificate
      family law spacing coupling)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector)
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector))
      (CReal.RCscale
        (Q'.mkPos 1 16 (by decide) * Q'.mkPos 1 16 (by decide))
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          vector vector)) :=
  centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (localGluing_completed_vacuum_form_gap_data certificate scale)
    vector horthogonal

/-! ## Axiom audit -/

#print axioms localGluing_centeredCorrection_form_le_sixteenth
#print axioms localGluing_cinnerRep_form_gap_sixteenth
#print axioms localGluing_completed_vacuum_form_gap_sixteenth
#print axioms localGluing_completed_vacuum_form_gap_data
#print axioms localGluing_completed_vacuum_operator_norm_gap_sixteenth

end YMGap.Continuum.BF4PhysicalLocalGluingCompletedOperatorNormGap
