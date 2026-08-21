/-
# Fixed-nome finite-cutoff BF4 operator-norm gap

`FixedNomeCutoffCenteredSixteenth` states the exact mean-zero physical BF4
form estimate at every representation cutoff of one fixed nome and finite
half-extent.  Its existing consumer constructs a connected Bishop-real form
gap for bounded observables.  This file sends the same certificate through
the genuine finite-cutoff physical GNS completion.

Exact rational centering treats arbitrary representatives of the completed
vacuum complement.  The resulting completed form gap then feeds the existing
constructive form-to-operator theorem, yielding squared-norm contraction by
`(1/16)^2` at every finite representation cutoff.

No fixed-nome certificate is inhabited here.  This is still a family of
finite-cutoff completed spaces, not the cutoff-removed physical completion.
Transport to that one object requires graph-norm convergence of centered
approximants and their transferred images.

## Axiom gate

Only explicit rational centering, constructive-real limits, quotient
induction, and the existing division-free form-to-operator proof are used.
There is no classical choice, noncomputable declaration, custom axiom, or
unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffConnectedGap
import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalFixedNomeCompletedOperatorNormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. The fixed-nome sixteenth on explicit completion representatives -/

/-- At every representative term, a fixed-nome cutoff certificate bounds the
exactly centered physical Markov form by `1/16` times the centered norm. -/
theorem fixedNome_cauchyCenteredFormSeq_le_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half)
    (cutoff : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw cutoff half).toGNSData)
    (stage : Nat) :
    CReal.leEv
      (centralPhysicalCauchyCenteredMarkovFormSeq
        w hw cutoff half X stage)
      (CReal.mul (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalCauchyCenteredNormSeq
          w hw cutoff half X stage)) := by
  let D := (centralPhysicalSmulGNS w hw cutoff half).toGNSData
  let E := (centralPhysicalMarkovFormGNS w hw cutoff half).toGNSData
  let mean := centralPhysicalStationaryMean w hw cutoff half (X.seq stage)
  let normCorrection := D.B (X.seq stage) (X.seq stage) + -(mean * mean)
  let formCorrection := E.B (X.seq stage) (X.seq stage) + -(mean * mean)
  have hfinite : formCorrection <=
      physicalCutoffSixteenth * normCorrection := by
    exact certificate.centeredCorrection_form_le cutoff (X.seq stage)
  refine CReal.leEv_trans
    (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hfinite)) ?_
  have hmul := CRealAlg.ofQ'_mul physicalCutoffSixteenth normCorrection
  exact CReal.leEv_of_equiv hmul

/-- The representative-level fixed-nome completed form gap. -/
theorem fixedNome_cinnerRep_form_gap_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half)
    (cutoff : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS w hw cutoff half).toGNSData)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      w hw cutoff half
      (Quotient.mk
        (cauchySetoid
          (centralPhysicalSmulGNS w hw cutoff half).toGNSData) X)) :
    CReal.leEv
      ((centralPhysicalSmulGNS w hw cutoff half).toGNSData.cinnerRep
        ((centralPhysicalMarkovSymbol
          w hw cutoff half).cDiagCauchy X) X)
      (CReal.mul (CReal.ofQ' physicalCutoffSixteenth)
        ((centralPhysicalSmulGNS
          w hw cutoff half).toGNSData.cinnerRep X X)) := by
  apply CReal.leEv_of_convergesTo_le
    (centralPhysicalCauchyCenteredMarkovFormSeq_converges_form
      w hw cutoff half X horthogonal)
    (CReal.convergesTo_constMul physicalCutoffSixteenth
      (centralPhysicalCauchyCenteredNormSeq_converges_self
        w hw cutoff half X horthogonal))
  exact fixedNome_cauchyCenteredFormSeq_le_sixteenth
    certificate cutoff X

/-! ## 2. The completed finite-cutoff form and operator gaps -/

/-- One fixed-nome certificate gives the literal `1/16` completed form gap at
every finite representation cutoff. -/
theorem fixedNome_completed_vacuum_form_gap_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half)
    (cutoff : Nat)
    (vector : CentralPhysicalGNSCompletion w hw cutoff half)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      w hw cutoff half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw cutoff half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer
          w hw cutoff half vector) vector)
      (CReal.RCscale physicalCutoffSixteenth
        ((centralPhysicalSmulGNS
          w hw cutoff half).toGNSData.cinnerCompl vector vector)) := by
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro X horthogonal
  exact fixedNome_cinnerRep_form_gap_sixteenth
    certificate cutoff X horthogonal

/-- The fixed-nome certificate bundled in the reusable completed physical
form-gap interface at one arbitrary cutoff. -/
def fixedNomeCutoffCompletedVacuumFormGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half)
    (cutoff : Nat) :
    CentralPhysicalCompletedVacuumFormGap
      w hw cutoff half physicalCutoffSixteenth :=
  ⟨physicalCutoffSixteenth_nonnegative,
    physicalCutoffSixteenth_lt_one,
    fixedNome_completed_vacuum_form_gap_sixteenth certificate cutoff⟩

/-- Therefore the genuine finite-cutoff completed Markov transfer contracts
the completed vacuum complement in squared norm by `(1/16)^2`, uniformly in
the representation cutoff. -/
theorem fixedNome_completed_vacuum_operator_norm_gap_sixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCutoffCenteredSixteenth w hw half)
    (cutoff : Nat)
    (vector : CentralPhysicalGNSCompletion w hw cutoff half)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      w hw cutoff half vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS w hw cutoff half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer
          w hw cutoff half vector)
        (centralPhysicalCompletedMarkovTransfer
          w hw cutoff half vector))
      (CReal.RCscale
        (physicalCutoffSixteenth * physicalCutoffSixteenth)
        ((centralPhysicalSmulGNS
          w hw cutoff half).toGNSData.cinnerCompl vector vector)) :=
  centralPhysicalCompletedMarkovTransfer_norm_gap_of_form_gap
    hw cutoff half
    (fixedNomeCutoffCompletedVacuumFormGap certificate cutoff)
    vector horthogonal

/-! ## Axiom audit -/

#print axioms fixedNome_cauchyCenteredFormSeq_le_sixteenth
#print axioms fixedNome_cinnerRep_form_gap_sixteenth
#print axioms fixedNome_completed_vacuum_form_gap_sixteenth
#print axioms fixedNomeCutoffCompletedVacuumFormGap
#print axioms fixedNome_completed_vacuum_operator_norm_gap_sixteenth

end YMGap.Continuum.BF4PhysicalFixedNomeCompletedOperatorNormGap
