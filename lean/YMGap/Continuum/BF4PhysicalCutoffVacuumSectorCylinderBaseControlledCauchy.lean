/-
# Base-controlled Cauchy representatives for the BF4 root sector

The global adaptive Markov transfer samples a Cauchy representative at an
input index chosen below the current action cutoff.  A raw sector
representative need not have its presentation base below its sequence index,
so finite root-sector closure cannot be applied directly.

This module removes that mismatch constructively.  A slow diagonal pays the
base of every selected presentation and an amplitude-scaled stationary-shell
cutoff used by the later recoding-tail estimate.  Before the zeroth requirement is paid
it uses the zero presentation; afterwards it selects a cofinal subsequence of
the original representative.  The result is Cauchy, explicitly close to the
original representative, and satisfies `base <= stage` at every stage.

Consequently every input selected by the existing adaptive Markov schedule
has base at most its action cutoff.  The finite support theorem can therefore
be applied at every adaptive stage.  This does not yet prove that the recoded
sector outputs are Cauchy or completion-close to the global adaptive output.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
import YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The base-paying slow diagonal -/

/-- The canonical zero presentation used only before the zeroth base
requirement becomes admissible. -/
def centralPhysicalVacuumSectorZeroPresentation
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} :
    CentralPhysicalVacuumSectorCylinderPresentation w hw half where
  base := 0
  coefficient := fun _ => 0

/-- The finite coefficient `l1` envelope of one sector presentation. -/
def centralPhysicalVacuumSectorPresentationL1
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) : Q' :=
  coefficientL1
    (centralPhysicalFiniteVacuumSectorIndices
      w hw presentation.base half)
    presentation.coefficient

/-- A squared envelope for the difference between two observables whose
absolute values are bounded by the presentation `l1` envelope. -/
def centralPhysicalVacuumSectorPresentationRecodingSqEnvelope
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) : Q' :=
  let doubled :=
    centralPhysicalVacuumSectorPresentationL1 presentation +
      centralPhysicalVacuumSectorPresentationL1 presentation
  doubled * doubled

theorem centralPhysicalVacuumSectorPresentationRecodingSqEnvelope_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) :
    (0 : Q') ≤
      centralPhysicalVacuumSectorPresentationRecodingSqEnvelope
        presentation := by
  have hl1 : (0 : Q') ≤
      centralPhysicalVacuumSectorPresentationL1 presentation := by
    unfold centralPhysicalVacuumSectorPresentationL1
    exact coefficientL1_nonnegative_local _ _
  unfold centralPhysicalVacuumSectorPresentationRecodingSqEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ hl1 hl1)
    (Q'.zero_le_add _ _ hl1 hl1)

/-- The source-shell mass tolerance which, after multiplication by the
recoding squared envelope, is at most `epsilon`. -/
def centralPhysicalVacuumSectorPresentationShellTolerance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (epsilon : Q') : Q' :=
  CReal.InnerRegularity.scaleTolerance
    (centralPhysicalVacuumSectorPresentationRecodingSqEnvelope
      presentation)
    epsilon

theorem centralPhysicalVacuumSectorPresentationEnvelope_mul_shellTolerance_le
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    centralPhysicalVacuumSectorPresentationRecodingSqEnvelope presentation *
        centralPhysicalVacuumSectorPresentationShellTolerance
          presentation epsilon ≤
      epsilon := by
  exact CReal.InnerRegularity.mul_scaleTolerance_le
    (centralPhysicalVacuumSectorPresentationRecodingSqEnvelope presentation)
    epsilon
    (centralPhysicalVacuumSectorPresentationRecodingSqEnvelope_nonnegative
      presentation)
    hepsilon

/-- At original sequence index `i`, pay both the literal carrier base and the
stationary shell schedule at amplitude-scaled tolerance `1/(i+1)`. -/
def centralPhysicalVacuumSectorBaseRequirement
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (index : Nat) : Nat :=
  max (X.seq index).base
    (centralPhysicalTargetShellCutoff w half
      (centralPhysicalVacuumSectorPresentationShellTolerance
        (X.seq index) (Q'.invSucc index)))

def centralPhysicalVacuumSectorBaseSampleIndex
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  slowIndex (centralPhysicalVacuumSectorBaseRequirement X) stage

def centralPhysicalVacuumSectorBaseControlledSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half :=
  if slowThreshold
      (centralPhysicalVacuumSectorBaseRequirement X) 0 <= stage then
    X.seq (centralPhysicalVacuumSectorBaseSampleIndex X stage)
  else
    centralPhysicalVacuumSectorZeroPresentation

/-- A common rate which makes the base selector admissible and carries its
selected input index beyond the original Cauchy modulus. -/
def centralPhysicalVacuumSectorBaseControlledRate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  max
    (slowThreshold (centralPhysicalVacuumSectorBaseRequirement X) 0)
    (slowThreshold (centralPhysicalVacuumSectorBaseRequirement X)
      (X.modulus epsilon))

theorem centralPhysicalVacuumSectorBaseControlledRate_zero_paid
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') :
    slowThreshold (centralPhysicalVacuumSectorBaseRequirement X) 0 <=
      centralPhysicalVacuumSectorBaseControlledRate X epsilon := by
  unfold centralPhysicalVacuumSectorBaseControlledRate
  exact Nat.le_max_left _ _

theorem centralPhysicalVacuumSectorBaseControlledRate_modulus_paid
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') :
    slowThreshold (centralPhysicalVacuumSectorBaseRequirement X)
        (X.modulus epsilon) <=
      centralPhysicalVacuumSectorBaseControlledRate X epsilon := by
  unfold centralPhysicalVacuumSectorBaseControlledRate
  exact Nat.le_max_right _ _

/-! ## 2. Cauchyness and equality in the completion -/

/-- The base-paying diagonal is itself a sector Cauchy representative. -/
def centralPhysicalVacuumSectorBaseControlledCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq := centralPhysicalVacuumSectorBaseControlledSeq X
  modulus := centralPhysicalVacuumSectorBaseControlledRate X
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    let required := centralPhysicalVacuumSectorBaseRequirement X
    have hfirstZero : slowThreshold required 0 <= first :=
      Nat.le_trans
        (centralPhysicalVacuumSectorBaseControlledRate_zero_paid X epsilon)
        hfirst
    have hsecondZero : slowThreshold required 0 <= second :=
      Nat.le_trans
        (centralPhysicalVacuumSectorBaseControlledRate_zero_paid X epsilon)
        hsecond
    have hfirstThreshold : slowThreshold required (X.modulus epsilon) <=
        first :=
      Nat.le_trans
        (centralPhysicalVacuumSectorBaseControlledRate_modulus_paid X epsilon)
        hfirst
    have hsecondThreshold : slowThreshold required (X.modulus epsilon) <=
        second :=
      Nat.le_trans
        (centralPhysicalVacuumSectorBaseControlledRate_modulus_paid X epsilon)
        hsecond
    have hfirstIndex : X.modulus epsilon <=
        centralPhysicalVacuumSectorBaseSampleIndex X first :=
      slowIndex_cofinal required (X.modulus epsilon) first hfirstThreshold
    have hsecondIndex : X.modulus epsilon <=
        centralPhysicalVacuumSectorBaseSampleIndex X second :=
      slowIndex_cofinal required (X.modulus epsilon) second hsecondThreshold
    unfold centralPhysicalVacuumSectorBaseControlledSeq
    rw [if_pos hfirstZero, if_pos hsecondZero]
    exact X.isCauchy epsilon hepsilon _ _ hfirstIndex hsecondIndex

/-- The controlled representative is explicitly close to the original one. -/
def centralPhysicalVacuumSectorBaseControlledClose
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X
      (centralPhysicalVacuumSectorBaseControlledCauchy X) where
  modulus := centralPhysicalVacuumSectorBaseControlledRate X
  close := by
    intro epsilon hepsilon stage hstage
    let required := centralPhysicalVacuumSectorBaseRequirement X
    have hzero : slowThreshold required 0 <= stage :=
      Nat.le_trans
        (centralPhysicalVacuumSectorBaseControlledRate_zero_paid X epsilon)
        hstage
    have hthreshold : slowThreshold required (X.modulus epsilon) <= stage :=
      Nat.le_trans
        (centralPhysicalVacuumSectorBaseControlledRate_modulus_paid X epsilon)
        hstage
    have hstageModulus : X.modulus epsilon <= stage :=
      Nat.le_trans (self_le_slowThreshold required (X.modulus epsilon))
        hthreshold
    have hindex : X.modulus epsilon <=
        centralPhysicalVacuumSectorBaseSampleIndex X stage :=
      slowIndex_cofinal required (X.modulus epsilon) stage hthreshold
    change CReal.leEv
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).distSq
          (X.seq stage)
          (centralPhysicalVacuumSectorBaseControlledSeq X stage))
      (CReal.ofQ' epsilon)
    rw [centralPhysicalVacuumSectorBaseControlledSeq, if_pos hzero]
    exact X.isCauchy epsilon hepsilon _ _ hstageModulus hindex

/-- Replacing a representative by its base-controlled version does not alter
its point in the sector completion. -/
theorem centralPhysicalVacuumSectorBaseControlledCompletion_eq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X =
      Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalVacuumSectorBaseControlledCauchy X) :=
  Quotient.sound
    ⟨centralPhysicalVacuumSectorBaseControlledClose X⟩

/-! ## 3. Every adaptive action cutoff dominates its selected base -/

theorem centralPhysicalVacuumSectorBaseControlled_base_le_stage
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    ((centralPhysicalVacuumSectorBaseControlledCauchy X).seq stage).base <=
      stage := by
  let required := centralPhysicalVacuumSectorBaseRequirement X
  change (centralPhysicalVacuumSectorBaseControlledSeq X stage).base <= stage
  unfold centralPhysicalVacuumSectorBaseControlledSeq
  split
  case isTrue hzero =>
    exact Nat.le_trans (Nat.le_max_left _ _)
      (required_slowIndex_le required stage hzero)
  case isFalse =>
    exact Nat.zero_le _

/-- Once the zeroth slow-diagonal requirement is admissible, the selected
presentation's amplitude-scaled stationary shell cutoff is also paid by the
current sequence stage. -/
theorem centralPhysicalVacuumSectorBaseControlled_shellCutoff_le_stage
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat)
    (hzero : slowThreshold
      (centralPhysicalVacuumSectorBaseRequirement X) 0 <= stage) :
    centralPhysicalTargetShellCutoff w half
        (centralPhysicalVacuumSectorPresentationShellTolerance
          (X.seq (centralPhysicalVacuumSectorBaseSampleIndex X stage))
          (Q'.invSucc
            (centralPhysicalVacuumSectorBaseSampleIndex X stage))) <=
      stage := by
  let required := centralPhysicalVacuumSectorBaseRequirement X
  exact Nat.le_trans (Nat.le_max_right _ _)
    (required_slowIndex_le required stage hzero)

/-- The generic adaptive input selector never exceeds its action stage. -/
theorem centralPhysicalAdaptiveMarkovSampleIndex_le_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    centralPhysicalAdaptiveMarkovSampleIndex
        hw0 hw1 half pointwise X stage <= stage :=
  greatestAdmissibleAux_le
    (centralPhysicalAdaptiveMarkovRequirement
      hw0 hw1 half pointwise X) stage stage

def centralPhysicalVacuumSectorAdaptiveSampleIndex
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  centralPhysicalAdaptiveMarkovSampleIndex hw0 hw1 half pointwise
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal
      (centralPhysicalVacuumSectorBaseControlledCauchy X)) stage

/-- The base of the presentation selected by the global adaptive transfer is
always below the current action cutoff. -/
theorem centralPhysicalVacuumSectorAdaptiveSample_base_le_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    ((centralPhysicalVacuumSectorBaseControlledCauchy X).seq
      (centralPhysicalVacuumSectorAdaptiveSampleIndex
        hw0 hw1 half pointwise X stage)).base <= stage := by
  exact Nat.le_trans
    (centralPhysicalVacuumSectorBaseControlled_base_le_stage X
      (centralPhysicalVacuumSectorAdaptiveSampleIndex
        hw0 hw1 half pointwise X stage))
    (centralPhysicalAdaptiveMarkovSampleIndex_le_stage
      hw0 hw1 half pointwise
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        (centralPhysicalVacuumSectorBaseControlledCauchy X)) stage)

/-- At every adaptive stage, the sampled finite Markov image therefore has an
exact canonical-sector cylinder realization on the whole current carrier. -/
theorem centralPhysicalVacuumSectorAdaptiveSample_realization_value
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage target : Nat)
    (htarget : target < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) stage half) :
    let input := (centralPhysicalVacuumSectorBaseControlledCauchy X).seq
      (centralPhysicalVacuumSectorAdaptiveSampleIndex
        hw0 hw1 half pointwise X stage)
    (centralPhysicalFiniteVacuumSectorLinearObservable
        w (Q'.le_of_lt hw0) stage half
        (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
          stage input)).value
        (centralPhysicalFiniteStateAt
          w (Q'.le_of_lt hw0) stage half target) ≈
      centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        stage input target := by
  let input := (centralPhysicalVacuumSectorBaseControlledCauchy X).seq
    (centralPhysicalVacuumSectorAdaptiveSampleIndex
      hw0 hw1 half pointwise X stage)
  exact centralPhysicalVacuumSectorMarkovCylinderRealization_value
    input
    (centralPhysicalVacuumSectorAdaptiveSample_base_le_stage
      hw0 hw1 half pointwise X stage)
    htarget

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.centralPhysicalVacuumSectorBaseControlledCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.centralPhysicalVacuumSectorPresentationEnvelope_mul_shellTolerance_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.centralPhysicalVacuumSectorBaseControlled_shellCutoff_le_stage
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.centralPhysicalVacuumSectorBaseControlledCompletion_eq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.centralPhysicalVacuumSectorAdaptiveSample_base_le_stage
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.centralPhysicalVacuumSectorAdaptiveSample_realization_value
