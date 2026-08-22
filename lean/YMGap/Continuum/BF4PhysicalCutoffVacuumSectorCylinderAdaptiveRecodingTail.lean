/-
# The remaining adaptive recoding tail for the completed BF4 root sector

Base-controlled sector representatives make every input selected by the
existing adaptive Markov schedule support-safe.  At each action cutoff, the
finite recoding constructed in the preceding modules therefore agrees with
the genuine adaptive action on the whole current positive carrier.

This file proves that exact current-cutoff agreement as a zero finite GNS
distance.  It then isolates the remaining infinitary issue as one tail field:
the limiting GNS distance between the sector recoding and the global adaptive
output must tend to zero along the adaptive diagonal.

One such tail field is enough.  A three-leg squared-distance estimate makes
the recoded sector sequence Cauchy, closeness identifies its global image
with the already constructed adaptive transfer, and injectivity of the sector
embedding gives quotient descent.  Thus the field compiles to the exact
completed transfer-lift datum.

No tail datum is constructed here.  A second record exposes a sufficient
diagonal inner-regularity estimate, using the proved zero approximation at
the action cutoff.  This is the precise analytic frontier after finite support
and base scheduling.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_of_pointwise
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-! ## 1. The concrete adaptive input and its sector recoding -/

def centralPhysicalVacuumSectorConcreteAdaptiveInput
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half :=
  (centralPhysicalVacuumSectorBaseControlledCauchy X).seq
    (centralPhysicalVacuumSectorAdaptiveSampleIndex
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) X stage)

def centralPhysicalVacuumSectorConcreteAdaptiveOutput
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half :=
  centralPhysicalVacuumSectorPresentationMarkovAtCutoff stage
    (centralPhysicalVacuumSectorConcreteAdaptiveInput
      hw0 hw1 half X stage)

def centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : CentralPhysicalLinearObservable :=
  (centralPhysicalVacuumSectorConcreteAdaptiveOutput
    hw0 hw1 half X stage).toLinearObservable

def centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy :=
  centralPhysicalAdaptiveMarkovMapCauchy
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal
      (centralPhysicalVacuumSectorBaseControlledCauchy X))

def centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : CentralPhysicalLinearObservable :=
  (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
    hw0 hw1 half X).seq stage

theorem centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable_eq_finite
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
        hw0 hw1 half X stage =
      centralPhysicalFiniteVacuumSectorLinearObservable
        w (Q'.le_of_lt hw0) stage half
        (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff stage
          (centralPhysicalVacuumSectorConcreteAdaptiveInput
            hw0 hw1 half X stage)) := by
  rfl

theorem centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable_eq_action
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
        hw0 hw1 half X stage =
      centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half
        (centralPhysicalVacuumSectorConcreteAdaptiveInput
          hw0 hw1 half X stage).toLinearObservable := by
  rfl

theorem centralPhysicalLinearSquaredSeminorm_distSq_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).distSq
        left right =
      physicalLinearDistSq hw0 hw1 half left right := by
  rfl

theorem centralPhysicalVacuumSectorCylinderSquaredSeminorm_distSq_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half).distSq
        left right =
      physicalLinearDistSq hw0 hw1 half
        left.toLinearObservable right.toLinearObservable := by
  rfl

/-! ## 2. Exact zero distance at the action cutoff -/

/-- The literal finite GNS squared distance of the two outputs is zero at the
action cutoff. -/
theorem centralPhysicalVacuumSectorConcreteAdaptiveOutput_finiteDistSq_eqv_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) stage half).toGNSData.distSqQ
        (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
          hw0 hw1 half X stage).value
        (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
          hw0 hw1 half X stage).value ≈ 0 := by
  rw [centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable_eq_finite,
    centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable_eq_action]
  exact
    centralPhysicalVacuumSectorMarkovCylinder_finiteDistSq_eqv_zero
      (centralPhysicalVacuumSectorConcreteAdaptiveInput
        hw0 hw1 half X stage)
      (centralPhysicalVacuumSectorAdaptiveSample_base_le_stage
        hw0 hw1 half
        (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) X stage)

/-- The named global adaptive output observables inherit the already proved
Cauchy estimate without forcing later proofs to unfold the adaptive sampler. -/
theorem centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutput_isCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (first second : Nat)
    (hfirst :
      (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
        hw0 hw1 half X).modulus epsilon <= first)
    (hsecond :
      (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
        hw0 hw1 half X).modulus epsilon <= second) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
          hw0 hw1 half X first)
        (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
          hw0 hw1 half X second))
      (CReal.ofQ' epsilon) := by
  rw [← centralPhysicalLinearSquaredSeminorm_distSq_eq]
  simpa only [centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable]
    using
    (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
      hw0 hw1 half X).isCauchy epsilon hepsilon first second hfirst hsecond

/-- The cutoff-indexed approximation of the limiting recoding error is
exactly zero at its own action cutoff. -/
theorem centralPhysicalVacuumSectorConcreteAdaptiveOutput_distSq_approx_self_eqv_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    (physicalLinearDistSq hw0 hw1 half
      (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
        hw0 hw1 half X stage)
      (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
        hw0 hw1 half X stage)).approx stage ≈ 0 :=
  Q'.eqv_trans _ _ _
    (physicalLinearDistSq_approx_eqv_stage hw0 hw1 half stage
      (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
        hw0 hw1 half X stage)
      (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
        hw0 hw1 half X stage))
    (centralPhysicalVacuumSectorConcreteAdaptiveOutput_finiteDistSq_eqv_zero
      hw0 hw1 half X stage)

/-! ## 3. One tail field and its diagonal-regularity sufficient condition -/

/-- The one remaining analytic datum: the sector recoding and global adaptive
output become close in the limiting GNS distance. -/
structure CentralPhysicalVacuumSectorAdaptiveRecodingTailData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  rate :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy → Q' → Nat
  close : ∀
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon →
    ∀ stage, rate X epsilon <= stage →
      CReal.leEv
        (physicalLinearDistSq hw0 hw1 half
          (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
            hw0 hw1 half X stage)
          (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
            hw0 hw1 half X stage))
        (CReal.ofQ' epsilon)

/-- A sufficient formulation of the tail: eventually the explicit inner
regularity rate of each moving recoding error is paid by its own action
cutoff. -/
structure CentralPhysicalVacuumSectorAdaptiveRecodingDiagonalRegularityData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  rate :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy → Q' → Nat
  paid : ∀
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q'), (0 : Q') < epsilon →
    ∀ stage, rate X epsilon <= stage →
      (regularizedInnerRegularity
        (physicalLinearDistSqInnerRegularity hw0 hw1 half
          (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
            hw0 hw1 half X stage)
          (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
            hw0 hw1 half X stage))).rate
        (HalfPow.half * epsilon) <= stage

namespace CentralPhysicalVacuumSectorAdaptiveRecodingDiagonalRegularityData

/-- Paying the moving inner regularity turns the exact self-cutoff zero into
the required limiting-distance tail. -/
def toAdaptiveRecodingTailData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingDiagonalRegularityData
      hw0 hw1 half) :
    CentralPhysicalVacuumSectorAdaptiveRecodingTailData hw0 hw1 half where
  rate := data.rate
  close := by
    intro X epsilon hepsilon stage hstage
    let q := HalfPow.half * epsilon
    let distance := physicalLinearDistSq hw0 hw1 half
      (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
        hw0 hw1 half X stage)
      (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
        hw0 hw1 half X stage)
    let regularity := regularizedInnerRegularity
      (physicalLinearDistSqInnerRegularity hw0 hw1 half
        (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
          hw0 hw1 half X stage)
        (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
          hw0 hw1 half X stage))
    have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
    have hpaid : regularity.rate q <= stage :=
      data.paid X epsilon hepsilon stage hstage
    have hzero : distance.approx stage ≈ 0 :=
      centralPhysicalVacuumSectorConcreteAdaptiveOutput_distSq_approx_self_eqv_zero
        hw0 hw1 half X stage
    intro delta hdelta
    refine ⟨regularity.rate q, fun later hlater => ?_⟩
    have hregular := (regularity.regular q hq later stage hlater hpaid).1
    have htoQ : distance.approx later <= q := by
      exact Q'.le_trans' _ _ _ hregular
        (Q'.le_of_eqv
          (Q'.eqv_trans _ (0 + q) _
            (Q'.add_eqv_congr_right _ _ q hzero)
            (Q'.eqv_of_eq (Q'.zero_add' q))))
    have hqepsilon : q <= epsilon := by
      exact Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hq))
        (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
    exact Q'.le_trans' _ _ _ htoQ
      (Q'.le_trans' _ _ _ hqepsilon
        (Q'.add_le_self_of_nonneg epsilon delta (Q'.le_of_lt hdelta)))

end CentralPhysicalVacuumSectorAdaptiveRecodingDiagonalRegularityData

/-! ## 4. The tail constructs the sector Cauchy output and completed lift -/

namespace CentralPhysicalVacuumSectorAdaptiveRecodingTailData

def recodedRate
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let tiny := adaptiveSixteenth epsilon
  max (data.rate X tiny)
    ((centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
      hw0 hw1 half X).modulus tiny)

/-- The three-leg estimate, stated before packaging the output as a Cauchy
record so elaboration does not need to normalize the record projection. -/
theorem recoded_distSq_le
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (first second : Nat)
    (hfirst : data.recodedRate X epsilon <= first)
    (hsecond : data.recodedRate X epsilon <= second) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
          hw0 hw1 half X first)
        (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
          hw0 hw1 half X second))
      (CReal.ofQ' epsilon) := by
  let tiny := adaptiveSixteenth epsilon
  let global := centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
    hw0 hw1 half X
  change max (data.rate X tiny) (global.modulus tiny) <= first at hfirst
  change max (data.rate X tiny) (global.modulus tiny) <= second at hsecond
  have htiny : (0 : Q') < tiny := adaptiveSixteenth_pos hepsilon
  have hfirstClose : data.rate X tiny <= first :=
    Nat.le_trans (Nat.le_max_left _ _) hfirst
  have hsecondClose : data.rate X tiny <= second :=
    Nat.le_trans (Nat.le_max_left _ _) hsecond
  have hfirstGlobal : global.modulus tiny <= first :=
    Nat.le_trans (Nat.le_max_right _ _) hfirst
  have hsecondGlobal : global.modulus tiny <= second :=
    Nat.le_trans (Nat.le_max_right _ _) hsecond
  have hleft := data.close X tiny htiny first hfirstClose
  have hmiddle :=
    centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutput_isCauchy
      hw0 hw1 half X tiny htiny first second
      hfirstGlobal hsecondGlobal
  have hrightRaw := data.close X tiny htiny second hsecondClose
  have hright : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
          hw0 hw1 half X second)
        (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
          hw0 hw1 half X second))
      (CReal.ofQ' tiny) :=
    CReal.leEv_trans
      (CReal.leEv_of_equiv
        (physicalLinearDistSq_symm hw0 hw1 half _ _))
      hrightRaw
  exact distSq_threeLeg_le_of_sixteenth
    (D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half)
    (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
      hw0 hw1 half X first)
    (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
      hw0 hw1 half X first)
    (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable
      hw0 hw1 half X second)
    (centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable
      hw0 hw1 half X second)
    epsilon hepsilon hleft hmiddle hright

def recodedCauchy
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := centralPhysicalVacuumSectorConcreteAdaptiveOutput
    hw0 hw1 half X stage
  modulus := data.recodedRate X
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    rw [centralPhysicalVacuumSectorCylinderSquaredSeminorm_distSq_eq]
    simpa only [centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable]
      using data.recoded_distSq_le X epsilon hepsilon first second
        hfirst hsecond

/-- The tail field, expressed in the exact termwise form required by the
global completion closeness record. -/
theorem recodedCauchyToGlobal_close_at
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat) (hstage : data.rate X epsilon <= stage) :
    CReal.leEv
      ((centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).distSq
        ((centralPhysicalVacuumSectorCylinderCauchyToGlobal
          (data.recodedCauchy X)).seq stage)
        ((centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
          hw0 hw1 half X).seq stage))
      (CReal.ofQ' epsilon) := by
  rw [centralPhysicalLinearSquaredSeminorm_distSq_eq]
  simpa only [centralPhysicalVacuumSectorCylinderCauchyToGlobal,
      recodedCauchy,
      centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable,
      centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable]
    using data.close X epsilon hepsilon stage hstage

/-- The realized recoded sector sequence is close to the already constructed
global adaptive output representative. -/
def recodedCauchyToGlobal_close_adaptive
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        (data.recodedCauchy X))
      (centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputCauchy
        hw0 hw1 half X) where
  modulus := data.rate X
  close := data.recodedCauchyToGlobal_close_at X

theorem recodedCompletionToGlobal_eq_concreteTransfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid
          (data.recodedCauchy X)) =
      centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (Quotient.mk
            (centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).completionSetoid X)) := by
  rw [centralPhysicalVacuumSectorBaseControlledCompletion_eq X]
  apply Quotient.sound
  exact ⟨data.recodedCauchyToGlobal_close_adaptive X⟩

theorem recodedCauchy_completionRel
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half)
    {X Y : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy}
    (h : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).CompletionRel X Y) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).CompletionRel
      (data.recodedCauchy X) (data.recodedCauchy Y) := by
  have hinput :
      Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid X =
        Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid Y :=
    Quotient.sound h
  have hglobalInput := congrArg
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal
      (hw0 := hw0) (hw1 := hw1) (half := half)) hinput
  have hglobalOutput := congrArg
    (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half)
    hglobalInput
  have hrecodedGlobal :
      centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (Quotient.mk
            (centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).completionSetoid
            (data.recodedCauchy X)) =
        centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (Quotient.mk
            (centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).completionSetoid
            (data.recodedCauchy Y)) :=
    Eq.trans (data.recodedCompletionToGlobal_eq_concreteTransfer X)
      (Eq.trans hglobalOutput
        (Eq.symm
          (data.recodedCompletionToGlobal_eq_concreteTransfer Y)))
  have hrecoded :=
    centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
      hrecodedGlobal
  exact Quotient.exact hrecoded

def transfer
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half) :
    CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half →
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half :=
  Quotient.lift
    (fun X => Quotient.mk
      (centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).completionSetoid
      (data.recodedCauchy X))
    (fun _ _ h => Quotient.sound
      (data.recodedCauchy_completionRel h))

def toTransferLiftData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalVacuumSectorAdaptiveRecodingTailData
      hw0 hw1 half) :
    CentralPhysicalVacuumSectorCylinderTransferLiftData hw0 hw1 half where
  transfer := data.transfer
  intertwines := by
    intro vector
    refine Quotient.inductionOn vector ?_
    intro X
    exact data.recodedCompletionToGlobal_eq_concreteTransfer X

end CentralPhysicalVacuumSectorAdaptiveRecodingTailData

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail.centralPhysicalVacuumSectorConcreteAdaptiveOutput_distSq_approx_self_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail.CentralPhysicalVacuumSectorAdaptiveRecodingDiagonalRegularityData.toAdaptiveRecodingTailData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail.CentralPhysicalVacuumSectorAdaptiveRecodingTailData.recodedCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail.CentralPhysicalVacuumSectorAdaptiveRecodingTailData.toTransferLiftData
