/-
# Lifting a dense BF4-to-endpoint comparison through both completions

This module moves the remaining comparison problem from an arbitrary map on
completed carriers to explicit dense-stage analytic data.  A physical GNS
Cauchy sequence is sent termwise to strict-cylinder stages; exact squared-
distance and inner-form identities then provide the metric and norm laws.

One constructive seam must remain visible.  `CauchyNull` in the physical GNS
completion states `forall epsilon, exists N` in `Prop`, whereas the strict
seminorm completion requires a Type-valued modulus `epsilon -> Nat`.  Lean
cannot extract the latter from the former without choice.  The field
`nullModulusTransport` records exactly this missing witness and nothing more.

Given that witness plus dense inner, macro-time, and vacuum identifications,
the module constructs the corrected four-field completed endpoint
intertwiner.  It does not construct the dense analytic data themselves.
-/

import YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner

namespace YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner
open YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner.CompletedBF4MacroEndpointIntertwiner
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Dense analytic comparison data -/

/-- Dense-stage data sufficient to construct the completed physical-to-strong
endpoint map.

`nullModulusTransport` is deliberately a `Sigma` witness in `Type`: it is the
constructive choice data needed to descend the termwise stage map through the
two completions' differently packaged null relations. -/
structure DenseBF4MacroEndpointLiftData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    {endpointCoupling : Q'}
    (hendpoint : (0 : Q') ≤ endpointCoupling)
    (hle : endpointCoupling ≤ anchorCoupling)
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) : Type 1 where
  /-- Map one finite physical observable to one finite strong-cylinder stage. -/
  toStrongStage : (scale : Nat) →
    (EdgeLabelling → Q') → StrictJointCylinderStage
  /-- The dense map is exactly isometric for squared distance. -/
  distSqIdentification : ∀ scale left right,
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hendpoint hle
        (toStrongStage scale left) (toStrongStage scale right))
      (CReal.ofQ'
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.distSqQ
          left right))
  /-- Explicit transport of an asymptotically null physical representative
  pair to the Type-valued modulus demanded by the strong completion. -/
  nullModulusTransport : ∀ scale
      (X Y : CauchyGNS
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData),
    CauchyNull
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData X Y →
      Σ' modulus : Q' → Nat,
        ∀ epsilon, (0 : Q') < epsilon → ∀ n, modulus epsilon ≤ n →
          CReal.leEv
            (strictJointCylinderStageReflectionDistSq hendpoint hle
              (toStrongStage scale (X.seq n))
              (toStrongStage scale (Y.seq n)))
            (CReal.ofQ' epsilon)
  /-- Exact dense identification of the full bilinear forms. -/
  innerIdentification : ∀ scale left right,
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hendpoint hle
        (toStrongStage scale left) (toStrongStage scale right))
      (CReal.ofQ'
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.B
          left right))
  /-- One physical macro action agrees, modulo the strong radical, with one
  strict two-step time translation. -/
  macroStageNull : ∀ scale observable,
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Null
      (toStrongStage scale
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable))
      ((toStrongStage scale observable).timeTranslate (1 + 1))
  /-- The dense physical constant vacuum maps to the strong vacuum stage,
  modulo exactly the radical used by the strong completion. -/
  vacuumStageNull : ∀ scale,
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Null
      (toStrongStage scale centralPhysicalVacuumCarrier)
      strictJointCylinderVacuumStage

namespace DenseBF4MacroEndpointLiftData

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    {endpointCoupling : Q'}
    {hendpoint : (0 : Q') ≤ endpointCoupling}
    {hle : endpointCoupling ≤ anchorCoupling}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}

abbrev AnchoredPhysicalMacroGap
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) : Prop :=
  CentralPhysicalCompletedMacroVacuumNormGap producer
    anchorDecoratedDoubledTimeRate

private theorem czero_le_ofQ'_of_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv CReal.czero (CReal.ofQ' epsilon) :=
  CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hepsilon))

/-! ## 2. Termwise map and quotient descent -/

/-- Map a physical GNS Cauchy representative termwise to the strict-stage
completion datum. -/
def mapPhysicalCauchy
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData) :
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Cauchy where
  seq := fun n => data.toStrongStage scale (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (data.distSqIdentification scale (X.seq m) (X.seq n)))
      (CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ'
          (X.isCauchy epsilon hepsilon m n hm hn)))

/-- The explicit null-modulus field is precisely what is needed for quotient
descent into the strong completion. -/
theorem mapPhysicalCauchy_completionRel
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    {X Y : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData}
    (hXY : CauchyNull
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData X Y) :
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).CompletionRel
      (data.mapPhysicalCauchy scale X)
      (data.mapPhysicalCauchy scale Y) := by
  obtain ⟨modulus, hmodulus⟩ :=
    data.nullModulusTransport scale X Y hXY
  exact ⟨{
    modulus := modulus
    close := hmodulus
  }⟩

/-- The completed map constructed from the dense stage map and its explicit
null-modulus transport. -/
def completedMap
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat) :
    CentralPhysicalGNSCompletion
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 →
      StrictJointCylinderOSCompletion hendpoint hle :=
  Quotient.lift
    (fun X => Quotient.mk
      (strictJointCylinderStageSquaredSeminorm hendpoint hle).completionSetoid
      (data.mapPhysicalCauchy scale X))
    (fun _ _ h => Quotient.sound
      (data.mapPhysicalCauchy_completionRel scale h))

/-- Computation of the completed map on a physical Cauchy representative. -/
@[simp] theorem completedMap_mk
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData) :
    data.completedMap scale
        (Quotient.mk
          (cauchySetoid
            (centralPhysicalSmulGNS
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0).toGNSData) X) =
      Quotient.mk
        (strictJointCylinderStageSquaredSeminorm hendpoint hle).completionSetoid
        (data.mapPhysicalCauchy scale X) :=
  rfl

/-- On the dense image, the constructed completion map is the strong constant
embedding of the selected finite stage. -/
theorem completedMap_embed
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat) (observable : EdgeLabelling → Q') :
    data.completedMap scale
        (centralPhysicalCompletedObservable
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable) =
      (strictJointCylinderStageSquaredSeminorm hendpoint hle).embedRep
        (data.toStrongStage scale observable) := by
  apply Quotient.sound
  exact ⟨{
    modulus := fun _ => 0
    close := by
      intro epsilon hepsilon n hn
      exact CReal.leEv_trans
        (CReal.leEv_of_equiv
          ((strictJointCylinderStageSquaredSeminorm hendpoint hle).distSq_refl
            (data.toStrongStage scale observable)))
        (czero_le_ofQ'_of_pos hepsilon)
  }⟩

/-! ## 3. Completed inner and norm identification -/

/-- Representative-level full inner-product identification. -/
theorem mappedCauchy_inner_equiv
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    (X Y : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData) :
    CReal.Equiv
      (cauchyPairingLimit hendpoint hle
        (data.mapPhysicalCauchy scale X)
        (data.mapPhysicalCauchy scale Y))
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerRep
        X Y) := by
  let D := (centralPhysicalSmulGNS
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0).toGNSData
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hendpoint hle
      (data.mapPhysicalCauchy scale X)
      (data.mapPhysicalCauchy scale Y))
    (bSeq := fun n => CReal.ofQ' (D.cInnerSeq X Y n))
  · intro n
    exact data.innerIdentification scale (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hendpoint hle
      (data.mapPhysicalCauchy scale X)
      (data.mapPhysicalCauchy scale Y)
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

/-- The constructed map preserves the full completed physical inner product,
not only diagonal norms. -/
theorem completedMap_inner
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    (left right : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0) :
    strictJointCylinderCompletedInner hendpoint hle
        (data.completedMap scale left) (data.completedMap scale right) =
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        left right := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  apply Quotient.sound
  exact data.mappedCauchy_inner_equiv scale X Y

/-! ## 4. Macro and vacuum laws on the completion -/

/-- The dense radical-valued macro identity descends to exact one-step
intertwining on the completions. -/
theorem completedMap_macroTransferIntertwining
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0) :
    data.completedMap scale
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector) =
      strictJointCylinderCompletedTwoStepTransfer hendpoint hle
        (data.completedMap scale vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  apply Quotient.sound
  exact ⟨{
    modulus := fun _ => 0
    close := by
      intro epsilon hepsilon n hn
      exact CReal.leEv_trans
        (CReal.leEv_of_equiv
          (data.macroStageNull scale (X.seq n)))
        (czero_le_ofQ'_of_pos hepsilon)
  }⟩

/-- The completed map sends the physical stationary vacuum to the constructed
strong stationary vacuum. -/
theorem completedMap_vacuum
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat) :
    data.completedMap scale
        (centralPhysicalCompletedVacuum
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0) =
      strictJointCylinderCompletionVacuum hendpoint hle := by
  change data.completedMap scale
      (centralPhysicalCompletedObservable
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        centralPhysicalVacuumCarrier) = _
  rw [data.completedMap_embed]
  exact (strictJointCylinderStageSquaredSeminorm hendpoint hle).embedRep_eq_of_null
    (data.vacuumStageNull scale)

/-- Full inner preservation and vacuum identification make preservation of the
completed vacuum complement a theorem. -/
theorem completedMap_mapsVacuumOrthogonal
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 vector) :
    StrictJointCylinderCompletionVacuumOrthogonal hendpoint hle
      (data.completedMap scale vector) := by
  unfold StrictJointCylinderCompletionVacuumOrthogonal
  rw [← data.completedMap_vacuum scale]
  rw [data.completedMap_inner scale]
  exact horthogonal

/-! ## 5. Contraction to the corrected completed residual -/

/-- Dense analytic comparison data plus the explicit null-modulus transport
construct the entire corrected completed endpoint intertwiner. -/
def toCompletedIntertwiner
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer) :
    CompletedBF4MacroEndpointIntertwiner hendpoint hle producer where
  toStrong := data.completedMap
  normIdentification := fun scale vector =>
    data.completedMap_inner scale vector vector
  macroTransferIntertwining := data.completedMap_macroTransferIntertwining
  mapsVacuumOrthogonal := data.completedMap_mapsVacuumOrthogonal

/-! ## 6. The first completed physical consequence -/

/-! The result type is inferred from the existing endpoint theorem.  Avoiding
an expanded expected type keeps this thin contraction within the module's
normal recursion budget. -/
/-- The dense endpoint certificate contracts directly to the uniform completed
physical vacuum-complement norm gap.  This theorem is intentionally a thin
named edge: it adds no new comparison hypothesis and makes explicit that the
only remaining input is the dense analytic lift data itself. -/
theorem toCompletedIntertwiner_physicalMacroVacuumNormGap
    (data : DenseBF4MacroEndpointLiftData hendpoint hle producer) :
    AnchoredPhysicalMacroGap producer :=
  CompletedBF4MacroEndpointIntertwiner.physicalMacroVacuumNormGap
    (data.toCompletedIntertwiner)

end DenseBF4MacroEndpointLiftData

end YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift

#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.mapPhysicalCauchy
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.completedMap
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.completedMap_embed
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.completedMap_inner
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.completedMap_macroTransferIntertwining
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.completedMap_vacuum
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.completedMap_mapsVacuumOrthogonal
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.toCompletedIntertwiner
#print axioms YMGap.Continuum.BF4PhysicalDenseMacroEndpointLift.DenseBF4MacroEndpointLiftData.toCompletedIntertwiner_physicalMacroVacuumNormGap
