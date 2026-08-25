/-
# Pointwise matched support-debt variation compiler

The exact matched support-debt factorization leaves three analytic inputs at
each physical scale: variation of the routed-load denominator, variation of
the supported-kernel numerator, and a positive uniform numerator floor.  This
module pushes all three down to the literal consecutive finite carriers.

The maximum and minimum variation inputs carry explicit current-to-next and
next-to-current pair recodings, their carrier-membership proofs, summable
pointwise budgets, and the one-sided estimates in the orientations required
by the extrema.  The floor input is a pointwise noncollapse inequality on the
same supported-kernel candidate.  Existing generic extrema compilers fold
those data, after which the exact matched ratio compiler contracts them into
variation of the existing compact support-debt stream.

No recoding estimate, tail modulus, or kernel floor is inhabited here.  No
persistence, observable pin, continuum Yang--Mills theory, or Clay conclusion
is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Literal matched dynamic carrier and pointwise values -/

/-- The exact finite vacuum-sector pair carrier at one matched physical scale
and one offset beyond its selected transition start. -/
def matchedEventualCanonicalVacuumSectorPairs
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat) : List (Nat × Nat) :=
  centralPhysicalFiniteVacuumSectorPairs
    (trajectory.nome scale)
    (Q'.le_of_lt (trajectory.nome_pos scale))
    (transitionStart scale + offset) 0

/-- The literal routed transition-product load on one pair in that carrier. -/
def matchedEventualCanonicalRoutedLoadOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat)
    (pair : Nat × Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)
    pair

/-- The literal support-aware conditional-kernel candidate on the same pair. -/
def matchedEventualCanonicalSupportedKernelCandidateOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale offset : Nat)
    (pair : Nat × Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
    (matchedEventualCanonicalRoutingAt
      trajectory transitionStart scale offset)
    pair.1 pair.2

/-! ## 2. Three parallel pointwise certificate types -/

/-- Bidirectional pointwise recoding and summable variation for the exact
matched routed-load maximum. -/
abbrev MatchedEventualCanonicalRoutedLoadMaximumVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) : Type 1 :=
  DynamicFiniteMaximumVariation
    (matchedEventualCanonicalRoutedLoadOnPair
      trajectory transitionStart scale)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart scale)

/-- Bidirectional pointwise recoding and summable variation for the exact
matched support-aware conditional-kernel minimum. -/
abbrev MatchedEventualCanonicalSupportedKernelMinimumVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) : Type 1 :=
  DynamicFiniteMinimumVariation
    (matchedEventualCanonicalSupportedKernelCandidateOnPair
      trajectory transitionStart scale)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart scale)

/-- A positive pointwise noncollapse floor for the same matched supported
kernel candidate on every later carrier. -/
abbrev MatchedEventualCanonicalSupportedKernelMinimumFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat) : Type 1 :=
  DynamicFiniteMinimumFloor
    (matchedEventualCanonicalSupportedKernelCandidateOnPair
      trajectory transitionStart scale)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart scale)

/-! ## 3. Fold the literal dynamic extrema -/

/-- Fold the two explicit carrier recodings into variation of the exact
routed-load maximum. -/
def matchedEventualCanonicalRoutedLoadMaximumVariationOfPointwise
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalRoutedLoadMaximumVariation
      trajectory transitionStart scale) :
    SummableRationalStepVariation
      (fun offset =>
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
          (matchedEventualCanonicalRoutingAt
            trajectory transitionStart scale offset)) := by
  change SummableRationalStepVariation
    (fun offset => listQMaxZero
      (matchedEventualCanonicalRoutedLoadOnPair
        trajectory transitionStart scale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart scale offset))
  exact data.toSummableRationalStepVariation

/-- Add the unchanged positive unit seed and obtain variation of the exact
matched routed-load denominator required by the ratio compiler. -/
def matchedEventualCanonicalRoutedLoadDenominatorVariationOfPointwise
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalRoutedLoadMaximumVariation
      trajectory transitionStart scale) :
    SummableRationalStepVariation
      (matchedEventualCanonicalRoutedLoadDenominator
        trajectory transitionStart scale) := by
  let unitVariation :=
    SummableRationalStepVariation.ofPointwiseEqvConstant
      (fun _offset => (1 : Q')) 1 (fun _offset => Q'.eqv_refl 1)
  let maximumVariation :=
    matchedEventualCanonicalRoutedLoadMaximumVariationOfPointwise
      trajectory transitionStart scale data
  exact add unitVariation maximumVariation

/-- Fold the dual pair recodings into variation of the exact support-aware
conditional-kernel minimum. -/
def matchedEventualCanonicalSupportedKernelMinimumVariationOfPointwise
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalSupportedKernelMinimumVariation
      trajectory transitionStart scale) :
    SummableRationalStepVariation
      (fun offset =>
        centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
          (matchedEventualCanonicalRoutingAt
            trajectory transitionStart scale offset)) := by
  change SummableRationalStepVariation
    (fun offset => listPositiveMinOne
      (matchedEventualCanonicalSupportedKernelCandidateOnPair
        trajectory transitionStart scale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart scale offset))
  exact data.toSummableRationalStepVariation

/-- Scale the folded minimum by the literal half factor used in the exact
matched support numerator. -/
def matchedEventualCanonicalSupportedKernelNumeratorVariationOfPointwise
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalSupportedKernelMinimumVariation
      trajectory transitionStart scale) :
    SummableRationalStepVariation
      (matchedEventualCanonicalSupportedKernelNumerator
        trajectory transitionStart scale) :=
  SummableRationalStepVariationAlgebra.scale
    (matchedEventualCanonicalSupportedKernelMinimumVariationOfPointwise
      trajectory transitionStart scale data)
    HalfPow.half (by decide)

/-- Scale the pointwise kernel floor by the same literal half factor. -/
def matchedEventualCanonicalSupportedKernelNumeratorFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalSupportedKernelMinimumFloor
      trajectory transitionStart scale) : Q' :=
  HalfPow.half * data.floor

theorem matchedEventualCanonicalSupportedKernelNumeratorFloor_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalSupportedKernelMinimumFloor
      trajectory transitionStart scale) :
    (0 : Q') <
      matchedEventualCanonicalSupportedKernelNumeratorFloor
        trajectory transitionStart scale data :=
  Q'.mul_pos (by decide) data.floor_pos

theorem matchedEventualCanonicalSupportedKernelNumeratorFloor_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (data : MatchedEventualCanonicalSupportedKernelMinimumFloor
      trajectory transitionStart scale)
    (offset : Nat) :
    matchedEventualCanonicalSupportedKernelNumeratorFloor
        trajectory transitionStart scale data <=
      matchedEventualCanonicalSupportedKernelNumerator
        trajectory transitionStart scale offset := by
  unfold matchedEventualCanonicalSupportedKernelNumeratorFloor
    matchedEventualCanonicalSupportedKernelNumerator
  change HalfPow.half * data.floor <=
    HalfPow.half * listPositiveMinOne
      (matchedEventualCanonicalSupportedKernelCandidateOnPair
        trajectory transitionStart scale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart scale offset)
  exact Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    (data.le_minimum offset) (by decide)

/-! ## 4. Observable-connected three-way join -/

/-- The three independently provable pointwise inputs contract to summable
variation of the existing compact matched support-debt stream. -/
def matchedEventualCanonicalSupportCapacityDebtVariationOfPointwise
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (scale : Nat)
    (loadData : MatchedEventualCanonicalRoutedLoadMaximumVariation
      trajectory transitionStart scale)
    (kernelVariationData :
      MatchedEventualCanonicalSupportedKernelMinimumVariation
        trajectory transitionStart scale)
    (kernelFloorData :
      MatchedEventualCanonicalSupportedKernelMinimumFloor
        trajectory transitionStart scale) :
    SummableRationalStepVariation
      (matchedEventualCanonicalSupportCapacityDebt
        trajectory transitionStart scale) :=
  matchedEventualCanonicalSupportCapacityDebtVariationOfPrimitiveComponents
    trajectory transitionStart scale
    (matchedEventualCanonicalRoutedLoadDenominatorVariationOfPointwise
      trajectory transitionStart scale loadData)
    (matchedEventualCanonicalSupportedKernelNumeratorVariationOfPointwise
      trajectory transitionStart scale kernelVariationData)
    (matchedEventualCanonicalSupportedKernelNumeratorFloor
      trajectory transitionStart scale kernelFloorData)
    (matchedEventualCanonicalSupportedKernelNumeratorFloor_pos
      trajectory transitionStart scale kernelFloorData)
    (matchedEventualCanonicalSupportedKernelNumeratorFloor_le
      trajectory transitionStart scale kernelFloorData)

/-! ## 5. End-to-end pointwise prefix-tail constructor -/

/-- Contract three explicit pointwise certificate families, a tail allowance,
and the computed initial-slack inequality to the pre-existing no-free-proxy
prefix-tail persistence producer.  Explicit arguments avoid an elaboration-
heavy dependent convenience record while retaining exactly the same data and
conclusion. -/
def matchedEventualCanonicalSupportDebtPrefixTailProducerOfPointwise
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (loadData : forall scale,
      MatchedEventualCanonicalRoutedLoadMaximumVariation
        trajectory transitionStart scale)
    (kernelVariationData : forall scale,
      MatchedEventualCanonicalSupportedKernelMinimumVariation
        trajectory transitionStart scale)
    (kernelFloorData : forall scale,
      MatchedEventualCanonicalSupportedKernelMinimumFloor
        trajectory transitionStart scale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall scale,
      (0 : Q') < tailAllowance scale)
    (initial_closure : forall scale,
      matchedEventualCanonicalSupportCapacityDebt
            trajectory transitionStart scale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalSupportCapacityDebtVariationOfPointwise
              trajectory transitionStart scale
              (loadData scale)
              (kernelVariationData scale)
              (kernelFloorData scale))
            (tailAllowance scale) <=
        (1 : Q')) :
    MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
      trajectory where
  transitionStart := transitionStart
  debtVariation := fun scale =>
    matchedEventualCanonicalSupportCapacityDebtVariationOfPointwise
      trajectory transitionStart scale
      (loadData scale) (kernelVariationData scale) (kernelFloorData scale)
  tailAllowance := tailAllowance
  tailAllowance_pos := tailAllowance_pos
  initial_closure := initial_closure

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalRoutedLoadMaximumVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalRoutedLoadDenominatorVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalSupportedKernelMinimumVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalSupportedKernelNumeratorVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalSupportedKernelNumeratorFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalSupportedKernelNumeratorFloor_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalSupportCapacityDebtVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.matchedEventualCanonicalSupportDebtPrefixTailProducerOfPointwise
