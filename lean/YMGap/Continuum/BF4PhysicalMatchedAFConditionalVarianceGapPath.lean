/-
# The matched AF path through posterior variance

For the physical BF4 Gram kernel, the transfer deficit is exactly one half of
the boundary-weighted posterior pairwise variance.  Thus a fraction `epsilon`
of stationary diagonal variance surviving inside the posterior gives the
same-object form rate

    q = 1 - epsilon.

This is the direct Hilbert-space route: it asks neither for total-variation
mixing of every row nor for a lower bound on the unconditioned mass of the
canonical component.  This file makes the finite conditional-variance datum
cofinal in representation cutoff, attaches it to the exact matched AF nome
and physical spacing, and retains the literal completed autocorrelation.

After the finite producer is supplied, the physical scaling obligation is
exactly

    lower * a_j <= epsilon_j <= upper * a_j.

No cofinal posterior-variance fraction, matched cubic law, spacing envelope,
observable pin, continuum carrier, continuum Yang--Mills theory, or Clay
conclusion is inhabited here.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, `noncomputable`, or enlarged heartbeat budget is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge

namespace YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cofinal finite posterior variance -/

/-- One positive posterior-variance fraction valid along a constructive
cofinal sequence of representation cutoffs at fixed nome and volume. -/
structure FixedNomeCofinalVacuumSectorConditionalVarianceFraction
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction <= (1 : Q')
  anchor : Nat -> Nat
  anchor_ge : forall request, request <= anchor request
  conditionalVarianceMargin : forall request (coefficient : Nat -> Q'),
    centralPhysicalFiniteVacuumSectorWeightedMean
        w hw (anchor request) half coefficient ≈ 0 ->
      fraction *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw (anchor request) half coefficient <=
        Q'.mkPos 1 2 (by decide) *
          centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
            w hw (anchor request) half coefficient

namespace FixedNomeCofinalVacuumSectorConditionalVarianceFraction

/-- Recover the exact finite conditional-variance datum at one selected
cutoff. -/
def finiteData
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w hw half)
    (request : Nat) :
    CentralPhysicalFiniteConditionalVarianceGapData
      w hw (family.anchor request) half where
  fraction := family.fraction
  fraction_pos := family.fraction_pos
  fraction_le_one := family.fraction_le_one
  conditionalVarianceMargin := family.conditionalVarianceMargin request

/-- The norm rate complementary to the posterior-variance fraction. -/
def rate
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w hw half) : Q' :=
  (1 : Q') + (-family.fraction)

/-- A cofinal posterior-variance fraction is already the direct cofinal
finite strict-form gap needed by the completed transfer. -/
def toFiniteStrictGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w hw half) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      w hw half family.rate where
  rate_nonnegative := (family.finiteData 0).rate_nonnegative
  rate_lt_one := (family.finiteData 0).rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  sectorGap := by
    intro request coefficient hcenter
    rw [abs_of_nonneg]
    · exact (family.finiteData request).formBound coefficient hcenter
    · exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
        w hw (family.anchor request) half coefficient

/-- The same posterior-variance fraction contracts the actual completed
canonical vacuum-sector transfer. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat}
    (family : FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  family.toFiniteStrictGap.toCompletedStrictContractionData
    hw0 hw1 half

end FixedNomeCofinalVacuumSectorConditionalVarianceFraction

/-! ## 2. The exact matched dynamic family -/

/-- At each physical scale, supply the cofinal posterior-variance fraction for
the literal matched block nome. -/
structure MatchedPhysicalConditionalVarianceGapProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 where
  cofinalFraction : forall scale,
    FixedNomeCofinalVacuumSectorConditionalVarianceFraction
      (trajectory.nome scale)
      (Q'.le_of_lt (trajectory.nome_pos scale))
      0

namespace MatchedPhysicalConditionalVarianceGapProducer

def fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory)
    (scale : Nat) : Q' :=
  (producer.cofinalFraction scale).fraction

def completedGapAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory)
    (scale : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (trajectory.nome_pos scale) (trajectory.nome_lt_one scale) 0 :=
  (producer.cofinalFraction scale).toCompletedStrictContractionData
    (trajectory.nome_pos scale) (trajectory.nome_lt_one scale)

def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory) :
    DynamicVacuumSectorCompletedFamily 0 where
  nome := trajectory.nome
  nome_pos := trajectory.nome_pos
  nome_lt_one := trajectory.nome_lt_one
  transferSpacing := matchedPhysicalDynamicSpacing spacing
    trajectory.coupling trajectory.coupling_pos
    trajectory.coupling_le_window
  transferSpacingToZero := trajectory.transferSpacingToZero
  completedGap := producer.completedGapAt

@[simp] theorem completedGapAt_rate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory)
    (scale : Nat) :
    (producer.completedGapAt scale).rate =
      (1 : Q') + (-producer.fraction scale) :=
  rfl

private theorem one_sub_one_sub_eqv (value : Q') :
    (1 : Q') + (-((1 : Q') + (-value))) ≈ value := by
  have hneg :
      (-((1 : Q') + (-value))) ≈ (-(1 : Q')) + value := by
    refine Q'.eqv_trans _ ((-(1 : Q')) + (-(-value))) _
      (Q'.neg_add_eqv 1 (-value)) ?_
    exact Q'.add_eqv_congr_left (-(1 : Q')) _ _
      (Q'.neg_neg_eqv value)
  refine Q'.eqv_trans _ ((1 : Q') + ((-(1 : Q')) + value)) _
    (Q'.add_eqv_congr_left 1 _ _ hneg) ?_
  refine Q'.eqv_trans _ (((1 : Q') + (-(1 : Q'))) + value) _
    (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) value)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + value) _
    (Q'.add_eqv_congr_right _ _ value
      (Q'.add_neg_self_eqv 1)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' value)

/-- The dimensionless lattice margin is exactly the posterior-variance
fraction in rational equivalence. -/
theorem toCompletedFamily_latticeMargin_eqv_fraction
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory)
    (scale : Nat) :
  producer.toCompletedFamily.latticeMargin scale ≈
      producer.fraction scale := by
  unfold DynamicVacuumSectorCompletedFamily.latticeMargin
  change (1 - (producer.completedGapAt scale).rate) ≈
    producer.fraction scale
  rw [completedGapAt_rate]
  exact one_sub_one_sub_eqv (producer.fraction scale)

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toCompletedFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory)
    (scale : Nat) :
    producer.toCompletedFamily.transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-! ## 3. Physical scaling and the same-object observable -/

/-- The only scale comparison after the posterior fraction is constructed. -/
structure FractionScaling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory) :
    Type 1 where
  lower : Q'
  lower_pos : (0 : Q') < lower
  upper : Q'
  upper_pos : (0 : Q') < upper
  lowerScale : forall scale,
    lower * spacing.a (trajectory.coupling scale) <=
      producer.fraction scale
  upperScale : forall scale,
    producer.fraction scale <=
      upper * spacing.a (trajectory.coupling scale)

namespace FractionScaling

def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConditionalVarianceGapProducer trajectory}
    (scaling : FractionScaling producer) :
    DynamicVacuumSectorPhysicalRateBand producer.toCompletedFamily where
  floor := scaling.lower
  floor_pos := scaling.lower_pos
  ceiling := scaling.upper
  ceiling_pos := scaling.upper_pos
  lowerRate := fun scale =>
    Q'.le_trans' _ _ _ (scaling.lowerScale scale)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (producer.toCompletedFamily_latticeMargin_eqv_fraction scale)))
  upperRate := fun scale =>
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (producer.toCompletedFamily_latticeMargin_eqv_fraction scale))
      (scaling.upperScale scale)

def toContinuumGapTheorem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConditionalVarianceGapProducer trajectory}
    (scaling : FractionScaling producer) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  scaling.toPhysicalRateBand.toContinuumGapTheorem

end FractionScaling

abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer : MatchedPhysicalConditionalVarianceGapProducer trajectory) :
    Type 1 :=
  DynamicVacuumSectorObservablePin producer.toCompletedFamily

def physicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConditionalVarianceGapProducer trajectory}
    (pin : SameObjectObservablePin producer) :
    PhysicalSeparator :=
  pin.toPhysicalSeparator

theorem connectedCorrSq_control
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConditionalVarianceGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (O : pin.Obs) (hO : pin.GaugeInvariantLocal O)
    (scale n : Nat) :
    pin.connectedCorrSq scale O n <=
      pin.amplitude O *
        (((1 : Q') + (-producer.fraction scale)) ^ n) := by
  simpa only [completedGapAt_rate] using
    pin.connectedCorrSq_control O hO scale n

def physicalGapFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : MatchedPhysicalConditionalVarianceGapProducer trajectory}
    (pin : SameObjectObservablePin producer)
    (scaling : FractionScaling producer) :
    PhysicalGapFloor (physicalSeparator pin)
      producer.toCompletedFamily.transferSpacing.spacing
      producer.toCompletedFamily.transferSpacing.spacing_pos :=
  pin.toPhysicalGapFloor scaling.toPhysicalRateBand

end MatchedPhysicalConditionalVarianceGapProducer

end YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.FixedNomeCofinalVacuumSectorConditionalVarianceFraction.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.FixedNomeCofinalVacuumSectorConditionalVarianceFraction.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.MatchedPhysicalConditionalVarianceGapProducer.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.MatchedPhysicalConditionalVarianceGapProducer.toCompletedFamily_latticeMargin_eqv_fraction
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.MatchedPhysicalConditionalVarianceGapProducer.FractionScaling.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.MatchedPhysicalConditionalVarianceGapProducer.FractionScaling.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.MatchedPhysicalConditionalVarianceGapProducer.connectedCorrSq_control
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFConditionalVarianceGapPath.MatchedPhysicalConditionalVarianceGapProducer.physicalGapFloor
