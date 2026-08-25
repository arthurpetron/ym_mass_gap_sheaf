/-
# Exact matched-BF4 AF trajectory into the dynamic completed family

The canonical dynamic-family compiler separates a scalar nome/spacing
trajectory from the local spin-ray capacity and adaptive transition-product
estimates.  Its previously inhabited scalar example is deliberately only a
canonical rational schedule.  This module supplies the missing physical
specialization: the nome at scale `scale` is definitionally

  blockedWeight family (coupling scale),

the exact observable- or exponent-Gram-matched finite BF4 block output, and
the transfer spacing is definitionally

  spacing.a (coupling scale).

No positivity or subunit hypothesis for the nome is added.  Positivity is the
existing finite-atlas theorem `blockedWeight_pos`; strict subunity follows
from the existing cubic matched-action law.  The remaining scalar data are
therefore only a coupling schedule inside that law's window and a constructive
to-zero modulus for the supplied physical spacing.

The local producer remains the genuine two-field analytic frontier: a
cofinal spin-ray capacity and an adaptive conditional transition product,
both indexed by the literal matched block weight at the same scale.  From an
inhabitant, the existing compiler constructs the actual completed canonical
BF4 carrier, transfer, vacuum complement, normalized strength law, and
same-object completed autocorrelation.  A second named certificate pins one
nonzero gauge-invariant observable channel to those exact completed objects.

This does not construct the four-dimensional cubic law, dimensional-
transmutation spacing, local producer, observable pin, strength band,
projective OS/GNS handoff, continuum Yang--Mills theory, or Clay conclusion.
It also does not identify the freely supplied matched finite block family
with the full nonperturbative continuum trajectory.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate

/-! ## 1. Strict subunity is already contained in the matched cubic law -/

/-- A positive rational margin `1 - x` implies `x < 1`. -/
theorem lt_one_of_one_add_neg_pos {x : Q'}
    (h : (0 : Q') < (1 : Q') + (-x)) :
    x < (1 : Q') := by
  have hnum : (0 : Int) < ((1 : Q') + (-x)).num :=
    Q'.num_pos_of_pos h
  show x.num * ((1 : Q').den : Int) <
    (1 : Q').num * (x.den : Int)
  change (0 : Int) <
    (1 : Q').num * (x.den : Int) +
      (-x.num) * ((1 : Q').den : Int) at hnum
  rw [Int.neg_mul] at hnum
  omega

/-- On the matched AF chart, the exact finite matched block weight is
strictly below one.  This is derived, not an extra trajectory field. -/
theorem blockedWeight_lt_one_of_cubicMarginLaw
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g <= law.g₁) :
    blockedWeight family g < (1 : Q') := by
  have hsquare : (0 : Q') < g * g := Q'.mul_pos hg hg
  have hlower : (0 : Q') < half * (g * g) :=
    Q'.mul_pos (by decide) hsquare
  have hmargin : (0 : Q') < blockedMargin family g :=
    Q'.pos_of_lt_of_le hlower
      (blockedMargin_ge_half_square family law g hg hgle)
  exact lt_one_of_one_add_neg_pos hmargin

/-! ## 2. The exact matched physical scalar trajectory -/

/-- The physical spacing evaluated on one coupling schedule.  Its positivity
is inherited from the same `PhysicalSpacingEnvelope` and the same chart
membership proofs used by the matched AF action. -/
def matchedPhysicalDynamicSpacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat -> Q')
    (coupling_pos : forall scale, (0 : Q') < coupling scale)
    (coupling_le_window : forall scale, coupling scale <= law.g₁) :
    PhysicalSpacing where
  spacing := fun scale => spacing.a (coupling scale)
  spacing_pos := fun scale =>
    spacing.a_pos (coupling scale)
      (coupling_pos scale) (coupling_le_window scale)

/-- The only remaining scalar trajectory data after the matched family,
cubic law, and physical spacing envelope have been fixed. -/
structure MatchedPhysicalDynamicScalarTrajectory
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁) : Type 1 where
  coupling : Nat -> Q'
  coupling_pos : forall scale, (0 : Q') < coupling scale
  coupling_le_window : forall scale, coupling scale <= law.g₁
  transferSpacingToZero : SpacingToZero
    (matchedPhysicalDynamicSpacing spacing coupling
      coupling_pos coupling_le_window)

namespace MatchedPhysicalDynamicScalarTrajectory

/-- The literal exact matched block nome at a physical scale. -/
def nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) : Q' :=
  blockedWeight family (trajectory.coupling scale)

theorem nome_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) :
    (0 : Q') < trajectory.nome scale :=
  blockedWeight_pos family (trajectory.coupling scale)

theorem nome_lt_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (scale : Nat) :
    trajectory.nome scale < (1 : Q') :=
  blockedWeight_lt_one_of_cubicMarginLaw family law
    (trajectory.coupling scale)
    (trajectory.coupling_pos scale)
    (trajectory.coupling_le_window scale)

/-- Losslessly expose the matched physical trajectory through the generic
dynamic scalar interface.  Both its nome and spacing reduce to the exact
matched-action data above. -/
def toAdaptiveScalarTrajectory
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    DynamicSpinCubeOffRayAdaptiveScalarTrajectory where
  nome := trajectory.nome
  nome_pos := trajectory.nome_pos
  nome_lt_one := trajectory.nome_lt_one
  transferSpacing := matchedPhysicalDynamicSpacing spacing
    trajectory.coupling trajectory.coupling_pos
    trajectory.coupling_le_window
  transferSpacingToZero := trajectory.transferSpacingToZero

/-! ## 3. The exact remaining local analytic producer and its contraction -/

/-- The local capacity/product producer indexed by the literal matched BF4
block weight and the same physical scale.  No inhabitant is asserted. -/
abbrev LocalProducer
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing) :
    Type 1 :=
  DynamicSpinCubeOffRayAdaptiveLocalProducer
    trajectory.toAdaptiveScalarTrajectory

/-- Construct the existing dynamic adaptive family without changing the
matched action, coupling schedule, spacing, capacity, or transition product. -/
def toDynamicFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  producer.toDynamicFamily

/-- Construct the actual completed canonical BF4 carriers, transfers, and
vacuum complements at every point of the matched physical trajectory. -/
def toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) :
    DynamicVacuumSectorCompletedFamily 0 :=
  producer.toCompletedFamily

/-- The exact normalized-strength law of those same completed transfers. -/
def toNormalizedStrengthLaw
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) :
    DynamicVacuumSectorNormalizedStrengthLaw
      (trajectory.toCompletedFamily producer) :=
  producer.toNormalizedStrengthLaw

/-- The sole two-sided physical scaling certificate remaining after the
matched local producer has constructed its exact normalized strength law. -/
abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  DynamicVacuumSectorStrengthBand
    (trajectory.toNormalizedStrengthLaw producer)

/-- Exact strength scaling compiles to a physical rate band on the literal
matched-action completed transfer family. -/
def toPhysicalRateBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (band : trajectory.StrengthBand producer) :
    DynamicVacuumSectorPhysicalRateBand
      (trajectory.toCompletedFamily producer) :=
  band.toPhysicalRateBand

@[simp] theorem toDynamicFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (scale : Nat) :
    (trajectory.toDynamicFamily producer).nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toDynamicFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (scale : Nat) :
    (trajectory.toDynamicFamily producer).transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-- The compiled nome is also definitionally the weight field of the
same matched physical AF envelope; no Padé trajectory is substituted. -/
@[simp] theorem toDynamicFamily_nome_eq_physicalAFEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (scale : Nat) :
    (trajectory.toDynamicFamily producer).nome scale =
      (physicalAFEnvelope family law spacing).w
        (trajectory.coupling scale) :=
  rfl

@[simp] theorem toCompletedFamily_nome
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (scale : Nat) :
    (trajectory.toCompletedFamily producer).nome scale =
      blockedWeight family (trajectory.coupling scale) :=
  rfl

@[simp] theorem toCompletedFamily_spacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (scale : Nat) :
    (trajectory.toCompletedFamily producer).transferSpacing.spacing scale =
      spacing.a (trajectory.coupling scale) :=
  rfl

/-! ## 4. The exact remaining same-object observable certificate -/

/-- The minimal semantic certificate still needed to select one nonzero
gauge-invariant local observable in these exact matched-action completed
sectors.  Its equality fields pin rational norm squares and connected
correlator squares to literal completed inner products and autocorrelations. -/
abbrev SameObjectObservablePin
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  DynamicVacuumSectorObservablePin
    (trajectory.toCompletedFamily producer)

/-- Any inhabitant of the exact same-object pin compiles to a physical
separator whose rate is the literal completed matched-action transfer rate. -/
def physicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (pin : trajectory.SameObjectObservablePin producer) :
    PhysicalSeparator :=
  pin.toPhysicalSeparator

@[simp] theorem physicalSeparator_rate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (pin : trajectory.SameObjectObservablePin producer)
    (scale : Nat) :
    (physicalSeparator pin).sep scale =
      ((trajectory.toCompletedFamily producer).completedGap scale).rate :=
  rfl

/-- The literal pinned rational connected correlator is controlled by the
same completed matched-action transfer; no proxy rate enters the estimate. -/
theorem connectedCorrSq_control
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (pin : trajectory.SameObjectObservablePin producer)
    (O : pin.Obs) (hO : pin.GaugeInvariantLocal O)
    (scale n : Nat) :
    pin.connectedCorrSq scale O n <=
      pin.amplitude O *
        (((trajectory.toCompletedFamily producer).completedGap scale).rate ^ n) :=
  pin.connectedCorrSq_control O hO scale n

/-- A strength band and the same-object pin produce a two-sided physical gap
floor for the exact separator and exact physical spacing selected above. -/
def physicalGapFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (pin : trajectory.SameObjectObservablePin producer)
    (band : trajectory.StrengthBand producer) :
    PhysicalGapFloor (physicalSeparator pin)
      (trajectory.toCompletedFamily producer).transferSpacing.spacing
      (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos :=
  pin.toPhysicalGapFloor (trajectory.toPhysicalRateBand producer band)

/-- The selected physical separator retains the distinguished nonzero
same-object channel at time zero. -/
theorem physicalSeparator_gapObservable_zero_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (pin : trajectory.SameObjectObservablePin producer)
    (scale : Nat) :
    (0 : Q') <
      (physicalSeparator pin).corrIface.connectedCorr
        scale pin.gapObservable 0 :=
  pin.physicalSeparator_gapObservable_zero_pos scale

end MatchedPhysicalDynamicScalarTrajectory

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.blockedWeight_lt_one_of_cubicMarginLaw
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.matchedPhysicalDynamicSpacing
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.toAdaptiveScalarTrajectory
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.toDynamicFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.toNormalizedStrengthLaw
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.toDynamicFamily_nome_eq_physicalAFEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.physicalSeparator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.connectedCorrSq_control
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.physicalGapFloor
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler.MatchedPhysicalDynamicScalarTrajectory.physicalSeparator_gapObservable_zero_pos
