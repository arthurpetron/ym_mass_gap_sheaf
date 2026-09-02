/-
# Put the physical observable transport schedule on one matched AF chart

The raw-transport tail is only physically interpretable when its heat nome
and lattice spacing come from the same trajectory.  This module builds that
coherent schedule from the existing exact matched-BF4 block output

  blockedWeight family (coupling scale)

and the existing physical spacing on the same rational AF coordinate

  spacing.a (coupling scale).

Positivity and strict subunity of the nome are theorems from the matched
cubic-margin law.  Vanishing of the spacing is derived from the quadratic
physical envelope and a constructive coupling-to-zero modulus.  A second
constructor obtains that modulus from an exact shifted-AF-trajectory
identification, so no independent spacing-to-zero field remains there.

The nested face geometry is still supplied explicitly.  No raw-mismatch or
sign-matching `O(a)` bound is constructed, and neither the cubic margin law
nor the physical spacing envelope is inhabited here.  Thus this is a
same-chart trajectory bridge, not a continuum Yang--Mills construction,
OS/GNS reconstruction, or mass-gap theorem.

Constructive contract: exact rational functions and Type-valued witnesses
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.BF4AFPhysicalSpacingToZero
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.CompactDualSlabObservablePhysicalSignMatchedTransportTail

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualSlabObservableDecimationPhysicalTransport
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSignMatchedTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep
open YMGap.Continuum.PhysicalSeparatorLinearTail

/-! ## 1. Geometry separated from the scalar AF data -/

/-- A nested dyadic face family.  These are exactly the geometric coherence
fields of `PhysicalObservableRefinementSchedule`, separated so the scalar
nome and spacing can be supplied by one matched AF chart. -/
structure NestedCutoffOneFaceGeometry : Type where
  geometry : Nat → CutoffOneFaceGeometry
  coarseHalf_succ : ∀ scale,
    (geometry (scale + 1)).block.coarseHalf =
      (geometry scale).block.fineHalf
  coarseRoot_succ : ∀ scale,
    (geometry (scale + 1)).coarseRoot = (geometry scale).fineRoot
  coarseTarget_succ : ∀ scale,
    (geometry (scale + 1)).coarseTarget = (geometry scale).fineTarget

/-! ## 2. The same-chart matched physical schedule -/

/-- Build the physical observable schedule with the exact matched block nome
and physical spacing evaluated on the same coupling coordinate. -/
def matchedAFPhysicalObservableRefinementSchedule
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (couplingToZero : CouplingToZero coupling)
    (nested : NestedCutoffOneFaceGeometry) :
    PhysicalObservableRefinementSchedule where
  geometry := nested.geometry
  fineCoupling := fun scale => blockedWeight family (coupling scale)
  fineCoupling_pos := fun scale =>
    blockedWeight_pos family (coupling scale)
  fineCoupling_lt_one := fun scale =>
    blockedWeight_lt_one_of_cubicMarginLaw family law
      (coupling scale) (coupling_pos scale) (coupling_le_window scale)
  spacing := physicalSpacingOfEnvelope spacing coupling
    coupling_pos coupling_le_window
  spacingToZero := spacingToZeroOfQuadraticEnvelope spacing coupling
    coupling_pos coupling_le_window couplingToZero
  coarseHalf_succ := nested.coarseHalf_succ
  coarseRoot_succ := nested.coarseRoot_succ
  coarseTarget_succ := nested.coarseTarget_succ

@[simp] theorem matchedAFPhysicalObservableRefinementSchedule_fineCoupling
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (couplingToZero : CouplingToZero coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (scale : Nat) :
    (matchedAFPhysicalObservableRefinementSchedule family law spacing
      coupling coupling_pos coupling_le_window couplingToZero nested
    ).fineCoupling scale = blockedWeight family (coupling scale) :=
  rfl

@[simp] theorem matchedAFPhysicalObservableRefinementSchedule_spacing
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (couplingToZero : CouplingToZero coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (scale : Nat) :
    (matchedAFPhysicalObservableRefinementSchedule family law spacing
      coupling coupling_pos coupling_le_window couplingToZero nested
    ).spacing.spacing scale = spacing.a (coupling scale) :=
  rfl

@[simp] theorem matchedAFPhysicalObservableRefinementSchedule_effectiveCoupling
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (couplingToZero : CouplingToZero coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (scale : Nat) :
    (matchedAFPhysicalObservableRefinementSchedule family law spacing
      coupling coupling_pos coupling_le_window couplingToZero nested
    ).effectiveCoupling scale =
      observableDecimationCoupling
        (blockedWeight family (coupling scale)) :=
  rfl

/-! ## 3. Exact shifted-AF specialization -/

/-- If the coupling sequence is definitionally identified with a proved
shifted AF schedule, its existing modulus supplies the only coupling-to-zero
input of the same-chart constructor. -/
def matchedShiftedAFPhysicalObservableRefinementSchedule
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) :
    PhysicalObservableRefinementSchedule :=
  matchedAFPhysicalObservableRefinementSchedule family law spacing
    coupling coupling_pos coupling_le_window
    (couplingToZeroOfAFTrajectory C coupling identification) nested

@[simp] theorem matchedShiftedAFPhysicalObservableRefinementSchedule_fineCoupling
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (scale : Nat) :
    (matchedShiftedAFPhysicalObservableRefinementSchedule family law spacing
      C coupling coupling_pos coupling_le_window identification nested
    ).fineCoupling scale = blockedWeight family (coupling scale) :=
  rfl

@[simp] theorem matchedShiftedAFPhysicalObservableRefinementSchedule_spacing
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (scale : Nat) :
    (matchedShiftedAFPhysicalObservableRefinementSchedule family law spacing
      C coupling coupling_pos coupling_le_window identification nested
    ).spacing.spacing scale = spacing.a (coupling scale) :=
  rfl

/-! ## 4. The still-open transport producer on this exact trajectory -/

/-- The remaining analytic producer, now pinned to the exact matched nome and
the physical spacing on the same shifted AF schedule.  This abbreviation has
no inhabitant here. -/
abbrev MatchedShiftedAFSignMatchedTransportTail
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type :=
  PhysicalObservableRefinementSchedule.SignMatchedSeparatedLinearRawTransportTail
    (matchedShiftedAFPhysicalObservableRefinementSchedule family law spacing
      C coupling coupling_pos coupling_le_window identification nested)

/-- On the exact matched nome/spacing chart, the remaining raw/sign `O(a)`
producer gives the literal fine covariance bound at its constructive epsilon
cutoff.  No producer is synthesized by this theorem. -/
theorem matchedShiftedAFFineCovariance_le_anchorRate_add_epsilon
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (tail : MatchedShiftedAFSignMatchedTransportTail family law spacing C
      coupling coupling_pos coupling_le_window identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule :=
      matchedShiftedAFPhysicalObservableRefinementSchedule family law spacing
        C coupling coupling_pos coupling_le_window identification nested
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

#print axioms NestedCutoffOneFaceGeometry
#print axioms matchedAFPhysicalObservableRefinementSchedule
#print axioms matchedAFPhysicalObservableRefinementSchedule_fineCoupling
#print axioms matchedAFPhysicalObservableRefinementSchedule_spacing
#print axioms matchedAFPhysicalObservableRefinementSchedule_effectiveCoupling
#print axioms matchedShiftedAFPhysicalObservableRefinementSchedule
#print axioms matchedShiftedAFPhysicalObservableRefinementSchedule_fineCoupling
#print axioms matchedShiftedAFPhysicalObservableRefinementSchedule_spacing
#print axioms MatchedShiftedAFSignMatchedTransportTail
#print axioms matchedShiftedAFFineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
