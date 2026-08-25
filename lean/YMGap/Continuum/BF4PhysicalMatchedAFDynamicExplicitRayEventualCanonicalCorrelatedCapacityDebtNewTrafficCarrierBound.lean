/-
# Carrier bounds for matched dynamic new-endpoint traffic

The factorized new-traffic estimator pays the cardinality of the literal
complementary residual endpoint list.  This module embeds that list into the
sharper full vacuum-pair shell at the later cutoff: all later vacuum-sector
pairs that are not wholly contained in the exact embedded-old index carrier.

The shell count is then bounded by the square of the literal later vacuum
sector and, finally, by the explicit ambient square

  ((later cutoff + 1)^24)^2.

Both bounds are retained.  The shell count is the sharper observable-connected
quantity for a future boundary-growth estimate; the ambient square is a fully
explicit fallback.  Either corresponding weighted normalized-term estimate
compiles to the existing exact new-debt, six-leaf traffic, regional, and
total-tail controls.

No decay estimate, capacity lower bound, continuum theory, or Clay conclusion
is supplied.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficEstimator
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare

/-! ## 1. The literal later vacuum-pair shell -/

/-- All pairs in the literal later vacuum sector that are not wholly in the
embedded-old index carrier.  This is larger than the new residual traffic only
because it also retains ray--ray pairs; it changes neither cutoff nor carrier. -/
def matchedEventualCanonicalLaterVacuumPairShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : List (Nat × Nat) :=
  (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1)).filter
    (fun pair =>
      !(matchedEventualCanonicalTransportedBridgeEndpointPairOldB
        trajectory transitionStart physicalScale cutoffOffset pair))

def matchedEventualCanonicalLaterVacuumPairShellCount
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  Q'.ofNat
    (matchedEventualCanonicalLaterVacuumPairShell
      trajectory transitionStart physicalScale cutoffOffset).length

theorem matchedEventualCanonicalNewEndpointPairs_mem_laterVacuumPairShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈ matchedEventualCanonicalLaterVacuumPairShell
      trajectory transitionStart physicalScale cutoffOffset := by
  have hparts := List.mem_filter.mp hpair
  apply List.mem_filter.mpr
  refine ⟨?_, hparts.2⟩
  have hsector :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hparts.1
  unfold matchedEventualCanonicalVacuumSectorPairs
  exact (mem_cartesian_iff _ _ pair).mpr hsector

theorem matchedEventualCanonicalNewEndpointPairs_length_le_laterVacuumPairShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset).length ≤
      (matchedEventualCanonicalLaterVacuumPairShell
        trajectory transitionStart physicalScale cutoffOffset).length := by
  apply FiniteListBound.nodup_subset_length_le
  · unfold matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    exact List.filter_sublist.nodup
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)))
  · intro pair hpair
    exact
      matchedEventualCanonicalNewEndpointPairs_mem_laterVacuumPairShell
        trajectory transitionStart physicalScale cutoffOffset pair hpair

theorem matchedEventualCanonicalNewEndpointPairCount_le_laterVacuumPairShellCount
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterVacuumPairShellCount
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
    matchedEventualCanonicalLaterVacuumPairShellCount
  exact Q'.ofNat_le_ofNat
    (matchedEventualCanonicalNewEndpointPairs_length_le_laterVacuumPairShell
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 2. Explicit ambient-square ceiling -/

private theorem cartesian_length_local
    {A B : Type} (right : List B) : forall left : List A,
    (cartesian left right).length = left.length * right.length
  | [] => by simp [cartesian]
  | head :: tail => by
      change
        (right.map (fun item => (head, item)) ++
          cartesian tail right).length =
        (head :: tail).length * right.length
      simp only [List.length_append, List.length_map, List.length_cons]
      rw [cartesian_length_local right tail, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- The exact complete lower-face ambient count at the later cutoff. -/
def matchedEventualCanonicalLaterAmbientCarrierSize
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Nat :=
  ((transitionStart physicalScale + (cutoffOffset + 1)) + 1) ^ 24

/-- The square of the explicit later ambient carrier count. -/
def matchedEventualCanonicalLaterAmbientPairCount
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  let size := matchedEventualCanonicalLaterAmbientCarrierSize
    transitionStart physicalScale cutoffOffset
  Q'.ofNat (size * size)

theorem matchedEventualCanonicalLaterVacuumPairShell_length_le_ambientSquare
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (matchedEventualCanonicalLaterVacuumPairShell
        trajectory transitionStart physicalScale cutoffOffset).length ≤
      matchedEventualCanonicalLaterAmbientCarrierSize
          transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalLaterAmbientCarrierSize
          transitionStart physicalScale cutoffOffset := by
  have hshell :
      (matchedEventualCanonicalLaterVacuumPairShell
          trajectory transitionStart physicalScale cutoffOffset).length ≤
        (matchedEventualCanonicalVacuumSectorPairs
          trajectory transitionStart physicalScale
          (cutoffOffset + 1)).length := by
    unfold matchedEventualCanonicalLaterVacuumPairShell
    exact List.length_filter_le _ _
  have hpairs :
      (matchedEventualCanonicalVacuumSectorPairs
          trajectory transitionStart physicalScale
          (cutoffOffset + 1)).length =
        (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale
            (cutoffOffset + 1)).length *
          (matchedEventualCanonicalVacuumSectorIndices
            trajectory transitionStart physicalScale
            (cutoffOffset + 1)).length := by
    unfold matchedEventualCanonicalVacuumSectorPairs
      matchedEventualCanonicalVacuumSectorIndices
      centralPhysicalFiniteVacuumSectorPairs
    exact cartesian_length_local _ _
  have hindices :
      (matchedEventualCanonicalVacuumSectorIndices
          trajectory transitionStart physicalScale
          (cutoffOffset + 1)).length ≤
        matchedEventualCanonicalLaterAmbientCarrierSize
          transitionStart physicalScale cutoffOffset := by
    unfold matchedEventualCanonicalVacuumSectorIndices
      matchedEventualCanonicalLaterAmbientCarrierSize
    exact centralPhysicalFiniteVacuumSectorIndices_length_le_ambient_zero
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1))
  exact Nat.le_trans hshell
    (Nat.le_trans (Nat.le_of_eq hpairs)
      (Nat.mul_le_mul hindices hindices))

theorem matchedEventualCanonicalLaterVacuumPairShellCount_le_ambientPairCount
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalLaterVacuumPairShellCount
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterAmbientPairCount
        transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalLaterVacuumPairShellCount
    matchedEventualCanonicalLaterAmbientPairCount
  exact Q'.ofNat_le_ofNat
    (matchedEventualCanonicalLaterVacuumPairShell_length_le_ambientSquare
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointPairCount_le_ambientPairCount
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointPairCount
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterAmbientPairCount
        transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointPairCount_le_laterVacuumPairShellCount
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterVacuumPairShellCount_le_ambientPairCount
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 3. Sharper shell and explicit ambient traffic envelopes -/

def matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalLaterVacuumPairShellCount
      trajectory transitionStart physicalScale cutoffOffset *
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
      trajectory transitionStart physicalScale cutoffOffset

def matchedEventualCanonicalLaterAmbientTrafficDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalLaterAmbientPairCount
      transitionStart physicalScale cutoffOffset *
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficDebtEnvelope_le_shellEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
    matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (matchedEventualCanonicalNewEndpointPairCount_le_laterVacuumPairShellCount
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope_le_ambientEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterAmbientTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope
    matchedEventualCanonicalLaterAmbientTrafficDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (matchedEventualCanonicalLaterVacuumPairShellCount_le_ambientPairCount
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtTermMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficDebtEnvelope_le_ambientEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterAmbientTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficDebtEnvelope_le_shellEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope_le_ambientEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. Count-discharged inverse-square inputs -/

/-- The sharper remaining analytic certificate: the literal later vacuum-pair
shell count times the unchanged normalized endpoint-term maximum decays at an
inverse-square rate. -/
structure MatchedEventualCanonicalNewEndpointTrafficShellCarrierInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  shellEnvelope_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficShellCarrierInverseSquareControl.toFactorizedControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficShellCarrierInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalNewEndpointTrafficDebtEnvelope_le_shellEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.shellEnvelope_le cutoffOffset)

/-- A fully explicit but coarser certificate.  The only varying analytic term
left inside the product is the same normalized endpoint-term maximum; the
carrier multiplier is the displayed ambient square. -/
structure MatchedEventualCanonicalNewEndpointTrafficAmbientCarrierInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  ambientEnvelope_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalLaterAmbientTrafficDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficAmbientCarrierInverseSquareControl.toShellCarrierControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficAmbientCarrierInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficShellCarrierInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  shellEnvelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalLaterVacuumPairShellTrafficDebtEnvelope_le_ambientEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.ambientEnvelope_le cutoffOffset)

def MatchedEventualCanonicalNewEndpointTrafficAmbientCarrierInverseSquareControl.toFactorizedControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficAmbientCarrierInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficFactorizedInverseSquareControl
      trajectory transitionStart physicalScale :=
  control.toShellCarrierControl.toFactorizedControl

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.matchedEventualCanonicalNewEndpointPairs_length_le_laterVacuumPairShell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.matchedEventualCanonicalLaterVacuumPairShell_length_le_ambientSquare
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.matchedEventualCanonicalNewEndpointPairCount_le_ambientPairCount
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.matchedEventualCanonicalNewEndpointTrafficDebtEnvelope_le_shellEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.matchedEventualCanonicalNewEndpointTrafficDebtEnvelope_le_ambientEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.MatchedEventualCanonicalNewEndpointTrafficShellCarrierInverseSquareControl.toFactorizedControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound.MatchedEventualCanonicalNewEndpointTrafficAmbientCarrierInverseSquareControl.toFactorizedControl
