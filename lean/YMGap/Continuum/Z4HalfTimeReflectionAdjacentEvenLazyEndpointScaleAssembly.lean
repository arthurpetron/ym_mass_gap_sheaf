/-
# Lazy plane features with endpoint deltas and exterior scales

The shared-link quaternion construction and the adjacent-even endpoint
construction meet immediately before Haar integration.  At that boundary a
single symbolic summand has three independent ingredients:

* two copies of one selected plane-feature factor list;
* the exact exterior lower-half scale on each physical half-state; and
* one terminal Kronecker delta on every fixed link.

This leaf assembles precisely those ingredients without multiplying any raw
polynomials.  It identifies the terminal product with its literal finite
product of equality deltas and regroups the two scaled half values into the
already established lazy square-factor evaluation.  The result is an exact
pre-Haar symbolic normal form.

No theorem here identifies this expression with the reachable kernel, a
spin/fusion sum, or a Haar integral, and no positivity statement is inferred
from the symbolic factorization.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazySectorSplit
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazySectorSplit
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. The selected plane half -/

/-- The unexpanded selected factor list carried by one half of the
production fixed-face SOS square. -/
def adjacentEvenLazyPlaneHalfFactors
    (cutoff radius : Nat) (faceTerm : Z4Plaq → Nat) : List RatPoly :=
  selectedGlobalAnchorFaceFactors cutoff
    (adjacentEvenActiveLinks radius)
    (adjacentEvenFixedFaceFeatureSelection radius faceTerm)

/-- Evaluation of the selected plane half in an arbitrary shared coordinate
environment. -/
def adjacentEvenLazyPlaneHalfValue
    (cutoff radius : Nat) (faceTerm : Z4Plaq → Nat)
    (rho : Nat → Q') : Q' :=
  evalRatPolyFactors rho
    (adjacentEvenLazyPlaneHalfFactors cutoff radius faceTerm)

/-- The half list is exactly the plane sector of the selected production
family; its negative and positive face sectors are empty by the preceding
leaf. -/
theorem adjacentEvenLazyPlaneHalfFactors_eq_planeSector
    (cutoff radius : Nat) (faceTerm : Z4Plaq → Nat) :
    adjacentEvenPlaneGlobalFaceFactors cutoff radius
        (adjacentEvenActiveLinks radius)
        (adjacentEvenFixedFaceFeatureSelection radius faceTerm) =
      adjacentEvenLazyPlaneHalfFactors cutoff radius faceTerm := by
  exact (adjacentEvenFixedFaceGlobalFactors_plane_only
    cutoff radius faceTerm).2.1

/-- The selected half retains the exact common-gauge-field semantics of its
constituent face features. -/
theorem eval_adjacentEvenLazyPlaneHalfFactors
    (cutoff radius : Nat) (faceTerm : Z4Plaq → Nat)
    (field : RationalUnitQuaternionGaugeField) :
    adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm
        (adjacentEvenActiveLinkEnvironment radius field) ≈
      selectedLatticeAnchorFaceFeatureProduct cutoff field
        (adjacentEvenFixedFaceFeatureSelection radius faceTerm) := by
  unfold adjacentEvenLazyPlaneHalfValue
    adjacentEvenLazyPlaneHalfFactors
    adjacentEvenActiveLinkEnvironment
  apply eval_selectedGlobalAnchorFaceFactors
  intro entry hentry link hlink
  obtain ⟨plaquette, hplaquette, heq⟩ := List.mem_map.mp hentry
  subst entry
  exact adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
    hplaquette hlink

/-! ## 2. Literal physical endpoint deltas -/

/-- Deterministic fixed-link endpoint assignment of one zero-padded physical
half-state index. -/
def adjacentEvenPhysicalEndpointAssignment
    (K radius state : Nat) : Z4Link → Nat :=
  adjacentEvenHalfStateEndpointAssignment radius
    (adjacentEvenPhysicalHalfStateAt K radius state)

/-- Terminal fixed-link constraint between two physical endpoint indices for
one internal incidence trajectory. -/
def adjacentEvenPhysicalEndpointTerminalProduct
    (K radius left right : Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  adjacentEvenLinkTerminalProduct radius
    (adjacentEvenPhysicalEndpointAssignment K radius left)
    (adjacentEvenPhysicalEndpointAssignment K radius right)
    trajectory

/-- The same constraint written as its literal product of equality deltas. -/
def adjacentEvenPhysicalEndpointExplicitDeltas
    (K radius left right : Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQProduct (fun link =>
    if adjacentEvenPhysicalEndpointAssignment K radius right link =
        adjacentEvenTrajectoryFinalChannel radius
          (adjacentEvenPhysicalEndpointAssignment K radius left)
          trajectory link
      then (1 : Q') else 0)
    (adjacentEvenFixedLinks radius)

/-- The production terminal indicator is exactly the advertised finite
Kronecker-delta product, with no endpoint-support premise. -/
theorem adjacentEvenPhysicalEndpointTerminalProduct_eqv_explicitDeltas
    (K radius left right : Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenPhysicalEndpointTerminalProduct
        K radius left right trajectory ≈
      adjacentEvenPhysicalEndpointExplicitDeltas
        K radius left right trajectory := by
  unfold adjacentEvenPhysicalEndpointTerminalProduct
    adjacentEvenPhysicalEndpointExplicitDeltas
  change
    listQProduct (fun link =>
        adjacentEvenTerminalDeltaFactor radius
          (adjacentEvenPhysicalEndpointAssignment K radius left)
          (adjacentEvenPhysicalEndpointAssignment K radius right)
          trajectory link)
        (adjacentEvenFixedLinks radius) ≈ _
  apply listQProduct_congr_eqv
  intro link _
  exact adjacentEvenTerminalDeltaFactor_eqv_delta radius
    (adjacentEvenPhysicalEndpointAssignment K radius left)
    (adjacentEvenPhysicalEndpointAssignment K radius right)
    trajectory link

/-! ## 3. Exterior scaling and exact pre-Haar assembly -/

/-- One selected plane half after attaching the exact exterior physical
scale.  No sign or nonvanishing property of that scale is assumed. -/
def adjacentEvenLazyScaledPlaneHalfValue
    (cutoff K radius : Nat) (faceTerm : Z4Plaq → Nat)
    (rho : Nat → Q') (state : Nat) : Q' :=
  adjacentEvenPhysicalOuterScale K radius state *
    adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm rho

/-- One fully exposed symbolic summand immediately before product-Haar and
spin/fusion comparison: scaled left half, scaled right half, and the terminal
endpoint constraint. -/
def adjacentEvenLazyPreHaarEndpointTerm
    (cutoff K radius : Nat) (faceTerm : Z4Plaq → Nat)
    (rho : Nat → Q') (left right : Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  adjacentEvenLazyScaledPlaneHalfValue
      cutoff K radius faceTerm rho left *
    (adjacentEvenLazyScaledPlaneHalfValue
        cutoff K radius faceTerm rho right *
      adjacentEvenPhysicalEndpointTerminalProduct
        K radius left right trajectory)

private theorem scaled_halves_regroup
    (leftScale halfLeft rightScale halfRight terminal : Q') :
    (leftScale * halfLeft) *
        ((rightScale * halfRight) * terminal) ≈
      (leftScale * rightScale) *
        ((halfLeft * halfRight) * terminal) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (leftScale * halfLeft) (rightScale * halfRight) terminal)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ terminal
      (YMGap.Continuum.RingNormaliser.q_mul4_swap
        leftScale halfLeft rightScale halfRight)) ?_
  exact Q'.mul_assoc_eqv _ _ _

/-- **Exact pre-Haar assembly normal form.**  Both exterior factors are
visible, the two identical plane halves are represented by the established
lazy square-factor list, and every endpoint constraint is a literal equality
delta.  This is only a symbolic summand identity; the remaining load-bearing
step is its product-Haar identification with the production spin/fusion
kernel. -/
theorem adjacentEvenLazyPreHaarEndpointTerm_eqv_assembled
    (cutoff K radius : Nat) (faceTerm : Z4Plaq → Nat)
    (rho : Nat → Q') (left right : Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenLazyPreHaarEndpointTerm
        cutoff K radius faceTerm rho left right trajectory ≈
      (adjacentEvenPhysicalOuterScale K radius left *
        adjacentEvenPhysicalOuterScale K radius right) *
        (evalRatPolyFactors rho
            (adjacentEvenFixedFaceSelectedSquareFactors
              cutoff radius faceTerm) *
          adjacentEvenPhysicalEndpointExplicitDeltas
            K radius left right trajectory) := by
  let half := adjacentEvenLazyPlaneHalfValue
    cutoff radius faceTerm rho
  let terminal := adjacentEvenPhysicalEndpointTerminalProduct
    K radius left right trajectory
  refine Q'.eqv_trans _ _ _
    (scaled_halves_regroup
      (adjacentEvenPhysicalOuterScale K radius left) half
      (adjacentEvenPhysicalOuterScale K radius right) half terminal) ?_
  apply Q'.mul_eqv_congr_left
  apply q_mul_congr
  · exact Q'.eqv_symm
      (eval_adjacentEvenFixedFaceSelectedSquareFactors
        cutoff radius faceTerm rho)
  · exact adjacentEvenPhysicalEndpointTerminalProduct_eqv_explicitDeltas
      K radius left right trajectory

#print axioms adjacentEvenLazyPlaneHalfFactors_eq_planeSector
#print axioms eval_adjacentEvenLazyPlaneHalfFactors
#print axioms adjacentEvenPhysicalEndpointTerminalProduct_eqv_explicitDeltas
#print axioms adjacentEvenLazyPreHaarEndpointTerm_eqv_assembled

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly
