/-
# Actual interacting conditional sweeps and their exact loss

Every operator here is the existing conditional projection for the ORIGINAL
full heat action, acting on its existing completed weighted GNS space. The
link subtype carries physical membership; there is no fallback link. No
interaction is removed between steps. Finite schedules return their actual
completed output and actual sum of squared residuals.

The mixed-pairing telescope stays signed. Nonneighbors cannot increase a
residual, and at most 25 entries of a duplicate-free schedule neighbor any
one link. This geometry is NOT yet a total residual-energy estimate. Nor is
the preserved joint-fixed complement identified with the physical vacuum
complement. A sweep is conditional L2 dynamics, NOT OS time translation.

OPEN: a bounded-degree total-energy estimate, useful original-action
coercivity, a spatial/off-diagonal estimate (an arbitrary ordered sweep can
propagate support across the slab), and the normalized signed-covariance,
scaling and OS joins. Nothing here asserts a uniform physical mass gap.
-/

import YMGap.Continuum.GNSProjectionSweep
import YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation
import YMGap.Continuum.BF4ExactSlabWardStarGeometry

namespace YMGap.Continuum.BF4ExactSlabConditionalSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarIndependentProbe
open YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def PhysicalLink (extent : Nat) :=
  { link : Z4Link // link ∈ boundaryCompleteSlabLinks extent }

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK

/-- All three fields are supplied by proved facts about the literal
completed conditional operator, not assumed analytic inputs. -/
def projections : Family F (PhysicalLink extent) where
  op i := conditionalProjection hw0 hw1 K extent hK i.val i.property
  adjoint i := conditionalProjection_selfAdjoint hw0 hw1 K extent hK i.val i.property
  idem i := conditionalProjection_idempotent hw0 hw1 K extent hK i.val i.property

local notation "P" => projections hw0 hw1 K extent hK

/-- Exact Pythagorean loss over the original action and actual sequence of
intermediate completed states, valid also for schedules with repetitions. -/
theorem sweep_loss (schedule : List (PhysicalLink extent)) (x : GNSCompletionSpace F) :
    (P).loss schedule x = RCsub (normSq x) (normSq ((P).sweep schedule x)) :=
  (P).loss_eq schedule x

theorem signed_pairing_telescope (schedule : List (PhysicalLink extent))
    (x y : GNSCompletionSpace F) :
    (P).pairingLoss schedule x y =
      RCsub ((F).cinnerCompl x y) ((F).cinnerCompl ((P).sweep schedule x) y) :=
  (P).pairingLoss_eq schedule x y

theorem sweep_norm (schedule : List (PhysicalLink extent)) (x : GNSCompletionSpace F) :
    RCle (normSq ((P).sweep schedule x)) (normSq x) := (P).sweep_norm schedule x

theorem sweep_preserves_joint_complement (schedule : List (PhysicalLink extent))
    (x : GNSCompletionSpace F) (hx : (P).OrthogonalJointFixed schedule x) :
    (P).OrthogonalJointFixed schedule ((P).sweep schedule x) :=
  (P).sweep_preserves_sector schedule x hx

/-- Nonneighbors shrink, rather than restore, the selected residual. -/
theorem nonneighbor_residual_norm (i j : PhysicalLink extent)
    (hij : ¬ Near extent i.val j.val) (x : GNSCompletionSpace F) :
    RCle (normSq ((P).residual i ((P).op j x))) (normSq ((P).residual i x)) := by
  apply (P).commuting_residual_norm
  intro y
  exact conditionalProjection_commute hw0 hw1 K extent hK
    i.val j.val i.property j.property
    (fun h => hij (List.mem_cons_of_mem i.val h)) y

/-- No independence hypothesis at a neighbor: the actual correction remains. -/
theorem neighboring_residual_identity (i j : PhysicalLink extent)
    (x : GNSCompletionSpace F) :
    (P).residual i ((P).op j x) =
      (F).cSub ((P).residual i x) ((P).residual i ((P).residual j x)) :=
  (P).residual_update i j x

theorem correction_norm (i j : PhysicalLink extent) (x : GNSCompletionSpace F) :
    RCle (normSq ((P).residual i ((P).residual j x)))
      (RCsub (normSq x) (normSq ((P).op j x))) :=
  (P).update_correction_norm i j x

/-- The only updates needing correction are in this explicit geometric row.
This is a count, not the still-missing sum-of-residuals estimate. -/
theorem neighbor_count (i : PhysicalLink extent) (schedule : List (PhysicalLink extent))
    (hs : schedule.Nodup) :
    (schedule.filter (fun j => decide (Near extent i.val j.val))).length ≤ 25 :=
  row_count_injective extent i.val (fun j : PhysicalLink extent => j.val)
    (fun _ _ h => Subtype.ext h) schedule hs

/-- A test whose literal support omits every updated link retains its exact
original weighted pairing throughout the sweep. -/
theorem local_test_pairing (schedule : List (PhysicalLink extent))
    (x : GNSCompletionSpace F) (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val)
    (homit : ∀ i, i ∈ schedule → i.val ∉ support) :
    (F).cinnerCompl ((P).sweep schedule x) (embedV F p) =
      (F).cinnerCompl x (embedV F p) := by
  apply (P).sweep_pair_fixed
  intro i hi
  exact conditionalProjection_fix_local hw0 hw1 K extent hK
    i.val i.property support p hp (homit i hi)

#print axioms projections
#print axioms sweep_loss
#print axioms signed_pairing_telescope
#print axioms sweep_norm
#print axioms sweep_preserves_joint_complement
#print axioms nonneighbor_residual_norm
#print axioms neighboring_residual_identity
#print axioms correction_norm
#print axioms neighbor_count
#print axioms local_test_pairing

end YMGap.Continuum.BF4ExactSlabConditionalSweep
