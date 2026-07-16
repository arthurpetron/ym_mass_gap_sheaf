/-
# Coupling-parametric arbitrary-cutoff support and pinned-layer activities

The cutoff-uniform spin-summed polymer gas was originally normalized at the
derived strong-coupling anchor.  This module exposes the same fixed-support
spin sum at an arbitrary nonnegative rational coupling and compares it
termwise with the anchor whenever the coupling lies below the anchor.

Consequently the complete activity of polymers meeting one pinned face is at
most the already proved anchor pinned layer, hence at most `1/2`, uniformly in
the representation cutoff, box volume, and pinned face.

This is an activity-level comparison.  Identifying the corresponding
arbitrary-coupling compatible-gas partition with the physical spin-foam
partition still requires coupling-parametric support reindexing and component
factorization.
-/

import YMGap.Continuum.Z4CouplingParametricMonotonicity
import YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion

namespace YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricMonotonicity
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Fixed-support spin sums at arbitrary coupling -/

/-- The complete finite spin sum on one literal excited-face support at a
specified heat-kernel coupling. -/
def couplingParametricKSupportActivity (coupling : Q') (cutoff n : Nat)
    (support : List Nat) : Q' :=
  listQSum (parametricKPhysicalTerm coupling cutoff n)
    (physicalLabellingsWithSupport cutoff n support)

private theorem listQSum_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ source : List A, (0 : Q') ≤ listQSum value source
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_local value hvalue tail)

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ source : List A,
      (∀ item, item ∈ source → lower item ≤ upper item) →
        listQSum lower source ≤ listQSum upper source
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

theorem couplingParametricKSupportActivity_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (support : List Nat) :
    (0 : Q') ≤
      couplingParametricKSupportActivity coupling cutoff n support := by
  unfold couplingParametricKSupportActivity
  exact listQSum_nonnegative_local _
    (parametricKPhysicalTerm_nonnegative hcoupling cutoff n) _

/-- Fixed-support spin-summed activities are monotone in every nonnegative
coupling interval. -/
theorem couplingParametricKSupportActivity_mono_coupling
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) (cutoff n : Nat) (support : List Nat) :
    couplingParametricKSupportActivity lower cutoff n support ≤
      couplingParametricKSupportActivity upper cutoff n support := by
  unfold couplingParametricKSupportActivity
  apply listQSum_mono_local
  intro physical hphysical
  exact parametricKPhysicalTerm_mono_coupling hlower hle
    (mem_physicalLabellingsWithSupport_iff.mp hphysical).1

/-- Below the derived strong-coupling anchor, every arbitrary-cutoff support
activity is bounded by the existing anchor support activity. -/
theorem couplingParametricKSupportActivity_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n : Nat) (support : List Nat) :
    couplingParametricKSupportActivity coupling cutoff n support ≤
      parametricKSupportActivity cutoff n support := by
  exact couplingParametricKSupportActivity_mono_coupling
    hcoupling hle cutoff n support

/-! ## 2. The coupling-parametric pinned layer -/

/-- Total spin-summed activity of every canonical connected support meeting
one pinned face, evaluated at the specified coupling. -/
def couplingParametricKCanonicalPinnedLayerActivity
    (coupling : Q') (cutoff n rootId : Nat) : Q' :=
  markedActivitySum
    (couplingParametricKSupportActivity coupling cutoff n)
    (canonicalContainsFaceB rootId) (canonicalSurfacePolymers n)

theorem couplingParametricKCanonicalPinnedLayerActivity_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n rootId : Nat) :
    (0 : Q') ≤
      couplingParametricKCanonicalPinnedLayerActivity
        coupling cutoff n rootId := by
  unfold couplingParametricKCanonicalPinnedLayerActivity
  exact markedActivitySum_nonnegative _
    (couplingParametricKSupportActivity_nonnegative hcoupling cutoff n)
    _ _

/-- The complete pinned layer below the anchor is dominated by the existing
cutoff-uniform anchor pinned layer. -/
theorem couplingParametricKCanonicalPinnedLayerActivity_le_anchor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n rootId : Nat) :
    couplingParametricKCanonicalPinnedLayerActivity
        coupling cutoff n rootId ≤
      parametricKCanonicalPinnedLayerActivity cutoff n rootId := by
  unfold couplingParametricKCanonicalPinnedLayerActivity
    parametricKCanonicalPinnedLayerActivity markedActivitySum
  apply listQSum_mono_local
  intro support _
  exact couplingParametricKSupportActivity_le_anchor
    hcoupling hle cutoff n support

/-- Uniform in coupling below the anchor, representation cutoff, box volume,
and pinned face. -/
theorem couplingParametricKCanonicalPinnedLayerActivity_le_half
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n rootId : Nat) :
    couplingParametricKCanonicalPinnedLayerActivity
        coupling cutoff n rootId ≤
      Q'.mkPos 1 2 (by decide) :=
  Q'.le_trans' _ _ _
    (couplingParametricKCanonicalPinnedLayerActivity_le_anchor
      hcoupling hle cutoff n rootId)
    (parametricKCanonicalPinnedLayerActivity_le_half cutoff n rootId)

#print axioms couplingParametricKSupportActivity_nonnegative
#print axioms couplingParametricKSupportActivity_mono_coupling
#print axioms couplingParametricKSupportActivity_le_anchor
#print axioms couplingParametricKCanonicalPinnedLayerActivity_nonnegative
#print axioms couplingParametricKCanonicalPinnedLayerActivity_le_anchor
#print axioms couplingParametricKCanonicalPinnedLayerActivity_le_half

end YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
