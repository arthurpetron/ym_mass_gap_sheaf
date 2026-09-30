/-
# Collective physical-face squares on the SAME original completion

Each distinct neighboring pair belongs to exactly one original face. Thus
the sum of four-link generator squares retains the entire signed neighbor
sum, with diagonal incidence at most six. Remote pairs are nonnegative.

The unconditional upper estimate is sum_face ||H_face x||^2 <= ||H x||^2+5E.
A genuine lower bound on those SAME full-action patch operators supplies
the margin 6*gamma-5. No isolated-plaquette, free-boundary or OS gap is used.
-/

import YMGap.Continuum.GNSProjectionPatchEnergy
import YMGap.Continuum.BF4ExactSlabFacePatchIncidence
import YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
import YMGap.Continuum.RCCollectivePatchBudget

namespace YMGap.Continuum.BF4ExactSlabFacePatchEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
open YMGap.Continuum.BF4ExactSlabFacePatchIncidence
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private instance (extent : Nat) : DecidableEq (PhysicalLink extent) :=
  inferInstanceAs (DecidableEq {i // i ∈ boundaryCompleteSlabLinks extent})

private theorem off_diagonal_count (extent : Nat) (i j : PhysicalLink extent)
    (hne : i ≠ j) :
    Family.jointCount (slabPhysicalFaceEdges extent) (keep extent) i j =
      if adjacent i j then 1 else 0 := by
  change BF4ExactSlabFacePatchIncidence.jointCount extent i j = _
  cases h : adjacent i j with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact jointCount_nonNear_eq_zero extent i j (of_decide_eq_false h)
  | true =>
      simp only [if_true]
      exact jointCount_distinct_near_eq_one extent i j
        (fun he => hne (Subtype.ext he)) (of_decide_eq_true h)

/-- Exact candidate margin from six-face incidence, with all coupling
dependence still carried by the supplied local coefficient. -/
def faceMargin (gamma : Q') : Q' := 1 + -(6 * ((1 : Q') + -gamma))

theorem faceMargin_eqv (gamma : Q') : Q'.eqv (faceMargin gamma) (6*gamma + -5) := by
  unfold faceMargin
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.mul (.const 6) (.add (.const 1) (.neg (.var 0))))))
    (.add (.mul (.const 6) (.var 0)) (.neg (.const 5))) (by decide) (fun _ => gamma)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "E" x => Family.finalEnergy
  (projections hw0 hw1 K extent hK) (schedule extent) x
local notation "H" x => conditionalGenerator hw0 hw1 K extent hK x
local notation "C" x => signedNeighborEnergy hw0 hw1 K extent hK x

/-- Actual squares of the sums of the original residuals on each face. -/
def faceSquareSum (x : GNSCompletionSpace F) : RC :=
  (P).patchSquareSum (schedule extent) ids (keep extent) x

/-- Actual residual energy counted once per incident physical face. -/
def faceEnergySum (x : GNSCompletionSpace F) : RC :=
  (P).patchEnergySum (schedule extent) ids (keep extent) x

/-- All signed neighboring pairings occur exactly once. Boundary diagonal
counts remain literal, rather than being incorrectly set equal to six. -/
theorem face_square_signed_identity (x : GNSCompletionSpace F) :
    faceSquareSum hw0 hw1 K extent hK x =
      RCadd (faceEnergySum hw0 hw1 K extent hK x) (C x) := by
  exact (P).patchSquareSum_eq_energy_add_cross
    (schedule extent) (schedule_nodup extent) ids (keep extent) adjacent x
    (fun i j _ _ hne => off_diagonal_count extent i j hne)

theorem faceEnergySum_le_six (x : GNSCompletionSpace F) :
    RCle (faceEnergySum hw0 hw1 K extent hK x) (RCscale 6 (E x)) := by
  exact (P).patchEnergySum_le_degree (schedule extent) ids (keep extent) x 6
    (fun i _ => jointCount_self_le_six extent i)

/-- Unconditional collective patch-to-global inequality on every completed
state, with no volume or cutoff multiplier and no assumed patch gap. -/
theorem faceSquareSum_le_generator_plus_five (x : GNSCompletionSpace F) :
    RCle (faceSquareSum hw0 hw1 K extent hK x)
      (RCadd (normSq (H x)) (RCscale 5 (E x))) := by
  have h := RCCollectivePatchBudget.patch_square_upper 6 (E x)
    (faceEnergySum hw0 hw1 K extent hK x) (C x)
    (faceSquareSum hw0 hw1 K extent hK x) (normSq (H x))
    (face_square_signed_identity hw0 hw1 K extent hK x)
    (faceEnergySum_le_six hw0 hw1 K extent hK x)
    (signed_energy_le_generator_square hw0 hw1 K extent hK x)
  simpa only [RCSignedPairBudget.scale_congr
    (by decide : Q'.eqv ((6 : Q') + -(1 : Q')) 5)] using h

/-- A supplied collective lower estimate on the ACTUAL face operators
implies the displayed global square-energy margin. No such lower estimate
is inferred from geometry, positivity, or a different plaquette law. -/
theorem generator_square_lower_of_collective_patch (gamma : Q')
    (hgamma : gamma ≤ (1 : Q')) (x : GNSCompletionSpace F)
    (hpatch : RCle (RCscale gamma (faceEnergySum hw0 hw1 K extent hK x))
      (faceSquareSum hw0 hw1 K extent hK x)) :
    RCle (RCscale (faceMargin gamma) (E x)) (normSq (H x)) :=
  RCCollectivePatchBudget.generator_lower 6 gamma hgamma (E x)
    (faceEnergySum hw0 hw1 K extent hK x) (C x)
    (faceSquareSum hw0 hw1 K extent hK x) (normSq (H x))
    (face_square_signed_identity hw0 hw1 K extent hK x)
    (faceEnergySum_le_six hw0 hw1 K extent hK x)
    (signed_energy_le_generator_square hw0 hw1 K extent hK x) hpatch

/-- Pointwise original face inequalities are sufficient; they are not
assumed for detached or free-boundary operators. The state remains fixed. -/
theorem generator_square_lower_of_face_bounds (gamma : Q')
    (hgamma : gamma ≤ (1 : Q')) (x : GNSCompletionSpace F)
    (hface : ∀ id, id ∈ ids → RCle
      (RCscale gamma ((P).finalEnergy ((schedule extent).filter (keep extent id)) x))
      (normSq ((P).residualSum ((schedule extent).filter (keep extent id)) x))) :
    RCle (RCscale (faceMargin gamma) (E x)) (normSq (H x)) := by
  apply generator_square_lower_of_collective_patch hw0 hw1 K extent hK gamma hgamma x
  have h := sumOn_mono ids _ _ hface
  rw [sumOn_scale] at h
  exact h

#print axioms faceMargin_eqv
#print axioms faceSquareSum
#print axioms faceEnergySum
#print axioms face_square_signed_identity
#print axioms faceEnergySum_le_six
#print axioms faceSquareSum_le_generator_plus_five
#print axioms generator_square_lower_of_collective_patch
#print axioms generator_square_lower_of_face_bounds

end YMGap.Continuum.BF4ExactSlabFacePatchEnergy
