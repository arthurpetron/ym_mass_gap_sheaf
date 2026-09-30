/-
# Certified spectator-weighted Haar family variance

Each valid slot carries both its in-range proof and the exact independence
of the supplied certified spectator weight. The resulting completed
coordinate maps commute, and their sweep is the already constructed Haar
family map in head-first list order. The variance bound is for that same
weighted completion, not for an interacting conditional law.
-/

import YMGap.Continuum.GNSCommutingPatchVariance
import YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion

namespace YMGap.Continuum.SU2QuaternionWeightedHaarFamilyVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
open YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate

/-- The coordinate certificate travels with each index; there is no
unrestricted-Nat projection on the weighted completion. -/
def ValidSlot (blocks : Nat) (W : RatPoly) : Type :=
  {i : Nat // i < blocks ∧ QuaternionBlockIndependent i W}

variable (blocks : Nat) (W : RatPoly) (H : Certificate blocks W)

local notation "D" => weightedGNSData blocks W H

/-- Genuine completed orthogonal projections for each certified slot. -/
def projections : Family D (ValidSlot blocks W) where
  op i := projection blocks W H i.val i.property.1 i.property.2
  adjoint i x y := projection_selfAdjoint blocks W H i.val i.property.1 i.property.2 x y
  idem i x := projection_idempotent blocks W H i.val i.property.1 i.property.2 x

local notation "P" => projections blocks W H

private theorem list_valid (tests : List (ValidSlot blocks W)) :
    ∀ i, i ∈ tests.map Subtype.val → i < blocks := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property.1

private theorem list_independent (tests : List (ValidSlot blocks W)) :
    ∀ i, i ∈ tests.map Subtype.val → QuaternionBlockIndependent i W := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property.2

/-- The abstract head-first projection sweep is literally the constructed
finite Haar family on the same weighted completion. Repetitions are allowed. -/
theorem sweep_eq_familyProjection (tests : List (ValidSlot blocks W))
    (x : GNSCompletionSpace D) :
    (P).sweep tests x =
      familyProjection blocks W H (tests.map Subtype.val)
        (list_valid blocks W tests) (list_independent blocks W tests) x := by
  induction tests generalizing x with
  | nil =>
      exact (familyProjection_nil blocks W H x).symm
  | cons i rest ih =>
      change (P).sweep rest (projection blocks W H i.val i.property.1 i.property.2 x) =
        familyProjection blocks W H (i.val :: rest.map Subtype.val)
          _ _ x
      rw [familyProjection_cons blocks W H (rest.map Subtype.val)
        (list_valid blocks W rest) (list_independent blocks W rest)
        i.val i.property.1 i.property.2 x]
      exact ih (projection blocks W H i.val i.property.1 i.property.2 x)

/-- Every certified weighted Haar coordinate map commutes with every other,
including the same coordinate listed twice. -/
theorem projections_commute (i j : ValidSlot blocks W)
    (x : GNSCompletionSpace D) : (P).op i ((P).op j x) = (P).op j ((P).op i x) :=
  projection_comm blocks W H i.val j.val i.property.1 j.property.1
    i.property.2 j.property.2 x

/-- Exact completed finite-family variance bound in the certified spectator
weight. The energy is evaluated on the original input, not a swept state. -/
theorem family_variance_le_energy (tests : List (ValidSlot blocks W))
    (x : GNSCompletionSpace D) :
    RCle
      (normSq ((D).cSub x
        (familyProjection blocks W H (tests.map Subtype.val)
          (list_valid blocks W tests) (list_independent blocks W tests) x)))
      ((P).finalEnergy tests x) := by
  rw [← sweep_eq_familyProjection blocks W H tests x]
  exact (P).commuting_sweep_variance_le_finalEnergy tests
    (fun i _ j _ y => projections_commute blocks W H i j y) x

#print axioms ValidSlot
#print axioms projections
#print axioms sweep_eq_familyProjection
#print axioms projections_commute
#print axioms family_variance_le_energy

end YMGap.Continuum.SU2QuaternionWeightedHaarFamilyVariance
