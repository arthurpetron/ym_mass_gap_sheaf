/-
# From the existing marginal root sector to its reflected cube completion

Every finite canonical-sector presentation is translated to a signed cube
span with the SAME literal finite-linear observable. The proved E<=B form
bound therefore contracts its squared distance into the actual reflected
seminorm. This constructs a map of the existing completed marginal sector
to the reflected completion, with unchanged representative moduli, and then
to the raw cube completion with the explicit 64/65 tolerance conversion.

No replacement of the source carrier is made, and no inverse or injectivity
is claimed for this norm-decreasing map. The inverse raw/reflected comparison
is a different, already proved map. Extending/intertwining the actual
conditional action on the reflected completion remains open, as do the
stationary sector vacuum, geometric time, strict gap and continuum target.
-/

import YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule

namespace YMGap.Continuum.BF4PhysicalCubeSectorComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "J" => cubeToCompleted (w := anchorCoupling) (by decide) (by decide)
local notation "E" => completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0

abbrev SectorPresentation := CentralPhysicalVacuumSectorCylinderPresentation
  anchorCoupling (by decide) 0

/-- Total finite lookup; the root fallback is never read on a sector index. -/
def presentationState (p : SectorPresentation) (i : Nat) : CubeSectorState :=
  if hi : i ∈ centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) p.base 0 then
    stateOfFiniteSector anchorCoupling (by decide) p.base
      (centralPhysicalFiniteStateAt anchorCoupling (by decide) p.base 0 i)
      (centralPhysicalFiniteVacuumSectorState_mem_of_index anchorCoupling (by decide) p.base 0 hi rfl)
  else rootState

theorem presentationState_val (p : SectorPresentation) {i : Nat}
    (hi : i ∈ centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) p.base 0) :
    (presentationState p i).val = centralPhysicalFiniteStateAt anchorCoupling (by decide) p.base 0 i := by
  simp only [presentationState, dif_pos hi, stateOfFiniteSector]

/-- Retain the original finite sector indices and coefficients exactly. -/
def presentationToCube (p : SectorPresentation) : CubeSpan :=
  (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) p.base 0).map
    (fun i => (presentationState p i, p.coefficient i))

private theorem observable_map_eq (states : Nat → CubeSectorState) (stateAt : Nat → EdgeLabelling)
    (coefficient : Nat → Q') : ∀ indices : List Nat,
    (∀ i, i ∈ indices → (states i).val = stateAt i) →
      cubeObservable (indices.map (fun i => (states i, coefficient i))) =
        centralPhysicalStateCylinderLinearCombination 0 stateAt coefficient indices
  | [], _ => rfl
  | i :: rest, h => by
    simp only [List.map_cons, cubeObservable, centralPhysicalStateCylinderLinearCombination]
    rw [h i List.mem_cons_self,
      observable_map_eq states stateAt coefficient rest (fun j hj => h j (List.mem_cons_of_mem i hj))]

/-- Literal syntax equality, stronger than an equality of selected expectations. -/
theorem presentationToCube_observable (p : SectorPresentation) :
    cubeObservable (presentationToCube p) = p.toLinearObservable :=
  observable_map_eq (presentationState p)
    (centralPhysicalFiniteStateAt anchorCoupling (by decide) p.base 0) p.coefficient _
    (fun _ hi => presentationState_val p hi)

private theorem difference_equivalent (left right : CubeSpan) :
    CentralPhysicalLinearObservable.Equivalent
      (cubeObservable ((D).sub left right))
      (CentralPhysicalLinearObservable.sub (cubeObservable left) (cubeObservable right)) := by
  intro state
  exact Q'.eqv_trans _ _ _ (cubeObservable_sub_value left right state)
    (Q'.eqv_symm (sub_value_equiv _ _ state))

private theorem difference_embed (left right : CubeSpan) :
    J ((D).sub left right) =
      (G).embedRep (CentralPhysicalLinearObservable.sub (cubeObservable left) (cubeObservable right)) :=
  (G).embedRep_eq_of_null (physicalLinearDistSq_equiv_czero_of_equivalent
    (w := anchorCoupling) (by decide) (by decide) 0 (difference_equivalent left right))

/-- E<=B for every pair of literal signed cube observables. -/
theorem cubeObservable_distance_le (left right : CubeSpan) :
    CReal.leEv (cubeReflectedSeminorm.distSq left right)
      ((G).distSq (cubeObservable left) (cubeObservable right)) := by
  change CReal.RCle (Quotient.mk CReal.crealSetoid
    (cubeReflectedSeminorm.distSq left right))
    (Quotient.mk CReal.crealSetoid ((G).distSq (cubeObservable left) (cubeObservable right)))
  rw [cubeReflectedSeminorm_physical_distance, difference_embed]
  have hb := (completedReflectedForm_interval (w := anchorCoupling) (by decide) (by decide) 0
    ((G).embedRep (CentralPhysicalLinearObservable.sub (cubeObservable left) (cubeObservable right)))).2
  rw [centralPhysicalCutoffCompletedInner_embedRep] at hb
  exact hb

theorem cubeObservable_null_of_equivalent {left right : CubeSpan}
    (h : CentralPhysicalLinearObservable.Equivalent (cubeObservable left) (cubeObservable right)) :
    cubeReflectedSeminorm.Null left right :=
  CReal.equiv_of_leEv_leEv
    (CReal.leEv_trans (cubeObservable_distance_le left right)
      (CReal.leEv_of_equiv (physicalLinearDistSq_equiv_czero_of_equivalent
        (w := anchorCoupling) (by decide) (by decide) 0 h)))
    (cubeReflectedSeminorm.distSq_nonneg left right)

/-- The actual E<=B bound contracts the original sector distance, with no
new uniform-gap or comparison hypothesis. -/
theorem presentationToCube_distance_le (p q : SectorPresentation) :
    CReal.leEv (cubeReflectedSeminorm.distSq (presentationToCube p) (presentationToCube q))
      ((M).distSq p q) := by
  have h := cubeObservable_distance_le (presentationToCube p) (presentationToCube q)
  rw [presentationToCube_observable, presentationToCube_observable] at h
  exact h

/-- Same rate, now for reflected distance on literal translated representatives. -/
def sectorCauchyToReflected (X : (M).Cauchy) : cubeReflectedSeminorm.Cauchy where
  seq n := presentationToCube (X.seq n)
  modulus := X.modulus
  isCauchy := fun e he m n hm hn => CReal.leEv_trans (presentationToCube_distance_le _ _)
    (X.isCauchy e he m n hm hn)

def sectorCloseToReflected {X Y : (M).Cauchy} (h : (M).Close X Y) :
    cubeReflectedSeminorm.Close (sectorCauchyToReflected X) (sectorCauchyToReflected Y) where
  modulus := h.modulus
  close := fun e he n hn => CReal.leEv_trans (presentationToCube_distance_le _ _)
    (h.close e he n hn)

/-- Canonical map from the EXISTING completed marginal sector to E completion. -/
def sectorToReflected : (M).Completion → CubeReflectedCompletion :=
  Quotient.lift (fun X => Quotient.mk cubeReflectedSeminorm.completionSetoid (sectorCauchyToReflected X))
    (fun _ _ h => by
      rcases h with ⟨hclose⟩
      exact Quotient.sound ⟨sectorCloseToReflected hclose⟩)

theorem sectorToReflected_mk (X : (M).Cauchy) :
    sectorToReflected (Quotient.mk (M).completionSetoid X) =
      Quotient.mk cubeReflectedSeminorm.completionSetoid (sectorCauchyToReflected X) := rfl

theorem sectorToReflected_embed (p : SectorPresentation) :
    sectorToReflected ((M).embedRep p) = cubeReflectedEmbed (presentationToCube p) := rfl

/-- On the dense source, the target pairing is the SAME physical reflected form. -/
theorem sectorToReflected_dense_pairing (p q : SectorPresentation) :
    cubeReflectedInner (sectorToReflected ((M).embedRep p)) (sectorToReflected ((M).embedRep q)) =
      E (centralPhysicalVacuumSectorCylinderCompletionToGlobal ((M).embedRep p))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal ((M).embedRep q)) := by
  rw [sectorToReflected_embed, sectorToReflected_embed, cubeReflectedInner_embed]
  unfold cubeToCompleted
  rw [presentationToCube_observable, presentationToCube_observable]
  rfl

def sectorCauchyToRaw (X : (M).Cauchy) : CauchyGNS D :=
  toRawCauchy D anchorNormalization (sectorCauchyToReflected X)

theorem sectorCauchyToRaw_modulus (X : (M).Cauchy) (epsilon : Q') :
    (sectorCauchyToRaw X).modulus epsilon = X.modulus (Q'.mkPos 64 65 (by decide) * epsilon) := rfl

def sectorToRaw : (M).Completion → CubeCompletion anchorCoupling (by decide) :=
  fun x => reflectedToRaw (sectorToReflected x)

theorem sectorToRaw_mk (X : (M).Cauchy) :
    sectorToRaw (Quotient.mk (M).completionSetoid X) =
      Quotient.mk (cauchySetoid D) (sectorCauchyToRaw X) := rfl

theorem sectorToRaw_embed (p : SectorPresentation) :
    sectorToRaw ((M).embedRep p) = embedSpan anchorCoupling (by decide) (presentationToCube p) := by
  unfold sectorToRaw
  rw [sectorToReflected_embed, reflectedToRaw_embed]

theorem rawToReflected_sectorToRaw (x : (M).Completion) :
    rawToReflected (sectorToRaw x) = sectorToReflected x := reflected_raw_inverse _

end YMGap.Continuum.BF4PhysicalCubeSectorComparison

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.presentationState
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.presentationState_val
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.presentationToCube
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.presentationToCube_observable
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.cubeObservable_distance_le
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.cubeObservable_null_of_equivalent
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.presentationToCube_distance_le
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorCauchyToReflected
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorCloseToReflected
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToReflected
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToReflected_mk
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToReflected_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToReflected_dense_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorCauchyToRaw
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorCauchyToRaw_modulus
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToRaw
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToRaw_mk
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.sectorToRaw_embed
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorComparison.rawToReflected_sectorToRaw
