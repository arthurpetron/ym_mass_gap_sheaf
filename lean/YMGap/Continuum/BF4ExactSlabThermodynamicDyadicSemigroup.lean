/-
# Representation-independent dyadic time on the ORIGINAL completion

Equivalent natural-number mesh presentations act identically by comparison
at their computed common refinement. Quotient descent then gives one
nonnegative dyadic-time semigroup on the original completed state space,
with positivity, symmetry, contraction, rational linearity, the same unit,
centering, and exact moment identities. A whole dyadic time unit remains
pinned to TWO original geometric time steps. Supplied time and input
representatives construct output Cauchy data; none is chosen from a quotient.

This is an algebraic dyadic semigroup at the original fixed SU(2) nome and
spacing. Continuity at time zero, a real-time extension, zero transfer
kernel, geometric T1 identification, the Hamiltonian, physical-scale control,
continuum QFT and the Clay conclusion are NOT asserted.
-/

import YMGap.Constructive.NonnegativeDyadicTime
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes

local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem doubleSteps_eq (extra steps : Nat) : doubleSteps extra steps = steps * 2^extra := by
  induction extra with
  | zero => exact (Nat.mul_one steps).symm
  | succ extra ih => rw [doubleSteps, ih, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem time_refinement_power (depth extra steps : Nat) (x : Completion) :
    time (depth+extra) (steps * 2^extra) x = time depth steps x := by
  rw [← doubleSteps_eq]
  exact time_refinement depth extra steps x

/-- Equal dyadic times are compared on the sum of their supplied mesh depths. -/
theorem mesh_action_congr {p q : MeshPoint} (h : Equivalent p q) (x : Completion) :
    time p.depth p.steps x = time q.depth q.steps x := by
  calc
    time p.depth p.steps x = time (p.depth+q.depth) (p.steps * 2^q.depth) x :=
      (time_refinement_power p.depth q.depth p.steps x).symm
    _ = time (q.depth+p.depth) (q.steps * 2^p.depth) x := by
      rw [h, Nat.add_comm p.depth q.depth]
    _ = time q.depth q.steps x := time_refinement_power q.depth p.depth q.steps x

def action (t : Time) (x : Completion) : Completion :=
  Quotient.lift (fun p => time p.depth p.steps x) (fun _ _ h => mesh_action_congr h x) t

theorem action_embed (p : MeshPoint) (x : Completion) :
    action (embed p) x = time p.depth p.steps x := rfl

theorem action_refine (p : MeshPoint) (extra : Nat) (x : Completion) :
    action (embed (refine p extra)) x = action (embed p) x :=
  congrArg (fun t => action t x) (embed_refine p extra)

theorem mesh_action_add (p q : MeshPoint) (x : Completion) :
    time (addMesh p q).depth (addMesh p q).steps x = time p.depth p.steps (time q.depth q.steps x) := by
  change time (p.depth+q.depth) (p.steps*2^q.depth + q.steps*2^p.depth) x = _
  rw [time_add, time_refinement_power]
  have h := time_refinement_power q.depth p.depth q.steps x
  rw [Nat.add_comm q.depth p.depth] at h
  rw [h]

/-- One semigroup law, independent of either time presentation. -/
theorem action_add (s t : Time) (x : Completion) :
    action (add s t) x = action s (action t x) := by
  refine Quotient.inductionOn₂ s t ?_
  intro p q
  exact mesh_action_add p q x

theorem action_zero (x : Completion) : action zero x = x := rfl

theorem action_commutes (s t : Time) (x : Completion) :
    action s (action t x) = action t (action s x) := by
  rw [← action_add, ← action_add, NonnegativeDyadicTime.add_comm]

theorem action_add_state (t : Time) (x y : Completion) :
    action t (completedAdd x y) = completedAdd (action t x) (action t y) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_add_state p.depth p.steps x y

theorem action_smul (t : Time) (c : Q') (x : Completion) :
    action t (completedSmul c x) = completedSmul c (action t x) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_smul p.depth p.steps c x

theorem action_symmetric (t : Time) (x y : Completion) :
    completedInner (action t x) y = completedInner x (action t y) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_symmetric p.depth p.steps x y

theorem action_nonnegative (t : Time) (x : Completion) :
    RCnonneg (completedInner (action t x) x) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_nonnegative p.depth p.steps x

theorem action_contraction (t : Time) (x : Completion) :
    RCle (completedInner (action t x) (action t x)) (completedInner x x) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_contraction p.depth p.steps x

theorem action_unit (t : Time) : action t completedUnit = completedUnit := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_unit p.depth p.steps

theorem action_center (t : Time) (x : Completion) : action t (center x) = center (action t x) := by
  refine Quotient.inductionOn t ?_
  intro p
  exact time_center p.depth p.steps x

/-- A unit of dyadic time means T2, not an unproved identification with geometric T1. -/
theorem action_whole (n : Nat) (x : Completion) : action (whole n) x = completedTime (2*n) x :=
  time_original_even n x

theorem action_one (x : Completion) : action (whole 1) x = twoStepTransfer x := generator_zero x

theorem action_generator (depth : Nat) (x : Completion) : action (embed ⟨depth,1⟩) x = generator depth x := rfl

theorem action_mixed_moments (s t : Time) (x y : Completion) :
    completedInner (action (add s t) x) y = completedInner (action t x) (action s y) := by
  rw [action_add, action_symmetric]

theorem action_doubled_moments (t : Time) (x y : Completion) :
    completedInner (action (add t t) x) y = completedInner (action t x) (action t y) :=
  action_mixed_moments t t x y

def representative (p : MeshPoint) (X : seminorm.Cauchy) : seminorm.Cauchy :=
  timeRepresentative p.depth p.steps X

theorem representative_pin (p : MeshPoint) (X : seminorm.Cauchy) :
    (point (representative p X)) = action (embed p) (point X) := timeRepresentative_pin p.depth p.steps X

/-- The output sequence and its Cauchy modulus are retained in the supplied-data interface. -/
def representativeCertificate (p : MeshPoint) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy, (point Y) = action (embed p) (point X) :=
  ⟨representative p X, representative_pin p X⟩

theorem representative_congr {p q : MeshPoint} (h : Equivalent p q) (X : seminorm.Cauchy) :
    (point (representative p X)) = (point (representative q X)) := by
  rw [representative_pin, representative_pin]
  exact mesh_action_congr h (point X)

end YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.doubleSteps_eq
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.time_refinement_power
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.mesh_action_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_embed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_refine
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.mesh_action_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_commutes
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_add_state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_whole
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_generator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_mixed_moments
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.action_doubled_moments
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.representative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.representative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.representativeCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup.representative_congr
