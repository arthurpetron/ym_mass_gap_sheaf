/-
# Exact transport of original block projections through auxiliary heads

Adjoining normalized quaternion head coordinates shifts every original
block index by the number of heads. The raw clear-mask and S³ moment
definitions commute with that shift, so finite family projections commute
with liftBoundary by literal polynomial equality. No support or analytic
hypothesis is needed.
-/

import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.SU2QuaternionLiftedFamilyProjection

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection

private theorem clearFrom_shift (block start : Nat) (monomial : List Nat) :
    clearQuaternionBlockFrom (block + 1) (start + 4) monomial =
      clearQuaternionBlockFrom block start monomial := by
  induction monomial generalizing start with
  | nil => rfl
  | cons exponent tail ih =>
      have hc : coordinateInQuaternionBlock (block + 1) (start + 4) ↔
          coordinateInQuaternionBlock block start := by
        unfold coordinateInQuaternionBlock
        constructor
        · intro h
          exact ⟨by omega, by omega⟩
        · intro h
          exact ⟨by omega, by omega⟩
      have hs : (start + 4) + 1 = (start + 1) + 4 := by omega
      cases (inferInstance : Decidable (4 * block ≤ start ∧ start < 4 * block + 4)) with
      | isTrue h =>
        change coordinateInQuaternionBlock block start at h
        have h' := hc.mpr h
        simp only [clearQuaternionBlockFrom, h, h', if_true, hs]
        exact congrArg (List.cons 0) (ih (start + 1))
      | isFalse h =>
        change ¬ coordinateInQuaternionBlock block start at h
        have h' : ¬ coordinateInQuaternionBlock (block + 1) (start + 4) :=
          fun h' => h (hc.mp h')
        simp only [clearQuaternionBlockFrom, h, h', if_false, hs]
        exact congrArg (List.cons exponent) (ih (start + 1))

private theorem clear_liftHead (block : Nat) (monomial : List Nat) :
    clearQuaternionBlock (block + 1) (0 :: 0 :: 0 :: 0 :: monomial) =
      0 :: 0 :: 0 :: 0 :: clearQuaternionBlock block monomial := by
  have h0 : ¬ coordinateInQuaternionBlock (block + 1) 0 := by
    unfold coordinateInQuaternionBlock
    omega
  have h1 : ¬ coordinateInQuaternionBlock (block + 1) 1 := by
    unfold coordinateInQuaternionBlock
    omega
  have h2 : ¬ coordinateInQuaternionBlock (block + 1) 2 := by
    unfold coordinateInQuaternionBlock
    omega
  have h3 : ¬ coordinateInQuaternionBlock (block + 1) 3 := by
    unfold coordinateInQuaternionBlock
    omega
  unfold clearQuaternionBlock
  simp only [clearQuaternionBlockFrom, h0, h1, h2, h3, if_false]
  exact congrArg (fun xs => 0 :: 0 :: 0 :: 0 :: xs)
    (clearFrom_shift block 0 monomial)

private theorem moment_liftHead (block : Nat) (monomial : List Nat) :
    quaternionBlockMoment (block + 1) (0 :: 0 :: 0 :: 0 :: monomial) =
      quaternionBlockMoment block monomial := by
  have he (component : Nat) :
      exponentAt (0 :: 0 :: 0 :: 0 :: monomial)
          (4 * (block + 1) + component) =
        exponentAt monomial (4 * block + component) := by
    rw [show 4 * (block + 1) + component =
      4 + (4 * block + component) by omega]
    rw [Nat.add_comm 4 (4 * block + component)]
    rfl
  unfold quaternionBlockMoment
  have he0 := he 0
  simp only [Nat.add_zero] at he0
  rw [he0, he 1, he 2, he 3]

/-- One newly adjoined head shifts the exact in-place projection by one
block, retaining every raw monomial and coefficient. -/
theorem project_liftHead (block : Nat) : ∀ p : RatPoly,
    project (block + 1) (liftHead p) = liftHead (project block p)
  | [] => rfl
  | term :: rest => by
      change
        (clearQuaternionBlock (block + 1) (0 :: 0 :: 0 :: 0 :: term.1),
          term.2 * quaternionBlockMoment (block + 1)
            (0 :: 0 :: 0 :: 0 :: term.1)) ::
            project (block + 1) (liftHead rest) =
          (0 :: 0 :: 0 :: 0 :: clearQuaternionBlock block term.1,
            term.2 * quaternionBlockMoment block term.1) ::
            liftHead (project block rest)
      rw [clear_liftHead block term.1, moment_liftHead block term.1,
        project_liftHead block rest]

/-- The exact one-head identity holds for any finite integration schedule,
including repetitions and blocks outside a named finite support. -/
theorem familyProject_liftHead (ids : List Nat) : ∀ p : RatPoly,
    familyProject (ids.map (fun i => i + 1)) (liftHead p) =
      liftHead (familyProject ids p) := by
  induction ids with
  | nil =>
      intro p
      rfl
  | cons block ids ih =>
      intro p
      change familyProject (ids.map (fun i => i + 1))
          (project (block + 1) (liftHead p)) =
        liftHead (familyProject ids (project block p))
      rw [project_liftHead block p]
      exact ih (project block p)

/-- Any number of auxiliary heads shifts an original finite projection
schedule by precisely that number, by literal polynomial equality. -/
theorem familyProject_lift (heads : Nat) (ids : List Nat) (p : RatPoly) :
    familyProject (ids.map (fun i => i + heads)) (liftBoundary heads p) =
      liftBoundary heads (familyProject ids p) := by
  induction heads with
  | zero =>
      have hid : ids.map (fun i => i+0) = ids := by
        induction ids with
        | nil => rfl
        | cons i ids ih => exact congrArg (List.cons i) ih
      rw [hid]
      rfl
  | succ heads ih =>
      have hids : ids.map (fun i => i + (heads + 1)) =
          (ids.map (fun i => i + heads)).map (fun i => i + 1) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro i hi
        change i + (heads + 1) = (i + heads) + 1
        omega
      change familyProject (ids.map (fun i => i + (heads + 1)))
          (liftHead (liftBoundary heads p)) =
        liftHead (liftBoundary heads (familyProject ids p))
      rw [hids, familyProject_liftHead]
      exact congrArg liftHead ih

#print axioms project_liftHead
#print axioms familyProject_liftHead
#print axioms familyProject_lift

end YMGap.Continuum.SU2QuaternionLiftedFamilyProjection
