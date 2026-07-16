/-
# The normalized finite-volume canonical cutoff-one polymer measure

The corrected canonical polymer partition is an exact finite sum of
nonnegative rational family activities.  This module proves that the vacuum
family occurs in every box, so the partition is at least one, and then
constructs normalized probabilities of arbitrary decidable family events by
division by that provably positive partition.

This is the finite-measure layer needed before a thermodynamic-limit proof can
even be stated without an unproved normalization hypothesis.  It does not
claim that the probabilities have converged as the box grows; that is the next
cluster/specification problem.
-/

import YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount

namespace YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The vacuum family makes the finite partition strictly positive -/

private theorem nil_mem_sublists_local {A : Type} :
    ∀ xs : List A, [] ∈ sublists xs
  | [] => List.mem_cons_self
  | head :: rest => by
      unfold sublists
      exact List.mem_append_left _ (nil_mem_sublists_local rest)

theorem nil_mem_canonicalCompatibleAmbientFamilies (n : Nat) :
    [] ∈ canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨nil_mem_sublists_local (canonicalSurfacePolymers n), rfl⟩

theorem listQSum_member_le {A : Type} (f : A → Q')
    (hf : ∀ x, (0 : Q') ≤ f x) :
    ∀ (xs : List A) {x : A}, x ∈ xs → f x ≤ listQSum f xs
  | [], _, h => absurd h List.not_mem_nil
  | head :: rest, x, h => by
      rcases List.mem_cons.mp h with hhead | hrest
      · subst x
        have htail0 := listQSum_nonnegative f hf rest
        exact Q'.add_le_self_of_nonneg (f head)
          (listQSum f rest) htail0
      · have ih := listQSum_member_le f hf rest hrest
        have hhead0 := hf head
        have hmono : listQSum f rest ≤ f head + listQSum f rest := by
          have h := Q'.add_le_add_right
            (0 : Q') (f head) (listQSum f rest) hhead0
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

/-- The exact corrected cutoff-one SU(2) polymer partition at the derived
strong-coupling anchor. -/
def anchorCanonicalPartition (n : Nat) : Q' :=
  parametricCanonicalCompatibleAmbientPartition anchorCoupling n

theorem anchorCanonicalPartition_nonnegative (n : Nat) :
    (0 : Q') ≤ anchorCanonicalPartition n := by
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  exact listQSum_nonnegative _
    (canonicalSurfaceFamilyActivity_nonnegative n)
    (canonicalCompatibleAmbientFamilies n)

theorem anchorCanonicalPartition_one_le (n : Nat) :
    (1 : Q') ≤ anchorCanonicalPartition n := by
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  have h := listQSum_member_le
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity_nonnegative n)
    (canonicalCompatibleAmbientFamilies n)
    (x := []) (nil_mem_canonicalCompatibleAmbientFamilies n)
  change (1 : Q') ≤ listQSum
    (canonicalSurfaceFamilyActivity anchorCoupling n)
      (canonicalCompatibleAmbientFamilies n)
  exact h

private theorem qlt_of_lt_of_le {a b c : Q'}
    (hleft : a < b) (hright : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := hleft
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hright
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hcd : (0 : Int) < (c.den : Int) := by
    exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by
    exact_mod_cast Nat.zero_le _
  have first : (a.num * (c.den : Int)) * (b.den : Int) <
      (b.num * (a.den : Int)) * (c.den : Int) := by
    have h := Int.mul_lt_mul_of_pos_right e1 hcd
    have hreorder : (a.num * (b.den : Int)) * (c.den : Int) =
        (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at h
  have second : (b.num * (a.den : Int)) * (c.den : Int) ≤
      (c.num * (a.den : Int)) * (b.den : Int) := by
    have h := Int.mul_le_mul_of_nonneg_left e2 had
    have hleft : (a.den : Int) * (b.num * (c.den : Int)) =
        (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hright : (a.den : Int) * (c.num * (b.den : Int)) =
        (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hleft, hright] at h
  have chained : (a.num * (c.den : Int)) * (b.den : Int) <
      (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le first second
  exact Int.lt_of_mul_lt_mul_right chained (by
    exact_mod_cast Nat.zero_le _)

theorem anchorCanonicalPartition_pos (n : Nat) :
    (0 : Q') < anchorCanonicalPartition n :=
  qlt_of_lt_of_le (by decide) (anchorCanonicalPartition_one_le n)

/-- The denominator is the actual localized spin-foam partition, not an
auxiliary majorant. -/
theorem anchorCanonicalPartition_eqv_localizedSpinFoam (n : Nat) :
    anchorCanonicalPartition n ≈
      parametricLocalizedSpinFoamPartition anchorCoupling n :=
  Q'.eqv_symm
    (parametricLocalizedSpinFoamPartition_eq_correctedPolymerPartition
      anchorCoupling n)

theorem anchorCanonicalPartition_eqv_gaugeCartesian (n : Nat) :
    anchorCanonicalPartition n ≈
      parametricGaugeBoxVertexCartesianSum anchorCoupling n :=
  Q'.eqv_trans _ _ _
    (anchorCanonicalPartition_eqv_localizedSpinFoam n)
    (Q'.eqv_symm
      (parametricGaugeBoxVertexCartesianSum_eq_localizedSpinFoam
        anchorCoupling n))

/-! ## 2. Normalized probabilities of decidable family events -/

def anchorEventNumerator (n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
    ((canonicalCompatibleAmbientFamilies n).filter event)

theorem anchorEventNumerator_nonnegative (n : Nat)
    (event : List (List Nat) → Bool) :
    (0 : Q') ≤ anchorEventNumerator n event := by
  unfold anchorEventNumerator
  exact listQSum_nonnegative _
    (canonicalSurfaceFamilyActivity_nonnegative n) _

theorem anchorEventNumerator_le_partition (n : Nat)
    (event : List (List Nat) → Bool) :
    anchorEventNumerator n event ≤ anchorCanonicalPartition n := by
  unfold anchorEventNumerator anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  exact listQSum_filter_le _ event
    (canonicalSurfaceFamilyActivity_nonnegative n)
    (canonicalCompatibleAmbientFamilies n)

/-- Exact rational probability of an arbitrary decidable event on corrected
compatible polymer families. -/
def anchorEventProbability (n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos (anchorEventNumerator n event)
    (anchorCanonicalPartition n) (anchorCanonicalPartition_pos n)

theorem anchorEventProbability_nonnegative (n : Nat)
    (event : List (List Nat) → Bool) :
    (0 : Q') ≤ anchorEventProbability n event := by
  unfold anchorEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (anchorEventNumerator_nonnegative n event)
    (Q'.le_of_lt
      (Q'.recipPos_pos (anchorCanonicalPartition n)
        (anchorCanonicalPartition_pos n)))

theorem anchorEventProbability_le_one (n : Nat)
    (event : List (List Nat) → Bool) :
    anchorEventProbability n event ≤ (1 : Q') := by
  unfold anchorEventProbability
  apply Q'.divPos_le_of_le_mul
  have hnum := anchorEventNumerator_le_partition n event
  exact Q'.le_trans' _ _ _ hnum
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv (anchorCanonicalPartition n)))

/-! ## 3. Canonical local occurrence observables -/

def familyContainsPolymerB (polymer : List Nat)
    (family : List (List Nat)) : Bool :=
  decide (polymer ∈ family)

def anchorPolymerOccurrenceProbability
    (n : Nat) (polymer : List Nat) : Q' :=
  anchorEventProbability n (familyContainsPolymerB polymer)

theorem anchorPolymerOccurrenceProbability_nonnegative
    (n : Nat) (polymer : List Nat) :
    (0 : Q') ≤ anchorPolymerOccurrenceProbability n polymer :=
  anchorEventProbability_nonnegative n _

theorem anchorPolymerOccurrenceProbability_le_one
    (n : Nat) (polymer : List Nat) :
    anchorPolymerOccurrenceProbability n polymer ≤ (1 : Q') :=
  anchorEventProbability_le_one n _

end YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorCanonicalPartition_one_le
#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorCanonicalPartition_pos
#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorCanonicalPartition_eqv_gaugeCartesian
#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorEventNumerator_le_partition
#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorEventProbability_nonnegative
#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorEventProbability_le_one
#print axioms YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure.anchorPolymerOccurrenceProbability_le_one
