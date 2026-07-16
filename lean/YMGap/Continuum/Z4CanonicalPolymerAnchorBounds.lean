/-
# Uniform anchor bounds for the canonical Z4 polymer gas

This module attaches the exact very-strong-coupling activity estimate to the
finite ambient polymer universe.  It records positivity and the product bound
for an entire compatible family, with exponent equal to the total number of
plaquettes in that family.  These are the quantitative inputs needed by the
pinned lattice-animal/KP summation.
-/

import YMGap.Continuum.Z4CanonicalPolymerAnimalBridge

namespace YMGap.Continuum.Z4CanonicalPolymerAnchorBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

theorem canonicalSurfacePolymer_activity_nonnegative
    (n : Nat) (polymer : List Nat) :
    (0 : Q') ≤ canonicalSurfaceActivity anchorCoupling n polymer :=
  canonicalSurfaceActivity_nonnegative (by decide) n polymer

theorem canonicalSurfacePolymer_activity_le
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity anchorCoupling n polymer ≤
      anchorPerFaceEnvelope ^ polymer.length :=
  canonicalSurfaceActivity_anchor_le_envelopePow
    (canonicalSurfacePolymer_mem_faceSupports hpolymer)

def familyFaceCount : List (List Nat) → Nat
  | [] => 0
  | polymer :: rest => polymer.length + familyFaceCount rest

theorem canonicalSurfaceFamilyActivity_nonnegative (n : Nat) :
    ∀ family : List (List Nat),
      (0 : Q') ≤
        canonicalSurfaceFamilyActivity anchorCoupling n family
  | [] => by
      change (0 : Q') ≤ 1
      decide
  | polymer :: rest => by
      change (0 : Q') ≤
        canonicalSurfaceActivity anchorCoupling n polymer *
          canonicalSurfaceFamilyActivity anchorCoupling n rest
      exact Q'.mul_nonneg _ _
        (canonicalSurfacePolymer_activity_nonnegative n polymer)
        (canonicalSurfaceFamilyActivity_nonnegative n rest)

theorem canonicalSurfaceFamilyActivity_le_totalFacePow
    (n : Nat) : ∀ family : List (List Nat),
    (∀ polymer, polymer ∈ family →
      polymer ∈ canonicalSurfacePolymers n) →
    canonicalSurfaceFamilyActivity anchorCoupling n family ≤
      anchorPerFaceEnvelope ^ familyFaceCount family
  | [], _ => by
      change (1 : Q') ≤ 1
      exact Q'.le_refl' 1
  | polymer :: rest, hmembers => by
      have hpolymer : polymer ∈ canonicalSurfacePolymers n :=
        hmembers polymer List.mem_cons_self
      have hrest : ∀ item, item ∈ rest →
          item ∈ canonicalSurfacePolymers n :=
        fun item hitem =>
          hmembers item (List.mem_cons_of_mem polymer hitem)
      have hhead := canonicalSurfacePolymer_activity_le hpolymer
      have htail :=
        canonicalSurfaceFamilyActivity_le_totalFacePow n rest hrest
      have htail0 := canonicalSurfaceFamilyActivity_nonnegative n rest
      have hheadPow0 : (0 : Q') ≤
          anchorPerFaceEnvelope ^ polymer.length :=
        Q'.pow_nonneg anchorPerFaceEnvelope (by decide) polymer.length
      have hfirst :
          canonicalSurfaceActivity anchorCoupling n polymer *
              canonicalSurfaceFamilyActivity anchorCoupling n rest ≤
            anchorPerFaceEnvelope ^ polymer.length *
              canonicalSurfaceFamilyActivity anchorCoupling n rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hhead htail0
      have hsecond :
          anchorPerFaceEnvelope ^ polymer.length *
              canonicalSurfaceFamilyActivity anchorCoupling n rest ≤
            anchorPerFaceEnvelope ^ polymer.length *
              anchorPerFaceEnvelope ^ familyFaceCount rest :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail hheadPow0
      change
        canonicalSurfaceActivity anchorCoupling n polymer *
            canonicalSurfaceFamilyActivity anchorCoupling n rest ≤
          anchorPerFaceEnvelope ^
            (polymer.length + familyFaceCount rest)
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.pow_add_eqv anchorPerFaceEnvelope polymer.length
                (familyFaceCount rest)))))

theorem compatibleFamily_member_mem_ambient
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    {polymer : List Nat} (hpolymer : polymer ∈ family) :
    polymer ∈ canonicalSurfacePolymers n := by
  have hsub : family ∈ sublists (canonicalSurfacePolymers n) :=
    (List.mem_filter.mp hfamily).1
  exact mem_of_mem_sublists (canonicalSurfacePolymers n) family
    hsub polymer hpolymer

theorem compatibleFamily_activity_le_totalFacePow
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    canonicalSurfaceFamilyActivity anchorCoupling n family ≤
      anchorPerFaceEnvelope ^ familyFaceCount family := by
  apply canonicalSurfaceFamilyActivity_le_totalFacePow n family
  intro polymer hpolymer
  exact compatibleFamily_member_mem_ambient hfamily hpolymer

end YMGap.Continuum.Z4CanonicalPolymerAnchorBounds

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPolymerAnchorBounds.canonicalSurfacePolymer_activity_le
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnchorBounds.canonicalSurfaceFamilyActivity_nonnegative
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnchorBounds.canonicalSurfaceFamilyActivity_le_totalFacePow
#print axioms YMGap.Continuum.Z4CanonicalPolymerAnchorBounds.compatibleFamily_activity_le_totalFacePow
