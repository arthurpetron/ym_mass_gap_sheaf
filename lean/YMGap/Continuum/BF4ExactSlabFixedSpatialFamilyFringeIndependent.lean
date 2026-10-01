/-
# Fringe independence of a padded signed spatial plaquette family

Every constituent face from the smaller spatial slice is fully active after
strict padding. Arbitrary rational coefficients preserve this locality,
including all signed combinations and repeated faces.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
  (plaquette_fringe_independent_after_padding)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini

/-- A signed finite family supported on the smaller slice omits every
fringe block of the padded slice, with no condition on its coefficients. -/
theorem spatialSpan_fringe_independent_after_padding {base width : Nat}
    (hwidth : base < width) (c : Z4Plaq → Q') :
    ∀ qs : List Z4Plaq,
      (∀ p, p ∈ qs → p ∈ spatialFaces base) →
      ∀ i, i ∈ fringeBlocks width →
        QuaternionBlockIndependent i (spatialSpan width c qs)
  | [], _, i, _ => by
      intro term ht
      exact False.elim (List.not_mem_nil ht)
  | p :: qs, hqs, i, hi => by
      change QuaternionBlockIndependent i (polyAdd
        (polySmul (c p) (characterPolynomial (plaquette width p).scalar 1))
        (spatialSpan width c qs))
      exact quaternionBlockIndependent_polyAdd
        (quaternionBlockIndependent_polySmul (c p)
          (plaquette_fringe_independent_after_padding hwidth p
            (hqs p List.mem_cons_self) i hi))
        (spatialSpan_fringe_independent_after_padding hwidth c qs
          (fun r hr => hqs r (List.mem_cons_of_mem p hr)) i hi)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent.spatialSpan_fringe_independent_after_padding
