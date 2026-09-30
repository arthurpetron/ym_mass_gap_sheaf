/-
# Exact encoding of the original signed physical-face source

The Nat-indexed observable and the plaquette-indexed source span are the
same polynomial when the latter uses every original physical face and the
coefficient function is pulled back by the slab face index. This is a literal
finite-list equality, not a change of action or a sphere-radical quotient.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
import YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

namespace YMGap.Continuum.BF4ExactSlabSignedSourceEncoding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing (faceSpan)
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter)
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient (term observable)
open YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
  (incidentCoefficient)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily (sourceSpan)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (affineSource)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
  (slabFaceIds_map idxOf_slabPlaquetteAt)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem faceSpan_mapped_ids (extent : Nat) (c : Nat → Q') :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      faceSpan extent
          ((ids.map (slabPlaquetteAt extent)).map
            (fun face => (incidentCoefficient extent c face, face))) =
        finitePolySum (term extent c) ids
  | [], _ => rfl
  | id :: ids, hids => by
      have hid := hids id List.mem_cons_self
      simp only [List.map_cons, faceSpan, finitePolySum, incidentCoefficient, term]
      rw [idxOf_slabPlaquetteAt hid]
      exact congrArg (polyAdd (polySmul (c id)
        (faceCharacter extent (slabPlaquetteAt extent id))))
        (faceSpan_mapped_ids extent c ids
          (fun other hother => hids other (List.mem_cons_of_mem id hother)))

/-- The entire original plaquette-indexed source is literally the
Nat-indexed signed physical-face observable. Every coefficient and every
physical face is retained exactly once. -/
theorem sourceSpan_full (extent : Nat) (c : Nat → Q') :
    sourceSpan extent (incidentCoefficient extent c)
      (boundaryCompleteSlabPlaquettes extent) = observable extent c := by
  rw [← slabFaceIds_map extent]
  unfold sourceSpan observable
  exact faceSpan_mapped_ids extent c (slabPhysicalFaceEdges extent)
    (fun _ hid => hid)

/-- The same literal identity after the arbitrary rational center is
subtracted. This is the affine source consumed by the signed mixed-energy
floor, on the same original polynomial carrier. -/
theorem affineSource_full (extent : Nat) (c : Nat → Q') (m : Q') :
    affineSource extent (incidentCoefficient extent c)
      (boundaryCompleteSlabPlaquettes extent) m =
        QuaternionHaarDensityVariance.shifted (observable extent c) m := by
  unfold affineSource
  exact congrArg (fun p => QuaternionHaarDensityVariance.shifted p m)
    (sourceSpan_full extent c)

#print axioms sourceSpan_full
#print axioms affineSource_full

end YMGap.Continuum.BF4ExactSlabSignedSourceEncoding
