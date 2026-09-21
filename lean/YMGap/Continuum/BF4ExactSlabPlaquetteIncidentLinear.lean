/-
# Head-linearity and dual-family pin for an incident plaquette sum

For one witnessed physical link, every summand of the literal signed incident
plaquette observable is homogeneous of degree one in that link quaternion.
The existing head swap therefore makes the whole incident sum head-linear.

The same file identifies this Nat-indexed signed sum with the existing
duplicate-free physical-face `sourceSpan`.  These are exact finite polynomial
statements.  They add no action, positivity, energy, or response assumption.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGradient
import YMGap.Continuum.BF4ExactSlabOddFaceIncidence
import YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily

namespace YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabPlaquetteGradient
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualPairing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- The actual physical plaquettes incident to the selected link, with the
existing physical-face order retained. -/
def incidentPlaquettes (extent : Nat) (link : Z4Link) : List Z4Plaq :=
  (incidentIds extent link).map (slabPlaquetteAt extent)

/-- Pull a Nat-indexed physical-face coefficient function back to the literal
plaquette labels used by `sourceSpan`. -/
def incidentCoefficient (extent : Nat) (c : Nat → Q') (face : Z4Plaq) : Q' :=
  c ((boundaryCompleteSlabPlaquettes extent).idxOf face)

/-- Every plaquette in the incident list is an original slab plaquette. -/
theorem incidentPlaquettes_physical (extent : Nat) (link : Z4Link)
    {face : Z4Plaq} (hf : face ∈ incidentPlaquettes extent link) :
    face ∈ boundaryCompleteSlabPlaquettes extent := by
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hf
  exact slabPlaquetteAt_mem (incidentIds_physical hid)

/-- The incident physical plaquette list has no duplicate labels. -/
theorem incidentPlaquettes_nodup (extent : Nat) (link : Z4Link) :
    (incidentPlaquettes extent link).Nodup := by
  unfold incidentPlaquettes
  exact CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) _
    (incidentIds_nodup extent link)
    (fun left hleft right hright heq =>
      slabPlaquetteAt_injective_on_physical
        (incidentIds_physical hleft) (incidentIds_physical hright) heq)

private theorem term_degree_one (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q')
    {id : Nat} (hid : id ∈ incidentIds extent link) :
    HasQuaternionBlockDegree
      ((boundaryCompleteSlabLinks extent).idxOf link) 1
      (term extent c id) := by
  have hphysical := incidentIds_physical hid
  have hface := slabPlaquetteAt_mem hphysical
  have hedge := ((mem_incidentIds_iff extent link id).mp hid).2
  have hdegree := face_degree extent
    ((boundaryCompleteSlabLinks extent).idxOf link)
    (slabPlaquetteAt extent id) hface
  have hpin : faceDegree extent
      ((boundaryCompleteSlabLinks extent).idxOf link)
      (slabPlaquetteAt extent id) = 1 := by
    rw [faceDegree_pin extent link (slabPlaquetteAt extent id) hl hface,
      if_pos hedge]
  unfold term faceCharacter
  exact ((HasQuaternionBlockDegree.relabel hpin hdegree).smul 2).smul (c id)

private theorem finiteIncidentSum_degree_one (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ incidentIds extent link) →
      HasQuaternionBlockDegree
        ((boundaryCompleteSlabLinks extent).idxOf link) 1
        (finitePolySum (term extent c) ids)
  | [], _ => by
      intro monomial hm
      exact False.elim (List.not_mem_nil hm)
  | id :: ids, hids => by
      simp only [finitePolySum]
      exact (term_degree_one extent link hl c (hids id List.mem_cons_self)).add
        (finiteIncidentSum_degree_one extent link hl c ids
          (fun other hother => hids other (List.mem_cons_of_mem id hother)))

/-- The literal signed incident observable becomes homogeneous of degree one
in the head quaternion after the existing selected-link swap. -/
theorem incidentObservable_head_degree_one (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (c : Nat → Q') :
    HasQuaternionBlockDegree 0 1
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (incidentObservable extent link c)) := by
  apply blockDegree_reindex (linkHeadSwap extent link hl)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
    (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl))
  exact finiteIncidentSum_degree_one extent link hl c _ (fun _ hid => hid)

private theorem faceSpan_incident_eq (extent : Nat) (c : Nat → Q') :
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
        (faceSpan_incident_eq extent c ids
          (fun other hother => hids other (List.mem_cons_of_mem id hother)))

/-- The existing dual-family `sourceSpan` on the mapped incident plaquettes is
exactly the literal Nat-indexed incident observable, with every signed
coefficient unchanged. -/
theorem sourceSpan_incident (extent : Nat) (link : Z4Link) (c : Nat → Q') :
    RatPolyCoeffEqv
      (BF4ExactSlabPlaquetteBoundaryDualFamily.sourceSpan extent
        (incidentCoefficient extent c) (incidentPlaquettes extent link))
      (incidentObservable extent link c) := by
  unfold BF4ExactSlabPlaquetteBoundaryDualFamily.sourceSpan incidentPlaquettes
    incidentObservable
  rw [faceSpan_incident_eq extent c _ (fun _ hid => incidentIds_physical hid)]
  exact RatPolyCoeffEqv.refl _

private theorem coefficientSquares_map (extent : Nat) (c : Nat → Q') :
    ∀ ids : List Nat, (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      listQSum
          (fun face => incidentCoefficient extent c face *
            incidentCoefficient extent c face)
          (ids.map (slabPlaquetteAt extent)) ≈
        listQSum (fun id => c id * c id) ids
  | [], _ => Q'.eqv_refl _
  | id :: ids, hids => by
      have hid := hids id List.mem_cons_self
      simp only [List.map_cons, listQSum]
      exact Q'.add_eqv_congr'
        (by
          rw [incidentCoefficient, idxOf_slabPlaquetteAt hid]
          exact Q'.eqv_refl _)
        (coefficientSquares_map extent c ids
          (fun other hother => hids other (List.mem_cons_of_mem id hother)))

/-- Squared coefficients of the mapped physical plaquette source are exactly
the original Nat-indexed squared coefficients on the incident IDs. -/
theorem coefficientSquares_incident (extent : Nat) (link : Z4Link) (c : Nat → Q') :
    listQSum
        (fun face => incidentCoefficient extent c face *
          incidentCoefficient extent c face)
        (incidentPlaquettes extent link) ≈
      listQSum (fun id => c id * c id) (incidentIds extent link) := by
  unfold incidentPlaquettes
  exact coefficientSquares_map extent c _ (fun _ hid => incidentIds_physical hid)

end YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.incidentPlaquettes
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.incidentCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.incidentPlaquettes_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.incidentPlaquettes_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.incidentObservable_head_degree_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.sourceSpan_incident
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear.coefficientSquares_incident
