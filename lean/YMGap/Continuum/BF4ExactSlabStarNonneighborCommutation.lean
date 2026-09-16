/-
# Non-neighbor conditional updates commute in the ORIGINAL completion

If two physical links share no plaquette, one link's update preserves
independence of the other. This is proved on the existing localized
polynomial representatives, then passed through their supplied Cauchy
limits. Self-adjointness turns the invariant-range identity into exact
commutation on the entire original full-action weighted completion.

No interaction is deleted from the operators. These are ordinary L2
conditional projections, not OS time transfer. The theorem removes
non-neighbor commutators; it supplies no small bound on neighboring
influences, spatial decay, continuum passage or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabStarIndependentProbe
import YMGap.Continuum.BF4ExactSlabStarConditionalLocality
import YMGap.Continuum.GNSDenseFixedPoint
import YMGap.Continuum.GNSProjectionCommutation

namespace YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarConditionalLocality
open YMGap.Continuum.BF4ExactSlabStarIndependentProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Literal absence from the other link's incident faces is symmetric. -/
theorem nonneighbor_symm (extent : Nat) (i j : Z4Link)
    (h : j ∉ faceLinks extent (incidentIds extent i)) :
    i ∉ faceLinks extent (incidentIds extent j) := by
  intro hi
  obtain ⟨id, hid, hi⟩ := List.mem_flatMap.mp hi
  have hj := (mem_incidentIds_iff extent j id).mp hid
  apply h
  exact List.mem_flatMap.mpr ⟨id,
    (mem_incidentIds_iff extent i id).mpr ⟨hj.1, hi⟩, hj.2⟩

/-- No hidden geometric separation is needed: inspect every physical face. -/
theorem nonneighbor_iff (extent : Nat) (i j : Z4Link) :
    j ∉ faceLinks extent (incidentIds extent i) ↔
      ∀ id, id ∈ slabPhysicalFaceEdges extent →
        i ∈ edgesOf (slabPlaquetteAt extent id) →
        j ∉ edgesOf (slabPlaquetteAt extent id) := by
  constructor
  · intro h id hid hi hj
    exact h (List.mem_flatMap.mpr ⟨id,
      (mem_incidentIds_iff extent i id).mpr ⟨hid, hi⟩, hj⟩)
  · intro h hj
    obtain ⟨id, hid, hj⟩ := List.mem_flatMap.mp hj
    have hi := (mem_incidentIds_iff extent i id).mp hid
    exact h id hi.1 hi.2 hj

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (i j : Z4Link) (hi : i ∈ boundaryCompleteSlabLinks extent)
  (hj : j ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "Ci" => conditionalProjection hw0 hw1 K extent hK i hi
local notation "Cj" => conditionalProjection hw0 hw1 K extent hK j hj

/-- The actual update of a j-independent input remains j-independent in
the sense of being fixed by the original j-conditional projection. -/
theorem conditionalProjection_preserves_omitted
    (hij : j ∉ faceLinks extent (incidentIds extent i))
    (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) (hnot : j ∉ support) :
    Cj (Ci (embedV F p)) = Ci (embedV F p) := by
  let X := conditionalProjection_localRepresentative hw0 hw1 K extent hK i hi support p hp
  have hnotUpdate : j ∉ updateLinks extent i support := by
    intro hm
    have ha := (List.mem_filter.mp hm).1
    rcases List.mem_append.mp ha with hs | hs
    · exact hnot hs
    · exact hij hs
  have hfix := GNSDenseFixedPoint.fixed_of_cauchy_terms Cj
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK j hj) X.val
    (fun n => conditionalProjection_fix_local hw0 hw1 K extent hK j hj
      (updateLinks extent i support) (X.val.seq n) (X.property.1 n) hnotUpdate)
  rw [X.property.2] at hfix
  exact hfix

/-- The supplied dense j-update representatives avoid j at every index.
Passing i through these representatives gives the dense invariant-range
identity without choosing any representative of an arbitrary quotient. -/
theorem conditionalProjection_invariant_dense
    (hij : j ∉ faceLinks extent (incidentIds extent i)) (p : (F).V) :
    Cj (Ci (Cj (embedV F p))) = Ci (Cj (embedV F p)) := by
  let X := (conditionalDenseMap hw0 hw1 K extent hK j hj).toRep p
  have hlocal (n : Nat) : LinkLocal extent (independentLinks extent j) (X.seq n).val := by
    change LinkLocal extent (independentLinks extent j)
      (probeMap hw0 hw1 K extent hK j hj
        ((inverseCauchy hw0 hw1 K extent hK j hj
          (numeratorMap hw0 hw1 K extent hK j hj p)).seq n)).val
    exact probeMap_local hw0 hw1 K extent hK j hj _
  have hfix := GNSDenseFixedPoint.fixed_of_cauchy_images Cj Ci
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK j hj)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK i hi) X
    (fun n => conditionalProjection_preserves_omitted hw0 hw1 K extent hK i j hi hj hij
      (independentLinks extent j) (X.seq n) (hlocal n) (by simp [independentLinks]))
  have he : Quotient.mk (cauchySetoid F) X = Cj (embedV F p) :=
    ((conditionalDenseMap hw0 hw1 K extent hK j hj).completionMap_embed p).symm
  rw [he] at hfix
  exact hfix

/-- Full-space invariant-range identity on the SAME original completion. -/
theorem conditionalProjection_invariant
    (hij : j ∉ faceLinks extent (incidentIds extent i)) (x : GNSCompletionSpace F) :
    Cj (Ci (Cj x)) = Ci (Cj x) :=
  GNSDenseFixedPoint.invariant_range_of_dense Cj Ci
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK j hj)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK i hi)
    (conditionalProjection_invariant_dense hw0 hw1 K extent hK i j hi hj hij) x

/-- Non-neighbor link updates commute exactly for every completed vector.
All late cutoffs and all rational 0<w<1 are covered; no gap is asserted. -/
theorem conditionalProjection_commute
    (hij : j ∉ faceLinks extent (incidentIds extent i)) (x : GNSCompletionSpace F) :
    Ci (Cj x) = Cj (Ci x) :=
  GNSProjectionCommutation.commute_of_invariant F Ci Cj
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK i hi)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK j hj)
    (conditionalProjection_invariant hw0 hw1 K extent hK i j hi hj hij) x

/-- The ordered pair update is self-adjoint in the original full-action form. -/
theorem twoLink_update_selfAdjoint
    (hij : j ∉ faceLinks extent (incidentIds extent i)) (x y : GNSCompletionSpace F) :
    (F).cinnerCompl (Ci (Cj x)) y = (F).cinnerCompl x (Ci (Cj y)) := by
  rw [conditionalProjection_selfAdjoint, conditionalProjection_selfAdjoint,
    ← conditionalProjection_commute hw0 hw1 K extent hK i j hi hj hij y]

/-- Updating the same non-neighbor pair a second time has no effect. -/
theorem twoLink_update_idempotent
    (hij : j ∉ faceLinks extent (incidentIds extent i)) (x : GNSCompletionSpace F) :
    Ci (Cj (Ci (Cj x))) = Ci (Cj x) := by
  rw [conditionalProjection_invariant hw0 hw1 K extent hK i j hi hj hij,
    conditionalProjection_idempotent]

/-- Its fixed space is EXACTLY the intersection of the two original fixed
spaces. This identifies a joint local projection, not a time-transfer step. -/
theorem twoLink_update_fixed_iff
    (hij : j ∉ faceLinks extent (incidentIds extent i)) (x : GNSCompletionSpace F) :
    Ci (Cj x) = x ↔ Ci x = x ∧ Cj x = x := by
  constructor
  · intro h
    constructor
    · calc
        Ci x = Ci (Ci (Cj x)) := congrArg Ci h.symm
        _ = Ci (Cj x) := conditionalProjection_idempotent hw0 hw1 K extent hK i hi _
        _ = x := h
    · calc
        Cj x = Cj (Ci (Cj x)) := congrArg Cj h.symm
        _ = Ci (Cj x) := conditionalProjection_invariant hw0 hw1 K extent hK i j hi hj hij x
        _ = x := h
  · intro h
    rw [h.2, h.1]

end YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation

#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.nonneighbor_symm
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.nonneighbor_iff
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.conditionalProjection_preserves_omitted
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.conditionalProjection_invariant_dense
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.conditionalProjection_invariant
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.conditionalProjection_commute
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.twoLink_update_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.twoLink_update_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation.twoLink_update_fixed_iff
