/-
# Exact BF4 vacuum reduction to the fixed-face Haar insertion

For vacuum source and target labels, the lower and upper spatial plaquette
characters are polynomial units.  This module proves that statement on the
literal 72-face carrier and removes those unit factors under exact normalized
product Haar.  Consequently the full 116-link vacuum--vacuum coefficient is
exactly the Haar value of the displayed 24-face interior insertion.

This is the algebraic/Fubini bridge needed before applying exposed-link
Peter--Weyl orthogonality.  It contains no positivity assumption.
-/

import YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
import YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
import YMGap.Continuum.BF4CompactActionCPOrder

namespace YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Put the vacuum spatial faces first and leave the genuine interior faces
last. -/
def exactVacuumSpatialFirstFaces : List Z4Plaq :=
  exactCorrectedSlabLowerSpatialFaces ++
    exactCorrectedSlabUpperSpatialFaces ++
      exactCorrectedSlabFixedFaces

theorem exactVacuumSpatialFirstFaces_perm :
    exactVacuumSpatialFirstFaces.Perm
      (boundaryCompleteSlabPlaquettes 1) := by
  have hswap :
      (exactCorrectedSlabLowerSpatialFaces ++
          exactCorrectedSlabUpperSpatialFaces ++
            exactCorrectedSlabFixedFaces).Perm
        (exactCorrectedSlabLowerSpatialFaces ++
          exactCorrectedSlabFixedFaces ++
            exactCorrectedSlabUpperSpatialFaces) := by
    exact
      (List.perm_append_comm
        (l₁ := exactCorrectedSlabUpperSpatialFaces)
        (l₂ := exactCorrectedSlabFixedFaces)).append_left
          exactCorrectedSlabLowerSpatialFaces
  exact hswap.trans exactCorrectedSlabPartitionedFaces_perm

private theorem assembledVacuum_lower_factor
    (boundary : EdgeLabelling) {face : Z4Plaq}
    (hface : face ∈ exactCorrectedSlabLowerSpatialFaces) :
    correctedSlabPlaquetteSpinFactor 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling)
        face = polyOne := by
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hface
  have hparts := mem_centralLowerFaceIds.mp hid
  have hphysical : id ∈ slabPhysicalFaceEdges 1 := by
    simpa [centralExtent] using hparts.1
  have hside :
      plaquetteHalfSide 0 (slabPlaquetteAt 1 id) =
        CrossPlaneSide.lower := by
    simpa [centralExtent] using hparts.2
  unfold correctedSlabPlaquetteSpinFactor
  rw [idxOf_slabPlaquetteAt_one hphysical]
  simp [assembleReflectedSlabLabelling, centralExtent, hphysical, hside,
    zeroEdgeLabelling, characterPolynomial]

private theorem assembledVacuum_upper_factor
    (boundary : EdgeLabelling) {face : Z4Plaq}
    (hface : face ∈ exactCorrectedSlabUpperSpatialFaces) :
    correctedSlabPlaquetteSpinFactor 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling)
        face = polyOne := by
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hface
  have hparts := mem_centralUpperFaceIds.mp hid
  have hphysical : id ∈ slabPhysicalFaceEdges 1 := by
    simpa [centralExtent] using hparts.1
  have hside :
      plaquetteHalfSide 0 (slabPlaquetteAt 1 id) =
        CrossPlaneSide.upper := by
    simpa [centralExtent] using hparts.2
  unfold correctedSlabPlaquetteSpinFactor
  rw [idxOf_slabPlaquetteAt_one hphysical]
  simp [assembleReflectedSlabLabelling, centralExtent, hphysical, hside,
    zeroEdgeLabelling, characterPolynomial]

private theorem assembledVacuum_fixed_factor
    (boundary : EdgeLabelling) {face : Z4Plaq}
    (hface : face ∈ exactCorrectedSlabFixedFaces) :
    correctedSlabPlaquetteSpinFactor 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling)
        face =
      correctedSlabPlaquetteSpinFactor 1 boundary face := by
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hface
  have hparts := mem_centralFixedFaceIds.mp hid
  have hphysical : id ∈ slabPhysicalFaceEdges 1 := by
    simpa [centralExtent] using hparts.1
  have hside :
      plaquetteHalfSide 0 (slabPlaquetteAt 1 id) =
        CrossPlaneSide.fixed := by
    simpa [centralExtent] using hparts.2
  unfold correctedSlabPlaquetteSpinFactor
  rw [idxOf_slabPlaquetteAt_one hphysical]
  rw [assembleReflectedSlabLabelling_fixed hphysical hside]

private theorem quaternionHaar_polyMul_one_left_local
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polynomial polyOne)) _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

/-- Unit factors may be deleted from a prefix even in the presence of an
arbitrary left insertion and an arbitrary non-vacuum suffix. -/
private theorem quaternionHaar_drop_unit_factor_prefix
    (blocks : Nat) (factor : Z4Plaq → RatPoly) :
    ∀ (leading suffix : List Z4Plaq),
      (∀ face, face ∈ leading → factor face = polyOne) →
      ∀ insertion : RatPoly,
        quaternionHaar blocks
            (polyMul insertion
              ((leading ++ suffix).foldr
                (fun face total => polyMul (factor face) total)
                polyOne)) ≈
          quaternionHaar blocks
            (polyMul insertion
              (suffix.foldr
                (fun face total => polyMul (factor face) total)
                polyOne))
  | [], suffix, _, insertion => Q'.eqv_refl _
  | face :: tail, suffix, hunit, insertion => by
      simp only [List.cons_append, List.foldr]
      rw [hunit face List.mem_cons_self]
      let remainder :=
        ((tail ++ suffix).foldr
          (fun next total => polyMul (factor next) total)
          polyOne)
      refine Q'.eqv_trans _
        (quaternionHaar blocks
          (polyMul insertion (polyMul remainder polyOne))) _ ?_ ?_
      · exact quaternionHaar_polyMul_middle_comm
          blocks insertion polyOne remainder
      refine Q'.eqv_trans _
        (quaternionHaar blocks
          (polyMul (polyMul insertion remainder) polyOne)) _ ?_ ?_
      · exact Q'.eqv_symm
          (quaternionHaar_polyMul_assoc
            blocks insertion remainder polyOne)
      refine Q'.eqv_trans _
        (quaternionHaar blocks (polyMul insertion remainder)) _ ?_ ?_
      · exact quaternionHaar_polyMul_one_right
          blocks (polyMul insertion remainder)
      exact quaternionHaar_drop_unit_factor_prefix
        blocks factor tail suffix
        (fun next hnext =>
          hunit next (List.mem_cons_of_mem face hnext))
        insertion

private theorem assembledVacuum_fixed_fold_eq_on
    (boundary : EdgeLabelling) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces → face ∈ exactCorrectedSlabFixedFaces) →
      faces.foldr
        (fun face total =>
          polyMul
            (correctedSlabPlaquetteSpinFactor 1
              (assembleReflectedSlabLabelling 0
                zeroEdgeLabelling boundary zeroEdgeLabelling)
              face)
            total)
        polyOne =
      faces.foldr
        (fun face total =>
          polyMul (correctedSlabPlaquetteSpinFactor 1 boundary face) total)
        polyOne
  | [], _ => rfl
  | face :: tail, hfaces => by
      simp only [List.foldr]
      rw [assembledVacuum_fixed_factor boundary
        (hfaces face List.mem_cons_self)]
      rw [assembledVacuum_fixed_fold_eq_on boundary tail
        (fun next hnext =>
          hfaces next (List.mem_cons_of_mem face hnext))]

private theorem assembledVacuum_fixed_fold_eq
    (boundary : EdgeLabelling) :
    exactCorrectedSlabFixedFaces.foldr
        (fun face total =>
          polyMul
            (correctedSlabPlaquetteSpinFactor 1
              (assembleReflectedSlabLabelling 0
                zeroEdgeLabelling boundary zeroEdgeLabelling)
              face)
            total)
        polyOne =
      exactCorrectedSlabInteriorInsertion boundary := by
  unfold exactCorrectedSlabInteriorInsertion
  exact assembledVacuum_fixed_fold_eq_on boundary
    exactCorrectedSlabFixedFaces (fun _ hface => hface)

/-- The literal full vacuum-boundary Haar coefficient is precisely the Haar
value of the 24-face fixed-plane insertion. -/
theorem exactCorrectedSlabVacuumBoundaryHaarCoefficient_eq_interior
    (boundary : EdgeLabelling) :
    exactCorrectedSlabHaarCoefficient 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling) ≈
      quaternionHaar (boundaryCompleteSlabLinks 1).length
        (exactCorrectedSlabInteriorInsertion boundary) := by
  let assembled :=
    assembleReflectedSlabLabelling 0
      zeroEdgeLabelling boundary zeroEdgeLabelling
  let factor : Z4Plaq → RatPoly := fun face =>
    correctedSlabPlaquetteSpinFactor 1 assembled face
  let spatial :=
    exactCorrectedSlabLowerSpatialFaces ++
      exactCorrectedSlabUpperSpatialFaces
  let fixedFold :=
    exactCorrectedSlabFixedFaces.foldr
      (fun face total => polyMul (factor face) total) polyOne
  have hperm := quaternionHaar_factorFold_perm
    (boundaryCompleteSlabLinks 1).length factor
    exactVacuumSpatialFirstFaces_perm polyOne
  have hunit : ∀ face, face ∈ spatial → factor face = polyOne := by
    intro face hface
    rcases List.mem_append.mp hface with hlower | hupper
    · exact assembledVacuum_lower_factor boundary hlower
    · exact assembledVacuum_upper_factor boundary hupper
  have hdrop := quaternionHaar_drop_unit_factor_prefix
    (boundaryCompleteSlabLinks 1).length factor
    spatial exactCorrectedSlabFixedFaces hunit polyOne
  unfold exactCorrectedSlabHaarCoefficient
    exactCorrectedSlabSpinNetworkIntegrand
  refine Q'.eqv_trans _
    (quaternionHaar (boundaryCompleteSlabLinks 1).length
      (polyMul polyOne
        ((boundaryCompleteSlabPlaquettes 1).foldr
          (fun face total => polyMul (factor face) total)
          polyOne))) _ ?_ ?_
  · exact Q'.eqv_symm
      (quaternionHaar_polyMul_one_left_local _ _)
  refine Q'.eqv_trans _
    (quaternionHaar (boundaryCompleteSlabLinks 1).length
      (polyMul polyOne
        (exactVacuumSpatialFirstFaces.foldr
          (fun face total => polyMul (factor face) total)
          polyOne))) _ ?_ ?_
  · exact Q'.eqv_symm hperm
  refine Q'.eqv_trans _
    (quaternionHaar (boundaryCompleteSlabLinks 1).length
      (polyMul polyOne fixedFold)) _ ?_ ?_
  · simpa [exactVacuumSpatialFirstFaces, spatial, fixedFold] using hdrop
  refine Q'.eqv_trans _
    (quaternionHaar (boundaryCompleteSlabLinks 1).length fixedFold) _ ?_ ?_
  · exact quaternionHaar_polyMul_one_left_local _ _
  rw [show fixedFold = exactCorrectedSlabInteriorInsertion boundary by
    exact assembledVacuum_fixed_fold_eq boundary]
  exact Q'.eqv_refl _

/-! ## The exact remaining one-link analytic atom -/

/-- Conditional Peter--Weyl orthogonality on the literal fixed-face
insertion.  The hypotheses select a nontrivial temporal plaquette; its
canonical exposed link is known, by `exactFixedFaceExposedLink_spec`, to occur
in no other surviving factor.  This proposition is therefore the precise
single-link Haar identity still required, with no arbitrary-kernel field. -/
def ExactFixedFaceConditionalHaarOrthogonality : Prop :=
  ∀ (boundary : EdgeLabelling) (face : Z4Plaq),
    face ∈ exactCorrectedSlabFixedFaces →
    boundary ((boundaryCompleteSlabPlaquettes 1).idxOf face) ≠ 0 →
      quaternionHaar (boundaryCompleteSlabLinks 1).length
          (exactCorrectedSlabInteriorInsertion boundary) ≈
        0

/-- Once the genuine single-exposed-link identity is supplied, every
non-vacuum vacuum-boundary term of every finite label cutoff vanishes.  The
proof uses the exact exposed-face selector and the 72-to-24 Haar reduction
above. -/
theorem exactVacuumNontrivialHaarTermsVanish_of_fixedFaceOrthogonality
    (orthogonality : ExactFixedFaceConditionalHaarOrthogonality)
    (K : Nat) : ExactVacuumNontrivialHaarTermsVanish K := by
  intro boundary hboundary hnonvacuum
  obtain ⟨face, hface, hlabel, hspec⟩ :=
    nonvacuumBoundary_has_exposed_nontrivial_face
      hboundary hnonvacuum
  exact Q'.eqv_trans _ _ _
    (exactCorrectedSlabVacuumBoundaryHaarCoefficient_eq_interior boundary)
    (orthogonality boundary face hface hlabel)

end YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction

#print axioms YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction.exactVacuumSpatialFirstFaces_perm
#print axioms YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction.exactCorrectedSlabVacuumBoundaryHaarCoefficient_eq_interior
#print axioms YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction.exactVacuumNontrivialHaarTermsVanish_of_fixedFaceOrthogonality
