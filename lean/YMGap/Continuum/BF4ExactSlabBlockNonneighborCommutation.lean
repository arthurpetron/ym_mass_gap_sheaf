/-
# Remote block conditionals commute on the original completion

If the S collar contains no T link, the actual S update preserves T
independence. Polynomial inverse approximants retain that independence;
their explicit Cauchy limits therefore lie in the fixed space of Q_T.
Self-adjointness promotes range invariance to exact full-space commutation.

Only one collar-separation premise is needed. Empty/repeated lists and
overlap on links with no incident action factor need no separate exclusion.
Every original action factor is retained. This removes remote commutators,
not interacting-block angle estimates, schedule-degree bounds, physical
scaling, reflected OS reconstruction or the Clay mass-gap frontier.
-/

import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.BF4ExactSlabBlockTower
import YMGap.Continuum.GNSDenseFixedPoint
import YMGap.Continuum.GNSProjectionCommutation

namespace YMGap.Continuum.BF4ExactSlabBlockNonneighborCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The literal S-collar weight has no dependence on a separated T slot. -/
theorem collarHeat_independent_of_separated (w : Q') (K extent : Nat)
    (S T : List Z4Link)
    (hT : ∀ link, link ∈ T → link ∈ boundaryCompleteSlabLinks extent)
    (hST : LinksDisjoint T (faceLinks extent (collar extent S)))
    (i : Nat) (hi : i ∈ slots extent T) :
    QuaternionBlockIndependent i (collarHeat w K extent S) := by
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hi
  exact independent_of_local (heatProduct_local w K extent (collar extent S))
    (List.idxOf_lt_length_of_mem (hT link hlink)) (by
      intro hm
      rw [correctedSlabLinkAt_idxOf (hT link hlink)] at hm
      exact hST link hlink hm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

/-- Inverse iteration preserves ANY coordinate omitted by its two inputs,
not only a coordinate in the selected integration list. -/
theorem approximateInverse_preserves_independent (S : List Z4Link)
    (r : (backgroundData hw0 hw1 K extent hK S).V) (i : Nat)
    (hD : QuaternionBlockIndependent i (normalizer w K extent S))
    (hr : QuaternionBlockIndependent i r.val) :
    ∀ n, QuaternionBlockIndependent i
      (approximateInverse hw0 hw1 K extent hK S r n).val
  | 0 => quaternionBlockIndependent_polySmul 0 (quaternionBlockIndependent_polyOne i)
  | n+1 =>
      quaternionBlockIndependent_polyAdd
        (approximateInverse_preserves_independent S r i hD hr n)
        (quaternionBlockIndependent_polySmul _
          (quaternionBlockIndependent_polyAdd hr
            (quaternionBlockIndependent_polySmul (-1)
              (quaternionBlockIndependent_polyMul
                (approximateInverse_preserves_independent S r i hD hr n) hD))))

variable (S T : List Z4Link)
  (hS : ∀ link, link ∈ S → link ∈ boundaryCompleteSlabLinks extent)
  (hT : ∀ link, link ∈ T → link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "CS" => conditionalProjection hw0 hw1 K extent hK S hS
local notation "CT" => conditionalProjection hw0 hw1 K extent hK T hT

include hT in
/-- The supplied ORIGINAL Cauchy representative preserves separated slots. -/
theorem conditionalRep_preserves_independent
    (hST : LinksDisjoint T (faceLinks extent (collar extent S)))
    (p : (F).V)
    (hp : ∀ i, i ∈ slots extent T → QuaternionBlockIndependent i p.val)
    (n i : Nat) (hi : i ∈ slots extent T) :
    QuaternionBlockIndependent i
      ((conditionalRep hw0 hw1 K extent hK S hS p).seq n).val := by
  have hc := collarHeat_independent_of_separated w K extent S T hT hST i hi
  exact approximateInverse_preserves_independent hw0 hw1 K extent hK S
    (numeratorVector hw0 hw1 K extent hK S p.val p.property) i
    (familyProject_preserves_independent _ hc)
    (familyProject_preserves_independent _
      (quaternionBlockIndependent_polyMul (hp i hi) hc)) n

/-- A T-exterior polynomial stays in the fixed space of the ACTUAL T map. -/
theorem conditionalProjection_preserves_exterior
    (hST : LinksDisjoint T (faceLinks extent (collar extent S)))
    (p : (F).V)
    (hp : ∀ i, i ∈ slots extent T → QuaternionBlockIndependent i p.val) :
    CT (CS (embedV F p)) = CS (embedV F p) := by
  rw [conditionalProjection_embed]
  exact GNSDenseFixedPoint.fixed_of_cauchy_terms CT
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK T hT)
    (conditionalRep hw0 hw1 K extent hK S hS p)
    (fun n => conditionalProjection_fix_exterior_polynomial hw0 hw1 K extent hK T hT _
      (conditionalRep_preserves_independent hw0 hw1 K extent hK S T hS hT hST p hp n))

theorem conditionalProjection_invariant_dense
    (hST : LinksDisjoint T (faceLinks extent (collar extent S))) (p : (F).V) :
    CT (CS (CT (embedV F p))) = CS (CT (embedV F p)) := by
  let X := conditionalRep hw0 hw1 K extent hK T hT p
  have hfix := GNSDenseFixedPoint.fixed_of_cauchy_images CT CS
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK T hT)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK S hS) X
    (fun n => conditionalProjection_preserves_exterior hw0 hw1 K extent hK S T hS hT
      hST (X.seq n) (fun i hi =>
        conditionalApproximation_independent hw0 hw1 K extent hK T p.val p.property n i hi))
  have he : Quotient.mk (cauchySetoid F) X = CT (embedV F p) :=
    (conditionalProjection_embed hw0 hw1 K extent hK T hT p).symm
  rw [he] at hfix
  exact hfix

theorem conditionalProjection_invariant
    (hST : LinksDisjoint T (faceLinks extent (collar extent S))) (x : GNSCompletionSpace F) :
    CT (CS (CT x)) = CS (CT x) :=
  GNSDenseFixedPoint.invariant_range_of_dense CT CS
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK T hT)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK S hS)
    (conditionalProjection_invariant_dense hw0 hw1 K extent hK S T hS hT hST) x

/-- Exact commutation on EVERY original completed vector, at all rational
0<w<1 and every late heat cutoff. No strict quantitative bound is asserted. -/
theorem conditionalProjection_commute
    (hST : LinksDisjoint T (faceLinks extent (collar extent S))) (x : GNSCompletionSpace F) :
    CS (CT x) = CT (CS x) :=
  GNSProjectionCommutation.commute_of_invariant F CS CT
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK S hS)
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK T hT)
    (conditionalProjection_invariant hw0 hw1 K extent hK S T hS hT hST) x

/-- Remote residual terms may be dropped from a lower energy estimate
because they are nonnegative, NOT because they vanish. -/
theorem remote_residual_pair_nonnegative
    (hST : LinksDisjoint T (faceLinks extent (collar extent S))) (x : GNSCompletionSpace F) :
    CReal.RCle CReal.RCzero
      ((F).cinnerCompl ((F).cSub x (CS x)) ((F).cSub x (CT x))) :=
  (BF4ExactSlabBlockTower.blockFamily hw0 hw1 K extent hK).commuting_residual_pairing_nonnegative
    ⟨S, hS⟩ ⟨T, hT⟩
    (conditionalProjection_commute hw0 hw1 K extent hK S T hS hT hST) x

#print axioms collarHeat_independent_of_separated
#print axioms approximateInverse_preserves_independent
#print axioms conditionalRep_preserves_independent
#print axioms conditionalProjection_preserves_exterior
#print axioms conditionalProjection_invariant_dense
#print axioms conditionalProjection_invariant
#print axioms conditionalProjection_commute
#print axioms remote_residual_pair_nonnegative

end YMGap.Continuum.BF4ExactSlabBlockNonneighborCommutation
