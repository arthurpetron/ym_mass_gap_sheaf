/-
# SAME-slab spatial head swap of arbitrary ordered Wilson loops

The concrete x0/x1 swap preserves each traversal's reverse flag and the
order of all edges. Endpoint compatibility and closedness are transported
on the actual lattice, and a source loop stays on the SAME base-link list.
The polynomial word pin uses the literal slab block involution and common
padding. No plaquette-only reduction or quaternion commutation is used.

This is a finite original-observable input, not a continuum rotation,
width-changing map, completed isometry or physical gap assertion.
-/

import YMGap.Continuum.BF4ExactSlabSpatialHeadSwapHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe

namespace YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapGeometry
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapHaar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation "B" extent => List.length (boundaryCompleteSlabLinks extent)

/-- An edge keeps its traversal orientation; only its actual link is swapped. -/
def swapEntry (e : OrientedBF4Link) : OrientedBF4Link :=
  ⟨swapLink e.link, e.reverse⟩

theorem swapEntry_involutive (e : OrientedBF4Link) :
    swapEntry (swapEntry e) = e := by
  cases e with
  | mk link reverse =>
      change OrientedBF4Link.mk (swapLink (swapLink link)) reverse =
        OrientedBF4Link.mk link reverse
      rw [swapLink_involutive]

theorem swapEntry_start (e : OrientedBF4Link) :
    entryStart (swapEntry e) = swapVertex (entryStart e) := by
  cases h : e.reverse <;>
    simp [entryStart, swapEntry, swapLink, h, swapVertex_addE]

theorem swapEntry_finish (e : OrientedBF4Link) :
    entryFinish (swapEntry e) = swapVertex (entryFinish e) := by
  cases h : e.reverse <;>
    simp [entryFinish, swapEntry, swapLink, h, swapVertex_addE]

theorem pathFinish_swap : ∀ (start : Z4Vertex) (edges : List OrientedBF4Link),
    pathFinish (swapVertex start) (edges.map swapEntry) =
      swapVertex (pathFinish start edges)
  | _, [] => rfl
  | _, e :: es => by
      simpa only [List.map_cons, pathFinish, swapEntry_finish] using
        pathFinish_swap (entryFinish e) es

theorem compatible_swap :
    ∀ (start : Z4Vertex) (edges : List OrientedBF4Link), Compatible start edges →
      Compatible (swapVertex start) (edges.map swapEntry)
  | _, [], _ => True.intro
  | start, e :: es, h => by
      refine ⟨(swapEntry_start e).trans (congrArg swapVertex h.1), ?_⟩
      simpa only [swapEntry_finish] using compatible_swap (entryFinish e) es h.2

/-- An actual source loop, with its original fixed-width membership retained. -/
def swapSourceLoop {width : Nat} (loop : SourceLoop width) : SourceLoop width where
  start := swapVertex loop.start
  edges := loop.edges.map swapEntry
  compatible := compatible_swap loop.start loop.edges loop.compatible
  closed := (pathFinish_swap loop.start loop.edges).trans
    (congrArg swapVertex loop.closed)
  physical := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact (swapLink_baseLinks_mem_iff width f.link).mpr (loop.physical f hf)

theorem swapSourceLoop_edges {width : Nat} (loop : SourceLoop width) :
    (swapSourceLoop loop).edges = loop.edges.map swapEntry := rfl

/-- Spatial swap and time placement commute without changing a reverse flag. -/
theorem swapEntry_shift_commute (time : Nat) (e : OrientedBF4Link) :
    swapEntry (shiftEntry time e) = shiftEntry time (swapEntry e) := by
  cases e with
  | mk link reverse =>
      change OrientedBF4Link.mk (swapLink (timeShiftLink time link)) reverse =
        OrientedBF4Link.mk (timeShiftLink time (swapLink link)) reverse
      rw [swapLink_timeShift_commute]

theorem oriented_swap (extent : Nat) (e : OrientedBF4Link) :
    PaddedQuaternionCoeffEqv (B extent)
      (swapQuaternion extent (orientedCorrectedSlabLinkPolynomial extent e))
      (orientedCorrectedSlabLinkPolynomial extent (swapEntry e)) := by
  unfold orientedCorrectedSlabLinkPolynomial swapEntry
  cases h : e.reverse
  · simp only [h, Bool.false_eq_true, if_false]
    exact link_swap extent e.link
  · simp only [h, if_true]
    unfold swapQuaternion
    rw [reindexPolyQuaternion_conj]
    exact (link_swap extent e.link).conj

/-- Arbitrary ordered original words, including the empty word and all inverse
flags. No physical guard is needed here: the checked link pin also covers
the original identity fallback outside the slab list. -/
theorem word_swap (extent : Nat) : ∀ edges : List OrientedBF4Link,
    PaddedQuaternionCoeffEqv (B extent)
      (swapQuaternion extent (word extent edges))
      (word extent (edges.map swapEntry))
  | [] => .of_prefix (reindex_polyQuaternionOne_prefix (swapQuaternionBlockInvolution extent))
  | e :: es => by
      change PaddedQuaternionCoeffEqv (B extent)
        (swapQuaternion extent (PolyQuaternion.mul
          (orientedCorrectedSlabLinkPolynomial extent e) (word extent es)))
        (PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial extent (swapEntry e))
          (word extent (es.map swapEntry)))
      unfold swapQuaternion
      rw [reindexPolyQuaternion_mul]
      exact (oriented_swap extent e).mul (word_swap extent es)

theorem word_scalar_swap (extent : Nat) (edges : List OrientedBF4Link) :
    PaddedPolynomialCoeffEqv (B extent)
      (swapPolynomial extent (word extent edges).scalar)
      (word extent (edges.map swapEntry)).scalar := by
  simpa only [PaddedPolynomialCoeffEqv, swapPolynomial, swapQuaternion,
    reindexPolyQuaternion] using (word_swap extent edges).scalar

/-- Every spin on the SAME ordered original loop, with padding retained. -/
theorem character_swap (extent : Nat) (edges : List OrientedBF4Link) (spin : Nat) :
    PaddedPolynomialCoeffEqv (B extent)
      (swapPolynomial extent (character extent edges spin))
      (character extent (edges.map swapEntry) spin) :=
  (PaddedPolynomialCoeffEqv.of_prefix
    (reindexQuaternionPolynomial_character_prefix (swapQuaternionBlockInvolution extent)
      (word extent edges).scalar spin)).trans
    ((word_scalar_swap extent edges).character spin)

end YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop

#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry_start
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry_finish
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.pathFinish_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.compatible_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapSourceLoop
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapSourceLoop_edges
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry_shift_commute
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.oriented_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.word_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.word_scalar_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop.character_swap
