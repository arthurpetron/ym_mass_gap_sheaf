/-
# A fixed-carrier spatial Wilson loop and its literal slab placement

The source is an endpoint-compatible closed word in the width-only spatial
link carrier. Its ordered quaternion product, and every character of that
product, are independent of ambient extent and placement time. The existing
slice embedding sends them to the actual shifted original-link word, with
only the coefficient-sensitive zero padding of that embedding.

The placement supplies the physical same-slice loop consumed by the common
temporal-ledger invariance theorem. This proves neither an embedding into the
face-generated spatial union nor coverage of all supported observables, and
does not change any cutoff, thermodynamic, or continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (link orientedLink)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "N" width => List.length (baseLinks width)
local notation "B" extent => List.length (boundaryCompleteSlabLinks extent)

/-- A concrete closed oriented word; all links use the SAME width-only carrier. -/
structure SourceLoop (width : Nat) where
  start : Z4Vertex
  edges : List OrientedBF4Link
  compatible : Compatible start edges
  closed : pathFinish start edges = start
  physical : ∀ e, e ∈ edges → e.link ∈ baseLinks width

/-- Time placement changes endpoints but never the traversal orientation. -/
def shiftEntry (time : Nat) (e : OrientedBF4Link) : OrientedBF4Link :=
  ⟨timeShiftLink time e.link, e.reverse⟩

theorem shiftEntry_start (time : Nat) (e : OrientedBF4Link) :
    entryStart (shiftEntry time e) = timeShiftVertex time (entryStart e) := by
  cases h : e.reverse <;>
    simp [entryStart, shiftEntry, timeShiftLink, h, timeShiftVertex_addE]

theorem shiftEntry_finish (time : Nat) (e : OrientedBF4Link) :
    entryFinish (shiftEntry time e) = timeShiftVertex time (entryFinish e) := by
  cases h : e.reverse <;>
    simp [entryFinish, shiftEntry, timeShiftLink, h, timeShiftVertex_addE]

theorem pathFinish_shift (time : Nat) : ∀ (start : Z4Vertex) (edges : List OrientedBF4Link),
    pathFinish (timeShiftVertex time start) (edges.map (shiftEntry time)) =
      timeShiftVertex time (pathFinish start edges)
  | _, [] => rfl
  | _, e :: es => by
      simpa only [List.map_cons, pathFinish, shiftEntry_finish] using
        pathFinish_shift time (entryFinish e) es

theorem compatible_shift (time : Nat) :
    ∀ (start : Z4Vertex) (edges : List OrientedBF4Link), Compatible start edges →
      Compatible (timeShiftVertex time start) (edges.map (shiftEntry time))
  | _, [], _ => True.intro
  | start, e :: es, h => by
      refine ⟨(shiftEntry_start time e).trans (congrArg (timeShiftVertex time) h.1), ?_⟩
      simpa only [shiftEntry_finish] using compatible_shift time (entryFinish e) es h.2

/-- Explicit physical placement, with both room guards retained in its type. -/
def placeLoop {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    (loop : SourceLoop width) : SpatialLoop extent time where
  start := timeShiftVertex time loop.start
  edges := loop.edges.map (shiftEntry time)
  compatible := compatible_shift time loop.start loop.edges loop.compatible
  closed := (pathFinish_shift time loop.start loop.edges).trans
    (congrArg (timeShiftVertex time) loop.closed)
  physical := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact sliceLinks_physical hw ht (List.mem_map.mpr ⟨f.link, loop.physical f hf, rfl⟩)
  spatial := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    have hs := (sliceLinks_mem_iff width time (timeShiftLink time f.link)).mp
      (List.mem_map.mpr ⟨f.link, loop.physical f hf, rfl⟩)
    exact ⟨hs.1, hs.2.2.2.2⟩

/-- Right-associated ordered product, exactly as in the actual slab word. -/
def sourceWord (width : Nat) (edges : List OrientedBF4Link) : PolyQuaternion :=
  wordWith (orientedLink width) edges

def sourceCharacter (width : Nat) (edges : List OrientedBF4Link) (spin : Nat) : RatPoly :=
  characterPolynomial (sourceWord width edges).scalar spin

private theorem support_one (blocks : Nat) : QuaternionSupported blocks PolyQuaternion.one :=
  ⟨supported_one blocks, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem source_link_supported (width : Nat) (l : Z4Link) :
    QuaternionSupported (N width) (link width l) := by
  unfold link
  split
  · exact QuaternionSupported.coordinate (List.idxOf_lt_length_of_mem ‹_›)
  · exact support_one _

private theorem source_oriented_supported (width : Nat) (e : OrientedBF4Link) :
    QuaternionSupported (N width) (orientedLink width e) := by
  unfold orientedLink
  split
  · exact (source_link_supported width e.link).conj
  · exact source_link_supported width e.link

theorem sourceWord_supported (width : Nat) : ∀ edges : List OrientedBF4Link,
    QuaternionSupported (N width) (sourceWord width edges)
  | [] => support_one _
  | e :: es => (source_oriented_supported width e).mul (sourceWord_supported width es)

theorem sourceCharacter_supported (width : Nat) (edges : List OrientedBF4Link) (spin : Nat) :
    SupportedQuaternionBlocks (N width) (sourceCharacter width edges spin) :=
  SU2QuaternionRelativeHeatPairGeometry.character_supported (sourceWord_supported width edges).scalar spin

/-- The exact original oriented link, with no commuting or trace-factorization step. -/
theorem oriented_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    {e : OrientedBF4Link} (he : e.link ∈ baseLinks width) :
    QuaternionPrefixPolyQuaternionEqv (B extent)
      ((embedding hw ht).quaternion (orientedLink width e))
      (orientedCorrectedSlabLinkPolynomial extent (shiftEntry time e)) := by
  unfold orientedLink orientedCorrectedSlabLinkPolynomial shiftEntry
  simp only [link, if_pos he]
  cases h : e.reverse
  · exact link_pin hw ht he
  · simp only [ite_true]
    rw [BlockEmbedding.quaternion_conj]
    exact (link_pin hw ht he).conj

/-- Every source edge and its multiplication order survive the slice embedding. -/
theorem sourceWord_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent) :
    ∀ edges : List OrientedBF4Link, (∀ e, e ∈ edges → e.link ∈ baseLinks width) →
    QuaternionPrefixPolyQuaternionEqv (B extent)
      ((embedding hw ht).quaternion (sourceWord width edges))
      (word extent (edges.map (shiftEntry time)))
  | [], _ => (embedding hw ht).quaternion_one
  | e :: es, he => by
      change QuaternionPrefixPolyQuaternionEqv (B extent)
        ((embedding hw ht).quaternion
          (PolyQuaternion.mul (orientedLink width e) (sourceWord width es)))
        (PolyQuaternion.mul (orientedCorrectedSlabLinkPolynomial extent (shiftEntry time e))
          (word extent (es.map (shiftEntry time))))
      rw [BlockEmbedding.quaternion_mul]
      exact (oriented_pin hw ht (he e List.mem_cons_self)).mul
        (sourceWord_pin hw ht es (fun f hf => he f (List.mem_cons_of_mem e hf)))

/-- Arbitrary spin on the SAME ordered word, as a coefficient-sensitive prefix identity. -/
theorem sourceCharacter_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    (edges : List OrientedBF4Link) (he : ∀ e, e ∈ edges → e.link ∈ baseLinks width) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (sourceCharacter width edges spin))
      (character extent (edges.map (shiftEntry time)) spin) :=
  (embedding hw ht).character_of_quaternion (sourceWord_pin hw ht edges he) spin

/-- Direct physical-loop form consumed by original-action invariant pairing. -/
theorem character_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    (loop : SourceLoop width) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (sourceCharacter width loop.edges spin))
      (character extent (placeLoop hw ht loop).edges spin) :=
  sourceCharacter_pin hw ht loop.edges loop.physical spin

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.SourceLoop
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.shiftEntry
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.shiftEntry_start
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.shiftEntry_finish
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.pathFinish_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.compatible_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.placeLoop
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.sourceWord
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.sourceCharacter
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.sourceWord_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.sourceCharacter_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.oriented_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.sourceWord_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.sourceCharacter_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe.character_pin
