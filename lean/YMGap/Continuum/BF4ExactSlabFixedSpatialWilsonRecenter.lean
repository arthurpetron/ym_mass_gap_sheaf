/-
# Spatial recentering of original closed Wilson words and signed windows

A common nonnegative spatial shift changes all three spatial coordinates,
retaining time offsets, orientations, loop ordering, spins and coefficients.
The explicit width+shift room bound includes the source carrier's fringe
links, whose base coordinates may equal the source width.

The literal slab Placement then transports the entire placed expression,
with its time shift, by a coefficient-sensitive prefix equality. This is
the observable input to the existing filtered selected-action comparison;
no equality with the full larger interacting action is asserted.
-/

import YMGap.Continuum.BF4ExactSlabTranslatedWilsonWord
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def translateEntry (space : Nat) (e : OrientedBF4Link) : OrientedBF4Link :=
  ⟨shiftLink space 0 e.link, e.reverse⟩

private theorem translateEntry_start (space : Nat) (e : OrientedBF4Link) :
    entryStart (translateEntry space e) = shiftVertex space 0 (entryStart e) := by
  cases h : e.reverse <;>
    simp [entryStart, translateEntry, shiftLink, h, shiftVertex_addE]

private theorem translateEntry_finish (space : Nat) (e : OrientedBF4Link) :
    entryFinish (translateEntry space e) = shiftVertex space 0 (entryFinish e) := by
  cases h : e.reverse <;>
    simp [entryFinish, translateEntry, shiftLink, h, shiftVertex_addE]

private theorem pathFinish_translate (space : Nat) :
    ∀ (start : Z4Vertex) (edges : List OrientedBF4Link),
    pathFinish (shiftVertex space 0 start) (edges.map (translateEntry space)) =
      shiftVertex space 0 (pathFinish start edges)
  | _, [] => rfl
  | _, e :: es => by
      simpa only [List.map_cons, pathFinish, translateEntry_finish] using
        pathFinish_translate space (entryFinish e) es

private theorem compatible_translate (space : Nat) :
    ∀ (start : Z4Vertex) (edges : List OrientedBF4Link), Compatible start edges →
    Compatible (shiftVertex space 0 start) (edges.map (translateEntry space))
  | _, [], _ => True.intro
  | start, e :: es, h => by
      refine ⟨(translateEntry_start space e).trans (congrArg (shiftVertex space 0) h.1), ?_⟩
      simpa only [translateEntry_finish] using compatible_translate space (entryFinish e) es h.2

theorem baseLink_translate {width targetWidth space : Nat}
    (hroom : width+space ≤ targetWidth) {link : Z4Link} (hp : link ∈ baseLinks width) :
    shiftLink space 0 link ∈ baseLinks targetWidth := by
  have hs := (baseLinks_mem_iff width link).mp hp
  rcases link with ⟨⟨x,y,z,t⟩,dir⟩
  change dir ≠ .x3 ∧ x ≤ width ∧ y ≤ width ∧ z ≤ width ∧ t=0 at hs
  apply (baseLinks_mem_iff targetWidth _).mpr
  change dir ≠ .x3 ∧ x+space ≤ targetWidth ∧ y+space ≤ targetWidth ∧
    z+space ≤ targetWidth ∧ t+0=0
  exact ⟨hs.1, by omega, by omega, by omega, by simpa only [Nat.add_zero] using hs.2.2.2.2⟩

/-- The same closed physical loop with a computed larger source-box guard. -/
def recenterLoop {width targetWidth space : Nat} (hroom : width+space ≤ targetWidth)
    (loop : SourceLoop width) : SourceLoop targetWidth where
  start := shiftVertex space 0 loop.start
  edges := loop.edges.map (translateEntry space)
  compatible := compatible_translate space loop.start loop.edges loop.compatible
  closed := (pathFinish_translate space loop.start loop.edges).trans
    (congrArg (shiftVertex space 0) loop.closed)
  physical := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact baseLink_translate hroom (loop.physical f hf)

def recenterExpression {width targetWidth space : Nat} (hroom : width+space ≤ targetWidth) :
    WindowExpression width → WindowExpression targetWidth
  | .one => .one
  | .loop offset value spin => .loop offset (recenterLoop hroom value) spin
  | .add e f => .add (recenterExpression hroom e) (recenterExpression hroom f)
  | .mul e f => .mul (recenterExpression hroom e) (recenterExpression hroom f)
  | .smul c e => .smul c (recenterExpression hroom e)

theorem recenter_within {width targetWidth space : Nat} (hroom : width+space ≤ targetWidth)
    (L : Nat) : ∀ e : WindowExpression width,
    Within L (recenterExpression hroom e) ↔ Within L e
  | .one => Iff.rfl
  | .loop _ _ _ => Iff.rfl
  | .add e f => and_congr (recenter_within hroom L e) (recenter_within hroom L f)
  | .mul e f => and_congr (recenter_within hroom L e) (recenter_within hroom L f)
  | .smul _ e => recenter_within hroom L e

theorem recenter_mapOffsets {width targetWidth space : Nat} (hroom : width+space ≤ targetWidth)
    (f : Nat → Nat) (e : WindowExpression width) :
    recenterExpression hroom (mapOffsets f e) = mapOffsets f (recenterExpression hroom e) := by
  induction e <;> simp_all only [recenterExpression, mapOffsets]

private theorem loop_ext {width : Nat} (p q : SourceLoop width)
    (hs : p.start=q.start) (he : p.edges=q.edges) : p=q := by
  cases p
  cases q
  cases hs
  cases he
  rfl

theorem recenterLoop_comp {width middle targetWidth first second : Nat}
    (hfirst : width+first ≤ middle) (hsecond : middle+second ≤ targetWidth)
    (loop : SourceLoop width) :
    recenterLoop hsecond (recenterLoop hfirst loop) =
      recenterLoop (space := first+second) (by omega : width+(first+second) ≤ targetWidth) loop := by
  apply loop_ext
  · change shiftVertex second 0 (shiftVertex first 0 loop.start) =
      shiftVertex (first+second) 0 loop.start
    rcases loop.start with ⟨x,y,z,t⟩
    simp only [shiftVertex, Nat.add_assoc, Nat.add_zero]
  · simp only [recenterLoop, List.map_map]
    apply List.map_congr_left
    intro e _
    rcases e with ⟨⟨⟨x,y,z,t⟩,dir⟩,reverse⟩
    simp only [Function.comp_def, translateEntry, shiftLink, shiftVertex, Nat.add_assoc, Nat.add_zero]

theorem recenterExpression_comp {width middle targetWidth first second : Nat}
    (hfirst : width+first ≤ middle) (hsecond : middle+second ≤ targetWidth)
    (e : WindowExpression width) :
    recenterExpression hsecond (recenterExpression hfirst e) =
      recenterExpression (space := first+second)
        (by omega : width+(first+second) ≤ targetWidth) e := by
  induction e <;> simp_all only [recenterExpression, recenterLoop_comp]

private theorem translated_shiftEntry (P : Placement) (time : Nat) (e : OrientedBF4Link) :
    P.shiftOriented (shiftEntry time e) = shiftEntry (time+P.time) (translateEntry P.space e) := by
  rcases e with ⟨⟨⟨x,y,z,t⟩,dir⟩,reverse⟩
  simp only [Placement.shiftOriented, shiftEntry, translateEntry, shiftLink, shiftVertex,
    timeShiftLink, timeShiftVertex, Nat.add_zero, Nat.add_assoc]

/-- Literal placement of one recentered loop, including the actual ambient time shift. -/
theorem placed_loop_pin (P : Placement) {width targetWidth time : Nat}
    (hroom : width+P.space ≤ targetWidth) (hw : width ≤ P.source) (ht : time ≤ P.source)
    (loop : SourceLoop width) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (B P.target)
      (P.embedding.polynomial (character P.source (loop.edges.map (shiftEntry time)) spin))
      (character P.target ((recenterLoop hroom loop).edges.map (shiftEntry (time+P.time))) spin) := by
  let placed := placeLoop hw ht loop
  have h := BF4ExactSlabTranslatedWilsonWord.character_pin P placed.edges placed.physical spin
  have he : (loop.edges.map (shiftEntry time)).map P.shiftOriented =
      (recenterLoop hroom loop).edges.map (shiftEntry (time+P.time)) := by
    simp only [recenterLoop, List.map_map]
    apply List.map_congr_left
    intro e _
    exact translated_shiftEntry P time e
  change QuaternionPrefixPolynomialEqv (B P.target)
    (P.embedding.polynomial (character P.source (loop.edges.map (shiftEntry time)) spin))
    (character P.target ((loop.edges.map (shiftEntry time)).map P.shiftOriented) spin) at h
  rw [he] at h
  exact h

/-- Whole signed expression under the SAME physical slab embedding. -/
theorem placed_pin (P : Placement) {width targetWidth start L : Nat}
    (hroom : width+P.space ≤ targetWidth) (hw : width ≤ P.source)
    (ht : start+L ≤ P.source) : ∀ e : WindowExpression width, Within L e →
    QuaternionPrefixPolynomialEqv (B P.target)
      (P.embedding.polynomial (placedPolynomial P.source start e))
      (placedPolynomial P.target (start+P.time) (recenterExpression hroom e))
  | .one, _ => P.embedding.polynomial_one_prefix
  | .loop offset value spin, he => by
      have htime : start+offset ≤ P.source := by have ho : offset ≤ L := he; omega
      have h := placed_loop_pin P hroom hw htime value spin
      have ht' : start+offset+P.time = start+P.time+offset := by omega
      rw [ht'] at h
      exact h
  | .add e f, he => by
      change QuaternionPrefixPolynomialEqv (B P.target)
        (P.embedding.polynomial (polyAdd _ _)) (polyAdd _ _)
      rw [BlockEmbedding.polynomial_add]
      exact (placed_pin P hroom hw ht e he.1).append (placed_pin P hroom hw ht f he.2)
  | .mul e f, he => by
      change QuaternionPrefixPolynomialEqv (B P.target)
        (P.embedding.polynomial (polyMul _ _)) (polyMul _ _)
      rw [BlockEmbedding.polynomial_mul]
      exact (placed_pin P hroom hw ht e he.1).mul (placed_pin P hroom hw ht f he.2)
  | .smul c e, he => by
      change QuaternionPrefixPolynomialEqv (B P.target)
        (P.embedding.polynomial (polySmul c _)) (polySmul c _)
      rw [BlockEmbedding.polynomial_smul]
      exact (placed_pin P hroom hw ht e he).smul c

#print axioms translateEntry
#print axioms baseLink_translate
#print axioms recenterLoop
#print axioms recenterExpression
#print axioms recenter_within
#print axioms recenter_mapOffsets
#print axioms recenterLoop_comp
#print axioms recenterExpression_comp
#print axioms placed_loop_pin
#print axioms placed_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
