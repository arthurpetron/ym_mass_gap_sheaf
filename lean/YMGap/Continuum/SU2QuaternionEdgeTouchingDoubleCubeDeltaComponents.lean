/-
# Exact Boolean delta components of the edge-touching double cube

The twenty-two bivalent Schur contractions impose forty-four crossed
equalities on the forty-eight face-corner tags.  This leaf proves, pointwise
in an arbitrary (and possibly short) Boolean list, that those constraints
have exactly sixteen consecutive three-tag components.

Twelve components carry a redundant third edge and are ordinary closed
triangles.  The four components meeting the omitted shared link carry two
edges each; their surviving Boolean values are precisely the four external
indices of the signed shared-link projector.  No Boolean assignment carrier
or depth-forty-eight sum is constructed, unfolded, simplified, or evaluated.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
Only fixed tag lists and the pointwise equality graph are reduced.
-/

import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction
import YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeDeltaComponents

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal crossed-edge graph -/

/-- The two crossed Boolean equalities supplied by one bivalent Schur row. -/
def TaggedDoubleCubeBivalentPair.crossedTagEqualityPairs
    (pair : TaggedDoubleCubeBivalentPair) : List (Nat × Nat) :=
  [(pair.forwardRowTag, pair.reverseColumnTag),
   (pair.forwardColumnTag, pair.reverseRowTag)]

/-- All forty-four bivalent equality edges in physical-link schedule order. -/
def radiusZeroEdgeTouchingDoubleCubeCrossedTagEqualityPairs :
    List (Nat × Nat) :=
  radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs.flatMap
    TaggedDoubleCubeBivalentPair.crossedTagEqualityPairs

theorem radiusZeroEdgeTouchingDoubleCubeCrossedTagEqualityPairs_exact :
    radiusZeroEdgeTouchingDoubleCubeCrossedTagEqualityPairs =
      [(1,0), (4,3), (0,2), (9,10), (9,11), (6,7),
       (5,3), (8,6), (2,1), (13,12), (14,12), (16,15),
       (4,5), (15,17), (13,14), (21,22), (11,10), (23,21),
       (16,17), (18,20), (8,7), (20,19),
       (24,26), (33,34), (33,35), (30,31), (29,27), (32,30),
       (26,25), (37,36), (38,36), (40,39), (28,29), (39,41),
       (37,38), (45,46), (35,34), (47,45), (47,46), (43,42),
       (40,41), (42,44), (32,31), (44,43)] := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeCrossedTagEqualityPairs_length :
    radiusZeroEdgeTouchingDoubleCubeCrossedTagEqualityPairs.length = 44 := by
  decide

/-! ## 2. The exact sixteen components -/

/-- The connected components of the crossed equality graph.  The tag
numbering makes them sixteen consecutive triples. -/
def radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples :
    List (List Nat) :=
  [[0,1,2], [3,4,5], [6,7,8], [9,10,11],
   [12,13,14], [15,16,17], [18,19,20], [21,22,23],
   [24,25,26], [27,28,29], [30,31,32], [33,34,35],
   [36,37,38], [39,40,41], [42,43,44], [45,46,47]]

/-- The twelve components not incident to the four-valent shared link. -/
def radiusZeroEdgeTouchingDoubleCubeOrdinaryDeltaComponentTagTriples :
    List (List Nat) :=
  [[0,1,2], [3,4,5], [6,7,8], [9,10,11],
   [12,13,14], [15,16,17],
   [30,31,32], [33,34,35], [36,37,38], [39,40,41],
   [42,43,44], [45,46,47]]

/-- The four path components whose surviving values enter the shared-link
projector. -/
def radiusZeroEdgeTouchingDoubleCubeSharedDeltaComponentTagTriples :
    List (List Nat) :=
  [[18,19,20], [21,22,23], [24,25,26], [27,28,29]]

theorem radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_length :
    radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples.length = 16 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_map_length :
    radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples.map List.length =
      List.replicate 16 3 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_flatten :
    radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples.flatten =
      List.range 48 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_flatten_nodup :
    radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples.flatten.Nodup := by
  rw [radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_flatten]
  decide

theorem radiusZeroEdgeTouchingDoubleCubeOrdinaryDeltaComponentTagTriples_length :
    radiusZeroEdgeTouchingDoubleCubeOrdinaryDeltaComponentTagTriples.length =
      12 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeSharedDeltaComponentTagTriples_length :
    radiusZeroEdgeTouchingDoubleCubeSharedDeltaComponentTagTriples.length =
      4 := by
  decide

/-! ## 3. Pointwise component and indicator certificates -/

/-- The double-cube and elementary-cube tag accessors are definitionally the
same total `List.getD` environment. -/
theorem doubleCubeTagValue_eq_cubeTagValue
    (assignment : List Bool) (tag : Nat) :
    doubleCubeTagValue assignment tag = cubeTagValue assignment tag := by
  rfl

/-- **Exact sixteen-component certificate.**  The conjunction of all
forty-four literal bivalent Schur equalities is equivalent to equality on
each of the sixteen consecutive tag triples.  The proof is pointwise in an
opaque list and therefore remains valid under the later symbolic sum. -/
theorem radiusZeroEdgeTouchingDoubleCubeContractionAllMatchBool_eq_components
    (assignment : List Bool) :
    contractionAllMatchBool
        (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment) =
      triangleAllMatchBool 16 assignment := by
  rw [Bool.eq_iff_iff]
  simp only [radiusZeroEdgeTouchingDoubleCubeBivalentSchedule,
    radiusZeroEdgeTouchingDoubleCubeTaggedBivalentPairs, List.map,
    TaggedDoubleCubeBivalentPair.contraction, contractionAllMatchBool,
    contractionMatchBool, triangleAllMatchBool,
    equalityTriangleMatchBool, doubleCubeTagValue_eq_cubeTagValue,
    cubeTagValue_drop, Bool.and_eq_true, decide_eq_true_eq,
    Nat.reduceAdd]
  constructor
  · intro h
    rcases h with
      ⟨⟨h10, h43⟩, ⟨h02, h910⟩, ⟨h911, h67⟩,
       ⟨h53, h86⟩, ⟨h21, h1312⟩, ⟨h1412, h1615⟩,
       ⟨h45, h1517⟩, ⟨h1314, h2122⟩, ⟨h1110, h2321⟩,
       ⟨h1617, h1820⟩, ⟨h87, h2019⟩,
       ⟨h2426, h3334⟩, ⟨h3335, h3031⟩, ⟨h2927, h3230⟩,
       ⟨h2625, h3736⟩, ⟨h3836, h4039⟩, ⟨h2829, h3941⟩,
       ⟨h3738, h4546⟩, ⟨h3534, h4745⟩, ⟨h4746, h4342⟩,
       ⟨h4041, h4244⟩, ⟨h3231, h4443⟩, _⟩
    simp_all
  · intro h
    rcases h with
      ⟨⟨h01, h12⟩, ⟨h34, h45⟩, ⟨h67, h78⟩,
       ⟨h910, h1011⟩, ⟨h1213, h1314⟩, ⟨h1516, h1617⟩,
       ⟨h1819, h1920⟩, ⟨h2122, h2223⟩,
       ⟨h2425, h2526⟩, ⟨h2728, h2829⟩,
       ⟨h3031, h3132⟩, ⟨h3334, h3435⟩,
       ⟨h3637, h3738⟩, ⟨h3940, h4041⟩,
       ⟨h4243, h4344⟩, ⟨h4546, h4647⟩, _⟩
    simp_all

/-- The literal tail-first product of twenty-two match indicators equals the
product of the sixteen component indicators. -/
theorem radiusZeroEdgeTouchingDoubleCubeContractionMatchProduct_eqv_components
    (assignment : List Bool) :
    contractionMatchProduct
        (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment) ≈
      triangleMatchProduct 16 assignment := by
  exact Q'.eqv_trans _ _ _
    (contractionMatchProduct_eqv_indicator
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (congrArg qBoolIndicator
        (radiusZeroEdgeTouchingDoubleCubeContractionAllMatchBool_eq_components
          assignment)))
      (Q'.eqv_symm
        (triangleMatchProduct_eqv_indicator 16 assignment)))

#print axioms radiusZeroEdgeTouchingDoubleCubeCrossedTagEqualityPairs_exact
#print axioms radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_flatten
#print axioms radiusZeroEdgeTouchingDoubleCubeDeltaComponentTagTriples_flatten_nodup
#print axioms radiusZeroEdgeTouchingDoubleCubeContractionAllMatchBool_eq_components
#print axioms radiusZeroEdgeTouchingDoubleCubeContractionMatchProduct_eqv_components

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeDeltaComponents
