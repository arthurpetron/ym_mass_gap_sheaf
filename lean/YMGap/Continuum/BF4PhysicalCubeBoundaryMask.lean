/-
# Exact Boolean production multiplicities on the cube carrier

For an arbitrary bounded cube state and arbitrary bounded interface boundary,
the lower link product is exactly twelve SU(2) triangle tests times twelve
boundary-zero tests. After those zero tests hold, the fixed link product is
exactly the eight corner triangle tests. These are production identities,
not upper estimates and not restrictions to the chosen difference boundary.
The formulas do not depend on the representation cutoff once labels fit it.
-/

import YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel

namespace YMGap.Continuum.BF4PhysicalCubeBoundaryMask

set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalHalfCubeSupport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

def cubeInactiveBoundaryIds : List Nat := [14, 22, 31, 32, 38, 47, 50, 56, 58, 65, 67, 68]

def cubeFullLowerActive : List Nat := centralLowerCubeFaceIds ++ centralFixedFaceIds 0

def cubeBoundaryZeroB (boundary : EdgeLabelling) : Bool :=
  cubeInactiveBoundaryIds.all (fun face => decide (boundary face = 0))

def cubeEdgeAdmissibleB (state boundary : EdgeLabelling) : Bool :=
  cubeDifferenceEdges.all (fun e => fusionOK (state e.1) (state e.2.1) (boundary e.2.2))

def cubeCornerAdmissibleB (boundary : EdgeLabelling) : Bool :=
  cubeDifferenceCorners.all (fun c => fusionOK (boundary c.1) (boundary c.2.1) (boundary c.2.2))

private def eraseWord (word : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | head :: tail => if word = head then tail else head :: eraseWord word tail

private theorem eraseWord_perm (word : List Nat) : ∀ words : List (List Nat),
    word ∈ words → (word :: eraseWord word words).Perm words
  | [], h => False.elim (List.not_mem_nil h)
  | head :: tail, h => by
      by_cases heq : word = head
      · subst word
        simp only [eraseWord]
        exact List.Perm.refl _
      · simp only [eraseWord, if_neg heq]
        have ht := (List.mem_cons.mp h).resolve_left heq
        exact (List.Perm.swap head word _).trans (List.Perm.cons head (eraseWord_perm word tail ht))

private def wordPermB : List (List Nat) → List (List Nat) → Bool
  | [], right => right.isEmpty
  | head :: tail, right => decide (head ∈ right) && wordPermB tail (eraseWord head right)

private theorem wordPermB_sound : ∀ left right : List (List Nat),
    wordPermB left right = true → left.Perm right
  | [], [], _ => List.Perm.nil
  | [], _ :: _, h => by cases h
  | head :: tail, right, h => by
      have hp : decide (head ∈ right) = true ∧ wordPermB tail (eraseWord head right) = true := by
        simpa only [wordPermB, Bool.and_eq_true] using h
      exact (List.Perm.cons head (wordPermB_sound tail _ hp.2)).trans
        (eraseWord_perm head right (of_decide_eq_true hp.1))

/-- Exact multiplicities of the geometric word catalog: twelve edge triples,
twelve inactive-boundary singletons, and twenty-four empty words. -/
theorem lower_word_product (value : List Nat → Nat) :
    natListProduct value ((centralLowerLinks 0).map (activeIncidentWord cubeFullLowerActive)) =
      natListProduct value ((cubeDifferenceEdges.map tripleFaces) ++
        (cubeInactiveBoundaryIds.map (fun face => [face])) ++ List.replicate 24 []) := by
  have hcheck : wordPermB ((centralLowerLinks 0).map (activeIncidentWord cubeFullLowerActive))
      ((cubeDifferenceEdges.map tripleFaces) ++
        (cubeInactiveBoundaryIds.map (fun face => [face])) ++ List.replicate 24 []) = true := by decide +kernel
  exact natListProduct_perm value (wordPermB_sound _ _ hcheck)

theorem fixed_word_product (value : List Nat → Nat) :
    natListProduct value ((centralFixedLinks 0).map (activeIncidentWord cubeDifferenceBoundaryIds)) =
      natListProduct value ((cubeDifferenceCorners.map tripleFaces) ++ List.replicate 12 []) := by
  have hcheck : wordPermB ((centralFixedLinks 0).map (activeIncidentWord cubeDifferenceBoundaryIds))
      ((cubeDifferenceCorners.map tripleFaces) ++ List.replicate 12 []) = true := by decide +kernel
  exact natListProduct_perm value (wordPermB_sound _ _ hcheck)

theorem inactive_faces_fixed {face : Nat} (hf : face ∈ cubeInactiveBoundaryIds) :
    face ∈ centralFixedFaceIds 0 := by
  simp only [cubeInactiveBoundaryIds, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem fixed_faces_active_or_inactive {face : Nat} (hf : face ∈ centralFixedFaceIds 0) :
    face ∈ cubeDifferenceBoundaryIds ∨ face ∈ cubeInactiveBoundaryIds := by
  have hg : (centralFixedFaceIds 0).all (fun face => decide
      (face ∈ cubeDifferenceBoundaryIds ∨ face ∈ cubeInactiveBoundaryIds)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hg face hf)

theorem corner_faces_fixed (corner : Nat × Nat × Nat) (hc : corner ∈ cubeDifferenceCorners) :
    corner.1 ∈ centralFixedFaceIds 0 ∧ corner.2.1 ∈ centralFixedFaceIds 0 ∧
      corner.2.2 ∈ centralFixedFaceIds 0 := by
  simp only [cubeDifferenceCorners, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem boundary_bounded {K : Nat} {boundary : EdgeLabelling}
    (hb : boundary ∈ centralBoundaryChannels K 0) : ∀ face, boundary face ≤ K := by
  have hh := boundedEdgeLabellings_sound K (centralFixedFaceIds 0) boundary hb
  intro face
  by_cases hf : face ∈ centralFixedFaceIds 0
  · exact Nat.le_of_lt_succ (hh.1 face hf)
  · rw [hh.2 face hf]; exact Nat.zero_le K

theorem boundary_zero_off_active {K : Nat} {boundary : EdgeLabelling}
    (hb : boundary ∈ centralBoundaryChannels K 0) (hz : cubeBoundaryZeroB boundary = true) :
    ∀ face, face ∉ cubeDifferenceBoundaryIds → boundary face = 0 := by
  intro face hf
  by_cases hfixed : face ∈ centralFixedFaceIds 0
  · have hi := (fixed_faces_active_or_inactive hfixed).resolve_left hf
    exact of_decide_eq_true (List.all_eq_true.mp hz face hi)
  · exact (boundedEdgeLabellings_sound K (centralFixedFaceIds 0) boundary hb).2 face hfixed

private theorem filter_zeroExtension (active : List Nat) (physical : EdgeLabelling)
    (hz : ∀ face, face ∉ active → physical face = 0) (faces : List Nat) :
    ZeroExtension ((faces.filter (fun face => decide (face ∈ active))).map physical)
      (faces.map physical) := by
  induction faces with
  | nil => exact ZeroExtension.nil
  | cons face faces ih =>
      by_cases hf : face ∈ active
      · simpa only [List.filter_cons, hf, decide_true, Bool.true_eq, ↓reduceIte,
          List.map_cons] using ZeroExtension.keep (physical face) ih
      · simpa only [List.filter_cons, hf, decide_false, Bool.false_eq_true, ↓reduceIte,
          List.map_cons, hz face hf] using ZeroExtension.insertZero ih

def wordMultiplicity (K : Nat) (physical : EdgeLabelling) (word : List Nat) : Nat :=
  explicitValenceMultiplicity (linkAuxiliaryCutoff K) (word.map physical).length
    (externalSpinsOfList (word.map physical))

theorem linkMultiplicity_eq_filtered (K : Nat) (physical : EdgeLabelling) (active : List Nat)
    (hb : ∀ face, physical face ≤ K) (hz : ∀ face, face ∉ active → physical face = 0)
    (link : Z4Link) :
    slabExplicitLinkMultiplicity K 1 physical link =
      wordMultiplicity K physical (activeIncidentWord active link) := by
  symm
  apply explicitValenceMultiplicity_zeroExtension
    (filter_zeroExtension active physical hz (slabIncidentPlaqIds 1 link))
  · simp only [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (slabIncidentPlaqIds_length_le_six 1 link)
  · simpa only [List.length_map] using slabIncidentPlaqIds_length_le_six 1 link
  · intro spin hs
    obtain ⟨face, _, rfl⟩ := List.mem_map.mp hs
    exact Nat.le_trans (hb face) (externalCutoff_le_linkAuxiliaryCutoff K)

private theorem product_append {A : Type} (value : A → Nat) : ∀ left right : List A,
    natListProduct value (left ++ right) = natListProduct value left * natListProduct value right
  | [], _ => by simp [natListProduct]
  | head :: tail, right => by simp only [List.cons_append, natListProduct, product_append, Nat.mul_assoc]

private theorem product_empty_words (K : Nat) (physical : EdgeLabelling) : ∀ n : Nat,
    natListProduct (wordMultiplicity K physical) (List.replicate n []) = 1
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, natListProduct, wordMultiplicity, explicitValenceMultiplicity,
      product_empty_words K physical n]

theorem boolMultiplicity_and (a b : Bool) :
    boolMultiplicity (a && b) = boolMultiplicity a * boolMultiplicity b := by cases a <;> cases b <;> rfl

theorem boolProduct_all {A : Type} (test : A → Bool) : ∀ items : List A,
    natListProduct (fun item => boolMultiplicity (test item)) items = boolMultiplicity (items.all test)
  | [] => rfl
  | head :: tail => by simp only [natListProduct, List.all_cons, boolMultiplicity_and, boolProduct_all]

private theorem lower_edge_word (K : Nat) (state boundary : EdgeLabelling)
    (edge : Nat × Nat × Nat) (he : edge ∈ cubeDifferenceEdges) :
    wordMultiplicity K (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)
      (tripleFaces edge) = boolMultiplicity
        (fusionOK (state edge.1) (state edge.2.1) (boundary edge.2.2)) := by
  have hg := cubeDifferenceEdge_faces edge he
  change boolMultiplicity (fusionOK
    (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling edge.1)
    (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling edge.2.1)
    (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling edge.2.2)) = _
  rw [assembled_lower state boundary (centralLowerCubeFaceIds_subset_lower _ hg.1),
    assembled_lower state boundary (centralLowerCubeFaceIds_subset_lower _ hg.2.1),
    assembled_fixed state boundary hg.2.2]

/-- All 48 original lower-link factors contract to exactly 24 Boolean tests. -/
theorem lower_product_eq_mask (K : Nat) (state boundary : EdgeLabelling)
    (hs : ∀ face, state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hb : boundary ∈ centralBoundaryChannels K 0) :
    slabLinkMultiplicityProductOn K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) (centralLowerLinks 0) =
      boolMultiplicity (cubeEdgeAdmissibleB state boundary && cubeBoundaryZeroB boundary) := by
  let physical := assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling
  have hzero := assembled_zero_off_support state boundary centralLowerCubeFaceIds (centralFixedFaceIds 0)
    hz (boundedEdgeLabellings_sound K (centralFixedFaceIds 0) boundary hb).2
  have hcount := natListProduct_congr _ _ (centralLowerLinks 0)
    (fun link _ => linkMultiplicity_eq_filtered K physical cubeFullLowerActive
      (assembled_bounded K state boundary hs (boundary_bounded hb)) hzero link)
  change natListProduct (slabExplicitLinkMultiplicity K 1 physical) (centralLowerLinks 0) = _
  rw [hcount, ← natListProduct_map, lower_word_product,
    product_append, product_append, product_empty_words, Nat.mul_one, natListProduct_map,
    natListProduct_map, boolMultiplicity_and]
  have he : natListProduct (fun edge => wordMultiplicity K physical (tripleFaces edge))
      cubeDifferenceEdges = boolMultiplicity (cubeEdgeAdmissibleB state boundary) := by
    unfold cubeEdgeAdmissibleB
    rw [← boolProduct_all]
    apply natListProduct_congr
    intro edge he
    exact lower_edge_word K state boundary edge he
  have hi : natListProduct (fun face => wordMultiplicity K physical [face])
      cubeInactiveBoundaryIds = boolMultiplicity (cubeBoundaryZeroB boundary) := by
    unfold cubeBoundaryZeroB
    rw [← boolProduct_all]
    apply natListProduct_congr
    intro face hf
    change oneValentMultiplicity (linkAuxiliaryCutoff K) (physical face) = _
    dsimp only [physical]
    rw [oneValentMultiplicity_eq_bool_zero, assembled_fixed state boundary (inactive_faces_fixed hf)]
  rw [he, hi]

/-- After the twelve zero tests, all fixed-link counts are the eight corner tests. -/
theorem fixed_product_eq_mask (K : Nat) (boundary : EdgeLabelling)
    (hb : boundary ∈ centralBoundaryChannels K 0) (hz : cubeBoundaryZeroB boundary = true) :
    slabLinkMultiplicityProductOn K 1
      (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary zeroEdgeLabelling) (centralFixedLinks 0) =
      boolMultiplicity (cubeCornerAdmissibleB boundary) := by
  let physical := assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary zeroEdgeLabelling
  have hzero : ∀ face, face ∉ cubeDifferenceBoundaryIds → physical face = 0 := by
    intro face hf
    exact assembled_zero_off_support zeroEdgeLabelling boundary [] cubeDifferenceBoundaryIds
      (fun _ _ => rfl) (boundary_zero_off_active hb hz) face hf
  have hcount := natListProduct_congr _ _ (centralFixedLinks 0)
    (fun link _ => linkMultiplicity_eq_filtered K physical cubeDifferenceBoundaryIds
      (assembled_bounded K _ _ (fun _ => Nat.zero_le K) (boundary_bounded hb)) hzero link)
  change natListProduct (slabExplicitLinkMultiplicity K 1 physical) (centralFixedLinks 0) = _
  rw [hcount, ← natListProduct_map, fixed_word_product,
    product_append, product_empty_words, Nat.mul_one, natListProduct_map]
  unfold cubeCornerAdmissibleB
  rw [← boolProduct_all]
  apply natListProduct_congr
  intro corner hc
  have hg := corner_faces_fixed corner hc
  change boolMultiplicity (fusionOK (physical corner.1) (physical corner.2.1) (physical corner.2.2)) = _
  dsimp only [physical]
  rw [assembled_fixed _ _ hg.1, assembled_fixed _ _ hg.2.1, assembled_fixed _ _ hg.2.2]

end YMGap.Continuum.BF4PhysicalCubeBoundaryMask

#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.lower_word_product
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.fixed_word_product
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.inactive_faces_fixed
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.fixed_faces_active_or_inactive
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.corner_faces_fixed
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.boundary_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.boundary_zero_off_active
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.linkMultiplicity_eq_filtered
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.boolMultiplicity_and
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.boolProduct_all
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.lower_product_eq_mask
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundaryMask.fixed_product_eq_mask
