/-
# Formula-level open-cube comb gauge

The internal open-cube link carrier admits the standard all-width comb split:
all positive `x` links are tree links, together with positive `y` links at
`x = 0` and positive `z` links at `x = y = 0`.  The complementary internal
links are chord coordinates.  This leaf constructs that finite partition,
the literal chord-to-edge inclusion matrix, and the curl/free-history
precision restricted to those chord coordinates.  An explicit rooted comb
path sum supplies a gauge potential whose transformed field vanishes on every
comb link.

This proves existence of a tree-zero gauge representative, not uniqueness or
invertibility of the resulting chord precision.  The rank/invertibility,
covariance, and original-transfer-filter bridges remain separate.  No Gaussian
law, ORIGINAL-law comparison, continuum theory, or physical mass gap is
asserted.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence

local infix:50 " ≈ " => Q'.eqv

/-- The standard open-cube comb: every `x` link, the `y` links at `x = 0`,
and the `z` links at `x = y = 0`. -/
def CombTreeLink (width : Nat) (link : Z4Link) : Prop :=
  InternalOpenCubeLink width link ∧
    match link.2 with
    | .x0 => True
    | .x1 => link.1.1 = 0
    | .x2 => link.1.1 = 0 ∧ link.1.2.1 = 0
    | .x3 => False

instance (width : Nat) (link : Z4Link) : Decidable (CombTreeLink width link) := by
  rcases link with ⟨vertex, dir⟩
  cases dir <;> unfold CombTreeLink <;> infer_instance

/-- Internal links selected by the comb predicate. -/
def combTreeLinks (width : Nat) : List Z4Link :=
  (internalOpenCubeLinks width).filter
    (fun link => decide (CombTreeLink width link))

/-- Internal links complementary to the comb; these are the gauge-fixed chord
coordinates. -/
def combGaugeLinks (width : Nat) : List Z4Link :=
  (internalOpenCubeLinks width).filter
    (fun link => decide (¬ CombTreeLink width link))

theorem combTreeLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ combTreeLinks width ↔ CombTreeLink width link := by
  constructor
  · intro hlink
    exact of_decide_eq_true (List.mem_filter.mp hlink).2
  · intro hlink
    exact List.mem_filter.mpr
      ⟨(internalOpenCubeLinks_mem_iff width link).mpr hlink.1,
        decide_eq_true hlink⟩

theorem combGaugeLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ combGaugeLinks width ↔
      InternalOpenCubeLink width link ∧ ¬ CombTreeLink width link := by
  constructor
  · intro hlink
    have hfiltered := List.mem_filter.mp hlink
    exact ⟨(internalOpenCubeLinks_mem_iff width link).mp hfiltered.1,
      of_decide_eq_true hfiltered.2⟩
  · intro hlink
    exact List.mem_filter.mpr
      ⟨(internalOpenCubeLinks_mem_iff width link).mpr hlink.1,
        decide_eq_true hlink.2⟩

theorem combTreeLinks_nodup (width : Nat) : (combTreeLinks width).Nodup :=
  (internalOpenCubeLinks_nodup width).filter _

theorem combGaugeLinks_nodup (width : Nat) : (combGaugeLinks width).Nodup :=
  (internalOpenCubeLinks_nodup width).filter _

theorem combTreeLink_not_mem_gauge {width : Nat} {link : Z4Link}
    (htree : link ∈ combTreeLinks width) : link ∉ combGaugeLinks width := by
  intro hgauge
  exact ((combGaugeLinks_mem_iff width link).mp hgauge).2
    ((combTreeLinks_mem_iff width link).mp htree)

/-- The comb and chord lists are an exact decidable partition of the internal
edge carrier. -/
theorem internalOpenCubeLink_mem_iff_comb_partition
    (width : Nat) (link : Z4Link) :
    link ∈ internalOpenCubeLinks width ↔
      link ∈ combTreeLinks width ∨ link ∈ combGaugeLinks width := by
  constructor
  · intro hlink
    by_cases htree : CombTreeLink width link
    · exact Or.inl ((combTreeLinks_mem_iff width link).mpr htree)
    · exact Or.inr ((combGaugeLinks_mem_iff width link).mpr
        ⟨(internalOpenCubeLinks_mem_iff width link).mp hlink, htree⟩)
  · rintro (htree | hgauge)
    · exact (internalOpenCubeLinks_mem_iff width link).mpr
        ((combTreeLinks_mem_iff width link).mp htree).1
    · exact (internalOpenCubeLinks_mem_iff width link).mpr
        ((combGaugeLinks_mem_iff width link).mp hgauge).1

private theorem listQSum_append_local {A : Type} (value : A → Q') :
    ∀ left right : List A,
      listQSum value (left ++ right) ≈
        listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | head :: tail, right => by
      change value head + listQSum value (tail ++ right) ≈
        (value head + listQSum value tail) + listQSum value right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_append_local value tail right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_range_succ_local (value : Nat → Q') (count : Nat) :
    listQSum value (List.range (count + 1)) ≈
      listQSum value (List.range count) + value count := by
  rw [List.range_succ]
  exact Q'.eqv_trans _ _ _
    (listQSum_append_local value (List.range count) [count])
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (QPoly.q_add_zero_eqv _))

/-- Rooted comb-path sum from `(0,0,0)` first in `z`, then `y`, then `x`.
The order is chosen so every comb edge is the final added segment for its
coordinate direction. -/
def combGaugePotential (field : Z4Link → Q') (vertex : Z4Vertex) : Q' :=
  listQSum (fun index => field ((0, 0, index, 0), .x2))
      (List.range vertex.2.2.1) +
    (listQSum (fun index => field ((0, index, vertex.2.2.1, 0), .x1))
        (List.range vertex.2.1) +
      listQSum
        (fun index => field ((index, vertex.2.1, vertex.2.2.1, 0), .x0))
        (List.range vertex.1))

/-- Along every comb link, the rooted path potential gains exactly that link's
field value. -/
theorem combGaugePotential_increment (field : Z4Link → Q')
    {width : Nat} {link : Z4Link} (htree : CombTreeLink width link) :
    combGaugePotential field (addE link.1 link.2) ≈
      combGaugePotential field link.1 + field link := by
  rcases link with ⟨⟨x, y, z, t⟩, direction⟩
  rcases htree with ⟨hinternal, hshape⟩
  rcases hinternal with ⟨⟨_, _, _, _, ht⟩, _⟩
  change t = 0 at ht
  subst t
  cases direction with
  | x0 =>
      unfold combGaugePotential
      simp only [addE]
      have hsum := listQSum_range_succ_local
        (fun index => field ((index, y, z, 0), .x0)) x
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) hsum)) ?_
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3))))
        (.add (.add (.var 0) (.add (.var 1) (.var 2))) (.var 3))
        (by decide) (fun
          | 0 => listQSum (fun index => field ((0, 0, index, 0), .x2))
              (List.range z)
          | 1 => listQSum (fun index => field ((0, index, z, 0), .x1))
              (List.range y)
          | 2 => listQSum (fun index => field ((index, y, z, 0), .x0))
              (List.range x)
          | _ => field ((x, y, z, 0), .x0))
  | x1 =>
      change x = 0 at hshape
      subst x
      unfold combGaugePotential
      simp only [addE, List.range_zero, listQSum]
      have hsum := listQSum_range_succ_local
        (fun index => field ((0, index, z, 0), .x1)) y
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' hsum (Q'.eqv_refl _))) ?_
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.add (.add (.var 1) (.var 2)) (.const 0)))
        (.add (.add (.var 0) (.add (.var 1) (.const 0))) (.var 2))
        (by decide) (fun
          | 0 => listQSum (fun index => field ((0, 0, index, 0), .x2))
              (List.range z)
          | 1 => listQSum (fun index => field ((0, index, z, 0), .x1))
              (List.range y)
          | _ => field ((0, y, z, 0), .x1))
  | x2 =>
      change x = 0 ∧ y = 0 at hshape
      rcases hshape with ⟨hx, hy⟩
      subst x
      subst y
      unfold combGaugePotential
      simp only [addE, List.range_zero, listQSum]
      have hsum := listQSum_range_succ_local
        (fun index => field ((0, 0, index, 0), .x2)) z
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hsum (Q'.eqv_refl _)) ?_
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.const 0) (.const 0)))
        (.add (.add (.var 0) (.add (.const 0) (.const 0))) (.var 1))
        (by decide) (fun
          | 0 => listQSum (fun index => field ((0, 0, index, 0), .x2))
              (List.range z)
          | _ => field ((0, 0, z, 0), .x2))
  | x3 => exact False.elim hshape

/-- Gauge transform by the explicit rooted comb potential. -/
def combGaugeFixedField (field : Z4Link → Q') (link : Z4Link) : Q' :=
  field link + combGaugePotential field link.1 +
    -combGaugePotential field (addE link.1 link.2)

/-- Every field has an explicit gauge-transformed representative vanishing on
all comb links. -/
theorem combGaugeFixedField_tree_zero (field : Z4Link → Q')
    {width : Nat} {link : Z4Link} (htree : link ∈ combTreeLinks width) :
    combGaugeFixedField field link ≈ 0 := by
  have hincrement := combGaugePotential_increment field
    ((combTreeLinks_mem_iff width link).mp htree)
  unfold combGaugeFixedField
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hincrement)) ?_
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 1) (.var 0))))
    (.const 0) (by decide) (fun
      | 0 => field link
      | _ => combGaugePotential field link.1)

/-- Literal oriented face curl in the standard `+A,+B,-C,-D` order. -/
def combGaugeFaceCurl (field : Z4Link → Q') (face : Z4Plaq) : Q' :=
  field (face.1, (dirsOf face.2).1) +
    (field (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2) +
      (-field (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1) +
        -field (face.1, (dirsOf face.2).2)))

private theorem addE_comb_directions_comm (face : Z4Plaq) :
    addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2 =
      addE (addE face.1 (dirsOf face.2).2) (dirsOf face.2).1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;> rfl

/-- The explicit comb gauge transform preserves the oriented curl on every
coordinate plaquette. -/
theorem combGaugeFaceCurl_fixed (field : Z4Link → Q') (face : Z4Plaq) :
    combGaugeFaceCurl (combGaugeFixedField field) face ≈
      combGaugeFaceCurl field face := by
  unfold combGaugeFaceCurl combGaugeFixedField
  rw [← addE_comb_directions_comm face]
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add
      (.add (.add (.var 0) (.var 4)) (.neg (.var 5)))
      (.add
        (.add (.add (.var 1) (.var 5)) (.neg (.var 6)))
        (.add
          (.neg (.add (.add (.var 2) (.var 7)) (.neg (.var 6))))
          (.neg (.add (.add (.var 3) (.var 4)) (.neg (.var 7)))))))
    (.add (.var 0)
      (.add (.var 1) (.add (.neg (.var 2)) (.neg (.var 3)))))
    (by decide) (fun
      | 0 => field (face.1, (dirsOf face.2).1)
      | 1 => field (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
      | 2 => field (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
      | 3 => field (face.1, (dirsOf face.2).2)
      | 4 => combGaugePotential field face.1
      | 5 => combGaugePotential field (addE face.1 (dirsOf face.2).1)
      | 6 => combGaugePotential field
          (addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2)
      | _ => combGaugePotential field (addE face.1 (dirsOf face.2).2))

def combGaugeEdgeCount (width : Nat) : Nat :=
  (combGaugeLinks width).length

def selectedCombGaugeLink (width gaugeIndex : Nat) : Z4Link :=
  (combGaugeLinks width).getD gaugeIndex ((0, 0, 0, 0), .x0)

theorem selectedCombGaugeLink_mem {width gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    selectedCombGaugeLink width gaugeIndex ∈ combGaugeLinks width := by
  rw [selectedCombGaugeLink, ← List.getElem_eq_getD (h := hgauge)]
  exact List.getElem_mem hgauge

theorem selectedCombGaugeLink_idxOf {width : Nat} {link : Z4Link}
    (hlink : link ∈ combGaugeLinks width) :
    selectedCombGaugeLink width ((combGaugeLinks width).idxOf link) = link := by
  have hindex := List.idxOf_lt_length_of_mem hlink
  rw [selectedCombGaugeLink, ← List.getElem_eq_getD (h := hindex)]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

/-- Literal inclusion of chord coordinates into the complete internal-edge
carrier. -/
def combGaugeEmbedding (width edgeIndex gaugeIndex : Nat) : Q' :=
  if edgeIndex < internalOpenCubeEdgeCount width ∧
      gaugeIndex < combGaugeEdgeCount width then
    if selectedInternalOpenCubeLink width edgeIndex =
        selectedCombGaugeLink width gaugeIndex then 1 else 0
  else 0

theorem combGaugeEmbedding_recovers_chord {width : Nat} {link : Z4Link}
    (hlink : link ∈ combGaugeLinks width) :
    combGaugeEmbedding width
        ((internalOpenCubeLinks width).idxOf link)
        ((combGaugeLinks width).idxOf link) = 1 := by
  have hinternal : link ∈ internalOpenCubeLinks width :=
    (internalOpenCubeLinks_mem_iff width link).mpr
      ((combGaugeLinks_mem_iff width link).mp hlink).1
  rw [combGaugeEmbedding, if_pos
      ⟨List.idxOf_lt_length_of_mem hinternal,
        List.idxOf_lt_length_of_mem hlink⟩,
    selectedInternalOpenCubeLink_idxOf hinternal,
    selectedCombGaugeLink_idxOf hlink, if_pos rfl]

theorem combGaugeEmbedding_tree_zero {width : Nat} {link : Z4Link}
    (htree : link ∈ combTreeLinks width) {gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combGaugeEmbedding width
        ((internalOpenCubeLinks width).idxOf link) gaugeIndex = 0 := by
  have hinternal : link ∈ internalOpenCubeLinks width :=
    (internalOpenCubeLinks_mem_iff width link).mpr
      ((combTreeLinks_mem_iff width link).mp htree).1
  rw [combGaugeEmbedding, if_pos
      ⟨List.idxOf_lt_length_of_mem hinternal, hgauge⟩,
    selectedInternalOpenCubeLink_idxOf hinternal, if_neg]
  intro heq
  apply combTreeLink_not_mem_gauge htree
  rw [heq]
  exact selectedCombGaugeLink_mem hgauge

/-- Internal-face curl restricted to the chord-coordinate columns. -/
def combGaugeCurl (width faceIndex gaugeIndex : Nat) : Q' :=
  if faceIndex < internalOpenCubeFaceCount width ∧
      gaugeIndex < combGaugeEdgeCount width then
    internalBoundaryCoefficient
      (selectedInternalOpenCubeFace width faceIndex)
      (selectedCombGaugeLink width gaugeIndex)
  else 0

theorem combGaugeCurl_eq_internalOpenCubeCurl {width faceIndex gaugeIndex : Nat}
    (hface : faceIndex < internalOpenCubeFaceCount width)
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combGaugeCurl width faceIndex gaugeIndex =
      internalOpenCubeCurl width faceIndex
        ((internalOpenCubeLinks width).idxOf
          (selectedCombGaugeLink width gaugeIndex)) := by
  have hselected := selectedCombGaugeLink_mem hgauge
  have hinternal : selectedCombGaugeLink width gaugeIndex ∈
      internalOpenCubeLinks width :=
    (internalOpenCubeLinks_mem_iff width _).mpr
      ((combGaugeLinks_mem_iff width _).mp hselected).1
  rw [combGaugeCurl, if_pos ⟨hface, hgauge⟩,
    internalOpenCubeCurl, if_pos
      ⟨hface, List.idxOf_lt_length_of_mem hinternal⟩,
    selectedInternalOpenCubeLink_idxOf hinternal]

theorem combGaugeCurl_idxOf {width : Nat} {face : Z4Plaq} {link : Z4Link}
    (hface : face ∈ internalOpenCubeFaces width)
    (hlink : link ∈ combGaugeLinks width) :
    combGaugeCurl width
        ((internalOpenCubeFaces width).idxOf face)
        ((combGaugeLinks width).idxOf link) =
      internalBoundaryCoefficient face link := by
  rw [combGaugeCurl, if_pos
      ⟨List.idxOf_lt_length_of_mem hface,
        List.idxOf_lt_length_of_mem hlink⟩,
    selectedInternalOpenCubeFace_idxOf hface,
    selectedCombGaugeLink_idxOf hlink]

def combGaugeSpatialPrecision (width : Nat) : Nat → Nat → Q' :=
  finiteCurlPrecision (internalOpenCubeFaceCount width) (combGaugeCurl width)

def combGaugeFreeHistoryPrecision (timeBonds width : Nat) : Nat → Nat → Q' :=
  freeHistoryCurlPrecision timeBonds
    (combGaugeEdgeCount width) (internalOpenCubeFaceCount width)
    (combGaugeCurl width)

theorem combGaugeFreeHistoryPrecision_symm
    (timeBonds width left right : Nat) :
    combGaugeFreeHistoryPrecision timeBonds width left right ≈
      combGaugeFreeHistoryPrecision timeBonds width right left :=
  freeHistoryCurlPrecision_symm timeBonds
    (combGaugeEdgeCount width) (internalOpenCubeFaceCount width)
    (combGaugeCurl width) left right

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combTreeLinks_mem_iff
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeLinks_mem_iff
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.internalOpenCubeLink_mem_iff_comb_partition
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugePotential_increment
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeFixedField_tree_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeFaceCurl_fixed
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeEmbedding_recovers_chord
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeEmbedding_tree_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeCurl_eq_internalOpenCubeCurl
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeCurl_idxOf
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge.combGaugeFreeHistoryPrecision_symm
