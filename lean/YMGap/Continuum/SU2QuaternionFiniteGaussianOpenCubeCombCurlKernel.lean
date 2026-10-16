/-
# Trivial curl kernel in the open-cube comb gauge

This leaf proves the finite topological fact needed before any inverse
certificate: an internal rational edge field that vanishes on the comb and has
zero oriented curl on every internal face vanishes on every internal link.

The proof is the concrete coordinate recursion.  Positive `x` links vanish by
the comb condition.  `p01` faces propagate positive `y` links from `x = 0`.
`p02` faces propagate positive `z` links to `x = 0`, and `p12` faces then
propagate them from `y = 0`.  This proves field-level injectivity of curl after
the explicit gauge fixing.  It does not yet prove a determinant formula,
positive LDL pivots, an all-width rational inverse, a Gaussian law, an
ORIGINAL-law comparison, a continuum theory, or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge

local infix:50 " ≈ " => Q'.eqv

/-- A rational edge field vanishes on every listed comb link. -/
def VanishesOnComb (width : Nat) (field : Z4Link → Q') : Prop :=
  ∀ link, link ∈ combTreeLinks width → field link ≈ 0

/-- A rational edge field has zero oriented curl on every listed internal
face. -/
def VanishesOnInternalCurls (width : Nat) (field : Z4Link → Q') : Prop :=
  ∀ face, face ∈ internalOpenCubeFaces width → combGaugeFaceCurl field face ≈ 0

private theorem coordinate_lt_of_add_one_lt {coordinate width : Nat}
    (hcoordinate : coordinate + 1 < width) : coordinate < width :=
  Nat.lt_of_succ_lt (by
    simpa only [Nat.succ_eq_add_one] using hcoordinate)

private theorem x0_ne_x3 : Dir4.x0 ≠ .x3 := by decide

private theorem x1_ne_x3 : Dir4.x1 ≠ .x3 := by decide

private theorem x2_ne_x3 : Dir4.x2 ≠ .x3 := by decide

private theorem curl_second_eq_fourth {first second third fourth : Q'}
    (hfirst : first ≈ 0) (hthird : third ≈ 0)
    (hcurl : first + (second + (-third + -fourth)) ≈ 0) :
    second ≈ fourth := by
  have hreduced : first + (second + (-third + -fourth)) ≈ second + -fourth :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hfirst
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hthird)
            (Q'.eqv_refl _))))
      (RingNormaliser.poly_identity_of_normal_eq
        (.add (.const 0)
          (.add (.var 0) (.add (.neg (.const 0)) (.neg (.var 1)))))
        (.add (.var 0) (.neg (.var 1)))
        (by decide) (fun
          | 0 => second
          | _ => fourth))
  exact QPoly.q_eqv_of_sub_zero
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hreduced) hcurl)

private theorem xLink_comb {width x y z : Nat}
    (hx : x + 1 < width) (hy : y < width) (hz : z < width) :
    CombTreeLink width (((x, y, z, 0), .x0) : Z4Link) :=
  ⟨⟨⟨x0_ne_x3, coordinate_lt_of_add_one_lt hx, hy, hz, rfl⟩, hx⟩,
    True.intro⟩

private theorem yLink_at_x_zero_comb {width y z : Nat}
    (hy : y + 1 < width) (hz : z < width) :
    CombTreeLink width (((0, y, z, 0), .x1) : Z4Link) :=
  ⟨⟨⟨x1_ne_x3, Nat.zero_lt_of_lt (coordinate_lt_of_add_one_lt hy),
      coordinate_lt_of_add_one_lt hy, hz, rfl⟩, hy⟩, rfl⟩

private theorem zLink_at_xy_zero_comb {width z : Nat}
    (hz : z + 1 < width) :
    CombTreeLink width (((0, 0, z, 0), .x2) : Z4Link) :=
  ⟨⟨⟨x2_ne_x3, Nat.zero_lt_of_lt (coordinate_lt_of_add_one_lt hz),
      Nat.zero_lt_of_lt (coordinate_lt_of_add_one_lt hz),
      coordinate_lt_of_add_one_lt hz, rfl⟩, hz⟩, ⟨rfl, rfl⟩⟩

private theorem yLink_succ_x_eq_prev (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field)
    {x y z : Nat} (hx : x + 1 < width) (hy : y + 1 < width)
    (hz : z < width) :
    field (((x + 1, y, z, 0), .x1) : Z4Link) ≈
      field (((x, y, z, 0), .x1) : Z4Link) := by
  have hfirst : field (((x, y, z, 0), .x0) : Z4Link) ≈ 0 :=
    hcomb _ ((combTreeLinks_mem_iff width _).mpr
      (xLink_comb hx (coordinate_lt_of_add_one_lt hy) hz))
  have hthird : field (((x, y + 1, z, 0), .x0) : Z4Link) ≈ 0 :=
    hcomb _ ((combTreeLinks_mem_iff width _).mpr (xLink_comb hx hy hz))
  have hface := hcurl (((x, y, z, 0), .p01) : Z4Plaq)
    ((internalOpenCubeFaces_mem_iff width _).mpr ⟨rfl, hx, hy, hz⟩)
  change field (((x, y, z, 0), .x0) : Z4Link) +
      (field (((x + 1, y, z, 0), .x1) : Z4Link) +
        (-field (((x, y + 1, z, 0), .x0) : Z4Link) +
          -field (((x, y, z, 0), .x1) : Z4Link))) ≈ 0 at hface
  exact curl_second_eq_fourth hfirst hthird hface

private theorem zLink_succ_x_eq_prev (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field)
    {x y z : Nat} (hx : x + 1 < width) (hy : y < width)
    (hz : z + 1 < width) :
    field (((x + 1, y, z, 0), .x2) : Z4Link) ≈
      field (((x, y, z, 0), .x2) : Z4Link) := by
  have hfirst : field (((x, y, z, 0), .x0) : Z4Link) ≈ 0 :=
    hcomb _ ((combTreeLinks_mem_iff width _).mpr
      (xLink_comb hx hy (coordinate_lt_of_add_one_lt hz)))
  have hthird : field (((x, y, z + 1, 0), .x0) : Z4Link) ≈ 0 :=
    hcomb _ ((combTreeLinks_mem_iff width _).mpr (xLink_comb hx hy hz))
  have hface := hcurl (((x, y, z, 0), .p02) : Z4Plaq)
    ((internalOpenCubeFaces_mem_iff width _).mpr ⟨rfl, hx, hy, hz⟩)
  change field (((x, y, z, 0), .x0) : Z4Link) +
      (field (((x + 1, y, z, 0), .x2) : Z4Link) +
        (-field (((x, y, z + 1, 0), .x0) : Z4Link) +
          -field (((x, y, z, 0), .x2) : Z4Link))) ≈ 0 at hface
  exact curl_second_eq_fourth hfirst hthird hface

private theorem zLink_succ_y_at_x_zero_eq_prev
    (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field)
    {y z : Nat} (hy : y + 1 < width) (hz : z + 1 < width) :
    field (((0, y + 1, z, 0), .x2) : Z4Link) ≈
      field (((0, y, z, 0), .x2) : Z4Link) := by
  have hfirst : field (((0, y, z, 0), .x1) : Z4Link) ≈ 0 :=
    hcomb _ ((combTreeLinks_mem_iff width _).mpr
      (yLink_at_x_zero_comb hy (coordinate_lt_of_add_one_lt hz)))
  have hthird : field (((0, y, z + 1, 0), .x1) : Z4Link) ≈ 0 :=
    hcomb _ ((combTreeLinks_mem_iff width _).mpr
      (yLink_at_x_zero_comb hy hz))
  have hface := hcurl (((0, y, z, 0), .p12) : Z4Plaq)
    ((internalOpenCubeFaces_mem_iff width _).mpr
      ⟨rfl, Nat.zero_lt_of_lt (coordinate_lt_of_add_one_lt hy), hy, hz⟩)
  change field (((0, y, z, 0), .x1) : Z4Link) +
      (field (((0, y + 1, z, 0), .x2) : Z4Link) +
        (-field (((0, y, z + 1, 0), .x1) : Z4Link) +
          -field (((0, y, z, 0), .x2) : Z4Link))) ≈ 0 at hface
  exact curl_second_eq_fourth hfirst hthird hface

private theorem yLink_eqv_zero (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field) (y z : Nat) :
    ∀ x, InternalOpenCubeLink width (((x, y, z, 0), .x1) : Z4Link) →
      field (((x, y, z, 0), .x1) : Z4Link) ≈ 0
  | 0, hlink =>
      hcomb _ ((combTreeLinks_mem_iff width _).mpr ⟨hlink, rfl⟩)
  | x + 1, hlink => by
      rcases hlink with ⟨⟨_, hx, hyBase, hz, _⟩, hy⟩
      have hx' : x + 1 < width := by
        simpa only [Nat.succ_eq_add_one] using hx
      have hpred :
          InternalOpenCubeLink width (((x, y, z, 0), .x1) : Z4Link) :=
        ⟨⟨x1_ne_x3, coordinate_lt_of_add_one_lt hx', hyBase, hz, rfl⟩, hy⟩
      exact Q'.eqv_trans _ _ _
        (yLink_succ_x_eq_prev width field hcomb hcurl hx' hy hz)
        (yLink_eqv_zero width field hcomb hcurl y z x hpred)

private theorem zLink_at_x_zero_eqv_zero
    (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field) (z : Nat) :
    ∀ y, InternalOpenCubeLink width (((0, y, z, 0), .x2) : Z4Link) →
      field (((0, y, z, 0), .x2) : Z4Link) ≈ 0
  | 0, hlink =>
      hcomb _ ((combTreeLinks_mem_iff width _).mpr
        ⟨hlink, ⟨rfl, rfl⟩⟩)
  | y + 1, hlink => by
      rcases hlink with ⟨⟨_, hxZero, hy, hzBase, _⟩, hz⟩
      have hy' : y + 1 < width := by
        simpa only [Nat.succ_eq_add_one] using hy
      have hpred :
          InternalOpenCubeLink width (((0, y, z, 0), .x2) : Z4Link) :=
        ⟨⟨x2_ne_x3, hxZero, coordinate_lt_of_add_one_lt hy', hzBase, rfl⟩, hz⟩
      exact Q'.eqv_trans _ _ _
        (zLink_succ_y_at_x_zero_eq_prev width field hcomb hcurl hy' hz)
        (zLink_at_x_zero_eqv_zero width field hcomb hcurl z y hpred)

private theorem zLink_eqv_zero (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field) (y z : Nat) :
    ∀ x, InternalOpenCubeLink width (((x, y, z, 0), .x2) : Z4Link) →
      field (((x, y, z, 0), .x2) : Z4Link) ≈ 0
  | 0, hlink => zLink_at_x_zero_eqv_zero width field hcomb hcurl z y hlink
  | x + 1, hlink => by
      rcases hlink with ⟨⟨_, hx, hy, hzBase, _⟩, hz⟩
      have hx' : x + 1 < width := by
        simpa only [Nat.succ_eq_add_one] using hx
      have hpred :
          InternalOpenCubeLink width (((x, y, z, 0), .x2) : Z4Link) :=
        ⟨⟨x2_ne_x3, coordinate_lt_of_add_one_lt hx', hy, hzBase, rfl⟩, hz⟩
      exact Q'.eqv_trans _ _ _
        (zLink_succ_x_eq_prev width field hcomb hcurl hx' hy hz)
        (zLink_eqv_zero width field hcomb hcurl y z x hpred)

/-- The oriented curl has trivial kernel after imposing the formula-level comb
gauge: every listed internal edge value is zero. -/
theorem internalField_eqv_zero_of_comb_and_curl
    (width : Nat) (field : Z4Link → Q')
    (hcomb : VanishesOnComb width field)
    (hcurl : VanishesOnInternalCurls width field)
    {link : Z4Link} (hlink : link ∈ internalOpenCubeLinks width) :
    field link ≈ 0 := by
  have hinternal := (internalOpenCubeLinks_mem_iff width link).mp hlink
  rcases link with ⟨⟨x, y, z, t⟩, direction⟩
  rcases hinternal with ⟨⟨_, hx, hy, hz, ht⟩, hdirection⟩
  change t = 0 at ht
  subst t
  cases direction with
  | x0 =>
      have hcurrent :
          InternalOpenCubeLink width (((x, y, z, 0), .x0) : Z4Link) :=
        ⟨⟨x0_ne_x3, hx, hy, hz, rfl⟩, hdirection⟩
      exact hcomb _ ((combTreeLinks_mem_iff width _).mpr
        ⟨hcurrent, True.intro⟩)
  | x1 =>
      exact yLink_eqv_zero width field hcomb hcurl y z x
        ⟨⟨x1_ne_x3, hx, hy, hz, rfl⟩, hdirection⟩
  | x2 =>
      exact zLink_eqv_zero width field hcomb hcurl y z x
        ⟨⟨x2_ne_x3, hx, hy, hz, rfl⟩, hdirection⟩
  | x3 => exact False.elim hdirection

/-- Extend chord coordinates to the complete formula-level internal carrier by
zero on every non-chord link. -/
def combGaugeCoordinateField (width : Nat) (coordinate : Nat → Q')
    (link : Z4Link) : Q' :=
  if link ∈ combGaugeLinks width then
    coordinate ((combGaugeLinks width).idxOf link)
  else 0

theorem combGaugeCoordinateField_tree_zero
    (width : Nat) (coordinate : Nat → Q') :
    VanishesOnComb width (combGaugeCoordinateField width coordinate) := by
  intro link htree
  unfold combGaugeCoordinateField
  rw [if_neg (combTreeLink_not_mem_gauge htree)]
  exact Q'.eqv_refl 0

/-- Field-level triviality already forces the coordinate attached to every
listed chord link to vanish. -/
theorem combGaugeCoordinate_idxOf_eqv_zero_of_face_curls
    (width : Nat) (coordinate : Nat → Q')
    (hcurl : VanishesOnInternalCurls width
      (combGaugeCoordinateField width coordinate))
    {link : Z4Link} (hlink : link ∈ combGaugeLinks width) :
    coordinate ((combGaugeLinks width).idxOf link) ≈ 0 := by
  have hinternal : link ∈ internalOpenCubeLinks width :=
    (internalOpenCubeLinks_mem_iff width link).mpr
      ((combGaugeLinks_mem_iff width link).mp hlink).1
  have hzero := internalField_eqv_zero_of_comb_and_curl width
    (combGaugeCoordinateField width coordinate)
    (combGaugeCoordinateField_tree_zero width coordinate) hcurl hinternal
  unfold combGaugeCoordinateField at hzero
  rw [if_pos hlink] at hzero
  exact hzero

private def fallbackLink : Z4Link := ((0, 0, 0, 0), .x0)

private theorem getD_mem_local : ∀ {links : List Z4Link} {index : Nat},
    index < links.length → links.getD index fallbackLink ∈ links
  | [], _, hindex => absurd hindex (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: _links, _index + 1, hindex =>
      List.mem_cons_of_mem _
        (getD_mem_local (Nat.lt_of_succ_lt_succ hindex))

private theorem idxOf_getD_local : ∀ (links : List Z4Link), links.Nodup →
    ∀ index, index < links.length →
      links.idxOf (links.getD index fallbackLink) = index
  | [], _, index, hindex => absurd hindex (Nat.not_lt_zero _)
  | head :: tail, _, 0, _ => by
      show (head :: tail).idxOf head = 0
      rw [List.idxOf_cons,
        show (head == head) = true from beq_iff_eq.mpr rfl]
      rfl
  | head :: tail, hnodup, index + 1, hindex => by
      have hnodup' := List.nodup_cons.mp hnodup
      have hindex' : index < tail.length := Nat.lt_of_succ_lt_succ hindex
      have hmem : tail.getD index fallbackLink ∈ tail := getD_mem_local hindex'
      have hne : (head == tail.getD index fallbackLink) = false := by
        cases heq : (head == tail.getD index fallbackLink) with
        | false => rfl
        | true => exact absurd ((beq_iff_eq.mp heq) ▸ hmem) hnodup'.1
      show (head :: tail).idxOf (tail.getD index fallbackLink) = index + 1
      rw [List.idxOf_cons, hne, cond_false,
        idxOf_getD_local tail hnodup'.2 index hindex']

/-- Coordinate form of the comb-curl kernel theorem: every in-range chord
coordinate is zero when the represented field has zero internal face curls. -/
theorem combGaugeCoordinate_eqv_zero_of_face_curls
    (width : Nat) (coordinate : Nat → Q')
    (hcurl : VanishesOnInternalCurls width
      (combGaugeCoordinateField width coordinate))
    {index : Nat} (hindex : index < combGaugeEdgeCount width) :
    coordinate index ≈ 0 := by
  have hselected := selectedCombGaugeLink_mem hindex
  have hzero := combGaugeCoordinate_idxOf_eqv_zero_of_face_curls
    width coordinate hcurl hselected
  change coordinate ((combGaugeLinks width).idxOf
    ((combGaugeLinks width).getD index fallbackLink)) ≈ 0 at hzero
  rw [idxOf_getD_local
    (combGaugeLinks width) (combGaugeLinks_nodup width) index hindex] at hzero
  exact hzero

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel.internalField_eqv_zero_of_comb_and_curl
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlKernel.combGaugeCoordinate_eqv_zero_of_face_curls
