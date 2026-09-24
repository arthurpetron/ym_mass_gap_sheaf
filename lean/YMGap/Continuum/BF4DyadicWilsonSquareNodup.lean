/-
# Distinct underlying links in a literal dyadic Wilson square

The four straight sides of a positive corner-anchored square use pairwise
distinct underlying positive links.  Padding changes neither the ordered word
nor its links.  Consequently their actual indices in the fixed spatial
carrier are distinct as well.  This is finite geometry only; it supplies the
selection premise for a later product-heat calculation and makes no analytic
claim.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareUniqueEdge
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger

namespace YMGap.Continuum.BF4DyadicWilsonSquareNodup

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquare

private theorem east_shape (x y n : Nat) :
    ∀ e, e ∈ eastFrom x y n →
      e.link.2 = .x0 ∧ e.link.1.2.1 = y ∧ x ≤ e.link.1.1 ∧ e.link.1.1 < x+n := by
  induction n generalizing x with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [eastFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨rfl, rfl, Nat.le_refl _, by change x < x+(n+1); omega⟩
      · obtain ⟨hd, hy, hlo, hhi⟩ := ih (x+1) e he
        exact ⟨hd, hy, by omega, by omega⟩

private theorem north_shape (x y n : Nat) :
    ∀ e, e ∈ northFrom x y n →
      e.link.2 = .x1 ∧ e.link.1.1 = x ∧ y ≤ e.link.1.2.1 ∧ e.link.1.2.1 < y+n := by
  induction n generalizing y with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [northFrom, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨rfl, rfl, Nat.le_refl _, by change y < y+(n+1); omega⟩
      · obtain ⟨hd, hx, hlo, hhi⟩ := ih (y+1) e he
        exact ⟨hd, hx, by omega, by omega⟩

private theorem west_shape (x y n : Nat) :
    ∀ e, e ∈ westTo x y n →
      e.link.2 = .x0 ∧ e.link.1.2.1 = y ∧ x ≤ e.link.1.1 ∧ e.link.1.1 < x+n := by
  induction n with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [westTo, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨rfl, rfl, by change x ≤ x+n; omega,
          by change x+n < x+(n+1); omega⟩
      · obtain ⟨hd, hy, hlo, hhi⟩ := ih e he
        exact ⟨hd, hy, hlo, by omega⟩

private theorem south_shape (x y n : Nat) :
    ∀ e, e ∈ southTo x y n →
      e.link.2 = .x1 ∧ e.link.1.1 = x ∧ y ≤ e.link.1.2.1 ∧ e.link.1.2.1 < y+n := by
  induction n with
  | zero => intro e he; exact False.elim (List.not_mem_nil he)
  | succ n ih =>
      intro e he
      simp only [southTo, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨rfl, rfl, by change y ≤ y+n; omega,
          by change y+n < y+(n+1); omega⟩
      · obtain ⟨hd, hx, hlo, hhi⟩ := ih e he
        exact ⟨hd, hx, hlo, by omega⟩

private theorem east_links_nodup (x y n : Nat) :
    (eastFrom x y n).map OrientedBF4Link.link |>.Nodup := by
  induction n generalizing x with
  | zero => exact List.nodup_nil
  | succ n ih =>
      simp only [eastFrom, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
        have hs := east_shape (x+1) y n e he
        have hx := hs.2.2.1
        rw [hh] at hx
        change x+1 ≤ x at hx
        omega
      · exact ih (x+1)

private theorem north_links_nodup (x y n : Nat) :
    (northFrom x y n).map OrientedBF4Link.link |>.Nodup := by
  induction n generalizing y with
  | zero => exact List.nodup_nil
  | succ n ih =>
      simp only [northFrom, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
        have hs := north_shape x (y+1) n e he
        have hy := hs.2.2.1
        rw [hh] at hy
        change y+1 ≤ y at hy
        omega
      · exact ih (y+1)

private theorem west_links_nodup (x y n : Nat) :
    (westTo x y n).map OrientedBF4Link.link |>.Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
      simp only [westTo, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
        have hs := west_shape x y n e he
        have hx := hs.2.2.2
        rw [hh] at hx
        change x+n < x+n at hx
        omega
      · exact ih

private theorem south_links_nodup (x y n : Nat) :
    (southTo x y n).map OrientedBF4Link.link |>.Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
      simp only [southTo, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
        have hs := south_shape x y n e he
        have hy := hs.2.2.2
        rw [hh] at hy
        change y+n < y+n at hy
        omega
      · exact ih

private theorem nodup_join (left right : List Z4Link)
    (h : left.Nodup ∧ right.Nodup ∧ ∀ a, a ∈ left → a ∈ right → False) :
    (left ++ right).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨h.1, h.2.1, ?_⟩
  intro a ha b hb he
  cases he
  exact h.2.2 a ha hb

/-- For positive side length, the literal square boundary never repeats an
underlying positive link, even though its west and south sides are traversed
with reverse orientation. -/
theorem squareEdges_links_nodup (side : Nat) (hside : 0 < side) :
    ((squareEdges side).map OrientedBF4Link.link).Nodup := by
  simp only [squareEdges, List.map_append]
  apply nodup_join
  constructor
  · exact east_links_nodup 0 0 side
  constructor
  · apply nodup_join
    constructor
    · exact north_links_nodup side 0 side
    constructor
    · apply nodup_join
      exact ⟨west_links_nodup 0 side side, south_links_nodup 0 0 side, by
        intro a ha hb
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
        obtain ⟨f, hf, hh⟩ := List.mem_map.mp hb
        have he' := west_shape 0 side side e he
        have hf' := south_shape 0 0 side f hf
        have hd := congrArg (fun link : Z4Link => link.2) hh
        change f.link.2 = e.link.2 at hd
        rw [hf'.1, he'.1] at hd
        cases hd⟩
    · intro a ha hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · obtain ⟨f, hf, hh⟩ := List.mem_map.mp hb
        have he' := north_shape side 0 side e he
        have hf' := west_shape 0 side side f hf
        have hd := congrArg (fun link : Z4Link => link.2) hh
        change f.link.2 = e.link.2 at hd
        rw [hf'.1, he'.1] at hd
        cases hd
      · obtain ⟨f, hf, hh⟩ := List.mem_map.mp hb
        have he' := north_shape side 0 side e he
        have hf' := south_shape 0 0 side f hf
        have hx := congrArg (fun link : Z4Link => link.1.1) hh
        change f.link.1.1 = e.link.1.1 at hx
        rw [hf'.2.1, he'.2.1] at hx
        omega
  · intro a ha hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨f, hf, hh⟩ := List.mem_map.mp hb
      have he' := east_shape 0 0 side e he
      have hf' := north_shape side 0 side f hf
      have hd := congrArg (fun link : Z4Link => link.2) hh
      change f.link.2 = e.link.2 at hd
      rw [hf'.1, he'.1] at hd
      cases hd
    · rcases hb with hb | hb
      · obtain ⟨f, hf, hh⟩ := List.mem_map.mp hb
        have he' := east_shape 0 0 side e he
        have hf' := west_shape 0 side side f hf
        have hy := congrArg (fun link : Z4Link => link.1.2.1) hh
        change f.link.1.2.1 = e.link.1.2.1 at hy
        rw [hf'.2.1, he'.2.1] at hy
        omega
      · obtain ⟨f, hf, hh⟩ := List.mem_map.mp hb
        have he' := east_shape 0 0 side e he
        have hf' := south_shape 0 0 side f hf
        have hd := congrArg (fun link : Z4Link => link.2) hh
        change f.link.2 = e.link.2 at hd
        rw [hf'.1, he'.1] at hd
        cases hd

/-- Padding a dyadic square preserves its literal globally distinct link word. -/
theorem paddedSquare_links_nodup (scale width : Nat)
    (hwidth : side scale < width) :
    ((paddedSquare scale width hwidth).edges.map OrientedBF4Link.link).Nodup := by
  rw [paddedSquare_edges]
  exact squareEdges_links_nodup (side scale) (side_positive scale)

/-- The actual fixed-spatial carrier indices of the padded square links are
pairwise distinct. -/
theorem paddedSquare_indices_nodup (scale width : Nat)
    (hwidth : side scale < width) :
    ((paddedSquare scale width hwidth).edges.map
      (fun e => (baseLinks width).idxOf e.link)).Nodup := by
  have h := YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    (baseLinks width).idxOf _ (paddedSquare_links_nodup scale width hwidth) (by
      intro a ha b hb hab
      apply idxOf_injective_on_members
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
        exact (paddedSquare scale width hwidth).physical e he
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
        exact (paddedSquare scale width hwidth).physical e he
      · exact hab)
  simpa only [List.map_map, Function.comp_def] using h

#print axioms squareEdges_links_nodup
#print axioms paddedSquare_links_nodup
#print axioms paddedSquare_indices_nodup

end YMGap.Continuum.BF4DyadicWilsonSquareNodup
