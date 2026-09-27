/-
# Eight colors for literal four-dimensional lattice links

Color a link by its direction and the parity of its base vertex's coordinate
sum.  The four links of every original coordinate plaquette have distinct
colors.  This is finite geometry only; it does not establish a conditional
projection estimate, layer locality, or spatial decay.
-/

import YMGap.Continuum.Z4EvenLinkMinimum

namespace YMGap.Continuum.Z4LinkEightColor

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4EvenLinkMinimum

abbrev Color : Type := Dir4 × Fin 2

/-- Link direction together with base-vertex coordinate-sum parity. -/
def color (link : Z4Link) : Color :=
  (link.2, ⟨height link.1 % 2, Nat.mod_lt _ (by decide)⟩)

/-- A change of one lattice coordinate flips the parity color. -/
theorem color_ne_shift (v : Z4Vertex) (d shift : Dir4) :
    color (v, d) ≠ color (addE v shift, d) := by
  intro h
  have hp := congrArg (fun c : Color => c.2.val) h
  change height v % 2 = height (addE v shift) % 2 at hp
  rw [height_addE] at hp
  omega

/-- Different link directions have different colors regardless of base. -/
theorem color_ne_of_dir_ne (v w : Z4Vertex) (d e : Dir4) (hde : d ≠ e) :
    color (v, d) ≠ color (w, e) := by
  intro h
  exact hde (congrArg Prod.fst h)

/-- All four genuine boundary links of a coordinate plaquette have different
colors; in particular, two distinct same-colored links cannot share a plaquette. -/
theorem face_colors_nodup (face : Z4Plaq) :
    ((edgesOf face).map color).Nodup := by
  let v := face.1
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  have hab : a ≠ b := dirsOf_ne face.2
  have hba : b ≠ a := Ne.symm hab
  have hAB : color (v, a) ≠ color (v, b) := color_ne_of_dir_ne v v a b hab
  have hAC : color (v, a) ≠ color (addE v b, a) := color_ne_shift v a b
  have hAD : color (v, a) ≠ color (addE v a, b) :=
    color_ne_of_dir_ne v (addE v a) a b hab
  have hBC : color (v, b) ≠ color (addE v b, a) :=
    color_ne_of_dir_ne v (addE v b) b a hba
  have hBD : color (v, b) ≠ color (addE v a, b) := color_ne_shift v b a
  have hCD : color (addE v b, a) ≠ color (addE v a, b) :=
    color_ne_of_dir_ne (addE v b) (addE v a) a b hab
  change ([color (v, a), color (v, b), color (addE v b, a),
    color (addE v a, b)] : List Color).Nodup
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hAB, hAC, hAD⟩
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hBC, hBD⟩
  apply List.nodup_cons.mpr
  constructor
  · simpa only [List.mem_singleton] using hCD
  · simp

private theorem eq_of_nodup_map {A B : Type} (f : A → B) :
    ∀ xs : List A, (xs.map f).Nodup →
      ∀ x y : A, x ∈ xs → y ∈ xs → f x = f y → x = y
  | [], _, _, _, hx, _, _ => False.elim (List.not_mem_nil hx)
  | a :: xs, hn, x, y, hx, hy, hxy => by
      have hparts := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exact False.elim (hparts.1 (List.mem_map.mpr ⟨y, hy', hxy.symm⟩))
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact False.elim (hparts.1 (List.mem_map.mpr ⟨x, hx', hxy⟩))
        · exact eq_of_nodup_map f xs hparts.2 x y hx' hy' hxy

/-- Same-colored boundary links of one plaquette must be the same link. -/
theorem same_color_on_face_eq (face : Z4Plaq) (i j : Z4Link)
    (hi : i ∈ edgesOf face) (hj : j ∈ edgesOf face)
    (hc : color i = color j) : i = j := by
  exact eq_of_nodup_map color (edgesOf face) (face_colors_nodup face) i j hi hj hc

/-- The explicit eight possible link colors. -/
def colors : List Color :=
  [(.x0, 0), (.x0, 1), (.x1, 0), (.x1, 1),
   (.x2, 0), (.x2, 1), (.x3, 0), (.x3, 1)]

theorem colors_length : colors.length = 8 := rfl

theorem colors_nodup : colors.Nodup := by decide

theorem color_mem_colors (link : Z4Link) : color link ∈ colors := by
  have hc : ∀ c : Color, c ∈ colors := by
    intro c
    have hp : c.2 = (0 : Fin 2) ∨ c.2 = 1 := by
      have hlt := c.2.isLt
      by_cases h0 : c.2.val = 0
      · left
        apply Fin.ext
        exact h0
      · right
        apply Fin.ext
        omega
    rcases c with ⟨d, p⟩
    cases d <;> rcases hp with rfl | rfl <;> decide
  exact hc (color link)

#print axioms face_colors_nodup
#print axioms same_color_on_face_eq
#print axioms colors_length
#print axioms colors_nodup
#print axioms color_mem_colors

end YMGap.Continuum.Z4LinkEightColor
